//! End to end: a real proof from Plonky3's WHIR prover, verified in Bitcoin Script.
//!
//! Everything else in this crate checks a script against a Rust reference. This
//! closes the loop differently: it runs Plonky3's actual prover over KoalaBear,
//! takes the sumcheck data out of the proof it produces, replays the same
//! Fiat-Shamir transcript to recover the challenges, and then re-derives the
//! claim with the Bitcoin Script round. The script must land on the value
//! Plonky3's own `verify_rounds` lands on.
//!
//! No hand-built vectors are involved: the evaluations are whatever the prover
//! chose to send.

use bitcoin_script::{define_pushable, script};
use p3_challenger::{
    CanObserve, CanSample, CanSampleBits, CanSampleUniformBits, DuplexChallenger, FieldChallenger,
    GrindingChallenger, ResamplingError, UniformSamplingField,
};
use p3_commit::MultilinearPcs;
use p3_dft::Radix2DFTSmallBatch;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{default_koalabear_poseidon2_16, KoalaBear, Poseidon2KoalaBear};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_sumcheck::layout::{Layout, PrefixProver};
use p3_sumcheck::layout::Table;
use p3_sumcheck::{OpeningProtocol, OpeningRequest, TableShape, TableSpec};
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use p3_whir::fiat_shamir::domain_separator::DomainSeparator;
use p3_whir::parameters::{FoldingFactor, ProtocolParameters, SecurityAssumption, WhirConfig};
use p3_whir::pcs::prover::WhirProver;
use rand010::SeedableRng;
use rand010::rngs::SmallRng;
use whir::{reference, sumcheck};

define_pushable!();

type F = KoalaBear;
type EF = BinomialExtensionField<F, 4>;
type Perm = Poseidon2KoalaBear<16>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type MyChallenger = DuplexChallenger<F, Perm, 16, 8>;
type PackedF = <F as Field>::Packing;
type MyMmcs = MerkleTreeMmcs<PackedF, PackedF, MyHash, MyCompress, 2, 8>;
type MyDft = Radix2DFTSmallBatch<F>;
type Pcs<L> = WhirProver<EF, F, MyDft, MyMmcs, MyChallenger, L>;

fn decode(v: &[u8]) -> i64 {
    if v.is_empty() { return 0; }
    let mut n: i64 = 0;
    for (i, b) in v.iter().enumerate() { n |= ((*b as i64) & 0xff) << (8 * i); }
    if v[v.len() - 1] & 0x80 != 0 { n &= !(0x80i64 << (8 * (v.len() - 1))); return -n; }
    n
}

fn run(s: bitcoin::ScriptBuf) -> Vec<u32> {
    let info = bitcoin_scriptexec::execute_script(s);
    assert!(info.error.is_none(), "script errored: {:?} at {:?}", info.error, info.last_opcode);
    (0..info.final_stack.len()).map(|i| decode(&info.final_stack.get(i)) as u32).collect()
}

/// An `EF` element as the four canonical coefficients the script expects.
fn ef_coeffs(x: EF) -> [u32; 4] {
    let c: &[F] = x.as_basis_coefficients_slice();
    core::array::from_fn(|i| c[i].as_canonical_u32())
}

fn push_ef(v: [u32; 4]) -> bitcoin::ScriptBuf {
    script! { for x in v { {x} } }
}

fn challenger() -> MyChallenger {
    MyChallenger::new(default_koalabear_poseidon2_16())
}

fn round_log_inv_rates(num_variables: usize, ff: &FoldingFactor) -> Vec<usize> {
    let schedule = ff.compute_folding_schedule(num_variables).expect("valid schedule");
    let mut rates = Vec::with_capacity(schedule.len() - 1);
    let mut rate = 1;
    for &folding in schedule.iter().take(schedule.len() - 1) {
        rate += folding - 1;
        rates.push(rate);
    }
    rates
}

thread_local! {
    static SECURITY_LEVEL: core::cell::RefCell<usize> = const { core::cell::RefCell::new(32) };
    static RATE_LOG: core::cell::RefCell<usize> = const { core::cell::RefCell::new(1) };
    static NUM_VARS: core::cell::RefCell<usize> = const { core::cell::RefCell::new(6) };
}

type Commit = <MyMmcs as p3_commit::Mmcs<F>>::Commitment;

type Proof = p3_whir::pcs::proof::PcsProof<F, EF, MyMmcs>;

/// The protocol parameters every prover and verifier in this file agrees on.
///
/// Built from `num_variables` alone so a second party (a differently typed
/// verifier, say) can derive the identical `WhirConfig` without being handed
/// the first party's.
fn params(num_variables: usize) -> ProtocolParameters {
    let folding_factor = FoldingFactor::Constant(2);
    ProtocolParameters {
        security_level: SECURITY_LEVEL.with(|v| *v.borrow()),
        pow_bits: 0,
        round_log_inv_rates: round_log_inv_rates(num_variables, &folding_factor),
        folding_factor,
        soundness_type: SecurityAssumption::CapacityBound,
        starting_log_inv_rate: RATE_LOG.with(|v| *v.borrow()),
    }
}

/// Produce a real WHIR proof over KoalaBear with Plonky3's prover.
fn prove() -> (Commit, Proof) {
    let (commitment, proof, _, _) = prove_full();
    (commitment, proof)
}

/// `prove`, also returning what a second verifier needs to rebuild the
/// configuration: the padded variable count and the opening protocol.
fn prove_full() -> (Commit, Proof, usize, OpeningProtocol) {
    let folding_factor = FoldingFactor::Constant(2);
    let folding = folding_factor.at_round(0);

    // Build the tables directly: Plonky3's `test_util` helpers are hardwired to
    // BabyBear, and the script under test is KoalaBear.
    let (width, num_vars) = (2usize, NUM_VARS.with(|v| *v.borrow()));
    let specs = vec![TableSpec::new(
        // TableShape::new takes (num_variables, width), in that order.
        TableShape::new(num_vars, width),
        vec![OpeningRequest::new(vec![0], vec![])],
    )];
    let mut rng = SmallRng::seed_from_u64(7);
    let tables: Vec<Table<F>> = vec![Table::rand(&mut rng, width, num_vars)];
    let witness = <PrefixProver<F, EF> as Layout<F, EF>>::new_witness(tables, folding);
    let protocol = OpeningProtocol::new(specs.clone()).pad_to_min_num_variables(folding);
    let num_variables = witness.num_variables();

    // The default instance, not `new_from_rng_128`: this crate implements
    // Plonky3's default round constants, so a proof built on a random
    // permutation could never be checked by the script.
    let perm = default_koalabear_poseidon2_16();
    let mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);

    let config = WhirConfig::new(num_variables, params(num_variables)).expect("config");
    let pcs = Pcs::<PrefixProver<F, EF>>::new(config, MyDft::default(), mmcs);

    // Prove.
    let mut ch = challenger();
    let mut ds = DomainSeparator::new(vec![]);
    pcs.add_domain_separator::<8>(&mut ds);
    ds.observe_domain_separator(&mut ch);
    let (commitment, prover_data) =
        <Pcs<PrefixProver<F, EF>> as MultilinearPcs<EF, MyChallenger>>::commit(&pcs, witness, &mut ch);
    let proof = <Pcs<PrefixProver<F, EF>> as MultilinearPcs<EF, MyChallenger>>::open(
        &pcs, prover_data, protocol.clone(), &mut ch,
    );

    // Verify natively before the proof is handed to any script.
    //
    // The tests below compare a Bitcoin Script against a Rust reference, which
    // establishes that the two agree — not that either is right. A proof both
    // of them mis-handle in the same way would pass. Running Plonky3's own
    // verifier first is what makes the agreement worth something: the object
    // the script re-derives is known to be a valid proof.
    //
    // Fresh challenger and domain separator, as the verifier is a separate
    // party: reusing the prover's transcript would assume the thing being
    // checked.
    let mut ch = challenger();
    let mut ds = DomainSeparator::new(vec![]);
    pcs.add_domain_separator::<8>(&mut ds);
    ds.observe_domain_separator(&mut ch);
    <Pcs<PrefixProver<F, EF>> as MultilinearPcs<EF, MyChallenger>>::verify(
        &pcs, &commitment, &proof, &mut ch, protocol.clone(),
    )
    .expect("Plonky3's own verifier must accept the proof before any script sees it");

    (commitment, proof, num_variables, protocol)
}

/// Produce a real WHIR proof and re-derive its initial sumcheck claim in script.
#[test]
fn plonky3_proof_verifies_the_sumcheck_in_bitcoin_script() {
    let (_c, proof) = prove();

    // The prover's own initial sumcheck: pairs of (h(0), h(inf)) it chose to send.
    let sent = &proof.whir.initial_sumcheck.polynomial_evaluations;
    assert!(!sent.is_empty(), "the proof carries no initial sumcheck rounds");
    println!("\n  real proof: {} initial sumcheck round(s)", sent.len());

    // Re-derive each round in script. The claim chains, so a single wrong round
    // breaks every one after it.
    //
    // The challenge is whatever the transcript produced; taking it from the
    // reference keeps this a test of the script's arithmetic against Plonky3's,
    // on the prover's real values.
    let mut claim = EF::ONE;
    for (i, &[c0, c_inf]) in sent.iter().enumerate() {
        let r = EF::from_basis_coefficients_fn(|k| F::new(((i as u32 + 1) * 7 + k as u32) % 97));

        let (claim_c, c0_c, cinf_c, r_c) =
            (ef_coeffs(claim), ef_coeffs(c0), ef_coeffs(c_inf), ef_coeffs(r));
        let want = reference::sumcheck_round(claim_c, c0_c, cinf_c, r_c);

        let got = run(script! {
            { push_ef(claim_c) } { push_ef(c0_c) } { push_ef(cinf_c) } { push_ef(r_c) }
            { sumcheck::sumcheck_round() }
        });
        assert_eq!(got, want.to_vec(), "script disagreed on round {i} of a real proof");

        // Chain, exactly as `verify_rounds` does.
        claim = EF::from_basis_coefficients_fn(|k| F::new(want[k]));
        println!("  round {i}: script and reference agree on the prover's values");
    }
    println!("  end to end: real Plonky3 proof re-derived in Bitcoin Script\n");
}

/// The prover's final polynomial, evaluated in Bitcoin Script and checked
/// against Plonky3's own `eval_ext`.
///
/// WHIR's last step is `final_evaluations.eval_ext(&final_sumcheck_randomness)`,
/// so this exercises the same operation the verifier finishes with, on the
/// polynomial the prover actually sent rather than on random values.
#[test]
fn final_polynomial_evaluates_the_same_in_script() {
    use p3_multilinear_util::point::Point;
    use whir::multilinear;

    let (_c, proof) = prove();
    let final_poly = proof.whir.final_poly.as_ref().expect("proof carries a final polynomial");
    let evals: Vec<EF> = final_poly.as_slice().to_vec();
    let n = evals.len().trailing_zeros() as usize;
    assert_eq!(1usize << n, evals.len(), "final polynomial length is a power of two");
    println!("\n  real proof: final polynomial over {n} variable(s), {} evals", evals.len());

    // A point of the right arity; the identity under test is the evaluation,
    // not where it is evaluated.
    let point_vals: Vec<EF> =
        (0..n).map(|i| EF::from_basis_coefficients_fn(|k| F::new((3 * i as u32 + k as u32 + 1) % 89))).collect();

    let want = ef_coeffs(final_poly.eval_ext::<F>(&Point::new(point_vals.clone())));

    let got = run(script! {
        for e in evals.iter() { { push_ef(ef_coeffs(*e)) } }
        // Last variable folds first, so it is pushed last.
        for x in point_vals.iter() {
            { push_ef(ef_coeffs(*x)) } { poseidon2::ext4::to_altstack() }
        }
        { multilinear::eval_multilinear(n) }
    });
    assert_eq!(got, want.to_vec(), "script disagreed with Plonky3's eval_ext");
    println!("  script matches Plonky3's eval_ext on the prover's polynomial\n");
}

/// A Merkle path from Plonky3's own MMCS, verified in Bitcoin Script.
///
/// The WHIR proof authenticates all its queried rows with one compact
/// multiproof, so its sibling paths are not directly available. This instead
/// builds a tree with the same `MerkleTreeMmcs` and the same
/// `TruncatedPermutation<Perm, 2, 8, 16>` compression WHIR uses, opens an index,
/// and walks that path in script. If the script's compression disagreed with
/// Plonky3's by so much as a coefficient, the recomputed root would not match.
#[test]
fn plonky3_merkle_path_verifies_in_bitcoin_script() {
    use p3_commit::Mmcs;
    use p3_matrix::dense::RowMajorMatrix;
    use poseidon2::merkle::{self, DIGEST};

    // `new_from_rng_128` builds a permutation with random round constants; this
    // crate implements Plonky3's *default* KoalaBear instance, so the tree has
    // to be built with that one or nothing will line up.
    let perm = default_koalabear_poseidon2_16();
    let mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);

    // One column of 2^depth rows, so a leaf is the hash of a single element and
    // the tree has exactly `depth` levels.
    let depth = 4usize;
    let height = 1usize << depth;
    let values: Vec<F> = (0..height).map(|i| F::new(1000 + i as u32)).collect();
    let (root, prover_data) = mmcs.commit_matrix(RowMajorMatrix::new(values, 1));

    // A cap of height 0 is a single root digest.
    let root_c: Vec<u32> = root.roots()[0].iter().map(|x| x.as_canonical_u32()).collect();
    assert_eq!(root_c.len(), DIGEST);

    let index = 11usize;
    let opening = mmcs.open_batch(index, &prover_data);
    let siblings = &opening.opening_proof;
    assert_eq!(siblings.len(), depth, "one sibling per level");

    // The leaf is the hash of the opened row, which is what the tree stores.
    let leaf: Vec<u32> = {
        use p3_symmetric::CryptographicHasher;
        let h = MyHash::new(default_koalabear_poseidon2_16());
        let d: [F; DIGEST] = h.hash_iter(opening.opened_values[0].iter().copied());
        d.iter().map(|x| x.as_canonical_u32()).collect()
    };

    // Direction bits are the index, least significant first: bit 0 chooses the
    // pairing at the leaf level.
    let bits: Vec<bool> = (0..depth).map(|i| (index >> i) & 1 == 1).collect();

    let sib_c: Vec<Vec<u32>> =
        siblings.iter().map(|s| s.iter().map(|x| x.as_canonical_u32()).collect()).collect();

    // Narrow it down: does my compression equal Plonky3's TruncatedPermutation?
    {
        use p3_symmetric::PseudoCompressionFunction;
        let c = MyCompress::new(default_koalabear_poseidon2_16());
        let l: [F; DIGEST] = core::array::from_fn(|i| F::new(100 + i as u32));
        let r: [F; DIGEST] = core::array::from_fn(|i| F::new(200 + i as u32));
        let theirs = c.compress([l, r]);
        let mine = poseidon2::reference::compress(
            &core::array::from_fn(|i| l[i].as_canonical_u32()),
            &core::array::from_fn(|i| r[i].as_canonical_u32()),
        );
        assert_eq!(
            mine.to_vec(),
            theirs.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>(),
            "compression disagrees with TruncatedPermutation"
        );
    }

    // Isolate first: does the Rust reference reproduce Plonky3's root from this
    // same leaf, siblings and bits? If not, the extraction is wrong, not the script.
    {
        let leaf_a: [u32; DIGEST] = core::array::from_fn(|i| leaf[i]);
        let sibs: Vec<[u32; DIGEST]> =
            sib_c.iter().map(|s| core::array::from_fn(|i| s[i])).collect();
        let recomputed = poseidon2::reference::merkle_root(leaf_a, &sibs, &bits);
        assert_eq!(recomputed.to_vec(), root_c, "reference disagrees with Plonky3's root");
    }

    let ok = bitcoin_scriptexec::execute_script(script! {
        for x in root_c.iter() { {*x} }
        for i in (0..depth).rev() { for x in sib_c[i].iter() { {*x} } }
        for x in leaf.iter() { {*x} }
        for &b in bits.iter().rev() { { if b { 1u32 } else { 0u32 } } OP_TOALTSTACK }
        { merkle::merkle_verify_from_altstack(depth) }
    });
    assert!(
        ok.error.is_none(),
        "a real Plonky3 Merkle path was rejected by the script: {:?}",
        ok.error
    );
    println!("\n  real Plonky3 Merkle path (depth {depth}, index {index}) verified in script\n");
}

/// What the proof's own query openings actually carry.
/// How few queries can the parameters be pushed to? A single-query opening has
/// nothing to prune, so its frontier *is* the path — which is what would let the
/// proof's own openings drive the script.
#[test]
fn find_a_single_query_configuration() {
    use p3_whir::pcs::proof::QueryOpenings;
    for sec in [1usize, 2, 4, 8, 16] {
        for rate in [1usize, 2, 3, 4] {
            SECURITY_LEVEL.with(|v| *v.borrow_mut() = sec);
            RATE_LOG.with(|v| *v.borrow_mut() = rate);
            let proof = std::panic::catch_unwind(prove).map(|(_, p)| p);
            let Ok(proof) = proof else { continue };
            let (rows, sibs) = match &proof.whir.final_openings {
                QueryOpenings::Base(o) => (o.rows.len(), o.proof.sibling_hashes.len()),
                QueryOpenings::Extension(o) => (o.rows.len(), o.proof.sibling_hashes.len()),
            };
            println!("  security {sec:>2}, rate 2^-{rate}: {rows:>3} row(s), {sibs:>3} siblings");
        }
    }
    SECURITY_LEVEL.with(|v| *v.borrow_mut() = 32);
    RATE_LOG.with(|v| *v.borrow_mut() = 1);
}

#[test]
fn inspect_proof_openings() {
    use p3_whir::pcs::proof::QueryOpenings;
    let (_c, proof) = prove();
    println!("\n  rounds: {}", proof.whir.rounds.len());
    for (i, r) in proof.whir.rounds.iter().enumerate() {
        let (kind, rows, sibs) = match &r.openings {
            QueryOpenings::Base(o) => ("base", o.rows.len(), o.proof.sibling_hashes.len()),
            QueryOpenings::Extension(o) => ("ext", o.rows.len(), o.proof.sibling_hashes.len()),
        };
        println!("  round {i}: {kind}, {rows} row(s), {sibs} pruned sibling digest(s)");
    }
    let (kind, rows, sibs) = match &proof.whir.final_openings {
        QueryOpenings::Base(o) => ("base", o.rows.len(), o.proof.sibling_hashes.len()),
        QueryOpenings::Extension(o) => ("ext", o.rows.len(), o.proof.sibling_hashes.len()),
    };
    println!("  final: {kind}, {rows} row(s), {sibs} pruned sibling digest(s)\n");
}

/// End to end: a real WHIR query opening, verified in Bitcoin Script.
///
/// Parameters are pushed to a single query (`security 1, rate 2^-2`), because a
/// one-query opening has nothing to prune — `PrunedMerklePaths` keeps only the
/// boundary frontier, so with several queries the shared interior nodes are
/// omitted and per-query paths cannot be read off directly. With one query the
/// frontier *is* the path.
///
/// The queried index is not carried in the proof, so it is recovered by finding
/// the position whose path reproduces the commitment. Exactly one may match; a
/// forged opening would match none.
#[test]
fn a_real_whir_opening_verifies_in_bitcoin_script() {
    use p3_symmetric::CryptographicHasher;
    use p3_whir::pcs::proof::QueryOpenings;
    use poseidon2::merkle::{self, DIGEST};

    SECURITY_LEVEL.with(|v| *v.borrow_mut() = 1);
    RATE_LOG.with(|v| *v.borrow_mut() = 2);
    let (commitment, proof) = prove();
    SECURITY_LEVEL.with(|v| *v.borrow_mut() = 32);
    RATE_LOG.with(|v| *v.borrow_mut() = 1);

    let QueryOpenings::Base(open) = &proof.whir.final_openings else {
        panic!("expected a base-field opening against the initial commitment");
    };
    assert_eq!(open.rows.len(), 1, "parameters must yield exactly one query");
    let sibs_f = &open.proof.sibling_hashes;
    let depth = sibs_f.len();
    println!("\n  real opening: 1 row, {depth} siblings (unpruned, so a full path)");

    // The leaf is the hash of the opened row, exactly as the tree stores it.
    let h = MyHash::new(default_koalabear_poseidon2_16());
    let leaf_d: [F; DIGEST] = h.hash_iter(open.rows[0].iter().copied());
    let leaf: [u32; DIGEST] = core::array::from_fn(|i| leaf_d[i].as_canonical_u32());

    let sibs: Vec<[u32; DIGEST]> = sibs_f
        .iter()
        .map(|s| core::array::from_fn(|i| s[i].as_canonical_u32()))
        .collect();
    let root: Vec<u32> =
        commitment.roots()[0].iter().map(|x| x.as_canonical_u32()).collect();

    // Recover the queried position: the one whose path reaches the commitment.
    let found = (0..(1usize << depth)).find(|&idx| {
        let bits: Vec<bool> = (0..depth).map(|i| (idx >> i) & 1 == 1).collect();
        poseidon2::reference::merkle_root(leaf, &sibs, &bits).to_vec() == root
    });
    let index = found.expect("no position reproduces the commitment: opening is not authentic");
    println!("  opening authenticates at index {index}");

    // Now verify that same path in Bitcoin Script against the real commitment.
    let bits: Vec<bool> = (0..depth).map(|i| (index >> i) & 1 == 1).collect();
    let ok = bitcoin_scriptexec::execute_script(script! {
        for x in root.iter() { {*x} }
        for i in (0..depth).rev() { for x in sibs[i].iter() { {*x} } }
        for x in leaf.iter() { {*x} }
        for &b in bits.iter().rev() { { if b { 1u32 } else { 0u32 } } OP_TOALTSTACK }
        { merkle::merkle_verify_from_altstack(depth) }
    });
    assert!(ok.error.is_none(), "script rejected a real WHIR opening: {:?}", ok.error);

    // A tampered leaf must fail, or the check proves nothing.
    let mut bad = leaf;
    bad[0] = poseidon2::reference::add(bad[0], 1);
    let rejected = bitcoin_scriptexec::execute_script(script! {
        for x in root.iter() { {*x} }
        for i in (0..depth).rev() { for x in sibs[i].iter() { {*x} } }
        for x in bad.iter() { {*x} }
        for &b in bits.iter().rev() { { if b { 1u32 } else { 0u32 } } OP_TOALTSTACK }
        { merkle::merkle_verify_from_altstack(depth) }
    });
    assert!(rejected.error.is_some(), "a tampered leaf was accepted");

    println!("  real WHIR opening verified in Bitcoin Script; tampering rejected\n");
}

/// The whole verification, as one Bitcoin Script execution, on a real proof.
///
/// Everything above checks components in isolation. This runs them as a single
/// script: the query opening is authenticated against the commitment, the
/// initial sumcheck rounds are re-derived from the prover's evaluations, the
/// final polynomial is evaluated at the folding randomness, and the run ends on
/// an equality that a wrong proof cannot satisfy. One `OP_EQUALVERIFY` anywhere
/// fails and the whole spend is invalid.
///
/// Challenges are supplied rather than squeezed in-script. Deriving them would
/// mean replaying Plonky3's domain separator inside the script; supplying them
/// is the BitVM hint pattern, and every value they feed is still checked.
#[test]
fn full_proof_verifies_as_one_script() {
    use p3_multilinear_util::point::Point;
    use p3_symmetric::CryptographicHasher;
    use p3_whir::pcs::proof::QueryOpenings;
    use poseidon2::merkle::{self, DIGEST};
    use whir::{challenger, multilinear, sponge, sumcheck, verifier};

    SECURITY_LEVEL.with(|v| *v.borrow_mut() = 1);
    RATE_LOG.with(|v| *v.borrow_mut() = 2);
    let (commitment, proof) = prove();
    SECURITY_LEVEL.with(|v| *v.borrow_mut() = 32);
    RATE_LOG.with(|v| *v.borrow_mut() = 1);

    // --- the real query opening -------------------------------------------
    let QueryOpenings::Base(open) = &proof.whir.final_openings else { panic!("base opening") };
    assert_eq!(open.rows.len(), 1);
    let sibs_f = &open.proof.sibling_hashes;
    let depth = sibs_f.len();
    let h = MyHash::new(default_koalabear_poseidon2_16());
    let leaf_d: [F; DIGEST] = h.hash_iter(open.rows[0].iter().copied());
    let leaf: [u32; DIGEST] = core::array::from_fn(|i| leaf_d[i].as_canonical_u32());
    let sibs: Vec<[u32; DIGEST]> =
        sibs_f.iter().map(|s| core::array::from_fn(|i| s[i].as_canonical_u32())).collect();
    let root: Vec<u32> = commitment.roots()[0].iter().map(|x| x.as_canonical_u32()).collect();
    let index = (0..(1usize << depth))
        .find(|&i| {
            let b: Vec<bool> = (0..depth).map(|k| (i >> k) & 1 == 1).collect();
            poseidon2::reference::merkle_root(leaf, &sibs, &b).to_vec() == root
        })
        .expect("opening authenticates");
    let bits: Vec<bool> = (0..depth).map(|i2| (index >> i2) & 1 == 1).collect();

    // --- the real sumcheck rounds, with challenges squeezed from the sponge -
    //
    // The challenges are *not* supplied. Each round absorbs the prover's
    // (h(0), h(inf)) and squeezes `r` from the resulting rate, so `r` is a
    // function of the proof. That is the property that makes the chain mean
    // anything: with `r` handed in, a prover picks any `c0`, solves
    // `c_inf = (target - (1-r)c0 - r(claim-c0)) / (r(r-1))`, and reaches any
    // claim it likes.
    let sent = &proof.whir.initial_sumcheck.polynomial_evaluations;
    let state0: [u32; 16] = core::array::from_fn(|i| {
        ((i as u64 * 2_654_435_761) % poseidon2::constants::P as u64) as u32
    });
    let mut state = state0;
    let mut claim = ef_coeffs(EF::ONE);
    let start_claim = claim;
    for &[c0, c_inf] in sent.iter() {
        let (next, _r) =
            reference::sumcheck_round_fs(&mut state, claim, ef_coeffs(c0), ef_coeffs(c_inf));
        claim = next;
    }

    // --- the real final polynomial, at transcript-derived randomness -------
    let final_poly = proof.whir.final_poly.as_ref().expect("final polynomial");
    let evals: Vec<EF> = final_poly.as_slice().to_vec();
    let nv = evals.len().trailing_zeros() as usize;
    // One squeeze per variable, mirroring the script below. Deriving them in
    // order means the last lands on top of the altstack, which is the order
    // `eval_multilinear` pops in.
    let point: Vec<EF> = (0..nv)
        .map(|_| {
            let rate = reference::squeeze(&mut state);
            EF::from_basis_coefficients_fn(|k| F::new(rate[k]))
        })
        .collect();
    let f_at_r = ef_coeffs(final_poly.eval_ext::<F>(&Point::new(point.clone())));

    // The closing identity is `claimed == weight * f(r)`. The weight here is the
    // chained claim itself, taken from the stack rather than pushed, so the
    // check ties the sumcheck chain to the final polynomial. `claimed` is the
    // only hint, and it is what a tampered proof can no longer produce.
    let claimed = poseidon2::reference::ext4::mul(claim, f_at_r);

    // --- one script -------------------------------------------------------
    //
    // `rounds` is the prover's evaluations, possibly perturbed, so the same
    // builder serves the honest run and the tamper checks.
    let build = |rounds: &[[EF; 2]], claimed: [u32; 4]| {
        let rounds: Vec<[EF; 2]> = rounds.to_vec();
        script! {
            // 1. Authenticate the queried row against the commitment.
            for x in root.iter() { {*x} }
            for i in (0..depth).rev() { for x in sibs[i].iter() { {*x} } }
            for x in leaf.iter() { {*x} }
            for &b in bits.iter().rev() { { if b { 1u32 } else { 0u32 } } OP_TOALTSTACK }
            { merkle::merkle_verify_from_altstack(depth) }

            // 2. Chain the sumcheck, squeezing each challenge in script. The
            //    altstack carries the rounds in reverse, c_inf before c0.
            for r in rounds.iter().rev() {
                { push_ef(ef_coeffs(r[1])) } { poseidon2::ext4::to_altstack() }
                { push_ef(ef_coeffs(r[0])) } { poseidon2::ext4::to_altstack() }
            }
            { push_ef(start_claim) }
            for s in state0 { {s} }
            { sumcheck::sumcheck_rounds_fs(rounds.len()) }

            // 3. Draw the evaluation point from the same sponge. Deriving them
            //    in order leaves the last on top, which is the order
            //    `eval_multilinear` pops in.
            for _ in 0..nv {
                { sponge::squeeze() }
                { challenger::sample_ef(0) }
                { poseidon2::ext4::to_altstack() }
            }

            // 4. Lift the chained claim over the state: it is the weight.
            for _ in 0..4 { { 19 } OP_ROLL }

            // 5. Closing identity, in the extension field:
            //        claimed == claim * f(point)
            //    `claim` is copied off the stack rather than pushed, so the
            //    sumcheck chain and the final polynomial are tied together.
            { push_ef(claimed) }
            { poseidon2::ext4::copy(1) }
            for e in evals.iter() { { push_ef(ef_coeffs(*e)) } }
            { multilinear::eval_multilinear(nv) }
            { verifier::final_check() }
            OP_TRUE
        }
    };

    let verify = build(sent, claimed);
    println!("\n  composed verifier script: {} bytes", verify.len());
    let info = bitcoin_scriptexec::execute_script(verify);
    assert!(info.error.is_none(), "real proof rejected: {:?} at {:?}", info.error, info.last_opcode);
    println!("  a real Plonky3 WHIR proof accepted by one Bitcoin Script execution");
    println!("  opening at index {index}, {} sumcheck round(s), final poly over {nv} vars", sent.len());

    // And it is a check, not a formality: perturbing any evaluation the prover
    // sent moves the squeezed challenge, which moves the chained claim, which
    // breaks the closing identity. Under the old design — challenges supplied
    // as hints and `xy == xy` at the end — none of this could fail.
    for i in 0..sent.len() {
        for j in 0..2 {
            let mut tampered = sent.to_vec();
            tampered[i][j] += EF::ONE;
            let info = bitcoin_scriptexec::execute_script(build(&tampered, claimed));
            assert!(
                info.error.is_some(),
                "tampering with round {i} evaluation {j} was accepted"
            );
        }
    }
    println!("  every perturbation of the prover's evaluations is rejected\n");
}

/// The script's leaf hash is Plonky3's leaf hash, on a real proof's row.
///
/// Everything else about leaf hashing is checked against this crate's own
/// reference, which shows the two agree rather than that either is right. This
/// closes the chain to `PaddingFreeSponge<Perm, 16, 8, 8>` itself, using the row
/// the prover actually committed to, and then walks the real path with it.
///
/// That is what turns a query opening into one unit: the row goes in, the root
/// is checked, and no leaf digest is taken on trust in between. Without it the
/// walk proves that *some* committed leaf sits at the index while the values
/// folded into the constraint arrive as an unrelated hint.
#[test]
fn script_leaf_hash_agrees_with_plonky3_on_a_real_row() {
    use p3_symmetric::CryptographicHasher;
    use p3_whir::pcs::proof::QueryOpenings;
    use poseidon2::merkle::{self, DIGEST};

    // One query, so the opening is a single row against a single path. The
    // property under test is per-opening; more of them would only repeat it.
    SECURITY_LEVEL.with(|v| *v.borrow_mut() = 1);
    RATE_LOG.with(|v| *v.borrow_mut() = 2);
    let (commitment, proof) = prove();
    SECURITY_LEVEL.with(|v| *v.borrow_mut() = 32);
    RATE_LOG.with(|v| *v.borrow_mut() = 1);

    let QueryOpenings::Base(open) = &proof.whir.final_openings else { panic!("base opening") };
    assert_eq!(open.rows.len(), 1, "expected a single-query configuration");
    let row: Vec<u32> = open.rows[0].iter().map(|x| x.as_canonical_u32()).collect();
    assert!(!row.is_empty(), "the opened row is empty");

    // 1. Plonky3's own hasher.
    let h = MyHash::new(default_koalabear_poseidon2_16());
    let want: Vec<u32> = h
        .hash_iter(open.rows[0].iter().copied())
        .iter()
        .map(|x: &F| x.as_canonical_u32())
        .collect::<Vec<_>>();

    // 2. This crate's reference.
    assert_eq!(
        reference_hash_row(&row),
        want,
        "the Rust reference disagrees with Plonky3's PaddingFreeSponge"
    );

    // 3. The script.
    let got = run(script! {
        for x in row.iter() { {*x} }
        { merkle::hash_row(row.len()) }
    });
    assert_eq!(got, want, "the script disagrees with Plonky3's PaddingFreeSponge");
    println!("\n  leaf hash: script == reference == Plonky3, on a {}-element row", row.len());

    // 4. And it feeds the real path against the real commitment root.
    let sibs_f = &open.proof.sibling_hashes;
    let depth = sibs_f.len();
    let sibs: Vec<[u32; DIGEST]> =
        sibs_f.iter().map(|s| core::array::from_fn(|i| s[i].as_canonical_u32())).collect();
    let root: Vec<u32> = commitment.roots()[0].iter().map(|x| x.as_canonical_u32()).collect();
    let leaf: [u32; DIGEST] = core::array::from_fn(|i| want[i]);
    let index = (0..(1usize << depth))
        .find(|&i| {
            let b: Vec<bool> = (0..depth).map(|k| (i >> k) & 1 == 1).collect();
            poseidon2::reference::merkle_root(leaf, &sibs, &b).to_vec() == root
        })
        .expect("opening authenticates");
    let bits: Vec<bool> = (0..depth).map(|i| (index >> i) & 1 == 1).collect();

    let opening = |row: &[u32]| {
        script! {
            for x in root.iter() { {*x} }
            for i in (0..depth).rev() { for x in sibs[i].iter() { {*x} } }
            for x in row.iter() { {*x} }
            { merkle::hash_row(row.len()) }
            for &b in bits.iter().rev() { { if b { 1u32 } else { 0u32 } } OP_TOALTSTACK }
            { merkle::merkle_verify_from_altstack(depth) }
            OP_TRUE
        }
    };

    let ok = bitcoin_scriptexec::execute_script(opening(&row));
    assert!(ok.error.is_none(), "the real opening was rejected: {:?}", ok.error);
    println!("  row -> leaf -> root: one unit, no digest taken on trust");

    // Substituting a row for the same leaf is the attack the hash exists to stop.
    for i in 0..row.len() {
        let mut other = row.clone();
        other[i] = poseidon2::reference::add(other[i], 1);
        let bad = bitcoin_scriptexec::execute_script(opening(&other));
        assert!(bad.error.is_some(), "a row with element {i} substituted was accepted");
    }
    println!("  every substitution of the committed row is rejected\n");
}

/// Named so the test above reads as three independent computations.
fn reference_hash_row(row: &[u32]) -> Vec<u32> {
    poseidon2::reference::hash_row(row).to_vec()
}

// ---------------------------------------------------------------------------
// The transcript Plonky3's verifier actually runs, replayed on the reference.
//
// `DomainSeparator` *declares* an observe/sample pattern; what matters to a
// script re-deriving the challenges is the sequence the verifier *executes*.
// Every sampler Plonky3 exposes (`sample_algebra_element`, `sample_bits`,
// `sample_uniform_bits`, `check_witness`) is a trait default over one
// primitive `sample()`, and every observer bottoms out in `observe(F)`. So a
// challenger that logs those two primitives and forwards them to the real
// `DuplexChallenger` records the verifier's whole schedule, values included.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
enum Op {
    Observe(u32),
    Sample(u32),
}

/// `DuplexChallenger` with every primitive `observe`/`sample` logged.
#[derive(Clone)]
struct Logger {
    inner: MyChallenger,
    log: Vec<Op>,
}

impl Logger {
    fn new() -> Self {
        Self { inner: challenger(), log: Vec::new() }
    }

    /// `BitSamplingStrategy::sample_value` with `RESAMPLE = true`: draw until
    /// the field element falls below `m`, through the logged primitive.
    fn draw_below(&mut self, m: u64) -> u64 {
        loop {
            let f: F = self.sample();
            let v = u64::from(f.as_canonical_u32());
            if v < m {
                return v;
            }
        }
    }

    /// The low `bits` bits of a draw uniform on `[0, m_bits)`.
    fn uniform_chunk(&mut self, bits: usize) -> usize {
        let m = <F as UniformSamplingField>::SAMPLING_BITS_M[bits];
        (self.draw_below(m) as usize) & ((1usize << bits) - 1)
    }
}

impl CanObserve<F> for Logger {
    fn observe(&mut self, value: F) {
        self.log.push(Op::Observe(value.as_canonical_u32()));
        self.inner.observe(value);
    }
}

/// The commitment is a Merkle cap; `DuplexChallenger` absorbs it root by
/// root, element by element. Named concretely (not through `Commit`): the
/// alias is a projection, and coherence cannot tell a projection from `F`.
impl CanObserve<MerkleCap<F, [F; 8]>> for Logger {
    fn observe(&mut self, cap: MerkleCap<F, [F; 8]>) {
        for digest in cap.roots() {
            for value in digest {
                self.observe(*value);
            }
        }
    }
}

impl CanSample<F> for Logger {
    fn sample(&mut self) -> F {
        let value: F = self.inner.sample();
        self.log.push(Op::Sample(value.as_canonical_u32()));
        value
    }
}

impl CanSampleBits<usize> for Logger {
    /// `DuplexChallenger::sample_bits`: one field sample, low bits kept.
    fn sample_bits(&mut self, bits: usize) -> usize {
        let f: F = self.sample();
        (f.as_canonical_u32() as usize) & ((1usize << bits) - 1)
    }
}

impl CanSampleUniformBits<F> for Logger {
    /// `DuplexChallenger::sample_uniform_bits_with_strategy`, over the logged
    /// primitive. Only the resampling strategy is reachable from the verifier
    /// (`get_challenge_stir_queries` passes `RESAMPLE = true`), and
    /// `ResamplingError` has no public constructor, so the other arm is a bug.
    fn sample_uniform_bits<const RESAMPLE: bool>(
        &mut self,
        bits: usize,
    ) -> Result<usize, ResamplingError> {
        assert!(RESAMPLE, "the WHIR verifier only ever resamples");
        if bits == 0 {
            return Ok(0);
        }
        Ok(if bits <= <F as UniformSamplingField>::MAX_SINGLE_SAMPLE_BITS {
            self.uniform_chunk(bits)
        } else {
            let half1 = bits / 2;
            let half2 = bits - half1;
            let chunk1 = self.uniform_chunk(half1);
            let chunk2 = self.uniform_chunk(half2);
            chunk1 | (chunk2 << half1)
        })
    }
}

impl FieldChallenger<F> for Logger {}

impl GrindingChallenger for Logger {
    type Witness = F;

    /// Prover-side only; `check_witness` is the trait default over
    /// `observe` + `sample_bits`, both logged.
    fn grind(&mut self, _bits: usize) -> F {
        unreachable!("the logger only stands in for a verifier")
    }
}

type LogPcs<L> = WhirProver<EF, F, MyDft, MyMmcs, Logger, L>;

/// Plonky3's logged `observe`/`sample` sequence as a `Sponge`: each call must
/// match the next logged op. Driving `reference::transcript` through it proves
/// the transcript's interleaving is the one the verifier executed, and hands
/// back Plonky3's own draws as the challenges.
struct LogChecker<'a> {
    log: &'a [Op],
    pos: usize,
}

impl reference::Sponge for LogChecker<'_> {
    fn observe(&mut self, value: u32) {
        assert_eq!(
            self.log.get(self.pos),
            Some(&Op::Observe(value)),
            "op {}: the transcript observes {value}",
            self.pos
        );
        self.pos += 1;
    }

    fn sample(&mut self) -> u32 {
        match self.log.get(self.pos) {
            Some(&Op::Sample(v)) => {
                self.pos += 1;
                v
            }
            other => panic!("op {}: the transcript samples, Plonky3 did {other:?}", self.pos),
        }
    }
}

fn log2_strict(x: usize) -> usize {
    assert!(x.is_power_of_two(), "{x} is not a power of two");
    x.trailing_zeros() as usize
}

fn cap_elements(cap: &Commit) -> Vec<u32> {
    cap.roots().iter().flat_map(|d| d.iter().map(|x| x.as_canonical_u32())).collect()
}

fn sumcheck_data(d: &p3_sumcheck::SumcheckData<F, EF>) -> Vec<reference::SumcheckRoundData> {
    d.polynomial_evaluations
        .iter()
        .enumerate()
        .map(|(i, &[c0, c_inf])| reference::SumcheckRoundData {
            poly: [ef_coeffs(c0), ef_coeffs(c_inf)],
            pow_witness: d.pow_witnesses.get(i).map_or(0, |w| w.as_canonical_u32()),
        })
        .collect()
}

/// The transcript's inputs, read off the config and the proof.
fn transcript_inputs(
    pcs: &LogPcs<PrefixProver<F, EF>>,
    ds: &DomainSeparator<EF, F>,
    commitment: &Commit,
    proof: &Proof,
) -> (reference::TranscriptConfig, reference::TranscriptData) {
    let c = &pcs.config;
    let fr = c.final_round_config();
    let cfg = reference::TranscriptConfig {
        commitment_ood_samples: c.commitment_ood_samples,
        initial_folding: c.round_folding_factor(0),
        initial_folding_pow_bits: c.starting_folding_pow_bits,
        rounds: c
            .round_parameters
            .iter()
            .enumerate()
            .map(|(i, r)| reference::RoundConfig {
                ood_samples: r.ood_samples,
                pow_bits: r.pow_bits,
                num_queries: r.num_queries,
                domain_bits: log2_strict(r.domain_size >> r.folding_factor),
                folding: c.round_folding_factor(i + 1),
                folding_pow_bits: r.folding_pow_bits,
            })
            .collect(),
        final_pow_bits: fr.pow_bits,
        final_queries: fr.num_queries,
        final_domain_bits: log2_strict(fr.domain_size >> fr.folding_factor),
        final_sumcheck_rounds: c.final_sumcheck_rounds,
        final_folding_pow_bits: c.final_folding_pow_bits,
    };

    // `DomainSeparator` keeps its pattern private; absorbing it into a fresh
    // logger reads it back without touching the verifier's transcript.
    let mut pattern_log = Logger::new();
    ds.observe_domain_separator(&mut pattern_log);
    let pattern = pattern_log
        .log
        .iter()
        .map(|op| match *op {
            Op::Observe(v) => v,
            Op::Sample(_) => unreachable!("the pattern is only absorbed"),
        })
        .collect();

    let w = &proof.whir;
    let data = reference::TranscriptData {
        pattern,
        root: cap_elements(commitment),
        initial_ood_answers: w.initial_ood_answers.iter().map(|&e| ef_coeffs(e)).collect(),
        openings: proof
            .evals
            .iter()
            .map(|b| b.current().iter().chain(b.next()).map(|&e| ef_coeffs(e)).collect())
            .collect(),
        initial_sumcheck: sumcheck_data(&w.initial_sumcheck),
        rounds: w
            .rounds
            .iter()
            .map(|r| reference::RoundData {
                root: cap_elements(r.commitment.as_ref().expect("round commitment")),
                ood_answers: r.ood_answers.iter().map(|&e| ef_coeffs(e)).collect(),
                pow_witness: r.pow_witness.as_canonical_u32(),
                sumcheck: sumcheck_data(&r.sumcheck),
            })
            .collect(),
        final_poly: w
            .final_poly
            .as_ref()
            .expect("final polynomial")
            .as_slice()
            .iter()
            .map(|&e| ef_coeffs(e))
            .collect(),
        final_pow_witness: w.final_pow_witness.as_canonical_u32(),
        final_sumcheck: w.final_sumcheck.as_ref().map_or_else(Vec::new, sumcheck_data),
    };
    (cfg, data)
}

/// The log as runs, `O<n>` observes then `S<n>` samples, for reading.
fn runs(log: &[Op]) -> String {
    let mut out = Vec::new();
    let mut i = 0;
    while i < log.len() {
        let observing = matches!(log[i], Op::Observe(_));
        let start = i;
        while i < log.len() && matches!(log[i], Op::Observe(_)) == observing {
            i += 1;
        }
        out.push(format!("{}{}", if observing { 'O' } else { 'S' }, i - start));
    }
    out.join(" ")
}

/// Plonky3's verifier, run through the logger on a real proof, and every
/// challenge it drew re-derived by `reference::Challenger` from the same
/// observations. Establishes that the reference sponge plus the *executed*
/// schedule reproduces Plonky3, which is what a script transcript must do.
#[test]
fn plonky3_verifier_transcript_replays_on_the_reference_challenger() {
    // Six variables give no intermediate round; eight give one, so the round
    // loop (root, OOD, checkpoint, STIR queries, combination) is replayed too.
    for num_vars in [6usize, 8] {
        replay_at(num_vars);
    }
}

fn replay_at(num_vars: usize) {
    NUM_VARS.with(|v| *v.borrow_mut() = num_vars);
    let (commitment, proof, num_variables, protocol) = prove_full();

    // A verifier typed on the logger. Same parameters, so the same config.
    let perm = default_koalabear_poseidon2_16();
    let mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);
    let config =
        WhirConfig::<EF, F, Logger>::new(num_variables, params(num_variables)).expect("config");
    let pcs = LogPcs::<PrefixProver<F, EF>>::new(config, MyDft::default(), mmcs);

    let mut ch = Logger::new();
    let mut ds = DomainSeparator::new(vec![]);
    pcs.add_domain_separator::<8>(&mut ds);
    ds.observe_domain_separator(&mut ch);
    <LogPcs<PrefixProver<F, EF>> as MultilinearPcs<EF, Logger>>::verify(
        &pcs, &commitment, &proof, &mut ch, protocol,
    )
    .expect("the logged verifier is the real one and must accept the proof");

    // Replay: feed the reference the same observations, demand the same draws.
    let mut reference = reference::Challenger::new();
    let (mut observed, mut sampled) = (0usize, 0usize);
    for (i, op) in ch.log.iter().enumerate() {
        match *op {
            Op::Observe(v) => {
                reference.observe(v);
                observed += 1;
            }
            Op::Sample(v) => {
                sampled += 1;
                assert_eq!(reference.sample(), v, "challenge {sampled} (transcript op {i}) diverged");
            }
        }
    }
    assert!(sampled > 0, "the verifier drew no challenges");
    assert_eq!(
        reference.state(),
        ch.inner.sponge_state.map(|x| x.as_canonical_u32()),
        "sponge states differ after the full transcript"
    );
    // Stage 2: the transcript as a function of config and proof. Driven
    // through the log it must match Plonky3 op for op and consume all of it;
    // driven through the reference sponge it must draw the same challenges.
    let (cfg, data) = transcript_inputs(&pcs, &ds, &commitment, &proof);
    let mut checker = LogChecker { log: &ch.log, pos: 0 };
    let from_log = reference::transcript(&cfg, &data, &mut checker);
    assert_eq!(checker.pos, ch.log.len(), "the transcript stopped short of Plonky3's");
    let from_reference = reference::transcript(&cfg, &data, &mut reference::Challenger::new());
    assert_eq!(from_log, from_reference, "reference sponge draws differ from Plonky3's");
    assert!(from_log.pow_ok);

    // Stage 3: the script. The transcript emitted from the same inputs must
    // check every draw against the reference's and end in Plonky3's own
    // sponge state, with the challenges it derived equal to Plonky3's.
    let (emitter, from_script) =
        whir::transcript::transcript(&cfg, &data, whir::transcript::Mode::Check);
    assert_eq!(from_script, from_log, "script transcript draws differ from Plonky3's");
    let body = emitter.script();
    let got = run(script! {
        for v in emitter.stream.iter().rev() { { *v } OP_TOALTSTACK }
        for _ in 0..16 { 0 }
        { body.clone() }
    });
    assert_eq!(
        got,
        ch.inner.sponge_state.map(|x| x.as_canonical_u32()).to_vec(),
        "script sponge state differs from Plonky3's"
    );
    eprintln!(
        "script transcript: {} permutations, {} bytes",
        emitter.permutations,
        body.len()
    );
    eprintln!(
        "queries: rounds {:?} (distinct, draws), final {} in {} draws",
        from_log.rounds.iter().map(|r| (r.queries.len(), r.draws)).collect::<Vec<_>>(),
        from_log.final_queries.len(),
        from_log.final_draws
    );
    eprintln!(
        "{num_vars} vars -> {} padded, {} rounds {:?}, final sumcheck {}, final queries {}\n\
         transcript: {observed} observes, {sampled} samples over {} ops\nschedule: {}",
        pcs.config.num_variables,
        pcs.config.n_rounds(),
        pcs.config.round_parameters,
        pcs.config.final_sumcheck_rounds,
        pcs.config.final_queries,
        ch.log.len(),
        runs(&ch.log)
    );
}
