//! A real WHIR proof over `BinaryField128` on the additive domain, with Blake3
//! commitments, checked three ways against Plonky3: its verifier accepts the
//! proof through a challenger that logs every byte; `reference::transcript`
//! reproduces that log op for op and draws the same challenges on the
//! reference sponge; and `reference::verify` accepts the proof and rejects
//! tampers.
//!
//! The prover is configured exactly as `examples/prove_hash_binary` configures
//! WHIR, minus the boolean-trace front end: the committed object is a plain
//! multilinear over `GF(2^128)`.

use p3_binary_field::{BinaryChallenger, BinaryField128, TowerLevel};
use p3_binary_pcs::whir::{BinaryWhirProfile, BooleanWhirDomain, recommended_cap_height};
use p3_blake3::Blake3;
use p3_challenger::{CanObserve, CanSample, HashChallenger};
use p3_commit::MultilinearPcs;
use p3_field::PrimeCharacteristicRing;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_sumcheck::{OpeningProtocol, OpeningRequest, TableShape, TableSpec};
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};
use p3_whir::pcs::proof::QueryOpenings;
use p3_whir::{WhirConfig, WhirProver};
use rand010::SeedableRng;
use rand010::rngs::SmallRng;
use std::sync::{Arc, Mutex};
use whir_gc::reference::{self, Sponge};

type F = BinaryField128;
type Hash = SerializingHasher<Blake3>;
type Compress = CompressionFunctionFromHasher<Blake3, 2, 32>;
type Mmcs = MerkleTreeMmcs<F, u8, Hash, Compress, 2, 32>;
type Inner = HashChallenger<u8, Blake3, 32>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Observe(u8),
    Sample(u8),
}

/// `HashChallenger` with every observed and sampled byte logged. Sampling into
/// a slice is forwarded whole, since `HashChallenger` overrides it, and the
/// bytes it produced are logged in order. The log is shared out, as
/// `BinaryChallenger` keeps its inner challenger private.
#[derive(Clone)]
struct ByteLogger {
    inner: Inner,
    log: Arc<Mutex<Vec<Op>>>,
}

impl CanObserve<u8> for ByteLogger {
    fn observe(&mut self, value: u8) {
        self.log.lock().unwrap().push(Op::Observe(value));
        self.inner.observe(value);
    }
}

impl CanSample<u8> for ByteLogger {
    fn sample(&mut self) -> u8 {
        let v = self.inner.sample();
        self.log.lock().unwrap().push(Op::Sample(v));
        v
    }

    fn sample_into_slice(&mut self, values: &mut [u8]) {
        self.inner.sample_into_slice(values);
        self.log.lock().unwrap().extend(values.iter().map(|&v| Op::Sample(v)));
    }
}

type Challenger = BinaryChallenger<F, ByteLogger>;
type Pcs = WhirProver<F, F, BooleanWhirDomain, Mmcs, Challenger, SuffixProver<F, F>>;
type Proof = p3_whir::pcs::proof::PcsProof<F, F, Mmcs>;
type Commit = <Mmcs as p3_commit::Mmcs<F>>::Commitment;

fn challenger() -> (Challenger, Arc<Mutex<Vec<Op>>>) {
    let log = Arc::new(Mutex::new(Vec::new()));
    let inner = ByteLogger { inner: HashChallenger::new(vec![], Blake3), log: log.clone() };
    (BinaryChallenger::new(inner), log)
}

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

struct Run {
    pcs: Pcs,
    commitment: Commit,
    proof: Proof,
    log: Vec<Op>,
    arity: usize,
}

/// Prove a random `GF(2^128)` multilinear and verify it through the logger.
fn prove_and_log(num_vars: usize, log_inv_rate: usize, folding: usize) -> Run {
    let width = 1usize;
    let specs = vec![TableSpec::new(
        TableShape::new(num_vars, width),
        vec![OpeningRequest::new(vec![0], vec![])],
    )];
    let mut rng = SmallRng::seed_from_u64(11);
    let tables: Vec<Table<F>> = vec![Table::rand(&mut rng, width, num_vars)];
    let witness = <SuffixProver<F, F> as Layout<F, F>>::new_witness(tables, folding);
    let protocol = OpeningProtocol::new(specs).pad_to_min_num_variables(folding);
    let num_variables = witness.num_variables();

    let domain = BooleanWhirDomain::default();
    let config = BinaryWhirProfile::proven_list_decoding(110, log_inv_rate, folding)
        .config::<F, F, Challenger, _>(num_variables, &domain)
        .expect("profile config");
    let cap_height = recommended_cap_height(&config);
    let mmcs = Mmcs::new(Hash::new(Blake3), Compress::new(Blake3), cap_height);
    let pcs = Pcs::new(config, domain, mmcs);

    let (mut ch, _) = challenger();
    let (commitment, prover_data) =
        <Pcs as MultilinearPcs<F, Challenger>>::commit(&pcs, witness, &mut ch).expect("commit");
    let proof = <Pcs as MultilinearPcs<F, Challenger>>::open(&pcs, prover_data, protocol.clone(), &mut ch)
        .expect("open");

    let (mut ch, log) = challenger();
    <Pcs as MultilinearPcs<F, Challenger>>::verify(&pcs, &commitment, &proof, &mut ch, protocol)
        .expect("Plonky3's own verifier must accept the proof");
    let log = log.lock().unwrap().clone();
    Run { pcs, commitment, proof, log, arity: num_vars }
}

// ---------------------------------------------------------------------------
// The reference's inputs, read off the config, the proof and the logged run.
// ---------------------------------------------------------------------------

fn elem_bytes(x: F) -> [u8; 16] {
    x.to_repr().to_le_bytes()
}

fn cap_bytes(cap: &Commit) -> Vec<u8> {
    cap.roots().iter().flat_map(|r| r.iter().copied()).collect()
}

fn sumcheck_data(d: &p3_sumcheck::SumcheckData<F, F>) -> Vec<reference::SumcheckRoundData> {
    d.polynomial_evaluations
        .iter()
        .enumerate()
        .map(|(i, &[c0, c_inf])| reference::SumcheckRoundData {
            poly: [c0, c_inf],
            pow_witness: d.pow_witnesses.get(i).copied().unwrap_or(F::ZERO),
        })
        .collect()
}

fn opening(o: &QueryOpenings<F, F, <Mmcs as p3_commit::Mmcs<F>>::MultiProof>) -> reference::Opening {
    match o {
        QueryOpenings::Base(s) => reference::Opening {
            rows: s.rows.clone(),
            boundaries: s.proof.sibling_hashes.clone(),
        },
        QueryOpenings::Extension(s) => reference::Opening {
            rows: s.rows.clone(),
            boundaries: s.proof.sibling_hashes.clone(),
        },
    }
}

/// A cursor over the logged run, for reading the seeds off it positionally.
struct Cursor<'a> {
    log: &'a [Op],
    pos: usize,
}

impl Cursor<'_> {
    fn observes(&mut self) -> Vec<u8> {
        let mut out = Vec::new();
        while let Some(&Op::Observe(v)) = self.log.get(self.pos) {
            out.push(v);
            self.pos += 1;
        }
        out
    }

    fn samples(&mut self) -> usize {
        let start = self.pos;
        while let Some(&Op::Sample(_)) = self.log.get(self.pos) {
            self.pos += 1;
        }
        self.pos - start
    }

    fn expect_samples(&mut self, n: usize, what: &str) {
        assert_eq!(self.samples(), n, "{what}: sample count");
    }

    /// The observes up to the next sample, which must end with `tail`.
    fn observes_ending_with(&mut self, tail: &[u8], what: &str) -> Vec<u8> {
        let mut block = self.observes();
        assert!(block.ends_with(tail), "{what}: block of {} does not end with the {}-byte message", block.len(), tail.len());
        block.truncate(block.len() - tail.len());
        block
    }

    fn expect_observes(&mut self, values: &[u8], what: &str) {
        assert_eq!(self.observes(), values, "{what}: observed message");
    }
}

fn poly_bytes(r: &reference::SumcheckRoundData, pow_bits: usize) -> Vec<u8> {
    let mut v = elem_bytes(r.poly[0]).to_vec();
    v.extend(elem_bytes(r.poly[1]));
    if pow_bits > 0 {
        v.extend(elem_bytes(r.pow_witness));
    }
    v
}

/// Read a sumcheck's seed and walk its rounds: the seed is what precedes the
/// first round's message; each round then samples `8` PoW bytes when grinding
/// and `16` for the folding randomness.
fn sumcheck_seed(cur: &mut Cursor, rounds: &[reference::SumcheckRoundData], pow_bits: usize, what: &str) -> Vec<u8> {
    let seed = cur.observes_ending_with(&poly_bytes(&rounds[0], pow_bits), what);
    let per_round = if pow_bits > 0 { 8 + 16 } else { 16 };
    cur.expect_samples(per_round, what);
    for r in &rounds[1..] {
        cur.expect_observes(&poly_bytes(r, pow_bits), what);
        cur.expect_samples(per_round, what);
    }
    seed
}

fn inputs(run: &Run) -> (reference::Config, reference::Data) {
    let c: &WhirConfig<F, F, Challenger> = &run.pcs;
    let fr = c.final_round_config();
    let k = c.num_variables();
    // `plan_layout` for one table of width 1: `k = arity`, no selector variables.
    assert_eq!(k, run.arity, "one table of width one has no selector variables");
    let cfg = reference::Config {
        num_variables: k,
        commitment_ood_samples: c.commitment_ood_samples(),
        claims: vec![reference::ClaimShape { row_vars: k, selectors: vec![vec![]] }],
        initial_folding: c.round_folding_factor(0),
        initial_folding_pow_bits: c.starting_folding_pow_bits(),
        rounds: c
            .round_parameters()
            .iter()
            .enumerate()
            .map(|(i, r)| reference::RoundConfig {
                ood_samples: r.ood_samples,
                pow_bits: r.pow_bits,
                num_queries: r.num_queries,
                index_width: r.log_folded_domain_size,
                num_variables: r.num_variables,
                folding: c.round_folding_factor(i + 1),
                folding_pow_bits: r.folding_pow_bits,
            })
            .collect(),
        final_pow_bits: fr.pow_bits,
        final_queries: fr.num_queries,
        final_index_width: fr.log_folded_domain_size,
        final_sumcheck_rounds: c.final_sumcheck_rounds(),
        final_folding_pow_bits: c.final_folding_pow_bits(),
    };

    let w = &run.proof.whir;
    let cap = cap_bytes(&run.commitment);
    let initial_ood_answers = w.initial_ood_answers.clone();
    let openings: Vec<Vec<F>> = run
        .proof
        .evals
        .iter()
        .map(|b| b.current().iter().chain(b.next()).copied().collect())
        .collect();
    let initial_sumcheck = sumcheck_data(&w.initial_sumcheck);
    let final_poly: Vec<F> = w.final_poly.as_ref().expect("final polynomial").as_slice().to_vec();
    let final_sumcheck = w.final_sumcheck.as_ref().map_or_else(Vec::new, sumcheck_data);

    let mut cur = Cursor { log: &run.log, pos: 0 };
    let head = cur.observes();
    let at_cap = head.windows(cap.len()).position(|win| win == cap).expect("the cap is absorbed first");
    let seed_commitment = head[..at_cap].to_vec();
    let mut carry = head[at_cap + cap.len()..].to_vec();
    let mut seed_virtual = Vec::new();
    for &answer in &initial_ood_answers {
        seed_virtual.push(std::mem::take(&mut carry));
        cur.expect_samples(16, "OOD point");
        carry = cur.observes();
        assert!(carry.starts_with(&elem_bytes(answer)), "the OOD answer follows its point");
        carry.drain(..16);
    }
    let mut seed_claim = Vec::new();
    for evals in &openings {
        seed_claim.push(std::mem::take(&mut carry));
        cur.expect_samples(16, "claim point");
        carry = cur.observes();
        let bytes: Vec<u8> = evals.iter().flat_map(|&e| elem_bytes(e)).collect();
        assert!(carry.starts_with(&bytes), "the evaluations follow their point");
        carry.drain(..bytes.len());
    }
    let seed_whir_batching = carry;
    cur.expect_samples(16, "alpha");
    let seed_initial_sumcheck = sumcheck_seed(&mut cur, &initial_sumcheck, cfg.initial_folding_pow_bits, "initial sumcheck");

    let rounds: Vec<reference::RoundData> = w
        .rounds
        .iter()
        .zip(&cfg.rounds)
        .map(|(r, rc)| {
            let cap = cap_bytes(r.commitment.as_ref().expect("round commitment"));
            let sumcheck = sumcheck_data(&r.sumcheck);
            cur.expect_observes(&cap, "round cap");
            for (i, &answer) in r.ood_answers.iter().enumerate() {
                cur.expect_samples(16, "round OOD point");
                let mut expected = elem_bytes(answer).to_vec();
                if i + 1 == r.ood_answers.len() && rc.pow_bits > 0 {
                    expected.extend(elem_bytes(r.pow_witness));
                }
                cur.expect_observes(&expected, "round OOD answer");
            }
            let draws = reference::query_draws(rc.index_width, rc.num_queries);
            cur.expect_samples((if rc.pow_bits > 0 { 8 } else { 0 }) + 8 * draws + 16, "round draws and gamma");
            let seed_sumcheck = sumcheck_seed(&mut cur, &sumcheck, rc.folding_pow_bits, "round sumcheck");
            reference::RoundData {
                cap,
                ood_answers: r.ood_answers.clone(),
                pow_witness: r.pow_witness,
                seed_sumcheck,
                sumcheck,
                opening: opening(&r.openings),
            }
        })
        .collect();

    let mut final_bytes: Vec<u8> = final_poly.iter().flat_map(|&e| elem_bytes(e)).collect();
    if cfg.final_pow_bits > 0 {
        final_bytes.extend(elem_bytes(w.final_pow_witness));
    }
    cur.expect_observes(&final_bytes, "final polynomial");
    let draws = reference::query_draws(cfg.final_index_width, cfg.final_queries);
    cur.expect_samples((if cfg.final_pow_bits > 0 { 8 } else { 0 }) + 8 * draws, "final draws");
    let seed_final_sumcheck = sumcheck_seed(&mut cur, &final_sumcheck, cfg.final_folding_pow_bits, "final sumcheck");
    assert_eq!(cur.pos, run.log.len(), "the run ends with the final sumcheck");

    let data = reference::Data {
        seed_commitment,
        seed_virtual,
        seed_claim,
        seed_whir_batching,
        seed_initial_sumcheck,
        seed_final_sumcheck,
        cap,
        initial_ood_answers,
        openings,
        initial_sumcheck,
        rounds,
        final_poly,
        final_pow_witness: w.final_pow_witness,
        final_sumcheck,
        final_opening: opening(&w.final_openings),
    };
    (cfg, data)
}

/// The logged run as a `Sponge`: each call must match the next logged op.
struct LogChecker<'a> {
    log: &'a [Op],
    pos: usize,
}

impl Sponge for LogChecker<'_> {
    fn observe(&mut self, byte: u8) {
        assert_eq!(self.log.get(self.pos), Some(&Op::Observe(byte)), "op {}: the transcript observes {byte}", self.pos);
        self.pos += 1;
    }

    fn sample(&mut self) -> u8 {
        match self.log.get(self.pos) {
            Some(&Op::Sample(v)) => {
                self.pos += 1;
                v
            }
            other => panic!("op {}: the transcript samples, Plonky3 did {other:?}", self.pos),
        }
    }
}

#[test]
fn reference_matches_plonky3_on_real_binary_whir_proofs() {
    for (num_vars, rate, folding) in [(8usize, 3usize, 4usize), (12, 3, 4)] {
        let run = prove_and_log(num_vars, rate, folding);
        let observed = run.log.iter().filter(|o| matches!(o, Op::Observe(_))).count();
        eprintln!(
            "{num_vars} vars, rate 1/{}, folding {folding}: {observed} bytes observed, {} sampled\nschedule: {}",
            1 << rate,
            run.log.len() - observed,
            runs(&run.log)
        );

        let (cfg, data) = inputs(&run);

        // The transcript, op for op against the log, and the reference sponge.
        let mut checker = LogChecker { log: &run.log, pos: 0 };
        let from_log = reference::transcript(&cfg, &data, &mut checker);
        assert_eq!(checker.pos, run.log.len(), "the transcript stopped short of Plonky3's");
        let from_sponge = reference::transcript(&cfg, &data, &mut reference::Challenger::new());
        assert_eq!(from_log, from_sponge, "reference sponge draws differ from Plonky3's");
        assert!(from_log.pow_ok);

        // The verifier.
        let ok = reference::verify(&cfg, &data).unwrap_or_else(|e| panic!("{num_vars} vars: {e:?}"));
        eprintln!(
            "{num_vars} vars: accepted; queries {:?} + final {}, grinding pow {}/{}",
            ok.challenges.rounds.iter().map(|r| r.queries.len()).collect::<Vec<_>>(),
            ok.challenges.final_queries.len(),
            cfg.initial_folding_pow_bits,
            cfg.final_pow_bits
        );

        // Tampers: a changed message desyncs the transcript and fails at the
        // first check that follows -- the grinding witness, when there is
        // grinding, else the openings; a changed opened row fails its Merkle
        // path.
        let mut bad = data.clone();
        bad.final_poly[0] += F::ONE;
        let e = reference::verify(&cfg, &bad).expect_err("changed final polynomial");
        eprintln!("{num_vars} vars: changed final polynomial -> {e:?}");
        assert!(
            matches!(e, reference::Error::Pow | reference::Error::Merkle { .. } | reference::Error::Opening { .. }),
            "{e:?}"
        );
        let mut bad = data.clone();
        bad.final_opening.rows[0][0] += F::ONE;
        let e = reference::verify(&cfg, &bad).expect_err("changed row");
        eprintln!("{num_vars} vars: changed row -> {e:?}");
        assert!(matches!(e, reference::Error::Merkle { .. }), "{e:?}");
    }
}
