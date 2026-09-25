//! A full binary-field STARK proof -- Plonky3's `p3-multi-stark` over the
//! Boolean WHIR trace commitment, proving Keccak-f permutations -- verified by
//! the reference (`stark` in front of `reference`) and by the circuit.
//!
//! The proof is produced through this test's own `MultiStarkConfig`, whose
//! challenger logs every byte, so the domain-separator seeds can be read off
//! the run and the reference's transcript compared with Plonky3's op for op.

use std::sync::{Arc, Mutex, MutexGuard};

/// The circuit tests hold gigabytes; one at a time.
static HEAVY: Mutex<()> = Mutex::new(());

fn heavy() -> MutexGuard<'static, ()> {
    HEAVY.lock().unwrap_or_else(|e| e.into_inner())
}

use p3_air::{AirLayout, BaseAir, get_symbolic_constraints};
use p3_binary_field::{BinaryChallenger, BinaryField2, BinaryField128, TowerLevel};
use p3_binary_pcs::whir::{
    BinaryWhirProfile, BooleanWhirDomain, BooleanWhirPcs, BooleanWhirProver, BooleanWhirTracePcs,
    recommended_cap_height,
};
use p3_blake3::Blake3;
use p3_challenger::{CanObserve, CanSample, HashChallenger};
use p3_field::PrimeCharacteristicRing;
use p3_keccak_air::{KeccakBinaryAir, NUM_KECCAK_BINARY_COLS};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_multi_stark::config::{MultiStarkConfig, ProverData};
use p3_multi_stark::verifier::verify;
use p3_multi_stark::{MultiStarkProof, ProverInstance, ProverInstances, VerifierInstance, VerifierInstances, prove, setup};
use p3_sumcheck::TableShape;
use p3_sumcheck::layout::{Table, plan_stacked_layout};
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};
use p3_whir::pcs::proof::QueryOpenings;
use p3_whir::{WhirConfig, WhirProver};
use garbled_snark_verifier::circuits::sect233k1::builder::CircuitTrait;
use whir_gc::circuit;
use whir_gc::reference::{self, Sponge};
use whir_gc::stark;
use whir_gc::stark_circuit;
use garbled_snark_verifier::circuits::sect233k1::stream::{Plan, Streaming, ValuedBuilder};

type F = BinaryField128;
type Hash = SerializingHasher<Blake3>;
type Compress = CompressionFunctionFromHasher<Blake3, 2, 32>;
type Mmcs = MerkleTreeMmcs<F, u8, Hash, Compress, 2, 32>;
type Inner = HashChallenger<u8, Blake3, 32>;
type Challenger = BinaryChallenger<F, ByteLogger>;
type TracePcs = BooleanWhirTracePcs<F, BooleanWhirDomain, Mmcs, Challenger>;
type Commit = <Mmcs as p3_commit::Mmcs<F>>::Commitment;

/// The harness's transcript prefix (`p3-examples`' `binary_challenger`).
const INITIAL_STATE: &[u8] = b"p3-examples-binary-hash-air-v1";

// ---------------------------------------------------------------------------
// A byte-logging challenger (as in `binary_whir.rs`).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Observe(u8),
    Sample(u8),
}

#[derive(Clone)]
struct ByteLogger {
    inner: Inner,
    log: Arc<Mutex<Vec<Op>>>,
    logging: bool,
}

impl CanObserve<u8> for ByteLogger {
    fn observe(&mut self, value: u8) {
        if self.logging {
            self.log.lock().unwrap().push(Op::Observe(value));
        }
        self.inner.observe(value);
    }
}

impl CanSample<u8> for ByteLogger {
    fn sample(&mut self) -> u8 {
        let v = self.inner.sample();
        if self.logging {
            self.log.lock().unwrap().push(Op::Sample(v));
        }
        v
    }

    fn sample_into_slice(&mut self, values: &mut [u8]) {
        self.inner.sample_into_slice(values);
        if self.logging {
            self.log.lock().unwrap().extend(values.iter().map(|&v| Op::Sample(v)));
        }
    }
}

/// The harness's challenger: the initial state, logged as observed bytes when
/// logging (the reference starts empty and absorbs them as part of the seed).
fn challenger(logging: bool) -> (Challenger, Arc<Mutex<Vec<Op>>>) {
    let log = Arc::new(Mutex::new(Vec::new()));
    if logging {
        log.lock().unwrap().extend(INITIAL_STATE.iter().map(|&b| Op::Observe(b)));
    }
    let inner = ByteLogger { inner: HashChallenger::new(INITIAL_STATE.to_vec(), Blake3), log: log.clone(), logging };
    (BinaryChallenger::new(inner), log)
}

/// The reference's sponge with its ops recorded, to compare with Plonky3's run.
struct Recorder {
    inner: reference::Challenger,
    log: Vec<Op>,
}

impl Sponge for Recorder {
    fn observe(&mut self, byte: u8) {
        self.log.push(Op::Observe(byte));
        self.inner.observe(byte);
    }
    fn sample(&mut self) -> u8 {
        let v = self.inner.sample();
        self.log.push(Op::Sample(v));
        v
    }
}

// ---------------------------------------------------------------------------
// The configuration: Plonky3's Boolean WHIR trace PCS under the logging challenger.
// ---------------------------------------------------------------------------

struct Cfg {
    pcs: TracePcs,
}

impl MultiStarkConfig for Cfg {
    type Val = F;
    type Challenge = F;
    type Challenger = Challenger;
    type Pcs = TracePcs;

    fn pcs(&self) -> &TracePcs {
        &self.pcs
    }

    fn collision_resistance_bits(&self) -> Option<usize> {
        Some(128)
    }

    fn min_num_variables(&self) -> usize {
        1
    }

    fn build_witness(&self, tables: Vec<Table<F>>) -> Vec<Table<F>> {
        tables
    }

    fn committed_table<'a>(&self, prover_data: &'a ProverData<Self>, table_index: usize) -> &'a Table<F> {
        prover_data.table(table_index)
    }
}

struct Params {
    log_height: usize,
    log_inv_rate: usize,
    folding: usize,
    term_bits: usize,
}

fn whir_config(p: &Params, packed: usize) -> WhirConfig<F, F, Challenger> {
    BinaryWhirProfile::proven_list_decoding(p.term_bits, p.log_inv_rate, p.folding)
        .config::<F, F, Challenger, _>(packed, &BooleanWhirDomain::default())
        .expect("profile config")
}

fn config(p: &Params) -> (Cfg, usize) {
    config_with(p, |packed| whir_config(p, packed))
}

/// `config` with the WHIR schedule chosen by `whir` from the packed variables.
fn config_with(p: &Params, whir: impl FnOnce(usize) -> WhirConfig<F, F, Challenger>) -> (Cfg, usize) {
    let shape = TableShape::new(p.log_height, NUM_KECCAK_BINARY_COLS);
    let (arity, _) = plan_stacked_layout(&[shape]);
    let packed = arity - stark::ABSORBED;
    let whir = whir(packed);
    let cap_height = recommended_cap_height(&whir);
    let mmcs = Mmcs::new(Hash::new(Blake3), Compress::new(Blake3), cap_height);
    let prover: BooleanWhirProver<F, BooleanWhirDomain, Mmcs, Challenger> =
        WhirProver::new(whir, BooleanWhirDomain::default(), mmcs);
    let pcs = BooleanWhirPcs::new(prover, arity).expect("boolean whir pcs");
    (Cfg { pcs: BooleanWhirTracePcs::from_commitment(pcs) }, packed)
}

struct Run {
    proof: MultiStarkProof<Cfg>,
    log: Vec<Op>,
    packed: usize,
    whir: WhirConfig<F, F, Challenger>,
}

/// Prove `2^log_height` rows of Keccak-f (`floor(2^log_height / 25)`
/// permutations) and verify with Plonky3, logging the verifier's run.
fn prove_and_log(p: &Params) -> Run {
    let air = KeccakBinaryAir::assuming_boolean_trace();
    let (cfg, packed) = config(p);
    let rows = 1usize << p.log_height;
    let num_hashes = rows / 25;
    assert!(num_hashes >= 1, "at least 32 rows for one permutation");
    let words = air.generate_random_trace_packed::<BinaryField2>(num_hashes);
    let table = Table::<F>::from_packed_bits(words, p.log_height);

    let (mut ch, _) = challenger(false);
    let (pk, vk) = setup(&cfg, &[&air], &mut ch).expect("setup");
    let (mut ch, _) = challenger(false);
    let instances = ProverInstances::new(vec![ProverInstance::new(&air, table, &pk, &[])]);
    let t = std::time::Instant::now();
    let proof = prove(&cfg, instances, 0, &mut ch).expect("prove");
    eprintln!("proved 2^{} rows ({num_hashes} Keccak-f) in {:.1?}", p.log_height, t.elapsed());

    let bytes = postcard::to_allocvec(&proof).expect("serialize");
    let opened = proof.opening.values.len() * 16;
    let whir_bytes = postcard::to_allocvec(&proof.opening.opening.opening).expect("serialize").len();
    eprintln!(
        "proof: {} bytes ({:.1} KiB): opened values {} B, WHIR opening {} B, ring switch and zerocheck {} B",
        bytes.len(),
        bytes.len() as f64 / 1024.0,
        opened,
        whir_bytes,
        bytes.len() - opened - whir_bytes
    );
    let (mut ch, log) = challenger(true);
    let instances = VerifierInstances::new(vec![VerifierInstance::new(&air, &vk, p.log_height, &[])]);
    verify(&cfg, instances, &proof, 0, &mut ch).expect("Plonky3's verifier must accept its own proof");
    let log = log.lock().unwrap().clone();
    Run { proof, log, packed, whir: whir_config(p, packed) }
}

// ---------------------------------------------------------------------------
// Reading the run: the proof's messages and the seeds between them.
// ---------------------------------------------------------------------------

fn elem_bytes(x: F) -> [u8; 16] {
    x.to_repr().to_le_bytes()
}

fn elems_bytes(xs: &[F]) -> Vec<u8> {
    xs.iter().flat_map(|&x| elem_bytes(x)).collect()
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
        QueryOpenings::Base(s) => reference::Opening { rows: s.rows.clone(), boundaries: s.proof.sibling_hashes.clone() },
        QueryOpenings::Extension(s) => reference::Opening { rows: s.rows.clone(), boundaries: s.proof.sibling_hashes.clone() },
    }
}

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
        assert_eq!(self.samples(), n, "{what}: sample count at op {}", self.pos);
    }

    fn observes_ending_with(&mut self, tail: &[u8], what: &str) -> Vec<u8> {
        let mut block = self.observes();
        assert!(
            block.ends_with(tail),
            "{what}: block of {} bytes does not end with the {}-byte message (op {})",
            block.len(),
            tail.len(),
            self.pos
        );
        block.truncate(block.len() - tail.len());
        block
    }

    fn expect_observes(&mut self, values: &[u8], what: &str) {
        assert_eq!(self.observes(), values, "{what}: observed message at op {}", self.pos);
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

/// The position of `needle` in `hay`, which must occur exactly once.
fn find(hay: &[u8], needle: &[u8], what: &str) -> usize {
    let hits: Vec<usize> = hay.windows(needle.len()).enumerate().filter(|(_, w)| *w == needle).map(|(i, _)| i).collect();
    assert_eq!(hits.len(), 1, "{what}: expected exactly one occurrence, found {}", hits.len());
    hits[0]
}

#[derive(Clone)]
struct Inputs {
    scfg: stark::Config,
    sdata: stark::Data,
    wcfg: reference::Config,
    wdata: reference::Data,
    air: stark::Air,
}

fn inputs(p: &Params, run: &Run) -> Inputs {
    let n = p.log_height;
    let width = NUM_KECCAK_BINARY_COLS;
    let c: &WhirConfig<F, F, Challenger> = &run.whir;
    let fr = c.final_round_config();
    let k = c.num_variables();
    assert_eq!(k, run.packed);

    let air = KeccakBinaryAir::assuming_boolean_trace();
    let layout = AirLayout::from_air::<F>(&air);
    let air_spec = stark::Air { width: BaseAir::<F>::width(&air), constraints: get_symbolic_constraints::<F, _>(&air, layout) };
    assert_eq!(air_spec.width, width);

    let wcfg = reference::Config {
        num_variables: k,
        commitment_ood_samples: c.commitment_ood_samples(),
        given_points: true,
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

    // The proof's messages.
    let proof = &run.proof;
    let red = &proof.opening.opening.reductions;
    assert_eq!(red.len(), 1, "one ring switch");
    let red = &red[0];
    let sdata = stark::Data {
        claimed_sum: proof.sumcheck.claimed_sum,
        round_polys: proof
            .sumcheck
            .round_polys
            .iter()
            .map(|p| <[F; 4]>::try_from(p.as_slice()).expect("degree-4 rounds carry 4 values"))
            .collect(),
        pow_witnesses: proof.sumcheck.pow_witnesses.clone(),
        values: proof.opening.values.clone(),
        tensor: red.tensor.rows().to_vec(),
        successor: red.successor.as_ref().map(|s| (s.carry.rows().to_vec(), s.last.rows().to_vec())),
        rs_sumcheck: red.sumcheck.polynomial_evaluations.clone(),
        final_eval: red.final_eval,
    };
    assert!(red.sumcheck.pow_witnesses.is_empty());
    let pcs_proof = &proof.opening.opening.opening;
    let w = &pcs_proof.whir;
    let cap = cap_bytes(&proof.commitment);
    let initial_ood_answers = w.initial_ood_answers.clone();
    let openings: Vec<Vec<F>> =
        pcs_proof.evals.iter().map(|b| b.current().iter().chain(b.next()).copied().collect()).collect();
    assert_eq!(openings, vec![vec![red.final_eval]], "WHIR opens the surviving claim");
    let initial_sumcheck = sumcheck_data(&w.initial_sumcheck);
    let final_poly: Vec<F> = w.final_poly.as_ref().expect("final polynomial").as_slice().to_vec();
    let final_sumcheck = w.final_sumcheck.as_ref().map_or_else(Vec::new, sumcheck_data);

    let mut scfg = stark::Config { log_height: n, width, pow_bits: 0, seeds: Default::default() };
    let column_vars = scfg.column_vars();
    let packed = scfg.packed_vars();
    assert_eq!(packed, k);

    // Walk the run.
    let mut cur = Cursor { log: &run.log, pos: 0 };
    let head = cur.observes();
    let at_cap = find(&head, &cap, "the commitment cap");
    let seed_commitment = head[..at_cap].to_vec();
    scfg.seeds.zerocheck = head[at_cap + cap.len()..].to_vec();
    let drawn = cur.samples();
    assert!(drawn % 16 == 0 && drawn >= 16 * (2 + n), "alpha, beta and {n} nonzero tau");
    let round0 = elems_bytes(&sdata.round_polys[0]);
    let mut block = cur.observes_ending_with(&round0, "generic-degree round 0");
    assert!(block.ends_with(&elem_bytes(sdata.claimed_sum)), "the claimed sum precedes round 0");
    block.truncate(block.len() - 16);
    scfg.seeds.generic_degree = block;
    cur.expect_samples(16, "r_0");
    for poly in &sdata.round_polys[1..] {
        cur.expect_observes(&elems_bytes(poly), "generic-degree round");
        cur.expect_samples(16, "r_i");
    }
    // Column batching: the row point is sampled, so it is what the block ends
    // with after the values; take the seed as everything before `n` elements
    // plus the values.
    let values_bytes = elems_bytes(&sdata.values);
    let mut block = cur.observes_ending_with(&values_bytes, "the opened values");
    block.truncate(block.len() - 16 * n);
    scfg.seeds.column_batching = block;
    cur.expect_samples(16 * column_vars, "the column point");
    let mut tensors = elems_bytes(&sdata.tensor);
    if let Some((carry, last)) = &sdata.successor {
        tensors.extend(elems_bytes(carry));
        tensors.extend(elems_bytes(last));
    }
    let mut block = cur.observes_ending_with(&tensors, "the ring switch tensors");
    block.truncate(block.len() - 16 * (column_vars + n));
    scfg.seeds.ring_switch = block;
    cur.expect_samples(16 * (stark::ABSORBED + usize::from(scfg.sends_successor())), "r_batch and alpha");
    assert_eq!(sdata.rs_sumcheck.len(), packed, "no Boolean prefix on the column point");
    let round0 = elems_bytes(&sdata.rs_sumcheck[0]);
    scfg.seeds.quadratic = cur.observes_ending_with(&round0, "ring switch round 0");
    cur.expect_samples(16, "r'_0");
    for poly in &sdata.rs_sumcheck[1..] {
        cur.expect_observes(&elems_bytes(poly), "ring switch round");
        cur.expect_samples(16, "r'_i");
    }
    // The surviving claim, then the WHIR statement.
    let block = cur.observes();
    assert!(block.starts_with(&elem_bytes(sdata.final_eval)), "the final evaluation follows the sumcheck");
    let mut carry = block[16..].to_vec();
    let mut seed_virtual = Vec::new();
    for &answer in &initial_ood_answers {
        seed_virtual.push(std::mem::take(&mut carry));
        cur.expect_samples(16, "OOD point");
        carry = cur.observes();
        assert!(carry.starts_with(&elem_bytes(answer)), "the OOD answer follows its point");
        carry.drain(..16);
    }
    let eval = elems_bytes(&openings[0]);
    let at_eval = find(&carry, &eval, "the claimed evaluation");
    let seed_claim = vec![carry[..at_eval].to_vec()];
    let seed_whir_batching = carry[at_eval + eval.len()..].to_vec();
    cur.expect_samples(16, "alpha");
    let seed_initial_sumcheck = sumcheck_seed(&mut cur, &initial_sumcheck, wcfg.initial_folding_pow_bits, "initial sumcheck");

    let rounds: Vec<reference::RoundData> = w
        .rounds
        .iter()
        .zip(&wcfg.rounds)
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

    let mut final_bytes = elems_bytes(&final_poly);
    if wcfg.final_pow_bits > 0 {
        final_bytes.extend(elem_bytes(w.final_pow_witness));
    }
    cur.expect_observes(&final_bytes, "final polynomial");
    let draws = reference::query_draws(wcfg.final_index_width, wcfg.final_queries);
    cur.expect_samples((if wcfg.final_pow_bits > 0 { 8 } else { 0 }) + 8 * draws, "final draws");
    let seed_final_sumcheck = sumcheck_seed(&mut cur, &final_sumcheck, wcfg.final_folding_pow_bits, "final sumcheck");
    assert_eq!(cur.pos, run.log.len(), "the run ends with the final sumcheck");

    let wdata = reference::Data {
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
    Inputs { scfg, sdata, wcfg, wdata, air: air_spec }
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

/// Rate 1/32, folding 4, 110 bits per WHIR term; `WHIR_GC_TERM_BITS` overrides
/// the per-term target (for example about 200 for a quantum target of 100 bits).
fn params(log_height: usize) -> Params {
    let term_bits = std::env::var("WHIR_GC_TERM_BITS").ok().map_or(110, |s| s.parse().expect("term bits"));
    Params { log_height, log_inv_rate: 5, folding: 4, term_bits }
}

/// The reference accepts real Keccak-f proofs, its transcript matching
/// Plonky3's byte for byte, and rejects a proof with an opened value changed.
#[test]
fn reference_verifies_real_keccak_stark_proofs() {
    for log_height in [5usize, 8] {
        let p = params(log_height);
        let run = prove_and_log(&p);
        let inp = inputs(&p, &run);
        eprintln!(
            "2^{log_height} rows: {} constraints, {} packed variables, cap of {}, queries {:?} + final {}",
            inp.air.constraints.len(),
            inp.wcfg.num_variables,
            inp.wdata.cap.len() / 32,
            inp.wcfg.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
            inp.wcfg.final_queries
        );

        // Op for op against Plonky3's run.
        let mut rec = Recorder { inner: reference::Challenger::new(), log: Vec::new() };
        let mut sch = None;
        reference::transcript_with(&inp.wcfg, &inp.wdata, &mut rec, |s| {
            let ch = stark::prefix(&inp.scfg, &inp.sdata, s);
            let point = ch.surviving.clone();
            sch = Some(ch);
            vec![point]
        });
        let first_diff = rec.log.iter().zip(&run.log).position(|(a, b)| a != b);
        assert_eq!(first_diff, None, "the reference's transcript diverges from Plonky3's at op {first_diff:?}");
        assert_eq!(rec.log.len(), run.log.len(), "the reference's transcript is as long as Plonky3's");

        // The checks.
        let sch = sch.expect("prefix ran");
        stark::check(&inp.scfg, &inp.sdata, &inp.air, &sch).expect("the STARK layers accept");
        let mut sch2 = None;
        let ok = reference::verify_with(&inp.wcfg, &inp.wdata, |s| {
            let ch = stark::prefix(&inp.scfg, &inp.sdata, s);
            let point = ch.surviving.clone();
            sch2 = Some(ch);
            vec![point]
        })
        .expect("WHIR accepts the surviving claim");
        assert_eq!(ok.final_value, ok.final_value);

        // A changed opened value: the zerocheck, the ring switch or WHIR must reject.
        let mut bad = inp.sdata.clone();
        bad.values[7] += F::ONE;
        let mut bch = None;
        let whir = reference::verify_with(&inp.wcfg, &inp.wdata, |s| {
            let ch = stark::prefix(&inp.scfg, &bad, s);
            let point = ch.surviving.clone();
            bch = Some(ch);
            vec![point]
        });
        let stark_ok = stark::check(&inp.scfg, &bad, &inp.air, &bch.expect("prefix ran"));
        assert!(stark_ok.is_err() || whir.is_err(), "a changed value must be rejected");
        eprintln!("2^{log_height} rows: changed value rejected by {:?} / WHIR {}", stark_ok.err(), whir.is_err());
    }
}

/// The full verifier circuit on any backend: the STARK inputs first, then the
/// WHIR inputs, then the gates. The query indices the Merkle paths are
/// expanded for come from `honest`'s run, so that a tampered `inp` (whose
/// transcript moves the queries) still gets paths to walk and is rejected by
/// the circuit's own checks.
fn build_full<T: ValuedBuilder>(b: &mut T, inp: &Inputs, honest: &Inputs) -> (circuit::Shape, Vec<bool>) {
    let sin = stark_circuit::Inputs::allocate(b, &inp.sdata);
    let ch = reference::transcript_with(&honest.wcfg, &honest.wdata, &mut reference::Challenger::new(), |s| {
        vec![stark::prefix(&honest.scfg, &honest.sdata, s).surviving]
    });
    let shape = circuit::build_with_prefix(b, &inp.wcfg, &inp.wdata, &ch, |b, s, checks, profile| {
        stark_circuit::run(b, s, &inp.scfg, &inp.air, &sin, checks, profile)
    });
    let mut witness = sin.witness.clone();
    witness.extend(&shape.witness);
    (shape, witness)
}

fn streamed_case(log_height: usize) {
    let _heavy = heavy();
    let p = params(log_height);
    let run = prove_and_log(&p);
    let inp = inputs(&p, &run);

    let t = std::time::Instant::now();
    let mut plan = Plan::new();
    build_full(&mut plan, &inp, &inp);
    let plan_time = t.elapsed();
    let plan_wires = plan.wires();

    let t = std::time::Instant::now();
    let mut s = Streaming::planned(plan, false);
    let (shape, witness) = build_full(&mut s, &inp, &inp);
    let build_time = t.elapsed();
    assert!(s.value(shape.output), "2^{log_height} rows: the full verifier circuit accepts");
    assert_eq!(s.wires(), plan_wires);
    let counts = s.gate_counts();
    eprintln!(
        "2^{log_height} rows, {} columns, {} packed variables: {} non-free gates ({} AND, {} OR), {} XOR, {} wires, {} inputs; planned in {:.1?}; garbled {} MB in {:.1?} with {} live slots at peak",
        NUM_KECCAK_BINARY_COLS,
        inp.wcfg.num_variables,
        s.non_free_gates(),
        counts.direct_and,
        counts.direct_or,
        counts.direct_xor,
        s.wires(),
        witness.len(),
        plan_time,
        s.non_free_gates() * 16 / 1_000_000,
        build_time,
        s.peak_live(),
    );
    assert_eq!(shape.profile.total(), s.non_free_gates());
    eprintln!("{}", shape.profile);

    if log_height <= 8 {
        // A changed opened value is rejected by the circuit.
        let mut bad = inp.clone();
        bad.sdata.values[7] += F::ONE;
        let mut plan = Plan::new();
        build_full(&mut plan, &bad, &inp);
        let mut s = Streaming::planned(plan, false);
        let (shape, _) = build_full(&mut s, &bad, &inp);
        assert!(!s.value(shape.output), "2^{log_height} rows: a changed value is rejected");
    }
}

/// The full verifier -- zerocheck, column batching, ring switch, WHIR -- as
/// a circuit, streamed through the garbler on small real proofs.
#[test]
fn full_verifier_circuit_accepts_real_keccak_stark_proofs() {
    for log_height in [5usize, 8] {
        streamed_case(log_height);
    }
}

/// The 2^18 schedule of the full verifier; run on its own under a memory cap.
#[test]
#[ignore]
fn full_verifier_circuit_on_the_2_18_schedule() {
    let log_height = std::env::var("WHIR_GC_LOG_HEIGHT").ok().map_or(18, |s| s.parse().expect("a log height"));
    streamed_case(log_height);
}

/// The same full verifier as a stored circuit (`CircuitAdapter`), for the
/// memory comparison with the streaming garbler: build it, evaluate it on the
/// honest witness, report its size. `WHIR_GC_LOG_HEIGHT` sets the trace height.
#[test]
#[ignore]
fn stored_build_of_the_full_verifier() {
    use garbled_snark_verifier::circuits::sect233k1::builder::CircuitAdapter;
    let _heavy = heavy();
    let log_height = std::env::var("WHIR_GC_LOG_HEIGHT").ok().map_or(5, |s| s.parse().expect("a log height"));
    let p = params(log_height);
    let run = prove_and_log(&p);
    let inp = inputs(&p, &run);
    let t = std::time::Instant::now();
    let mut b = CircuitAdapter::default();
    let (shape, witness) = build_full(&mut b, &inp, &inp);
    let build_time = t.elapsed();
    let counts = b.gate_counts();
    let wires = b.eval_gates(&witness);
    assert!(wires[shape.output], "2^{log_height} rows: the stored circuit accepts");
    eprintln!(
        "stored 2^{log_height} rows: {} AND, {} OR, {} XOR, {} wires; built in {:.1?}",
        counts.direct_and,
        counts.direct_or,
        counts.direct_xor,
        b.next_wire(),
        build_time
    );
}

/// The WHIR schedule of a configuration: queries and proof-of-work bits per
/// round, for the post-quantum analysis (grinding is what Grover speeds up).
#[test]
#[ignore]
fn whir_schedule_of_the_measured_configurations() {
    for log_height in [5usize, 8, 12, 16, 18, 20] {
        let p = params(log_height);
        let (_cfg, packed) = config(&p);
        let w = whir_config(&p, packed);
        eprintln!(
            "2^{log_height} rows, {packed} packed variables: starting folding pow {}, commitment OOD {}, folding {:?}",
            w.starting_folding_pow_bits(),
            w.commitment_ood_samples(),
            w.folding_schedule()
        );
        for (i, r) in w.round_parameters().iter().enumerate() {
            eprintln!(
                "    round {i}: {} queries, pow {} bits, folding pow {} bits, {} OOD",
                r.num_queries, r.pow_bits, r.folding_pow_bits, r.ood_samples
            );
        }
        let t = w.terminal();
        eprintln!(
            "    terminal: {} queries, pow {} bits; final folding pow {} bits",
            t.num_queries,
            t.pow_bits,
            w.final_folding_pow_bits()
        );
    }
}

/// Plonky3's own security assessment of the configurations measured: every
/// soundness term of the multi-STARK statement and their composition.
#[test]
fn security_of_the_measured_configurations() {
    let air = KeccakBinaryAir::assuming_boolean_trace();
    for log_height in [5usize, 8, 12, 16, 18, 20] {
        let p = params(log_height);
        let (cfg, packed) = config(&p);
        let (mut ch, _) = challenger(false);
        let (_pk, vk) = setup(&cfg, &[&air], &mut ch).expect("setup");
        let instances = VerifierInstances::new(vec![VerifierInstance::new(&air, &vk, log_height, &[])]);
        let report = p3_multi_stark::security::security_report(&cfg, &instances).expect("security report");
        eprintln!(
            "2^{log_height} rows, {packed} packed variables: {:.2} bits composed; unassessed {:?}",
            report.security_bits().unwrap_or(f64::NAN),
            report.unassessed_components()
        );
        for term in report.terms() {
            eprintln!("    {term:?}");
        }
    }
}

/// The verifier's input bits by proof component, from the WHIR schedule
/// alone: what the dispute must reveal on-chain. The layout is `inputs`'s and
/// `build_full`'s: 128 bits per field element, 256 per digest, full Merkle
/// paths below each cap.
fn input_bits(log_height: usize, whir: &WhirConfig<F, F, Challenger>) -> Vec<(&'static str, usize)> {
    const E: usize = 128;
    const D: usize = 256;
    let scfg = stark::Config { log_height, width: NUM_KECCAK_BINARY_COLS, pow_bits: 0, seeds: Default::default() };
    let packed = scfg.packed_vars();
    let cap_h = recommended_cap_height(whir);
    let tensors = stark::DIM * if scfg.sends_successor() { 3 } else { 1 };
    let sumcheck = |rounds: usize, pow: usize| rounds * (2 + usize::from(pow > 0)) * E;
    let mut caps = 0;
    let mut rows = 0;
    let mut paths = 0;
    let mut rest = whir.commitment_ood_samples() * E + E + sumcheck(whir.round_folding_factor(0), whir.starting_folding_pow_bits());
    let mut open = |queries: usize, index_width: usize, folding: usize| {
        let h = cap_h.min(index_width);
        caps += (1 << h) * D;
        rows += queries * (1 << folding) * E;
        paths += queries * (index_width - h) * D;
    };
    for (i, r) in whir.round_parameters().iter().enumerate() {
        open(r.num_queries, r.log_folded_domain_size, whir.round_folding_factor(i));
        rest += r.ood_samples * E + usize::from(r.pow_bits > 0) * E + sumcheck(whir.round_folding_factor(i + 1), r.folding_pow_bits);
    }
    let fr = whir.final_round_config();
    let last = whir.folding_schedule().len() - 1;
    open(fr.num_queries, fr.log_folded_domain_size, whir.round_folding_factor(last));
    let final_poly = (1 << whir.final_sumcheck_rounds()) * E;
    rest += final_poly + usize::from(fr.pow_bits > 0) * E + sumcheck(whir.final_sumcheck_rounds(), whir.final_folding_pow_bits());
    vec![
        ("opened values", 2 * NUM_KECCAK_BINARY_COLS * E),
        ("zerocheck", (1 + 4 * log_height) * E),
        ("ring switch", (tensors + 2 * packed + 1) * E),
        ("WHIR caps", caps),
        ("WHIR leaf rows", rows),
        ("WHIR Merkle paths", paths),
        ("WHIR other", rest),
    ]
}

/// A WHIR schedule with a grinding budget of `pow` bits per round instead of
/// the profile's minimum: more grinding buys fewer queries.
fn whir_with_budget(p: &Params, packed: usize, pow: usize) -> Option<WhirConfig<F, F, Challenger>> {
    let parameters = p3_whir::ProtocolParameters {
        starting_log_inv_rate: p.log_inv_rate,
        round_log_inv_rates: Vec::new(),
        folding_factor: p3_whir::FoldingFactor::Constant(p.folding),
        soundness_type: p3_whir::SecurityAssumption::JohnsonBound,
        security_level: p.term_bits,
        pow_bits: pow,
    };
    WhirConfig::new_with_domain(packed, parameters, &BooleanWhirDomain::default()).ok()
}

/// The input-size study: input bits and their split for the measured
/// configurations (checked against the circuits' measured input counts), then
/// across rates, folding factors and grinding budgets at `WHIR_GC_LOG_HEIGHT`.
#[test]
#[ignore]
fn input_bits_of_whir_configurations() {
    for (log_height, measured) in [(5usize, 586_240usize), (8, 743_808), (12, 874_240), (16, 997_760), (18, 1_041_024)] {
        let p = params(log_height);
        let (_cfg, packed) = config(&p);
        let parts = input_bits(log_height, &whir_config(&p, packed));
        let total: usize = parts.iter().map(|(_, b)| b).sum();
        eprintln!("2^{log_height} rows: {total} input bits (measured {measured}) {parts:?}");
    }
    let log_height = std::env::var("WHIR_GC_LOG_HEIGHT").ok().map_or(18, |s| s.parse().expect("a log height"));
    let (_cfg, packed) = config(&params(log_height));
    for log_inv_rate in 3..=8 {
        for folding in 2..=6 {
            for pow in [0usize, 32, 40, 48] {
                let p = Params { log_height, log_inv_rate, folding, term_bits: params(log_height).term_bits };
                let whir = if pow == 0 { BinaryWhirProfile::proven_list_decoding(p.term_bits, log_inv_rate, folding).config::<F, F, Challenger, _>(packed, &BooleanWhirDomain::default()).ok() } else { whir_with_budget(&p, packed, pow) };
                let Some(whir) = whir else {
                    eprintln!("rate 1/{} folding {folding} pow {pow}: refused", 1 << log_inv_rate);
                    continue;
                };
                let parts = input_bits(log_height, &whir);
                let total: usize = parts.iter().map(|(_, b)| b).sum();
                let security = if pow == 48 && folding == 4 {
                    let air = KeccakBinaryAir::assuming_boolean_trace();
                    let (cfg, _) = config_with(&p, |_| whir.clone());
                    let (mut ch, _) = challenger(false);
                    let (_pk, vk) = setup(&cfg, &[&air], &mut ch).expect("setup");
                    let instances = VerifierInstances::new(vec![VerifierInstance::new(&air, &vk, log_height, &[])]);
                    let report = p3_multi_stark::security::security_report(&cfg, &instances).expect("security report");
                    format!(" {:.2} bits composed, unassessed {:?};", report.security_bits().unwrap_or(f64::NAN), report.unassessed_components())
                } else {
                    String::new()
                };
                let queries: Vec<usize> = whir.round_parameters().iter().map(|r| r.num_queries).chain([whir.terminal().num_queries]).collect();
                eprintln!(
                    "rate 1/{} folding {folding} pow {pow} (max {}):{security} queries {queries:?}, {total} input bits, WHIR {} {parts:?}",
                    1 << log_inv_rate,
                    whir.max_pow_bits(),
                    parts[3..].iter().map(|(_, b)| b).sum::<usize>()
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Garbling before the proof exists, evaluating afterwards.
// ---------------------------------------------------------------------------

use garbled_snark_verifier::circuits::sect233k1::builder::{CustomGateParams, CustomGateType, GateCounts, GateOperation, Template};
use garbled_snark_verifier::core::gate::{GateType, gate_evaluate};
use garbled_snark_verifier::core::s::S;

/// The garbler at setup: `Streaming` with every input held at 0, so that the
/// garbling depends on the circuit alone. It records the false label of
/// every fresh wire in creation order, which is what the evaluator's input
/// labels are derived from.
struct Blind {
    inner: Streaming,
    input_label0: Vec<S>,
}

impl CircuitTrait for Blind {
    fn fresh_one(&mut self) -> usize {
        let w = self.inner.fresh_one();
        self.input_label0.push(self.inner.label0(w));
        w
    }
    fn fresh<const N: usize>(&mut self) -> [usize; N] {
        core::array::from_fn(|_| self.fresh_one())
    }
    fn zero(&mut self) -> usize {
        self.inner.zero()
    }
    fn one(&mut self) -> usize {
        self.inner.one()
    }
    fn xor_wire(&mut self, x: usize, y: usize) -> usize {
        self.inner.xor_wire(x, y)
    }
    fn or_wire(&mut self, x: usize, y: usize) -> usize {
        self.inner.or_wire(x, y)
    }
    fn and_wire(&mut self, x: usize, y: usize) -> usize {
        self.inner.and_wire(x, y)
    }
    fn push_custom_gate(&mut self, params: CustomGateParams, new_wire_idx: usize) {
        self.inner.push_custom_gate(params, new_wire_idx)
    }
    fn get_gates(&self) -> &Vec<GateOperation> {
        self.inner.get_gates()
    }
    fn gate_counts(&self) -> GateCounts {
        self.inner.gate_counts()
    }
    fn next_wire(&self) -> usize {
        self.inner.next_wire()
    }
    fn init_circuit_config_for_custom_gate(&mut self, templ_type: CustomGateType) -> &Template {
        self.inner.init_circuit_config_for_custom_gate(templ_type)
    }
    fn get_template(&self, templ_type: CustomGateType) -> Option<&Template> {
        self.inner.get_template(templ_type)
    }
}

impl ValuedBuilder for Blind {
    fn set_input(&mut self, wire: usize, _value: bool) {
        self.inner.set_input(wire, false);
    }
}

/// The evaluator: the same builder run on the proof, holding one label per
/// wire (the label of its value) and reading the stored ciphertexts in gate
/// order. It never sees `Δ` or a false label it does not hold.
struct Evaluator<'a> {
    label: Vec<S>,
    value: Vec<bool>,
    inputs: &'a [S],
    next_input: usize,
    ciphertexts: &'a [S],
    gid: usize,
    counts: GateCounts,
    empty: Vec<GateOperation>,
}

impl<'a> Evaluator<'a> {
    /// `constants`: the held labels of wires 0 and 1; `inputs`: the held label
    /// of each fresh wire, in creation order.
    fn new(constants: [S; 2], inputs: &'a [S], ciphertexts: &'a [S]) -> Self {
        Self { label: constants.to_vec(), value: vec![false, true], inputs, next_input: 0, ciphertexts, gid: 0, counts: GateCounts::default(), empty: Vec::new() }
    }

    fn push(&mut self, label: S, value: bool) -> usize {
        self.label.push(label);
        self.value.push(value);
        self.label.len() - 1
    }

    fn non_free(&mut self, x: usize, y: usize, gate_type: GateType) -> usize {
        let gid = u32::try_from(self.gid).expect("gate ids fit in u32");
        let ct = self.ciphertexts[self.gid];
        self.gid += 1;
        let label = gate_evaluate(gate_type, self.value[x], self.label[x], self.label[y], Some(ct), gid, None);
        let value = if gate_type == GateType::Or { self.value[x] | self.value[y] } else { self.value[x] & self.value[y] };
        self.push(label, value)
    }
}

impl CircuitTrait for Evaluator<'_> {
    fn fresh_one(&mut self) -> usize {
        let label = self.inputs[self.next_input];
        self.next_input += 1;
        self.push(label, false)
    }
    fn fresh<const N: usize>(&mut self) -> [usize; N] {
        core::array::from_fn(|_| self.fresh_one())
    }
    fn zero(&mut self) -> usize {
        0
    }
    fn one(&mut self) -> usize {
        1
    }
    // The folding rules are `Streaming`'s, rule for rule, so the two builds
    // meet the same non-free gates in the same order.
    fn xor_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return 0;
        }
        if x == 0 {
            return y;
        }
        if y == 0 {
            return x;
        }
        self.counts.direct_xor += 1;
        let (l, v) = (self.label[x] ^ self.label[y], self.value[x] ^ self.value[y]);
        self.push(l, v)
    }
    fn or_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return x;
        }
        if x == 1 || y == 1 {
            return 1;
        }
        if x == 0 {
            return y;
        }
        if y == 0 {
            return x;
        }
        self.counts.direct_or += 1;
        self.non_free(x, y, GateType::Or)
    }
    fn and_wire(&mut self, x: usize, y: usize) -> usize {
        if x == y {
            return x;
        }
        if x == 0 || y == 0 {
            return 0;
        }
        if x == 1 {
            return y;
        }
        if y == 1 {
            return x;
        }
        self.counts.direct_and += 1;
        self.non_free(x, y, GateType::And)
    }
    fn push_custom_gate(&mut self, _params: CustomGateParams, _new_wire_idx: usize) {
        unimplemented!("custom gates are not used")
    }
    fn get_gates(&self) -> &Vec<GateOperation> {
        &self.empty
    }
    fn gate_counts(&self) -> GateCounts {
        self.counts
    }
    fn next_wire(&self) -> usize {
        self.label.len()
    }
    fn init_circuit_config_for_custom_gate(&mut self, _templ_type: CustomGateType) -> &Template {
        unimplemented!("custom gates are not used")
    }
    fn get_template(&self, _templ_type: CustomGateType) -> Option<&Template> {
        None
    }
}

impl ValuedBuilder for Evaluator<'_> {
    fn set_input(&mut self, wire: usize, value: bool) {
        self.value[wire] = value;
    }
}

/// Garble the full verifier before any proof is used (every input held at
/// 0), store the ciphertexts, then evaluate them on the labels of a real
/// proof, which must give the label of 1, and of the proof with one opened
/// value changed, which must give the label of 0: the label a challenger
/// takes to Disprove.
fn garble_then_evaluate(log_height: usize) {
    let _heavy = heavy();
    let p = params(log_height);
    let run = prove_and_log(&p);
    let inp = inputs(&p, &run);

    let mut plan = Plan::new();
    build_full(&mut plan, &inp, &inp);
    let t = std::time::Instant::now();
    let mut g = Blind { inner: Streaming::planned(plan, true), input_label0: Vec::new() };
    let (shape, _) = build_full(&mut g, &inp, &inp);
    let garble_time = t.elapsed();
    assert!(!g.inner.value(shape.output), "the placeholder witness is rejected");
    let delta = g.inner.delta();
    let reject = g.inner.label0(shape.output);
    let accept = reject ^ delta;
    let constants = [g.inner.label0(0), g.inner.label0(1) ^ delta];
    let ciphertexts = g.inner.ciphertexts().to_vec();
    let input_label0 = std::mem::take(&mut g.input_label0);
    let non_free = g.inner.non_free_gates();
    drop(g);

    let evaluate = |proof: &Inputs, what: &str| -> (S, std::time::Duration) {
        // The witness in allocation order, as the circuit reads it; the
        // soldering hands over the label of each published bit's value.
        let mut counter = Plan::new();
        let (_, witness) = build_full(&mut counter, proof, &inp);
        assert_eq!(witness.len(), input_label0.len(), "{what}: every fresh wire is an input");
        let held: Vec<S> = input_label0.iter().zip(&witness).map(|(&l, &b)| if b { l ^ delta } else { l }).collect();
        let t = std::time::Instant::now();
        let mut e = Evaluator::new(constants, &held, &ciphertexts);
        let (shape, _) = build_full(&mut e, proof, &inp);
        let time = t.elapsed();
        assert_eq!(e.gid, non_free, "{what}: the same non-free gates");
        (e.label[shape.output], time)
    };

    let (honest, eval_time) = evaluate(&inp, "honest");
    assert_eq!(honest, accept, "the honest proof yields the label of 1");
    assert_ne!(honest, reject);
    let mut bad = inp.clone();
    bad.sdata.values[7] += F::ONE;
    let (changed, _) = evaluate(&bad, "changed");
    assert_eq!(changed, reject, "a changed proof yields the label of 0");
    eprintln!(
        "2^{log_height} rows: garbled {non_free} non-free gates with every input at 0 in {garble_time:.1?} ({} MB stored); \
         evaluated on the proof in {eval_time:.1?}: label of 1; on the changed proof: label of 0",
        ciphertexts.len() * 16 / 1_000_000
    );
}

#[test]
#[ignore]
fn garbled_before_the_proof_evaluates_real_proofs() {
    let log_height = std::env::var("WHIR_GC_LOG_HEIGHT").ok().map_or(5, |s| s.parse().expect("a log height"));
    garble_then_evaluate(log_height);
}
