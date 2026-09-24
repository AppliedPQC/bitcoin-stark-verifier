//! The verifier of [`crate::reference`] as a boolean circuit.
//!
//! One output wire: 1 iff every check the reference makes passes -- each
//! grinding witness, each opened row's Merkle path against the absorbed root,
//! each final query's fold against the final polynomial, and the closing
//! identity. Everything the reference derives, the circuit derives from the
//! same input bits: the transcript runs on a wire-level `HashChallenger` over
//! the Blake3 gadget, every challenge is read off its digests, and every
//! opened row is hashed and walked to the root that was absorbed.
//!
//! The circuit's *shape* depends only on the configuration: the transcript's
//! schedule has no data-dependent branch (queries are a fixed number of masked
//! draws; a PoW check is a fixed number of sampled bits), so the same circuit
//! serves every proof of a configuration and can be garbled once. The
//! sub-transcripts' seeds are constants of the configuration and are baked in
//! as constant wires; everything the prover sends is an input.
//!
//! The builder wants every input wire allocated before any gate, so
//! [`Inputs::allocate`] lays the whole proof out first -- messages in
//! transcript order, then the opened rows with their full sibling paths --
//! and records the bits a real proof puts on them; [`build`] then yields the
//! circuit and a witness to run it on.

use garbled_snark_verifier::circuits::sect233k1::builder::{CircuitAdapter, CircuitTrait, GateCounts};
use p3_binary_field::TowerLevel;

use garbled_snark_verifier::circuits::sect233k1::blake3_ckt as blake3;
use crate::pruned;
use crate::reference::{self, Config, Data, F};
use garbled_snark_verifier::circuits::sect233k1::stream::ValuedBuilder;
use crate::tower;

pub type Byte = [usize; 8];
/// A field element: 128 wires, bit `i` of the little-endian representation.
pub type Elem = Vec<usize>;

const ELEM_BYTES: usize = 16;
const INDEX_BYTES: usize = 8;

// ---------------------------------------------------------------------------
// Bit helpers.
// ---------------------------------------------------------------------------

pub(crate) fn not<T: CircuitTrait>(b: &mut T, x: usize) -> usize {
    let one = b.one();
    b.xor_wire(x, one)
}

pub(crate) fn or_all<T: CircuitTrait>(b: &mut T, xs: &[usize]) -> usize {
    let mut acc = b.zero();
    for &x in xs {
        acc = b.or_wire(acc, x);
    }
    acc
}

pub(crate) fn and_all<T: CircuitTrait>(b: &mut T, xs: &[usize]) -> usize {
    let mut acc = b.one();
    for &x in xs {
        acc = b.and_wire(acc, x);
    }
    acc
}

/// 1 iff the two wire vectors carry the same bits.
pub(crate) fn equal<T: CircuitTrait>(b: &mut T, x: &[usize], y: &[usize]) -> usize {
    assert_eq!(x.len(), y.len());
    let diff: Vec<usize> = x.iter().zip(y).map(|(&p, &q)| b.xor_wire(p, q)).collect();
    let any = or_all(b, &diff);
    not(b, any)
}

/// `sel ? y : x`, bit by bit: `x ⊕ (sel ∧ (x ⊕ y))`, one AND per bit.
pub(crate) fn mux<T: CircuitTrait>(b: &mut T, sel: usize, x: &[usize], y: &[usize]) -> Vec<usize> {
    assert_eq!(x.len(), y.len());
    x.iter()
        .zip(y)
        .map(|(&p, &q)| {
            let d = b.xor_wire(p, q);
            let t = b.and_wire(sel, d);
            b.xor_wire(p, t)
        })
        .collect()
}

pub(crate) fn bytes_to_wires(bytes: &[Byte]) -> Vec<usize> {
    bytes.iter().flat_map(|b| b.iter().copied()).collect()
}

pub(crate) fn wires_to_bytes(wires: &[usize]) -> Vec<Byte> {
    assert_eq!(wires.len() % 8, 0);
    wires.chunks(8).map(|c| c.try_into().expect("8 wires")).collect()
}

pub(crate) fn const_bytes<T: CircuitTrait>(b: &mut T, bytes: &[u8]) -> Vec<Byte> {
    let zero = b.zero();
    let one = b.one();
    bytes.iter().map(|&v| core::array::from_fn(|i| if (v >> i) & 1 == 1 { one } else { zero })).collect()
}

pub(crate) fn elem_bits(x: F) -> Vec<bool> {
    let v = x.to_repr();
    (0..128).map(|i| (v >> i) & 1 == 1).collect()
}

// ---------------------------------------------------------------------------
// Inputs: the whole proof, allocated before any gate, witness alongside.
// ---------------------------------------------------------------------------

struct SumcheckInputs {
    c0: Elem,
    c_inf: Elem,
    witness: Option<Elem>,
}

struct OpeningInputs {
    rows: Vec<Vec<Elem>>,
    /// Per query, one sibling digest per level, level 0 first.
    siblings: Vec<Vec<Vec<Byte>>>,
}

struct RoundInputs {
    root: Vec<Byte>,
    ood_answers: Vec<Elem>,
    pow_witness: Option<Elem>,
    sumcheck: Vec<SumcheckInputs>,
    opening: OpeningInputs,
}

pub struct Inputs {
    root: Vec<Byte>,
    initial_ood_answers: Vec<Elem>,
    openings: Vec<Vec<Elem>>,
    initial_sumcheck: Vec<SumcheckInputs>,
    rounds: Vec<RoundInputs>,
    final_poly: Vec<Elem>,
    final_pow_witness: Option<Elem>,
    final_sumcheck: Vec<SumcheckInputs>,
    final_opening: OpeningInputs,
    pub witness: Vec<bool>,
}

/// Fresh input wires carrying `bytes`, their bits appended to `witness`.
pub(crate) fn alloc_bytes<T: ValuedBuilder>(b: &mut T, witness: &mut Vec<bool>, bytes: &[u8]) -> Vec<Byte> {
    bytes
        .iter()
        .map(|&v| {
            let w: Byte = b.fresh();
            for (i, &wire) in w.iter().enumerate() {
                let bit = (v >> i) & 1 == 1;
                b.set_input(wire, bit);
                witness.push(bit);
            }
            w
        })
        .collect()
}

/// A fresh input element carrying `x`, its bits appended to `witness`.
pub(crate) fn alloc_elem<T: ValuedBuilder>(b: &mut T, witness: &mut Vec<bool>, x: F) -> Elem {
    let w = tower::fresh(b, 128);
    for (&wire, bit) in w.iter().zip(elem_bits(x)) {
        b.set_input(wire, bit);
        witness.push(bit);
    }
    w
}

impl Inputs {
    fn bytes<T: ValuedBuilder>(&mut self, b: &mut T, bytes: &[u8]) -> Vec<Byte> {
        alloc_bytes(b, &mut self.witness, bytes)
    }

    fn elem<T: ValuedBuilder>(&mut self, b: &mut T, x: F) -> Elem {
        alloc_elem(b, &mut self.witness, x)
    }

    fn sumcheck<T: ValuedBuilder>(&mut self, b: &mut T, rounds: &[reference::SumcheckRoundData], pow_bits: usize) -> Vec<SumcheckInputs> {
        rounds
            .iter()
            .map(|r| SumcheckInputs {
                c0: self.elem(b, r.poly[0]),
                c_inf: self.elem(b, r.poly[1]),
                witness: (pow_bits > 0).then(|| self.elem(b, r.pow_witness)),
            })
            .collect()
    }

    /// Rows and full sibling paths: the pruned proof expanded outside the
    /// circuit, which is sound -- a path is a hint, the root is not.
    fn opening<T: ValuedBuilder>(
        &mut self,
        b: &mut T,
        o: &reference::Opening,
        indices: &[usize],
        index_width: usize,
        cap_height: usize,
    ) -> OpeningInputs {
        let leaves: Vec<pruned::Digest> = o.rows.iter().map(|r| reference::leaf(r)).collect();
        let paths = pruned::expand(&o.boundaries, indices, &leaves, index_width, cap_height).expect("openings expand");
        let rows = o.rows.iter().map(|row| row.iter().map(|&x| self.elem(b, x)).collect()).collect();
        let siblings = paths.iter().map(|p| p.siblings.iter().map(|s| self.bytes(b, s)).collect()).collect();
        OpeningInputs { rows, siblings }
    }

    /// Lay out the proof: every message in transcript order, then the openings.
    pub fn allocate<T: ValuedBuilder>(b: &mut T, cfg: &Config, d: &Data, ch: &reference::Challenges) -> Self {
        let mut me = Self {
            root: Vec::new(),
            initial_ood_answers: Vec::new(),
            openings: Vec::new(),
            initial_sumcheck: Vec::new(),
            rounds: Vec::new(),
            final_poly: Vec::new(),
            final_pow_witness: None,
            final_sumcheck: Vec::new(),
            final_opening: OpeningInputs { rows: Vec::new(), siblings: Vec::new() },
            witness: Vec::new(),
        };
        me.root = me.bytes(b, &d.cap);
        me.initial_ood_answers = d.initial_ood_answers.iter().map(|&x| me.elem(b, x)).collect();
        me.openings = d.openings.iter().map(|evals| evals.iter().map(|&x| me.elem(b, x)).collect()).collect();
        me.initial_sumcheck = me.sumcheck(b, &d.initial_sumcheck, cfg.initial_folding_pow_bits);
        // Each round opens the previous commitment.
        let mut prev_cap: &[u8] = &d.cap;
        for (i, (rc, rd)) in cfg.rounds.iter().zip(&d.rounds).enumerate() {
            let root = me.bytes(b, &rd.cap);
            let ood_answers = rd.ood_answers.iter().map(|&x| me.elem(b, x)).collect();
            let pow_witness = (rc.pow_bits > 0).then(|| me.elem(b, rd.pow_witness));
            let sumcheck = me.sumcheck(b, &rd.sumcheck, rc.folding_pow_bits);
            let opening = me.opening(b, &rd.opening, &ch.rounds[i].queries, rc.index_width, cap_height(prev_cap));
            prev_cap = &rd.cap;
            me.rounds.push(RoundInputs { root, ood_answers, pow_witness, sumcheck, opening });
        }
        me.final_poly = d.final_poly.iter().map(|&x| me.elem(b, x)).collect();
        me.final_pow_witness = (cfg.final_pow_bits > 0).then(|| me.elem(b, d.final_pow_witness));
        me.final_sumcheck = me.sumcheck(b, &d.final_sumcheck, cfg.final_folding_pow_bits);
        me.final_opening = me.opening(b, &d.final_opening, &ch.final_queries, cfg.final_index_width, cap_height(prev_cap));
        me
    }
}

// ---------------------------------------------------------------------------
// The wire-level challenger.
// ---------------------------------------------------------------------------

/// `HashChallenger<u8, Blake3, 32>` over wires: the input buffer is hashed
/// whole on refill, the digest chains into the input, and bytes are popped
/// from the digest's end.
pub struct Sponge {
    input: Vec<Byte>,
    output: Vec<Byte>,
    pub flushes: usize,
}

impl Sponge {
    pub(crate) fn new() -> Self {
        Self { input: Vec::new(), output: Vec::new(), flushes: 0 }
    }

    pub(crate) fn observe(&mut self, bytes: &[Byte]) {
        if !bytes.is_empty() {
            self.output.clear();
            self.input.extend_from_slice(bytes);
        }
    }

    pub(crate) fn sample<T: CircuitTrait>(&mut self, b: &mut T) -> Byte {
        if self.output.is_empty() {
            let digest = blake3::hash_bytes(b, &self.input);
            self.flushes += 1;
            self.input = digest.to_vec();
            self.output = digest.to_vec();
        }
        self.output.pop().expect("refilled")
    }

    pub(crate) fn sample_bytes<T: CircuitTrait>(&mut self, b: &mut T, n: usize) -> Vec<Byte> {
        (0..n).map(|_| self.sample(b)).collect()
    }

    pub(crate) fn observe_elem(&mut self, x: &Elem) {
        self.observe(&wires_to_bytes(x));
    }

    pub(crate) fn sample_elem<T: CircuitTrait>(&mut self, b: &mut T) -> Elem {
        bytes_to_wires(&self.sample_bytes(b, ELEM_BYTES))
    }

    /// The low `bits` of an 8-byte draw, as wires.
    pub(crate) fn sample_bits<T: CircuitTrait>(&mut self, b: &mut T, bits: usize) -> Vec<usize> {
        let bytes = self.sample_bytes(b, INDEX_BYTES);
        bytes_to_wires(&bytes)[..bits].to_vec()
    }

    /// `check_witness`: absorb the witness; 1 iff `bits` sampled bits are zero.
    pub(crate) fn check_witness<T: CircuitTrait>(&mut self, b: &mut T, bits: usize, witness: &Elem) -> Option<usize> {
        if bits == 0 {
            return None;
        }
        self.observe_elem(witness);
        let drawn = self.sample_bits(b, bits);
        let any = or_all(b, &drawn);
        Some(not(b, any))
    }
}

// ---------------------------------------------------------------------------
// Field arithmetic on wires.
// ---------------------------------------------------------------------------

pub(crate) fn one_elem<T: CircuitTrait>(b: &mut T) -> Elem {
    tower::constant(b, 1, 128)
}

pub(crate) fn zero_elem<T: CircuitTrait>(b: &mut T) -> Elem {
    tower::constant(b, 0, 128)
}

/// `[y^(2^(m-1)), …, y², y]`.
fn expand_univariate<T: CircuitTrait>(b: &mut T, y: &Elem, m: usize) -> Vec<Elem> {
    let mut out = vec![Vec::new(); m];
    let mut cur = y.clone();
    for i in (0..m).rev() {
        out[i] = cur.clone();
        cur = tower::square(b, &cur);
    }
    out
}

/// `eq(p, r) = prod (1 + p_i + r_i)`, Plonky3's `eval_eq` in characteristic two.
pub(crate) fn eq_eval<T: CircuitTrait>(b: &mut T, p: &[Elem], r: &[Elem]) -> Elem {
    assert_eq!(p.len(), r.len());
    let one = one_elem(b);
    let mut acc = one.clone();
    for (pi, ri) in p.iter().zip(r) {
        let s = tower::add(b, pi, ri);
        let term = tower::add(b, &s, &one);
        acc = tower::mul(b, &acc, &term);
    }
    acc
}

/// `prod (r_i·(p_i − 1) + 1)`, the weight of a direct point.
fn select_point_weight<T: CircuitTrait>(b: &mut T, p: &[Elem], r: &[Elem]) -> Elem {
    assert_eq!(p.len(), r.len());
    let one = one_elem(b);
    let mut acc = one.clone();
    for (pi, ri) in p.iter().zip(r) {
        let pm1 = tower::add(b, pi, &one);
        let prod = tower::mul(b, ri, &pm1);
        let term = tower::add(b, &prod, &one);
        acc = tower::mul(b, &acc, &term);
    }
    acc
}

/// `extrapolate_01inf(c0, claim − c0, c_inf, r)`.
pub(crate) fn sumcheck_round<T: CircuitTrait>(b: &mut T, claim: &Elem, c0: &Elem, c_inf: &Elem, r: &Elem) -> Elem {
    let one = one_elem(b);
    let one_minus_r = tower::add(b, &one, r);
    let e1 = tower::add(b, claim, c0);
    let r_minus_1 = tower::add(b, r, &one);
    let r_r1 = tower::mul(b, r, &r_minus_1);
    let t0 = tower::mul(b, c0, &one_minus_r);
    let t1 = tower::mul(b, &e1, r);
    let t2 = tower::mul(b, c_inf, &r_r1);
    let s = tower::add(b, &t0, &t1);
    tower::add(b, &s, &t2)
}

/// `eval_multilinear`: fold the last variable first, `a + x·(b − a)`.
pub(crate) fn eval_multilinear<T: CircuitTrait>(b: &mut T, evals: &[Elem], point: &[Elem]) -> Elem {
    assert_eq!(evals.len(), 1 << point.len());
    let mut cur: Vec<Elem> = evals.to_vec();
    for x in point.iter().rev() {
        cur = (0..cur.len() / 2)
            .map(|j| {
                let d = tower::add(b, &cur[2 * j + 1], &cur[2 * j]);
                let xd = tower::mul(b, x, &d);
                tower::add(b, &cur[2 * j], &xd)
            })
            .collect();
    }
    cur.pop().expect("one value")
}

/// The coefficient table folded coordinate by coordinate: `s[i] = s[2i] + s[2i+1]·c`.
fn eval_coefficients<T: CircuitTrait>(b: &mut T, coeffs: &[Elem], point: &[Elem]) -> Elem {
    assert_eq!(coeffs.len(), 1 << point.len());
    let mut cur: Vec<Elem> = coeffs.to_vec();
    for c in point.iter().rev() {
        cur = (0..cur.len() / 2)
            .map(|j| {
                let t = tower::mul(b, &cur[2 * j + 1], c);
                tower::add(b, &cur[2 * j], &t)
            })
            .collect();
    }
    cur.pop().expect("one value")
}

/// `claim += sum chi^(shift+i) e_i`.
pub(crate) fn combine_into<T: CircuitTrait>(b: &mut T, claim: &mut Elem, chi: &Elem, shift: usize, evals: &[Elem]) {
    let mut power = one_elem(b);
    for _ in 0..shift {
        power = tower::mul(b, &power, chi);
    }
    for e in evals {
        let t = tower::mul(b, &power, e);
        *claim = tower::add(b, claim, &t);
        power = tower::mul(b, &power, chi);
    }
}

/// The domain point of an index given as wires: `sum bit_r · cantor_basis(r)`,
/// a selection of constant bits by the index bits and no gate at all but XORs.
fn domain_point<T: CircuitTrait>(b: &mut T, index_bits: &[usize]) -> Elem {
    let zero = b.zero();
    let mut acc: Elem = vec![zero; 128];
    for (r, &bit) in index_bits.iter().enumerate() {
        let basis = F::cantor_basis(r).to_repr();
        for j in 0..128 {
            if (basis >> j) & 1 == 1 {
                acc[j] = b.xor_wire(acc[j], bit);
            }
        }
    }
    acc
}

/// `(S_{n-1}(x), …, S_0(x))`, `S_j` the `j`-fold iterate of `v ↦ v² + v`.
fn query_point<T: CircuitTrait>(b: &mut T, num_variables: usize, index_bits: &[usize]) -> Vec<Elem> {
    let x = domain_point(b, index_bits);
    let mut iterates = Vec::with_capacity(num_variables);
    let mut v = x;
    for _ in 0..num_variables {
        iterates.push(v.clone());
        let sq = tower::square(b, &v);
        v = tower::add(b, &sq, &v);
    }
    iterates.reverse();
    iterates
}

// ---------------------------------------------------------------------------
// The transcript on wires.
// ---------------------------------------------------------------------------

struct RoundWires {
    ood_points: Vec<Elem>,
    /// Per query, the index's bits, bit 0 first (constant wires for the stratum).
    queries: Vec<Vec<usize>>,
    combination: Elem,
    folding: Vec<Elem>,
}

struct TranscriptWires {
    given_points: Vec<Vec<Elem>>,
    initial_ood_points: Vec<Elem>,
    opening_points: Vec<Elem>,
    alpha: Elem,
    initial_folding: Vec<Elem>,
    rounds: Vec<RoundWires>,
    final_queries: Vec<Vec<usize>>,
    final_folding: Vec<Elem>,
    /// One wire per grinding check.
    pow_checks: Vec<usize>,
}

/// The message wires the transcript allocates, which the arithmetic reads.
struct Messages {
    root: Vec<Byte>,
    initial_ood_answers: Vec<Elem>,
    openings: Vec<Vec<Elem>>,
    initial_sumcheck: Vec<[Elem; 2]>,
    rounds: Vec<RoundMessages>,
    final_poly: Vec<Elem>,
    final_sumcheck: Vec<[Elem; 2]>,
}

struct RoundMessages {
    root: Vec<Byte>,
    ood_answers: Vec<Elem>,
    sumcheck: Vec<[Elem; 2]>,
}

fn stir_queries<T: CircuitTrait>(b: &mut T, s: &mut Sponge, index_width: usize, num_queries: usize) -> Vec<Vec<usize>> {
    let draws = reference::query_draws(index_width, num_queries);
    let zero = b.zero();
    let one = b.one();
    if draws == 0 {
        return (0..1usize << index_width)
            .map(|i| (0..index_width).map(|j| if (i >> j) & 1 == 1 { one } else { zero }).collect())
            .collect();
    }
    let mut out = Vec::with_capacity(draws);
    for depth in reference::summand_depths(draws) {
        for stratum in 0..1usize << depth {
            let mut bits = s.sample_bits(b, index_width - depth);
            bits.extend((0..depth).map(|j| if (stratum >> j) & 1 == 1 { one } else { zero }));
            out.push(bits);
        }
    }
    out
}

fn sumcheck_rounds<T: CircuitTrait>(
    b: &mut T,
    s: &mut Sponge,
    rounds: &[SumcheckInputs],
    pow_bits: usize,
    pow_checks: &mut Vec<usize>,
) -> (Vec<[Elem; 2]>, Vec<Elem>) {
    let mut polys = Vec::new();
    let mut folding = Vec::new();
    for r in rounds {
        s.observe_elem(&r.c0);
        s.observe_elem(&r.c_inf);
        if pow_bits > 0 {
            let w = r.witness.as_ref().expect("a grinding witness");
            pow_checks.extend(s.check_witness(b, pow_bits, w));
        }
        folding.push(s.sample_elem(b));
        polys.push([r.c0.clone(), r.c_inf.clone()]);
    }
    (polys, folding)
}

/// What a layer in front of the opening hands over: the claims' given points
/// and the values it bound them to (checked equal to the claimed openings).
pub struct PrefixOut {
    pub points: Vec<Vec<Elem>>,
    pub values: Vec<Vec<Elem>>,
}

fn transcript<T: CircuitTrait>(
    b: &mut T,
    inputs: &Inputs,
    cfg: &Config,
    d: &Data,
    prefix: impl FnOnce(&mut T, &mut Sponge, &mut Vec<usize>) -> PrefixOut,
    checks: &mut Vec<usize>,
) -> (TranscriptWires, Messages, usize) {
    let mut s = Sponge::new();
    let mut pow_checks = Vec::new();

    let seed = const_bytes(b, &d.seed_commitment);
    s.observe(&seed);
    let root = inputs.root.clone();
    s.observe(&root);
    let PrefixOut { points: given_points, values: given_values } = prefix(b, &mut s, checks);
    assert_eq!(given_points.len(), if cfg.given_points { inputs.openings.len() } else { 0 });
    for (ws, vs) in inputs.openings.iter().zip(&given_values) {
        assert_eq!(ws.len(), vs.len());
        for (w, v) in ws.iter().zip(vs) {
            checks.push(equal(b, w, v));
        }
    }
    let mut initial_ood_points = Vec::new();
    for (a, seed) in inputs.initial_ood_answers.iter().zip(&d.seed_virtual) {
        let seed = const_bytes(b, seed);
        s.observe(&seed);
        initial_ood_points.push(s.sample_elem(b));
        s.observe_elem(a);
    }
    let initial_ood_answers = inputs.initial_ood_answers.clone();
    let mut opening_points = Vec::new();
    for (ws, seed) in inputs.openings.iter().zip(&d.seed_claim) {
        let seed = const_bytes(b, seed);
        s.observe(&seed);
        opening_points.push(if cfg.given_points { zero_elem(b) } else { s.sample_elem(b) });
        for w in ws {
            s.observe_elem(w);
        }
    }
    let openings = inputs.openings.clone();
    let seed = const_bytes(b, &d.seed_whir_batching);
    s.observe(&seed);
    let alpha = s.sample_elem(b);
    let seed = const_bytes(b, &d.seed_initial_sumcheck);
    s.observe(&seed);
    let (initial_sumcheck, initial_folding) =
        sumcheck_rounds(b, &mut s, &inputs.initial_sumcheck, cfg.initial_folding_pow_bits, &mut pow_checks);

    let mut rounds = Vec::new();
    let mut round_messages = Vec::new();
    for ((rc, rd), ri) in cfg.rounds.iter().zip(&d.rounds).zip(&inputs.rounds) {
        let root = ri.root.clone();
        s.observe(&root);
        let mut ood_points = Vec::new();
        for a in &ri.ood_answers {
            ood_points.push(s.sample_elem(b));
            s.observe_elem(a);
        }
        let ood_answers = ri.ood_answers.clone();
        if rc.pow_bits > 0 {
            let w = ri.pow_witness.as_ref().expect("a grinding witness");
            pow_checks.extend(s.check_witness(b, rc.pow_bits, w));
        }
        let queries = stir_queries(b, &mut s, rc.index_width, rc.num_queries);
        let combination = s.sample_elem(b);
        let seed = const_bytes(b, &rd.seed_sumcheck);
        s.observe(&seed);
        let (sumcheck, folding) = sumcheck_rounds(b, &mut s, &ri.sumcheck, rc.folding_pow_bits, &mut pow_checks);
        rounds.push(RoundWires { ood_points, queries, combination, folding });
        round_messages.push(RoundMessages { root, ood_answers, sumcheck });
    }

    let final_poly: Vec<Elem> = inputs.final_poly.clone();
    for c in &final_poly {
        s.observe_elem(c);
    }
    if cfg.final_pow_bits > 0 {
        let w = inputs.final_pow_witness.as_ref().expect("a grinding witness");
        pow_checks.extend(s.check_witness(b, cfg.final_pow_bits, w));
    }
    let final_queries = stir_queries(b, &mut s, cfg.final_index_width, cfg.final_queries);
    let seed = const_bytes(b, &d.seed_final_sumcheck);
    s.observe(&seed);
    let (final_sumcheck, final_folding) =
        sumcheck_rounds(b, &mut s, &inputs.final_sumcheck, cfg.final_folding_pow_bits, &mut pow_checks);

    let wires = TranscriptWires {
        given_points,
        initial_ood_points,
        opening_points,
        alpha,
        initial_folding,
        rounds,
        final_queries,
        final_folding,
        pow_checks,
    };
    let messages = Messages {
        root,
        initial_ood_answers,
        openings,
        initial_sumcheck,
        rounds: round_messages,
        final_poly,
        final_sumcheck,
    };
    (wires, messages, s.flushes)
}

// ---------------------------------------------------------------------------
// The openings on wires.
// ---------------------------------------------------------------------------

/// Non-free gates by phase: where the circuit's size goes. Names repeat
/// across rounds and are summed.
#[derive(Default, Clone, Debug)]
pub struct Profile {
    pub phases: Vec<(&'static str, usize)>,
    last: usize,
}

impl Profile {
    fn non_free<T: CircuitTrait>(b: &T) -> usize {
        let c = b.gate_counts();
        c.direct_and + c.direct_or
    }

    /// Charge the non-free gates since the last mark to `name`.
    pub(crate) fn mark<T: CircuitTrait>(&mut self, b: &T, name: &'static str) {
        let now = Self::non_free(b);
        let delta = now - self.last;
        self.last = now;
        match self.phases.iter_mut().find(|(n, _)| *n == name) {
            Some((_, v)) => *v += delta,
            None => self.phases.push((name, delta)),
        }
    }

    pub fn total(&self) -> usize {
        self.phases.iter().map(|(_, v)| v).sum()
    }
}

impl core::fmt::Display for Profile {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let total = self.total().max(1);
        for (name, v) in &self.phases {
            writeln!(f, "  {name:<28} {v:>12}  {:5.1}%", 100.0 * *v as f64 / total as f64)?;
        }
        Ok(())
    }
}

/// The height of a Merkle cap of `cap.len() / 32` roots.
fn cap_height(cap: &[u8]) -> usize {
    let roots = cap.len() / 32;
    assert!(roots.is_power_of_two() && roots * 32 == cap.len(), "a cap is a power of two of 32-byte roots");
    roots.trailing_zeros() as usize
}

/// `entries[sel]`, for `sel` given as bits, least significant first: a mux
/// tree, one AND per wire per pair merged.
fn select<T: CircuitTrait>(b: &mut T, entries: &[Vec<usize>], sel: &[usize]) -> Vec<usize> {
    assert_eq!(entries.len(), 1 << sel.len());
    let mut layer: Vec<Vec<usize>> = entries.to_vec();
    for &bit in sel {
        layer = layer.chunks(2).map(|pair| mux(b, bit, &pair[0], &pair[1])).collect();
    }
    layer.pop().expect("one entry left")
}

/// Authenticate every query's row against the Merkle cap `cap` (`2^h` roots
/// of 32 bytes, the root of query index `i` being entry `i >> depth`) and
/// fold it at `fold_point`. Returns per query the fold and the check wire.
fn openings<T: CircuitTrait>(
    b: &mut T,
    opening: &OpeningInputs,
    queries: &[Vec<usize>],
    cap: &[Byte],
    fold_point: &[Elem],
    profile: &mut Profile,
) -> (Vec<Elem>, Vec<usize>) {
    let roots: Vec<Vec<usize>> = cap.chunks(32).map(bytes_to_wires).collect();
    assert!(roots.len().is_power_of_two(), "a cap is a power of two of roots");
    let height = roots.len().trailing_zeros() as usize;
    let mut folds = Vec::new();
    let mut checks = Vec::new();
    for ((elems, bits), siblings) in opening.rows.iter().zip(queries).zip(&opening.siblings) {
        assert_eq!(siblings.len() + height, bits.len(), "the path reaches the cap layer");
        // The row, as elements for the fold and as bytes for the leaf.
        let row_bytes: Vec<Byte> = elems.iter().flat_map(|e| wires_to_bytes(e)).collect();
        let mut node = bytes_to_wires(&blake3::hash_bytes(b, &row_bytes));
        profile.mark(b, "leaf hashes");
        for (level, sibling) in siblings.iter().enumerate() {
            let sib = bytes_to_wires(sibling);
            // The running node is the right child when the index bit is set.
            let left = mux(b, bits[level], &node, &sib);
            let right = mux(b, bits[level], &sib, &node);
            let pair: Vec<Byte> = [wires_to_bytes(&left), wires_to_bytes(&right)].concat();
            node = bytes_to_wires(&blake3::hash_bytes(b, &pair));
        }
        profile.mark(b, "merkle paths");
        let root = select(b, &roots, &bits[siblings.len()..]);
        checks.push(equal(b, &node, &root));
        profile.mark(b, "cap selection");
        folds.push(eval_multilinear(b, elems, fold_point));
        profile.mark(b, "query folds");
    }
    (folds, checks)
}

// ---------------------------------------------------------------------------
// The verifier.
// ---------------------------------------------------------------------------

/// The circuit, its witness for the proof it was built from, and its size.
pub struct Built {
    pub circuit: CircuitAdapter,
    pub witness: Vec<bool>,
    pub output: usize,
    pub counts: GateCounts,
    pub flushes: usize,
}

/// What building on any backend yields: the output wire, the transcript's
/// flush count and the witness the proof puts on the inputs.
pub struct Shape {
    pub output: usize,
    pub flushes: usize,
    pub witness: Vec<bool>,
    pub profile: Profile,
}

/// Build the verifier circuit for `cfg` on `CircuitAdapter`, keeping the gates.
pub fn build(cfg: &Config, d: &Data) -> Built {
    let mut b = CircuitAdapter::default();
    let shape = build_with(&mut b, cfg, d);
    let counts = b.gate_counts();
    Built { circuit: b, witness: shape.witness, output: shape.output, counts, flushes: shape.flushes }
}

/// Build the verifier circuit for `cfg` on any backend, with the values `d`
/// puts on its inputs.
pub fn build_with<T: ValuedBuilder>(b: &mut T, cfg: &Config, d: &Data) -> Shape {
    // The reference run, for the query indices the expanded paths need.
    let ch = reference::transcript(cfg, d, &mut reference::Challenger::new());
    build_with_prefix(b, cfg, d, &ch, |_, _, _, _| PrefixOut { points: Vec::new(), values: Vec::new() })
}

/// Build with a layer in front of the opening: `prefix` runs on the sponge
/// after the commitment is absorbed, may push its own checks and profile
/// marks, and hands over the claims' given points and values. Its inputs
/// must have been allocated before this call, and `ch` must be the
/// reference run of the same prefix.
pub fn build_with_prefix<T: ValuedBuilder>(
    b: &mut T,
    cfg: &Config,
    d: &Data,
    ch: &reference::Challenges,
    prefix: impl FnOnce(&mut T, &mut Sponge, &mut Vec<usize>, &mut Profile) -> PrefixOut,
) -> Shape {
    let mut profile = Profile::default();
    let inputs = Inputs::allocate(b, cfg, d, ch);
    let mut checks: Vec<usize> = Vec::new();
    let (t, m, flushes) = {
        let profile_ref = &mut profile;
        let prefix = |b: &mut T, s: &mut Sponge, checks: &mut Vec<usize>| prefix(b, s, checks, profile_ref);
        transcript(b, &inputs, cfg, d, prefix, &mut checks)
    };
    profile.mark(b, "transcript (sponge)");
    checks.extend(t.pow_checks.iter().copied());

    // The initial constraint and claim.
    let mut eq_groups: Vec<Vec<Vec<Elem>>> = Vec::new();
    let mut eval_groups: Vec<Vec<Elem>> = Vec::new();
    for (i, ((shape, y), evals)) in cfg.claims.iter().zip(&t.opening_points).zip(&m.openings).enumerate() {
        let points: Vec<Vec<Elem>> = if cfg.given_points {
            assert_eq!(shape.selectors, vec![Vec::<F>::new()], "a given point names the whole polynomial");
            vec![t.given_points[i].clone()]
        } else {
            let row = expand_univariate(b, y, shape.row_vars);
            shape
                .selectors
                .iter()
                .map(|sel| {
                    let sel_wires: Vec<Elem> = sel.iter().map(|&c| tower::constant(b, c.to_repr(), 128)).collect();
                    sel_wires.into_iter().chain(row.iter().cloned()).collect()
                })
                .collect()
        };
        eq_groups.push(points);
        eval_groups.push(evals.clone());
    }
    if !t.initial_ood_points.is_empty() {
        let points = t.initial_ood_points.iter().map(|y| expand_univariate(b, y, cfg.num_variables)).collect();
        eq_groups.push(points);
        eval_groups.push(m.initial_ood_answers.clone());
    }
    let mut claim = zero_elem(b);
    let mut shift = 0;
    for g in &eval_groups {
        combine_into(b, &mut claim, &t.alpha, shift, g);
        shift += g.len();
    }
    // (challenge, arity, initial power, eq points, direct points); the eq
    // points keep their statement order, openings then OOD.
    let mut constraints: Vec<(Elem, usize, usize, Vec<Vec<Elem>>, Vec<Vec<Elem>>)> =
        vec![(t.alpha.clone(), cfg.num_variables, 0, eq_groups.concat(), Vec::new())];

    profile.mark(b, "initial claim");
    for (r, x) in m.initial_sumcheck.iter().zip(&t.initial_folding) {
        claim = sumcheck_round(b, &claim, &r[0], &r[1], x);
    }
    profile.mark(b, "sumcheck rounds");
    let mut randomness: Vec<Elem> = t.initial_folding.clone();
    let mut prev_root: Vec<Byte> = m.root.clone();
    let mut prev_folding: Vec<Elem> = t.initial_folding.clone();

    for (i, (rc, rt)) in cfg.rounds.iter().zip(&t.rounds).enumerate() {
        let reversed: Vec<Elem> = prev_folding.iter().rev().cloned().collect();
        let (folds, merkle) = openings(b, &inputs.rounds[i].opening, &rt.queries, &prev_root, &reversed, &mut profile);
        checks.extend(merkle);
        let points: Vec<Vec<Elem>> = rt.queries.iter().map(|bits| query_point(b, rc.num_variables, bits)).collect();
        profile.mark(b, "query points");
        let ood: Vec<Vec<Elem>> = rt.ood_points.iter().map(|y| expand_univariate(b, y, rc.num_variables)).collect();
        combine_into(b, &mut claim, &rt.combination, 1, &m.rounds[i].ood_answers);
        combine_into(b, &mut claim, &rt.combination, 1 + m.rounds[i].ood_answers.len(), &folds);
        constraints.push((rt.combination.clone(), rc.num_variables, 1, ood, points));
        profile.mark(b, "claim combination");
        for (r, x) in m.rounds[i].sumcheck.iter().zip(&rt.folding) {
            claim = sumcheck_round(b, &claim, &r[0], &r[1], x);
        }
        profile.mark(b, "sumcheck rounds");
        randomness.extend(rt.folding.iter().cloned());
        prev_root = m.rounds[i].root.clone();
        prev_folding = rt.folding.clone();
    }

    // The final openings against the final polynomial.
    let reversed: Vec<Elem> = prev_folding.iter().rev().cloned().collect();
    let (folds, merkle) = openings(b, &inputs.final_opening, &t.final_queries, &prev_root, &reversed, &mut profile);
    checks.extend(merkle);
    let final_vars = m.final_poly.len().trailing_zeros() as usize;
    for (fold, bits) in folds.iter().zip(&t.final_queries) {
        let point = query_point(b, final_vars, bits);
        profile.mark(b, "query points");
        let at = eval_coefficients(b, &m.final_poly, &point);
        checks.push(equal(b, &at, fold));
        profile.mark(b, "final polynomial at queries");
    }
    for (r, x) in m.final_sumcheck.iter().zip(&t.final_folding) {
        claim = sumcheck_round(b, &claim, &r[0], &r[1], x);
    }
    profile.mark(b, "sumcheck rounds");
    randomness.extend(t.final_folding.iter().cloned());

    // The weights in suffix order, and the closing identity.
    let reversed_all: Vec<Elem> = randomness.iter().rev().cloned().collect();
    let mut total = zero_elem(b);
    for (chi, arity, initial_power, eq_points, direct_points) in &constraints {
        let local = &reversed_all[..*arity];
        let mut shift = *initial_power;
        let eq_w: Vec<Elem> = eq_points.iter().map(|p| eq_eval(b, p, local)).collect();
        profile.mark(b, "closing eq weights");
        let mut acc = zero_elem(b);
        combine_into(b, &mut acc, chi, shift, &eq_w);
        shift += eq_w.len();
        profile.mark(b, "claim combination");
        let sel_w: Vec<Elem> = direct_points.iter().map(|p| select_point_weight(b, p, local)).collect();
        profile.mark(b, "closing query weights");
        combine_into(b, &mut acc, chi, shift, &sel_w);
        total = tower::add(b, &total, &acc);
        profile.mark(b, "claim combination");
    }
    let final_reversed: Vec<Elem> = t.final_folding.iter().rev().cloned().collect();
    let final_value = eval_multilinear(b, &m.final_poly, &final_reversed);
    let expected = tower::mul(b, &total, &final_value);
    checks.push(equal(b, &claim, &expected));

    profile.mark(b, "closing identity");
    let output = and_all(b, &checks);
    profile.mark(b, "closing identity");
    Shape { output, flushes, witness: inputs.witness, profile }
}
