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

use crate::blake3;
use crate::pruned;
use crate::reference::{self, Config, Data, F};
use crate::tower;

pub type Byte = [usize; 8];
/// A field element: 128 wires, bit `i` of the little-endian representation.
pub type Elem = Vec<usize>;

const ELEM_BYTES: usize = 16;
const INDEX_BYTES: usize = 8;
/// The Blake3 gadget hashes one chunk.
const CHUNK: usize = 1024;

// ---------------------------------------------------------------------------
// Bit helpers.
// ---------------------------------------------------------------------------

fn not<T: CircuitTrait>(b: &mut T, x: usize) -> usize {
    let one = b.one();
    b.xor_wire(x, one)
}

fn or_all<T: CircuitTrait>(b: &mut T, xs: &[usize]) -> usize {
    let mut acc = b.zero();
    for &x in xs {
        acc = b.or_wire(acc, x);
    }
    acc
}

fn and_all<T: CircuitTrait>(b: &mut T, xs: &[usize]) -> usize {
    let mut acc = b.one();
    for &x in xs {
        acc = b.and_wire(acc, x);
    }
    acc
}

/// 1 iff the two wire vectors carry the same bits.
fn equal<T: CircuitTrait>(b: &mut T, x: &[usize], y: &[usize]) -> usize {
    assert_eq!(x.len(), y.len());
    let diff: Vec<usize> = x.iter().zip(y).map(|(&p, &q)| b.xor_wire(p, q)).collect();
    let any = or_all(b, &diff);
    not(b, any)
}

/// `sel ? y : x`, bit by bit: `x ⊕ (sel ∧ (x ⊕ y))`, one AND per bit.
fn mux<T: CircuitTrait>(b: &mut T, sel: usize, x: &[usize], y: &[usize]) -> Vec<usize> {
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

fn bytes_to_wires(bytes: &[Byte]) -> Vec<usize> {
    bytes.iter().flat_map(|b| b.iter().copied()).collect()
}

fn wires_to_bytes(wires: &[usize]) -> Vec<Byte> {
    assert_eq!(wires.len() % 8, 0);
    wires.chunks(8).map(|c| c.try_into().expect("8 wires")).collect()
}

fn const_bytes<T: CircuitTrait>(b: &mut T, bytes: &[u8]) -> Vec<Byte> {
    let zero = b.zero();
    let one = b.one();
    bytes.iter().map(|&v| core::array::from_fn(|i| if (v >> i) & 1 == 1 { one } else { zero })).collect()
}

fn elem_bits(x: F) -> Vec<bool> {
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

impl Inputs {
    fn bytes<T: CircuitTrait>(&mut self, b: &mut T, bytes: &[u8]) -> Vec<Byte> {
        bytes
            .iter()
            .map(|&v| {
                let w: Byte = b.fresh();
                self.witness.extend((0..8).map(|i| (v >> i) & 1 == 1));
                w
            })
            .collect()
    }

    fn elem<T: CircuitTrait>(&mut self, b: &mut T, x: F) -> Elem {
        let w = tower::fresh(b, 128);
        self.witness.extend(elem_bits(x));
        w
    }

    fn sumcheck<T: CircuitTrait>(&mut self, b: &mut T, rounds: &[reference::SumcheckRoundData], pow_bits: usize) -> Vec<SumcheckInputs> {
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
    fn opening<T: CircuitTrait>(&mut self, b: &mut T, o: &reference::Opening, indices: &[usize], index_width: usize) -> OpeningInputs {
        let leaves: Vec<pruned::Digest> = o.rows.iter().map(|r| reference::leaf(r)).collect();
        let paths = pruned::expand(&o.boundaries, indices, &leaves, index_width, 0).expect("openings expand");
        let rows = o.rows.iter().map(|row| row.iter().map(|&x| self.elem(b, x)).collect()).collect();
        let siblings = paths.iter().map(|p| p.siblings.iter().map(|s| self.bytes(b, s)).collect()).collect();
        OpeningInputs { rows, siblings }
    }

    /// Lay out the proof: every message in transcript order, then the openings.
    pub fn allocate<T: CircuitTrait>(b: &mut T, cfg: &Config, d: &Data, ch: &reference::Challenges) -> Self {
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
        for (i, (rc, rd)) in cfg.rounds.iter().zip(&d.rounds).enumerate() {
            let root = me.bytes(b, &rd.cap);
            let ood_answers = rd.ood_answers.iter().map(|&x| me.elem(b, x)).collect();
            let pow_witness = (rc.pow_bits > 0).then(|| me.elem(b, rd.pow_witness));
            let sumcheck = me.sumcheck(b, &rd.sumcheck, rc.folding_pow_bits);
            let opening = me.opening(b, &rd.opening, &ch.rounds[i].queries, rc.index_width);
            me.rounds.push(RoundInputs { root, ood_answers, pow_witness, sumcheck, opening });
        }
        me.final_poly = d.final_poly.iter().map(|&x| me.elem(b, x)).collect();
        me.final_pow_witness = (cfg.final_pow_bits > 0).then(|| me.elem(b, d.final_pow_witness));
        me.final_sumcheck = me.sumcheck(b, &d.final_sumcheck, cfg.final_folding_pow_bits);
        me.final_opening = me.opening(b, &d.final_opening, &ch.final_queries, cfg.final_index_width);
        me
    }
}

// ---------------------------------------------------------------------------
// The wire-level challenger.
// ---------------------------------------------------------------------------

/// `HashChallenger<u8, Blake3, 32>` over wires: the input buffer is hashed
/// whole on refill, the digest chains into the input, and bytes are popped
/// from the digest's end.
struct Sponge {
    input: Vec<Byte>,
    output: Vec<Byte>,
    pub flushes: usize,
}

impl Sponge {
    fn new() -> Self {
        Self { input: Vec::new(), output: Vec::new(), flushes: 0 }
    }

    fn observe(&mut self, bytes: &[Byte]) {
        if !bytes.is_empty() {
            self.output.clear();
            self.input.extend_from_slice(bytes);
        }
    }

    fn sample<T: CircuitTrait>(&mut self, b: &mut T) -> Byte {
        if self.output.is_empty() {
            assert!(self.input.len() <= CHUNK, "a flush input of {} bytes needs multi-chunk Blake3", self.input.len());
            let digest = blake3::hash_bytes(b, &self.input);
            self.flushes += 1;
            self.input = digest.to_vec();
            self.output = digest.to_vec();
        }
        self.output.pop().expect("refilled")
    }

    fn sample_bytes<T: CircuitTrait>(&mut self, b: &mut T, n: usize) -> Vec<Byte> {
        (0..n).map(|_| self.sample(b)).collect()
    }

    fn observe_elem(&mut self, x: &Elem) {
        self.observe(&wires_to_bytes(x));
    }

    fn sample_elem<T: CircuitTrait>(&mut self, b: &mut T) -> Elem {
        bytes_to_wires(&self.sample_bytes(b, ELEM_BYTES))
    }

    /// The low `bits` of an 8-byte draw, as wires.
    fn sample_bits<T: CircuitTrait>(&mut self, b: &mut T, bits: usize) -> Vec<usize> {
        let bytes = self.sample_bytes(b, INDEX_BYTES);
        bytes_to_wires(&bytes)[..bits].to_vec()
    }

    /// `check_witness`: absorb the witness; 1 iff `bits` sampled bits are zero.
    fn check_witness<T: CircuitTrait>(&mut self, b: &mut T, bits: usize, witness: &Elem) -> Option<usize> {
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

fn one_elem<T: CircuitTrait>(b: &mut T) -> Elem {
    tower::constant(b, 1, 128)
}

fn zero_elem<T: CircuitTrait>(b: &mut T) -> Elem {
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
fn eq_eval<T: CircuitTrait>(b: &mut T, p: &[Elem], r: &[Elem]) -> Elem {
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
fn sumcheck_round<T: CircuitTrait>(b: &mut T, claim: &Elem, c0: &Elem, c_inf: &Elem, r: &Elem) -> Elem {
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
fn eval_multilinear<T: CircuitTrait>(b: &mut T, evals: &[Elem], point: &[Elem]) -> Elem {
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
fn combine_into<T: CircuitTrait>(b: &mut T, claim: &mut Elem, chi: &Elem, shift: usize, evals: &[Elem]) {
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

fn transcript<T: CircuitTrait>(b: &mut T, inputs: &Inputs, cfg: &Config, d: &Data) -> (TranscriptWires, Messages, usize) {
    let mut s = Sponge::new();
    let mut pow_checks = Vec::new();

    let seed = const_bytes(b, &d.seed_commitment);
    s.observe(&seed);
    let root = inputs.root.clone();
    s.observe(&root);
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
        opening_points.push(s.sample_elem(b));
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

/// Authenticate every query's row against `root` and fold it at `fold_point`.
/// Returns per query the fold and the check wire.
fn openings<T: CircuitTrait>(
    b: &mut T,
    opening: &OpeningInputs,
    queries: &[Vec<usize>],
    root: &[Byte],
    fold_point: &[Elem],
) -> (Vec<Elem>, Vec<usize>) {
    assert_eq!(root.len(), 32, "a single root: cap height zero");
    let root_wires = bytes_to_wires(root);
    let mut folds = Vec::new();
    let mut checks = Vec::new();
    for ((elems, bits), siblings) in opening.rows.iter().zip(queries).zip(&opening.siblings) {
        // The row, as elements for the fold and as bytes for the leaf.
        let row_bytes: Vec<Byte> = elems.iter().flat_map(|e| wires_to_bytes(e)).collect();
        let mut node = bytes_to_wires(&blake3::hash_bytes(b, &row_bytes));
        for (level, sibling) in siblings.iter().enumerate() {
            let sib = bytes_to_wires(sibling);
            // The running node is the right child when the index bit is set.
            let left = mux(b, bits[level], &node, &sib);
            let right = mux(b, bits[level], &sib, &node);
            let pair: Vec<Byte> = [wires_to_bytes(&left), wires_to_bytes(&right)].concat();
            node = bytes_to_wires(&blake3::hash_bytes(b, &pair));
        }
        checks.push(equal(b, &node, &root_wires));
        folds.push(eval_multilinear(b, elems, fold_point));
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

/// Build the verifier circuit for `cfg`, with the witness `d` puts on it.
pub fn build(cfg: &Config, d: &Data) -> Built {
    // The reference run, for the query indices the expanded paths need.
    let ch = reference::transcript(cfg, d, &mut reference::Challenger::new());

    let mut b = CircuitAdapter::default();
    let inputs = Inputs::allocate(&mut b, cfg, d, &ch);
    let (t, m, flushes) = transcript(&mut b, &inputs, cfg, d);
    let mut checks: Vec<usize> = t.pow_checks.clone();

    // The initial constraint and claim.
    let mut eq_groups: Vec<Vec<Vec<Elem>>> = Vec::new();
    let mut eval_groups: Vec<Vec<Elem>> = Vec::new();
    for ((shape, y), evals) in cfg.claims.iter().zip(&t.opening_points).zip(&m.openings) {
        let row = expand_univariate(&mut b, y, shape.row_vars);
        let points: Vec<Vec<Elem>> = shape
            .selectors
            .iter()
            .map(|sel| {
                let sel_wires: Vec<Elem> = sel.iter().map(|&c| tower::constant(&mut b, c.to_repr(), 128)).collect();
                sel_wires.into_iter().chain(row.iter().cloned()).collect()
            })
            .collect();
        eq_groups.push(points);
        eval_groups.push(evals.clone());
    }
    if !t.initial_ood_points.is_empty() {
        let points = t.initial_ood_points.iter().map(|y| expand_univariate(&mut b, y, cfg.num_variables)).collect();
        eq_groups.push(points);
        eval_groups.push(m.initial_ood_answers.clone());
    }
    let mut claim = zero_elem(&mut b);
    let mut shift = 0;
    for g in &eval_groups {
        combine_into(&mut b, &mut claim, &t.alpha, shift, g);
        shift += g.len();
    }
    // (challenge, arity, initial power, eq points, direct points); the eq
    // points keep their statement order, openings then OOD.
    let mut constraints: Vec<(Elem, usize, usize, Vec<Vec<Elem>>, Vec<Vec<Elem>>)> =
        vec![(t.alpha.clone(), cfg.num_variables, 0, eq_groups.concat(), Vec::new())];

    for (r, x) in m.initial_sumcheck.iter().zip(&t.initial_folding) {
        claim = sumcheck_round(&mut b, &claim, &r[0], &r[1], x);
    }
    let mut randomness: Vec<Elem> = t.initial_folding.clone();
    let mut prev_root: Vec<Byte> = m.root.clone();
    let mut prev_folding: Vec<Elem> = t.initial_folding.clone();

    for (i, (rc, rt)) in cfg.rounds.iter().zip(&t.rounds).enumerate() {
        let reversed: Vec<Elem> = prev_folding.iter().rev().cloned().collect();
        let (folds, merkle) = openings(&mut b, &inputs.rounds[i].opening, &rt.queries, &prev_root, &reversed);
        checks.extend(merkle);
        let points: Vec<Vec<Elem>> = rt.queries.iter().map(|bits| query_point(&mut b, rc.num_variables, bits)).collect();
        let ood: Vec<Vec<Elem>> = rt.ood_points.iter().map(|y| expand_univariate(&mut b, y, rc.num_variables)).collect();
        combine_into(&mut b, &mut claim, &rt.combination, 1, &m.rounds[i].ood_answers);
        combine_into(&mut b, &mut claim, &rt.combination, 1 + m.rounds[i].ood_answers.len(), &folds);
        constraints.push((rt.combination.clone(), rc.num_variables, 1, ood, points));
        for (r, x) in m.rounds[i].sumcheck.iter().zip(&rt.folding) {
            claim = sumcheck_round(&mut b, &claim, &r[0], &r[1], x);
        }
        randomness.extend(rt.folding.iter().cloned());
        prev_root = m.rounds[i].root.clone();
        prev_folding = rt.folding.clone();
    }

    // The final openings against the final polynomial.
    let reversed: Vec<Elem> = prev_folding.iter().rev().cloned().collect();
    let (folds, merkle) = openings(&mut b, &inputs.final_opening, &t.final_queries, &prev_root, &reversed);
    checks.extend(merkle);
    let final_vars = m.final_poly.len().trailing_zeros() as usize;
    for (fold, bits) in folds.iter().zip(&t.final_queries) {
        let point = query_point(&mut b, final_vars, bits);
        let at = eval_coefficients(&mut b, &m.final_poly, &point);
        checks.push(equal(&mut b, &at, fold));
    }
    for (r, x) in m.final_sumcheck.iter().zip(&t.final_folding) {
        claim = sumcheck_round(&mut b, &claim, &r[0], &r[1], x);
    }
    randomness.extend(t.final_folding.iter().cloned());

    // The weights in suffix order, and the closing identity.
    let reversed_all: Vec<Elem> = randomness.iter().rev().cloned().collect();
    let mut total = zero_elem(&mut b);
    for (chi, arity, initial_power, eq_points, direct_points) in &constraints {
        let local = &reversed_all[..*arity];
        let mut shift = *initial_power;
        let eq_w: Vec<Elem> = eq_points.iter().map(|p| eq_eval(&mut b, p, local)).collect();
        let mut acc = zero_elem(&mut b);
        combine_into(&mut b, &mut acc, chi, shift, &eq_w);
        shift += eq_w.len();
        let sel_w: Vec<Elem> = direct_points.iter().map(|p| select_point_weight(&mut b, p, local)).collect();
        combine_into(&mut b, &mut acc, chi, shift, &sel_w);
        total = tower::add(&mut b, &total, &acc);
    }
    let final_reversed: Vec<Elem> = t.final_folding.iter().rev().cloned().collect();
    let final_value = eval_multilinear(&mut b, &m.final_poly, &final_reversed);
    let expected = tower::mul(&mut b, &total, &final_value);
    checks.push(equal(&mut b, &claim, &expected));

    let output = and_all(&mut b, &checks);
    let counts = b.gate_counts();
    Built { circuit: b, witness: inputs.witness, output, counts, flushes }
}
