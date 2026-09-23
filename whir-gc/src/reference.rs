//! The WHIR verifier over `GF(2^128)` on the additive Cantor domain, in plain
//! Rust: Plonky3's `WhirVerifier::verify` and the PCS adapter around it, as run
//! with `WhirProver<F, F, BooleanWhirDomain, _, BinaryChallenger<F, _>, SuffixProver>`.
//!
//! This is the specification the circuit mirrors. It is checked two ways in
//! `tests/binary_whir.rs`: the transcript op for op against a logged run of
//! Plonky3's verifier, and the whole verifier by accepting Plonky3's proofs.
//! The arithmetic is `p3-binary-field`'s own, since that is the oracle the
//! circuit's gadgets are checked against.
//!
//! # The transcript
//!
//! Everything is bytes. The challenger is `BinaryChallenger` over
//! `HashChallenger<u8, Blake3, 32>`: an observe clears the output buffer and
//! appends to the input; a sample refills, when the output is empty, by hashing
//! the whole input buffer, replacing the input with that digest (chaining),
//! then pops bytes from the *end* of the digest. A field element is 16 bytes
//! little-endian; a query index is 8 bytes read as a little-endian `u64` and
//! masked; a PoW check observes the 16-byte witness then requires `bits`
//! sampled bits to be zero. Every sub-transcript seeds the sponge with its
//! domain separator, a constant of the configuration taken here as data.
//!
//! The order, as logged from Plonky3 0.7.0 and attributed byte by byte:
//!
//!   1. the commitment seed, the Merkle cap (every root, 32 bytes each)
//!   2. per commitment OOD sample: its seed, draw the point, absorb the answer
//!   3. per opening claim: its seed, draw the point, absorb the evaluations
//!   4. the WHIR seed and the batching seed, then draw `alpha`
//!   5. the initial sumcheck: its seed; per round absorb `[c0, c_inf]`, PoW
//!      (observe the witness, sample `bits`), draw the folding randomness
//!   6. per intermediate round: absorb the cap; per OOD draw and absorb; PoW;
//!      the STIR queries, *stratified*: `num_queries` draws split into
//!      power-of-two strata, each draw 8 bytes masked to the stratum's width;
//!      draw `gamma`; the round's sumcheck as in 5
//!   7. absorb the final polynomial; PoW; the final queries; the final
//!      sumcheck as in 5 (no PoW when its bits are zero)
//!
//! # The arithmetic
//!
//! `SuffixProver` binding: folds use the previous folding randomness
//! *reversed*, the final value is the final polynomial at the final sumcheck
//! randomness reversed, and a constraint of arity `n` reads the *first* `n`
//! coordinates of the reversed total randomness. A query index `i` becomes
//! the domain point `x = sum of cantor_basis(r) over the set bits of i` and
//! the multilinear point `(S_{n-1}(x), …, S_0(x))` with `S_j(x)` the `j`-fold
//! iterate of `v ↦ v² + v`; its weight is `prod (r_i·(p_i − 1) + 1)` and the
//! final polynomial is checked against it in the coefficient basis. The
//! commitment's OOD and opening claims are `eq` weights at
//! `expand(y, ·)`, batched by `alpha` from `alpha^0`; a round's constraint is
//! batched by `gamma` from `gamma^1`.

use p3_binary_field::{BinaryField128, TowerLevel};
use p3_field::PrimeCharacteristicRing;

use crate::pruned::{self, Digest, compress};

pub type F = BinaryField128;

/// What the transcript needs of a challenger: bytes in, bytes out.
pub trait Sponge {
    fn observe(&mut self, byte: u8);
    fn sample(&mut self) -> u8;

    fn observe_bytes(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.observe(b);
        }
    }

    fn sample_bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// `BinaryChallenger::observe(F)`: 16 little-endian bytes.
    fn observe_elem(&mut self, x: F) {
        self.observe_bytes(&x.to_repr().to_le_bytes());
    }

    /// `BinaryChallenger::sample::<F>()`: 16 bytes, little-endian.
    fn sample_elem(&mut self) -> F {
        let bytes = self.sample_bytes(16);
        F::from_repr(u128::from_le_bytes(bytes.try_into().expect("16 bytes")))
    }

    /// `BinaryChallenger::sample_bits`: 8 bytes as a little-endian `u64`, masked.
    fn sample_bits(&mut self, bits: usize) -> usize {
        let bytes = self.sample_bytes(8);
        let v = u64::from_le_bytes(bytes.try_into().expect("8 bytes"));
        (v & ((1u64 << bits) - 1)) as usize
    }

    /// `check_witness`: absorb the witness, then `bits` sampled bits must be zero.
    fn check_witness(&mut self, bits: usize, witness: F) -> bool {
        if bits == 0 {
            return true;
        }
        self.observe_elem(witness);
        self.sample_bits(bits) == 0
    }
}

/// `HashChallenger<u8, Blake3, 32>` from an empty initial state.
#[derive(Clone, Debug, Default)]
pub struct Challenger {
    input: Vec<u8>,
    output: Vec<u8>,
}

impl Challenger {
    pub fn new() -> Self {
        Self::default()
    }

    /// The buffers, for tests that compare against Plonky3's.
    pub fn buffers(&self) -> (&[u8], &[u8]) {
        (&self.input, &self.output)
    }
}

impl Sponge for Challenger {
    fn observe(&mut self, byte: u8) {
        self.output.clear();
        self.input.push(byte);
    }

    fn sample(&mut self) -> u8 {
        if self.output.is_empty() {
            let digest = *blake3::hash(&self.input).as_bytes();
            self.input = digest.to_vec();
            self.output = digest.to_vec();
        }
        self.output.pop().expect("refilled")
    }
}

/// One intermediate round's public parameters.
#[derive(Clone, Debug)]
pub struct RoundConfig {
    pub ood_samples: usize,
    pub pow_bits: usize,
    pub num_queries: usize,
    /// log2 of the folded domain the queries index.
    pub index_width: usize,
    /// Variables of the polynomial this round commits to.
    pub num_variables: usize,
    /// Sumcheck rounds after this round's commitment.
    pub folding: usize,
    pub folding_pow_bits: usize,
}

/// A claim's shape: the row point's arity and, per opening, the column
/// selector's coordinates that *prefix* it (`SuffixProver` lifts as prefix).
#[derive(Clone, Debug)]
pub struct ClaimShape {
    pub row_vars: usize,
    pub selectors: Vec<Vec<F>>,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub num_variables: usize,
    pub commitment_ood_samples: usize,
    pub claims: Vec<ClaimShape>,
    pub initial_folding: usize,
    pub initial_folding_pow_bits: usize,
    pub rounds: Vec<RoundConfig>,
    pub final_pow_bits: usize,
    pub final_queries: usize,
    pub final_index_width: usize,
    pub final_sumcheck_rounds: usize,
    pub final_folding_pow_bits: usize,
}

#[derive(Clone, Debug)]
pub struct SumcheckRoundData {
    pub poly: [F; 2],
    pub pow_witness: F,
}

/// A commitment opened at the transcript's queries.
#[derive(Clone, Debug)]
pub struct Opening {
    /// Per query in draw order, the row.
    pub rows: Vec<Vec<F>>,
    pub boundaries: Vec<Digest>,
}

#[derive(Clone, Debug)]
pub struct RoundData {
    /// The Merkle cap, every root's 32 bytes in order.
    pub cap: Vec<u8>,
    pub ood_answers: Vec<F>,
    pub pow_witness: F,
    pub seed_sumcheck: Vec<u8>,
    pub sumcheck: Vec<SumcheckRoundData>,
    /// The *previous* commitment's opening at this round's queries.
    pub opening: Opening,
}

#[derive(Clone, Debug)]
pub struct Data {
    pub seed_commitment: Vec<u8>,
    pub seed_virtual: Vec<Vec<u8>>,
    pub seed_claim: Vec<Vec<u8>>,
    /// The WHIR seed and the batching seed together: one block in the transcript.
    pub seed_whir_batching: Vec<u8>,
    pub seed_initial_sumcheck: Vec<u8>,
    pub seed_final_sumcheck: Vec<u8>,
    pub cap: Vec<u8>,
    pub initial_ood_answers: Vec<F>,
    pub openings: Vec<Vec<F>>,
    pub initial_sumcheck: Vec<SumcheckRoundData>,
    pub rounds: Vec<RoundData>,
    pub final_poly: Vec<F>,
    pub final_pow_witness: F,
    pub final_sumcheck: Vec<SumcheckRoundData>,
    pub final_opening: Opening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoundChallenges {
    pub ood_points: Vec<F>,
    pub queries: Vec<usize>,
    pub combination: F,
    pub folding: Vec<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Challenges {
    pub initial_ood_points: Vec<F>,
    pub opening_points: Vec<F>,
    pub alpha: F,
    pub initial_folding: Vec<F>,
    pub rounds: Vec<RoundChallenges>,
    pub final_queries: Vec<usize>,
    pub final_folding: Vec<F>,
    pub pow_ok: bool,
}

/// `query_draws`: none when every position is opened.
pub fn query_draws(index_width: usize, num_queries: usize) -> usize {
    if num_queries >= 1 << index_width { 0 } else { num_queries }
}

/// `query_summand_depths`: one stratum partition per set bit of the count,
/// deepest first.
pub fn summand_depths(draws: usize) -> Vec<usize> {
    let mut remaining = draws;
    let mut out = Vec::new();
    while remaining != 0 {
        let depth = usize::BITS as usize - 1 - remaining.leading_zeros() as usize;
        out.push(depth);
        remaining -= 1 << depth;
    }
    out
}

/// `assemble_query_indices`, stratified: per stratum partition of depth `d`,
/// `2^d` draws of `width − d` bits, index `(stratum << (width − d)) | low`.
pub fn stir_queries<S: Sponge>(s: &mut S, index_width: usize, num_queries: usize) -> Vec<usize> {
    let draws = query_draws(index_width, num_queries);
    if draws == 0 {
        return (0..1usize << index_width).collect();
    }
    let mut out = Vec::with_capacity(draws);
    for depth in summand_depths(draws) {
        for stratum in 0..1usize << depth {
            let low = s.sample_bits(index_width - depth);
            out.push((stratum << (index_width - depth)) | low);
        }
    }
    out
}

fn sumcheck_rounds<S: Sponge>(
    s: &mut S,
    rounds: &[SumcheckRoundData],
    expected: usize,
    pow_bits: usize,
    pow_ok: &mut bool,
) -> Vec<F> {
    assert_eq!(rounds.len(), expected, "sumcheck round count");
    rounds
        .iter()
        .map(|r| {
            s.observe_elem(r.poly[0]);
            s.observe_elem(r.poly[1]);
            *pow_ok &= s.check_witness(pow_bits, r.pow_witness);
            s.sample_elem()
        })
        .collect()
}

/// Drive `s` through the verifier's transcript and collect what it draws.
pub fn transcript<S: Sponge>(cfg: &Config, d: &Data, s: &mut S) -> Challenges {
    let mut pow_ok = true;
    s.observe_bytes(&d.seed_commitment);
    s.observe_bytes(&d.cap);
    assert_eq!(d.initial_ood_answers.len(), cfg.commitment_ood_samples);
    assert_eq!(d.seed_virtual.len(), cfg.commitment_ood_samples);
    let initial_ood_points = d
        .initial_ood_answers
        .iter()
        .zip(&d.seed_virtual)
        .map(|(&answer, seed)| {
            s.observe_bytes(seed);
            let point = s.sample_elem();
            s.observe_elem(answer);
            point
        })
        .collect();
    assert_eq!(d.seed_claim.len(), d.openings.len());
    let opening_points = d
        .openings
        .iter()
        .zip(&d.seed_claim)
        .map(|(evals, seed)| {
            s.observe_bytes(seed);
            let point = s.sample_elem();
            for &e in evals {
                s.observe_elem(e);
            }
            point
        })
        .collect();
    s.observe_bytes(&d.seed_whir_batching);
    let alpha = s.sample_elem();
    s.observe_bytes(&d.seed_initial_sumcheck);
    let initial_folding = sumcheck_rounds(
        s,
        &d.initial_sumcheck,
        cfg.initial_folding,
        cfg.initial_folding_pow_bits,
        &mut pow_ok,
    );
    assert_eq!(d.rounds.len(), cfg.rounds.len());
    let rounds = cfg
        .rounds
        .iter()
        .zip(&d.rounds)
        .map(|(rc, rd)| {
            s.observe_bytes(&rd.cap);
            assert_eq!(rd.ood_answers.len(), rc.ood_samples);
            let ood_points = rd
                .ood_answers
                .iter()
                .map(|&answer| {
                    let point = s.sample_elem();
                    s.observe_elem(answer);
                    point
                })
                .collect();
            pow_ok &= s.check_witness(rc.pow_bits, rd.pow_witness);
            let queries = stir_queries(s, rc.index_width, rc.num_queries);
            let combination = s.sample_elem();
            s.observe_bytes(&rd.seed_sumcheck);
            let folding = sumcheck_rounds(s, &rd.sumcheck, rc.folding, rc.folding_pow_bits, &mut pow_ok);
            RoundChallenges { ood_points, queries, combination, folding }
        })
        .collect();
    for &c in &d.final_poly {
        s.observe_elem(c);
    }
    pow_ok &= s.check_witness(cfg.final_pow_bits, d.final_pow_witness);
    let final_queries = stir_queries(s, cfg.final_index_width, cfg.final_queries);
    s.observe_bytes(&d.seed_final_sumcheck);
    let final_folding = sumcheck_rounds(
        s,
        &d.final_sumcheck,
        cfg.final_sumcheck_rounds,
        cfg.final_folding_pow_bits,
        &mut pow_ok,
    );
    Challenges { initial_ood_points, opening_points, alpha, initial_folding, rounds, final_queries, final_folding, pow_ok }
}

// ---------------------------------------------------------------------------
// Arithmetic.
// ---------------------------------------------------------------------------

/// `Point::expand_from_univariate`: `[y^(2^(m-1)), …, y², y]`.
pub fn expand_univariate(y: F, m: usize) -> Vec<F> {
    let mut out = vec![F::ZERO; m];
    let mut cur = y;
    for i in (0..m).rev() {
        out[i] = cur;
        cur = cur.square();
    }
    out
}

/// `Point::eval_eq`, as Plonky3 writes it (`2·p·r − p − r + 1`, which is
/// `1 + p + r` in characteristic two).
pub fn eq_eval(p: &[F], r: &[F]) -> F {
    assert_eq!(p.len(), r.len());
    p.iter().zip(r).map(|(&l, &r)| r.double() * l - l - r + F::ONE).product()
}

/// `extrapolate_01inf`.
pub fn extrapolate_01inf(e0: F, e1: F, e_inf: F, r: F) -> F {
    e0 * (F::ONE - r) + e1 * r + e_inf * (r * (r - F::ONE))
}

pub fn sumcheck_round(claim: F, c0: F, c_inf: F, r: F) -> F {
    extrapolate_01inf(c0, claim - c0, c_inf, r)
}

/// `eval_multilinear_recursive`: `2^n` evaluations, the last variable pairs
/// adjacent entries.
pub fn eval_multilinear(evals: &[F], point: &[F]) -> F {
    assert_eq!(evals.len(), 1 << point.len());
    let mut cur = evals.to_vec();
    for &x in point.iter().rev() {
        cur = (0..cur.len() / 2).map(|j| cur[2 * j] + x * (cur[2 * j + 1] - cur[2 * j])).collect();
    }
    cur[0]
}

/// `SelectStatement::verify` for a direct point: the coefficient table folded
/// coordinate by coordinate, last coordinate first: `s[i] = s[2i] + s[2i+1]·c`.
pub fn eval_coefficients(coeffs: &[F], point: &[F]) -> F {
    assert_eq!(coeffs.len(), 1 << point.len());
    let mut cur = coeffs.to_vec();
    for &c in point.iter().rev() {
        cur = (0..cur.len() / 2).map(|j| cur[2 * j] + cur[2 * j + 1] * c).collect();
    }
    cur[0]
}

/// The weight of a direct point: `prod (r_i·(p_i − 1) + 1)`.
pub fn select_point_weight(p: &[F], r: &[F]) -> F {
    assert_eq!(p.len(), r.len());
    p.iter().zip(r).map(|(&c, &r)| r * (c - F::ONE) + F::ONE).product()
}

/// `domain_point`: the Cantor-basis vector with the index's bits.
pub fn domain_point(index: usize) -> F {
    let mut point = F::ZERO;
    let mut remaining = index;
    let mut r = 0;
    while remaining != 0 {
        if remaining & 1 == 1 {
            point += F::cantor_basis(r);
        }
        remaining >>= 1;
        r += 1;
    }
    point
}

/// `subspace_polynomial(j, x)`: `j` iterations of `v ↦ v² + v`.
pub fn subspace_polynomial(j: usize, x: F) -> F {
    let mut v = x;
    for _ in 0..j {
        v = v.square() + v;
    }
    v
}

/// The multilinear point of a queried position: `(S_{n-1}(x), …, S_0(x))`.
pub fn query_point(num_variables: usize, index: usize) -> Vec<F> {
    let x = domain_point(index);
    (0..num_variables).rev().map(|j| subspace_polynomial(j, x)).collect()
}

fn combine_into(claim: &mut F, chi: F, shift: usize, evals: &[F]) {
    let mut power = chi.exp_u64(shift as u64);
    for &e in evals {
        *claim += power * e;
        power *= chi;
    }
}

#[derive(Clone, Debug)]
enum Statement {
    Eq(Vec<Vec<F>>),
    Points(Vec<Vec<F>>),
}

#[derive(Clone, Debug)]
struct Constraint {
    challenge: F,
    num_variables: usize,
    initial_power: usize,
    statements: Vec<Statement>,
}

/// `eval_constraints_poly` in suffix order: arity `n` reads the first `n`
/// coordinates of the reversed randomness.
fn weights(constraints: &[Constraint], randomness: &[F]) -> F {
    let reversed: Vec<F> = randomness.iter().rev().copied().collect();
    let mut total = F::ZERO;
    for c in constraints {
        let local = &reversed[..c.num_variables];
        let mut shift = c.initial_power;
        for s in &c.statements {
            let ws: Vec<F> = match s {
                Statement::Eq(points) => points.iter().map(|p| eq_eval(p, local)).collect(),
                Statement::Points(points) => points.iter().map(|p| select_point_weight(p, local)).collect(),
            };
            let mut acc = F::ZERO;
            combine_into(&mut acc, c.challenge, shift, &ws);
            total += acc;
            shift += ws.len();
        }
    }
    total
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Pow,
    Opening { round: usize },
    Merkle { round: usize, query: usize },
    FinalStir { query: usize },
    Closing { claimed: u128, expected: u128 },
}

/// `SerializingHasher<Blake3>` on a row: Blake3 of the elements' bytes.
pub fn leaf(row: &[F]) -> Digest {
    let bytes: Vec<u8> = row.iter().flat_map(|x| x.to_repr().to_le_bytes()).collect();
    *blake3::hash(&bytes).as_bytes()
}

/// Every query's path must reach its root in the cap.
fn check_opening(
    opening: &Opening,
    cap: &[u8],
    indices: &[usize],
    index_width: usize,
    round: usize,
) -> Result<(), Error> {
    if opening.rows.len() != indices.len() || cap.len() % 32 != 0 || cap.is_empty() {
        return Err(Error::Opening { round });
    }
    let roots: Vec<Digest> = cap.chunks(32).map(|c| c.try_into().expect("32 bytes")).collect();
    let cap_height = roots.len().trailing_zeros() as usize;
    assert!(roots.len().is_power_of_two() && cap_height <= index_width);
    let depth = index_width - cap_height;
    let leaves: Vec<Digest> = opening.rows.iter().map(|r| leaf(r)).collect();
    let paths = pruned::expand(&opening.boundaries, indices, &leaves, index_width, cap_height)
        .map_err(|_| Error::Opening { round })?;
    for (query, path) in paths.iter().enumerate() {
        let mut cur = path.leaf;
        for (level, sib) in path.siblings.iter().enumerate() {
            cur = if (path.index >> level) & 1 == 1 { compress(sib, &cur) } else { compress(&cur, sib) };
        }
        if cur != roots[path.index >> depth] {
            return Err(Error::Merkle { round, query });
        }
    }
    Ok(())
}

/// What an accepted proof pinned down.
#[derive(Clone, Debug)]
pub struct Verified {
    pub challenges: Challenges,
    pub claimed: F,
    pub weights: F,
    pub final_value: F,
}

/// The verifier: the transcript, then the arithmetic.
pub fn verify(cfg: &Config, d: &Data) -> Result<Verified, Error> {
    let ch = transcript(cfg, d, &mut Challenger::new());
    if !ch.pow_ok {
        return Err(Error::Pow);
    }

    // The initial constraint: opening claims, then the OOD claims, under alpha.
    let mut statements = Vec::new();
    let mut groups: Vec<Vec<F>> = Vec::new();
    for ((shape, &y), evals) in cfg.claims.iter().zip(&ch.opening_points).zip(&d.openings) {
        let row = expand_univariate(y, shape.row_vars);
        let points: Vec<Vec<F>> = shape
            .selectors
            .iter()
            .map(|sel| sel.iter().copied().chain(row.iter().copied()).collect())
            .collect();
        assert!(points.iter().all(|p| p.len() == cfg.num_variables));
        statements.push(Statement::Eq(points));
        groups.push(evals.clone());
    }
    if !ch.initial_ood_points.is_empty() {
        statements.push(Statement::Eq(
            ch.initial_ood_points.iter().map(|&y| expand_univariate(y, cfg.num_variables)).collect(),
        ));
        groups.push(d.initial_ood_answers.clone());
    }
    let mut claimed = F::ZERO;
    let mut shift = 0;
    for g in &groups {
        combine_into(&mut claimed, ch.alpha, shift, g);
        shift += g.len();
    }
    let mut constraints = vec![Constraint {
        challenge: ch.alpha,
        num_variables: cfg.num_variables,
        initial_power: 0,
        statements,
    }];

    for (r, &x) in d.initial_sumcheck.iter().zip(&ch.initial_folding) {
        claimed = sumcheck_round(claimed, r.poly[0], r.poly[1], x);
    }
    let mut randomness: Vec<F> = ch.initial_folding.clone();
    let mut prev_cap: &[u8] = &d.cap;
    let mut prev_folding: Vec<F> = ch.initial_folding.clone();

    for (i, ((rc, rd), rch)) in cfg.rounds.iter().zip(&d.rounds).zip(&ch.rounds).enumerate() {
        check_opening(&rd.opening, prev_cap, &rch.queries, rc.index_width, i)?;
        let reversed: Vec<F> = prev_folding.iter().rev().copied().collect();
        let folds: Vec<F> = rd.opening.rows.iter().map(|row| eval_multilinear(row, &reversed)).collect();
        let points: Vec<Vec<F>> = rch.queries.iter().map(|&q| query_point(rc.num_variables, q)).collect();
        let ood: Vec<Vec<F>> = rch.ood_points.iter().map(|&y| expand_univariate(y, rc.num_variables)).collect();
        combine_into(&mut claimed, rch.combination, 1, &rd.ood_answers);
        combine_into(&mut claimed, rch.combination, 1 + rd.ood_answers.len(), &folds);
        constraints.push(Constraint {
            challenge: rch.combination,
            num_variables: rc.num_variables,
            initial_power: 1,
            statements: vec![Statement::Eq(ood), Statement::Points(points)],
        });
        for (r, &x) in rd.sumcheck.iter().zip(&rch.folding) {
            claimed = sumcheck_round(claimed, r.poly[0], r.poly[1], x);
        }
        randomness.extend_from_slice(&rch.folding);
        prev_cap = &rd.cap;
        prev_folding = rch.folding.clone();
    }

    let final_round = cfg.rounds.len();
    check_opening(&d.final_opening, prev_cap, &ch.final_queries, cfg.final_index_width, final_round)?;
    let reversed: Vec<F> = prev_folding.iter().rev().copied().collect();
    let final_vars = d.final_poly.len().trailing_zeros() as usize;
    for (query, (row, &q)) in d.final_opening.rows.iter().zip(&ch.final_queries).enumerate() {
        let fold = eval_multilinear(row, &reversed);
        if eval_coefficients(&d.final_poly, &query_point(final_vars, q)) != fold {
            return Err(Error::FinalStir { query });
        }
    }
    for (r, &x) in d.final_sumcheck.iter().zip(&ch.final_folding) {
        claimed = sumcheck_round(claimed, r.poly[0], r.poly[1], x);
    }
    randomness.extend_from_slice(&ch.final_folding);
    let w = weights(&constraints, &randomness);
    let final_reversed: Vec<F> = ch.final_folding.iter().rev().copied().collect();
    let final_value = eval_multilinear(&d.final_poly, &final_reversed);
    let expected = w * final_value;
    if claimed != expected {
        return Err(Error::Closing { claimed: claimed.to_repr(), expected: expected.to_repr() });
    }
    Ok(Verified { challenges: ch, claimed, weights: w, final_value })
}
