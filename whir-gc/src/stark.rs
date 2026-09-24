//! The multi-STARK layers in front of the WHIR opening, as Plonky3's
//! `p3-multi-stark` runs them over the Boolean WHIR trace commitment: the
//! zerocheck of the AIR, the batching of the opened columns into one bit-level
//! claim, and the bit ring switch that turns that claim into a `GF(2^128)`
//! claim on the packed polynomial WHIR committed to.
//!
//! This is the reference (field elements, not wires), op for op with the
//! Plonky3 verifier; `stark_circuit` mirrors it on wires. The transcript runs
//! as a prefix inside [`crate::reference::transcript_with`]: after the
//! commitment is absorbed and before the OOD draws, and it hands WHIR the
//! surviving point as the claim's given point.
//!
//! One AIR instance, no public values, no preprocessed columns, no lookups
//! (the Boolean WHIR harness refuses all three), every column read on the
//! current and the next row.

use std::collections::HashMap;
use std::sync::Arc;

use p3_air::{BaseEntry, BaseLeaf, SymbolicExpr, SymbolicExpression};
use p3_binary_field::TowerLevel;
use p3_field::{Field, PrimeCharacteristicRing};

use crate::reference::{extrapolate_01inf, F, Sponge};

/// Coordinates one packed element absorbs: `log2(128)`.
pub const ABSORBED: usize = 7;
/// The tensor's dimension: `GF(2^128)` over `GF(2)`.
pub const DIM: usize = 128;

/// The AIR, as the verifier needs it: its width and its constraints in the
/// order `eval` asserts them, over the current row (`Main { offset: 0 }`) and
/// the next row (`offset: 1`).
#[derive(Clone, Debug)]
pub struct Air {
    pub width: usize,
    pub constraints: Vec<SymbolicExpression<F>>,
}

/// The domain-separator seeds each layer absorbs, as bytes, from the run.
#[derive(Clone, Debug, Default)]
pub struct Seeds {
    pub zerocheck: Vec<u8>,
    pub generic_degree: Vec<u8>,
    pub column_batching: Vec<u8>,
    pub ring_switch: Vec<u8>,
    pub quadratic: Vec<u8>,
}

#[derive(Clone, Debug)]
pub struct Config {
    /// `log2` of the trace height.
    pub log_height: usize,
    pub width: usize,
    /// Grinding bits per zerocheck sumcheck round.
    pub pow_bits: usize,
    pub seeds: Seeds,
}

impl Config {
    /// Selector coordinates of a column: `log2(width.next_power_of_two())`.
    pub fn column_vars(&self) -> usize {
        self.width.next_power_of_two().trailing_zeros() as usize
    }

    /// Variables of the bit-level polynomial: the stacked layout's arity.
    pub fn bit_vars(&self) -> usize {
        self.log_height + self.column_vars()
    }

    /// Variables of the packed polynomial WHIR commits to.
    pub fn packed_vars(&self) -> usize {
        self.bit_vars() - ABSORBED
    }

    /// Whether the ring switch sends successor tensors (`log_height > 7`).
    pub fn sends_successor(&self) -> bool {
        self.log_height > ABSORBED
    }

    /// Row coordinates the successor keeps: `log_height - 7`.
    pub fn kept_rows(&self) -> usize {
        self.log_height.saturating_sub(ABSORBED)
    }
}

/// The proof's messages, in the order the transcript consumes them.
#[derive(Clone, Debug)]
pub struct Data {
    pub claimed_sum: F,
    /// Per zerocheck round: `h(0), h(2), h(3), h(4)` (node 1 is derived).
    pub round_polys: Vec<[F; 4]>,
    pub pow_witnesses: Vec<F>,
    /// The opened columns: current row, then next row.
    pub values: Vec<F>,
    /// The ring switch's tensor, 128 rows.
    pub tensor: Vec<F>,
    /// The carry and last tensors, when `log_height > 7`.
    pub successor: Option<(Vec<F>, Vec<F>)>,
    /// The ring switch's sumcheck: per round `h(0), h(inf)`.
    pub rs_sumcheck: Vec<[F; 2]>,
    pub final_eval: F,
}

#[derive(Clone, Debug)]
pub struct Challenges {
    pub alpha: F,
    pub beta: F,
    pub tau: Vec<F>,
    /// The zerocheck's bound point, and the sum it closed on.
    pub r: Vec<F>,
    pub final_sum: F,
    /// The column point.
    pub c: Vec<F>,
    /// Ring switch: batching point, tensor batching, sumcheck point.
    pub r_batch: Vec<F>,
    pub alpha_rs: Option<F>,
    pub r_prime: Vec<F>,
    /// The Boolean prefix the ring switch fixed (leading 0/1 coordinates of
    /// the column point), and the surviving point WHIR opens at.
    pub prefix: usize,
    pub surviving: Vec<F>,
    pub pow_ok: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Pow,
    ClaimedSum,
    Zerocheck,
    Incoming,
    Successor,
    RingSwitch,
}

// ---------------------------------------------------------------------------
// Field helpers.
// ---------------------------------------------------------------------------

/// `from_repr(i)`: the interpolation node `i`.
pub fn node(i: usize) -> F {
    F::from_repr(i as u128)
}

/// The eq table of `point`, big-endian: entry `i` is
/// `∏_j (1 + p_j + bit_{m-1-j}(i))`.
pub fn eq_table(point: &[F]) -> Vec<F> {
    let m = point.len();
    let mut table = vec![F::ONE];
    for &p in point {
        // Splitting on the next most significant bit.
        let mut next = Vec::with_capacity(table.len() * 2);
        for &t in &table {
            next.push(t * (F::ONE + p));
            next.push(t * p);
        }
        table = next;
    }
    debug_assert_eq!(table.len(), 1 << m);
    table
}

/// The degree-4 round polynomial through the nodes `0..=4`, at `r`, from the
/// transmitted values `h(0), h(2), h(3), h(4)` and the running sum
/// (`h(1) = sum - h(0)`): Lagrange interpolation, which agrees with Plonky3's
/// barycentric form at every `r`.
pub fn round_poly_at(evals: &[F; 4], running: F, r: F) -> F {
    let full = [evals[0], running - evals[0], evals[1], evals[2], evals[3]];
    let nodes: Vec<F> = (0..5).map(node).collect();
    let mut out = F::ZERO;
    for j in 0..5 {
        let mut num = F::ONE;
        let mut den = F::ONE;
        for i in 0..5 {
            if i != j {
                num *= r - nodes[i];
                den *= nodes[j] - nodes[i];
            }
        }
        out += full[j] * num * den.inverse();
    }
    out
}

// ---------------------------------------------------------------------------
// The tensor algebra GF(2^128) ⊗ GF(2^128), as 128 rows.
// ---------------------------------------------------------------------------

/// Row `u` is an element whose bit `v` is the coefficient of `β_u ⊗ β_v`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tensor {
    pub rows: Vec<F>,
}

fn bit(x: F, i: usize) -> bool {
    (x.to_repr() >> i) & 1 == 1
}

fn from_bits(bits: impl Iterator<Item = bool>) -> F {
    let mut r: u128 = 0;
    for (i, b) in bits.enumerate() {
        if b {
            r |= 1 << i;
        }
    }
    F::from_repr(r)
}

impl Tensor {
    pub fn zero() -> Self {
        Self { rows: vec![F::ZERO; DIM] }
    }

    /// `1 ⊗ 1`.
    pub fn one() -> Self {
        let mut t = Self::zero();
        t.rows[0] = F::ONE;
        t
    }

    pub fn from_rows(rows: &[F]) -> Self {
        assert_eq!(rows.len(), DIM);
        Self { rows: rows.to_vec() }
    }

    /// Column `v`: the element whose bit `u` is bit `v` of row `u`.
    pub fn columns(&self) -> Vec<F> {
        (0..DIM).map(|v| from_bits(self.rows.iter().map(|&r| bit(r, v)))).collect()
    }

    fn from_columns(cols: &[F]) -> Self {
        Self::from_rows(&(0..DIM).map(|u| from_bits(cols.iter().map(|&c| bit(c, u)))).collect::<Vec<_>>())
    }

    /// `a ⊗ b`: row `u` is `b` where bit `u` of `a` is set.
    pub fn exterior(a: F, b: F) -> Self {
        Self { rows: (0..DIM).map(|u| if bit(a, u) { b } else { F::ZERO }).collect() }
    }

    pub fn add(&self, other: &Self) -> Self {
        Self { rows: self.rows.iter().zip(&other.rows).map(|(&x, &y)| x + y).collect() }
    }

    /// `(1 ⊗ b) · self`.
    pub fn scale_rows(&self, b: F) -> Self {
        Self { rows: self.rows.iter().map(|&r| r * b).collect() }
    }

    /// `(a ⊗ 1) · self`.
    pub fn scale_columns(&self, a: F) -> Self {
        let cols: Vec<F> = self.columns().into_iter().map(|c| c * a).collect();
        Self::from_columns(&cols)
    }

    /// `(1 + a ⊗ 1 + 1 ⊗ b) · self`, which in characteristic 2 is what
    /// Plonky3's `mul_equality_factor` and its `equality_element` step
    /// (`E ↦ (1+a ⊗ 1+b)·E + (a ⊗ b)·E`) both compute.
    pub fn mul_equality_factor(&self, a: F, b: F) -> Self {
        self.add(&self.scale_columns(a)).add(&self.scale_rows(b))
    }

    /// `Σ_u rows[u] · weights[u]`.
    pub fn batch_rows(&self, weights: &[F]) -> F {
        self.rows.iter().zip(weights).map(|(&r, &w)| r * w).sum()
    }
}

/// `∏_i (1 + a_i ⊗ 1 + 1 ⊗ b_i)` from `1 ⊗ 1`.
pub fn equality_element(a: &[F], b: &[F]) -> Tensor {
    assert_eq!(a.len(), b.len());
    let mut e = Tensor::one();
    for (&x, &y) in a.iter().zip(b) {
        e = e.mul_equality_factor(x, y);
    }
    e
}

/// Plonky3's `BitTensor::successor_element(point, other)`: the coordinates
/// from last to first.
pub fn successor_element(point: &[F], other: &[F]) -> Tensor {
    assert_eq!(point.len(), other.len());
    let mut done = Tensor::zero();
    let mut carry_a = F::ONE;
    let mut carry_b = F::ONE;
    for (&a, &b) in point.iter().zip(other).rev() {
        done = done.mul_equality_factor(a, b);
        done = done.add(&Tensor::exterior(carry_a * (F::ONE + a), carry_b * b));
        carry_a *= a;
        carry_b *= F::ONE + b;
    }
    done
}

// ---------------------------------------------------------------------------
// The AIR at a point.
// ---------------------------------------------------------------------------

/// The row selectors at the bound point.
pub struct Boundary {
    pub first: F,
    pub last: F,
    pub transition: F,
}

impl Boundary {
    pub fn at(point: &[F]) -> Self {
        let first = point.iter().fold(F::ONE, |acc, &r| acc * (F::ONE + r));
        let last = point.iter().fold(F::ONE, |acc, &r| acc * r);
        Self { first, last, transition: F::ONE + last }
    }
}

/// One constraint at the point, from the opened rows.
fn eval_expr(
    e: &SymbolicExpression<F>,
    local: &[F],
    next: &[F],
    boundary: &Boundary,
    memo: &mut HashMap<*const SymbolicExpression<F>, F>,
) -> F {
    let key = e as *const _;
    if let Some(&v) = memo.get(&key) {
        return v;
    }
    let v = match e {
        SymbolicExpr::Leaf(leaf) => match leaf {
            BaseLeaf::Variable(var) => match var.entry {
                BaseEntry::Main { offset: 0 } => local[var.index],
                BaseEntry::Main { offset: 1 } => next[var.index],
                other => panic!("unsupported variable {other:?}"),
            },
            BaseLeaf::IsFirstRow => boundary.first,
            BaseLeaf::IsLastRow => boundary.last,
            BaseLeaf::IsTransition => boundary.transition,
            BaseLeaf::Constant(c) => *c,
        },
        SymbolicExpr::Add { x, y, .. } => eval_arc(x, local, next, boundary, memo) + eval_arc(y, local, next, boundary, memo),
        SymbolicExpr::Sub { x, y, .. } => eval_arc(x, local, next, boundary, memo) - eval_arc(y, local, next, boundary, memo),
        SymbolicExpr::Neg { x, .. } => -eval_arc(x, local, next, boundary, memo),
        SymbolicExpr::Mul { x, y, .. } => eval_arc(x, local, next, boundary, memo) * eval_arc(y, local, next, boundary, memo),
    };
    memo.insert(key, v);
    v
}

fn eval_arc(
    e: &Arc<SymbolicExpression<F>>,
    local: &[F],
    next: &[F],
    boundary: &Boundary,
    memo: &mut HashMap<*const SymbolicExpression<F>, F>,
) -> F {
    eval_expr(e, local, next, boundary, memo)
}

/// The alpha-batched constraint at the point: Horner over the constraints in
/// assertion order, `g = Σ alpha^{m-1-i} C_i`.
pub fn air_at(air: &Air, local: &[F], next: &[F], boundary: &Boundary, alpha: F) -> F {
    let mut memo = HashMap::new();
    let mut acc = F::ZERO;
    for c in &air.constraints {
        acc = acc * alpha + eval_expr(c, local, next, boundary, &mut memo);
    }
    acc
}

// ---------------------------------------------------------------------------
// The transcript prefix.
// ---------------------------------------------------------------------------

/// Everything between the commitment and the OOD draws, in transcript order.
pub fn prefix<S: Sponge>(cfg: &Config, d: &Data, s: &mut S) -> Challenges {
    let n = cfg.log_height;
    let w = cfg.width;
    let mut pow_ok = true;

    // Zerocheck challenges: alpha, beta, tau (nonzero, rejecting).
    s.observe_bytes(&cfg.seeds.zerocheck);
    let alpha = s.sample_elem();
    let beta = s.sample_elem();
    let mut tau = Vec::with_capacity(n);
    while tau.len() < n {
        let t = s.sample_elem();
        if t != F::ZERO {
            tau.push(t);
        }
    }

    // The generic-degree sumcheck, degree 4, `n` rounds.
    s.observe_bytes(&cfg.seeds.generic_degree);
    s.observe_elem(d.claimed_sum);
    assert_eq!(d.round_polys.len(), n);
    let mut running = d.claimed_sum;
    let mut r = Vec::with_capacity(n);
    for (i, evals) in d.round_polys.iter().enumerate() {
        for &e in evals {
            s.observe_elem(e);
        }
        if cfg.pow_bits > 0 {
            pow_ok &= s.check_witness(cfg.pow_bits, d.pow_witnesses[i]);
        }
        let ri = s.sample_elem();
        running = round_poly_at(evals, running, ri);
        r.push(ri);
    }
    let final_sum = running;

    // Column batching: the row point, the values, the column point.
    let column_vars = cfg.column_vars();
    s.observe_bytes(&cfg.seeds.column_batching);
    for &x in &r {
        s.observe_elem(x);
    }
    assert_eq!(d.values.len(), 2 * w);
    for &v in &d.values {
        s.observe_elem(v);
    }
    let c: Vec<F> = (0..column_vars).map(|_| s.sample_elem()).collect();

    // The ring switch: statement, batching, sumcheck, surviving claim.
    let mut point = c.clone();
    point.extend_from_slice(&r);
    s.observe_bytes(&cfg.seeds.ring_switch);
    for &x in &point {
        s.observe_elem(x);
    }
    assert_eq!(d.tensor.len(), DIM);
    for &x in &d.tensor {
        s.observe_elem(x);
    }
    assert_eq!(d.successor.is_some(), cfg.sends_successor());
    if let Some((carry, last)) = &d.successor {
        assert_eq!((carry.len(), last.len()), (DIM, DIM));
        for &x in carry {
            s.observe_elem(x);
        }
        for &x in last {
            s.observe_elem(x);
        }
    }
    let r_batch: Vec<F> = (0..ABSORBED).map(|_| s.sample_elem()).collect();
    let alpha_rs = cfg.sends_successor().then(|| s.sample_elem());

    let packed = cfg.packed_vars();
    let high = &point[..packed];
    let prefix_limit = packed.min(point.len() - n);
    let prefix = high[..prefix_limit].iter().take_while(|&&x| x == F::ZERO || x == F::ONE).count();
    let rounds = packed - prefix;
    let mut r_prime = Vec::with_capacity(rounds);
    if rounds > 0 {
        s.observe_bytes(&cfg.seeds.quadratic);
        assert_eq!(d.rs_sumcheck.len(), rounds);
        for _ in 0..rounds {
            let [h0, hinf] = d.rs_sumcheck[r_prime.len()];
            s.observe_elem(h0);
            s.observe_elem(hinf);
            r_prime.push(s.sample_elem());
        }
    }
    s.observe_elem(d.final_eval);

    let mut surviving = high[..prefix].to_vec();
    surviving.extend_from_slice(&r_prime);
    Challenges { alpha, beta, tau, r, final_sum, c, r_batch, alpha_rs, r_prime, prefix, surviving, pow_ok }
}

// ---------------------------------------------------------------------------
// The checks.
// ---------------------------------------------------------------------------

/// `combine_columns`: `Σ_i eq(c, i) · values[i]`, the values zero-padded to
/// `2^|c|`.
pub fn combine_columns(values: &[F], c: &[F]) -> F {
    let eq = eq_table(c);
    values.iter().zip(&eq).map(|(&v, &e)| v * e).sum()
}

/// The successor weights `n[v]` on the tensor's columns.
fn successor_weights(cfg: &Config, eq_low: &[F]) -> Vec<F> {
    let mut n = vec![F::ZERO; DIM];
    if cfg.sends_successor() {
        for v in 1..DIM {
            n[v] = eq_low[v - 1];
        }
    } else {
        let last = (1usize << cfg.log_height) - 1;
        for v in 0..DIM {
            let row = v & last;
            let mut acc = F::ZERO;
            if row != 0 {
                acc += eq_low[v - 1];
            }
            if row == last {
                acc += eq_low[v];
            }
            n[v] = acc;
        }
    }
    n
}

/// What the ring switch and the zerocheck pin down; the arithmetic after the
/// prefix's transcript.
pub fn check(cfg: &Config, d: &Data, air: &Air, ch: &Challenges) -> Result<(), Error> {
    if !ch.pow_ok {
        return Err(Error::Pow);
    }
    if d.claimed_sum != F::ZERO {
        return Err(Error::ClaimedSum);
    }
    let w = cfg.width;

    // The zerocheck's closing identity: final_sum = eq(tau, r) · g(r).
    let boundary = Boundary::at(&ch.r);
    let g = air_at(air, &d.values[..w], &d.values[w..], &boundary, ch.alpha);
    let eq_at = ch.tau.iter().zip(&ch.r).fold(F::ONE, |acc, (&t, &x)| acc * (F::ONE + t + x));
    if ch.final_sum != eq_at * g {
        return Err(Error::Zerocheck);
    }

    // The batched readings.
    let current = combine_columns(&d.values[..w], &ch.c);
    let next = combine_columns(&d.values[w..], &ch.c);

    // The ring switch's statement checks.
    let mut point = ch.c.clone();
    point.extend_from_slice(&ch.r);
    let eq_low = eq_table(&point[point.len() - ABSORBED..]);
    let tensor = Tensor::from_rows(&d.tensor);
    let columns = tensor.columns();
    let incoming: F = columns.iter().zip(&eq_low).map(|(&c, &e)| c * e).sum();
    if incoming != current {
        return Err(Error::Incoming);
    }
    let weights = successor_weights(cfg, &eq_low);
    let mut successor: F = columns.iter().zip(&weights).map(|(&c, &e)| c * e).sum();
    let tensors = d.successor.as_ref().map(|(c, l)| (Tensor::from_rows(c), Tensor::from_rows(l)));
    if let Some((carry, last)) = &tensors {
        successor += eq_low[DIM - 1] * (carry.columns()[0] + last.columns()[DIM - 1]);
    }
    if successor != next {
        return Err(Error::Successor);
    }

    // The batched sum, its sumcheck, and the closing weight.
    let eq_batch = eq_table(&ch.r_batch);
    let batch = |t: &Tensor| t.batch_rows(&eq_batch);
    let mut sum = batch(&tensor);
    if let (Some((carry, last)), Some(a)) = (&tensors, ch.alpha_rs) {
        sum += a * (batch(carry) + a * batch(last));
    }
    for (&[h0, hinf], &x) in d.rs_sumcheck.iter().zip(&ch.r_prime) {
        sum = extrapolate_01inf(h0, sum - h0, hinf, x);
    }
    let packed = cfg.packed_vars();
    let high = &point[..packed];
    let rest = &high[ch.prefix..];
    let mut closing = batch(&equality_element(rest, &ch.r_prime));
    if let (Some(_), Some(a)) = (&tensors, ch.alpha_rs) {
        let kept = cfg.kept_rows();
        let (selector, rho) = rest.split_at(rest.len() - kept);
        let (r_sel, r_rows) = ch.r_prime.split_at(ch.r_prime.len() - kept);
        let mut carry = successor_element(rho, r_rows);
        let prod = |xs: &[F]| xs.iter().fold(F::ONE, |acc, &x| acc * x);
        let mut last = Tensor::exterior(prod(rho), prod(r_rows));
        for (&a_i, &b_i) in selector.iter().zip(r_sel) {
            carry = carry.mul_equality_factor(a_i, b_i);
            last = last.mul_equality_factor(a_i, b_i);
        }
        closing += a * (batch(&carry) + a * batch(&last));
    }
    if sum != closing * d.final_eval {
        return Err(Error::RingSwitch);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The simplified equality step equals Plonky3's four-scaling form.
    #[test]
    fn equality_factor_matches_the_four_scaling_form() {
        let a = F::from_repr(0x1234_5678_9abc_def0_0fed_cba9_8765_4321);
        let b = F::from_repr(0x0f0f_1234_5678_ffff_0000_1111_2222_3333);
        let mut e = Tensor::one();
        for i in 0..3 {
            let (x, y) = (a * node(i + 2), b + node(i + 5));
            let agree = e.scale_columns(x).scale_rows(y);
            let four = e.scale_columns(F::ONE + x).scale_rows(F::ONE + y).add(&agree);
            let two = e.mul_equality_factor(x, y);
            assert_eq!(two, four);
            e = two;
        }
    }

    /// The Lagrange form of the round polynomial through five nodes.
    #[test]
    fn round_poly_interpolates_its_nodes() {
        let evals = [node(11), node(22), node(33), node(44)];
        let running = node(99);
        let full = [evals[0], running - evals[0], evals[1], evals[2], evals[3]];
        for (j, &f) in full.iter().enumerate() {
            assert_eq!(round_poly_at(&evals, running, node(j)), f);
        }
    }
}
