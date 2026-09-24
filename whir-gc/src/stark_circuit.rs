//! The multi-STARK layers of [`crate::stark`] on wires: the zerocheck, the
//! column batching and the bit ring switch, run as the prefix of the WHIR
//! circuit through [`crate::circuit::build_with_prefix`].
//!
//! Every step is the reference's, gate for gate: multiplications are
//! `tower::mul` (2,187 AND each; a multiplication by a constant element folds
//! to none), additions are free, and the tensor algebra is 128 elements a
//! side with its transposition a rewiring.
//!
//! Two of the reference's data-dependent branches are fixed here and
//! guarded by checks instead: the zerocheck's `tau` draws are taken as `n`
//! samples that must each be nonzero (the reference redraws a zero), and the
//! ring switch's Boolean prefix is taken as empty (the reference would fix a
//! column-point coordinate that is exactly 0 or 1). Both events have
//! probability about `2^-127` per coordinate and make the circuit reject
//! where Plonky3 would continue, never the reverse.

use std::collections::HashMap;

use garbled_snark_verifier::circuits::sect233k1::builder::CircuitTrait;
use p3_air::{BaseEntry, BaseLeaf, SymbolicExpr, SymbolicExpression};
use p3_binary_field::TowerLevel;
use p3_field::{Field, PrimeCharacteristicRing};

use crate::circuit::{
    Elem, PrefixOut, Profile, Sponge, alloc_elem, and_all, const_bytes, equal, not, one_elem, or_all, sumcheck_round,
    zero_elem,
};
use crate::reference::F;
use crate::stark::{ABSORBED, Air, Config, DIM, Data, node};
use garbled_snark_verifier::circuits::sect233k1::stream::ValuedBuilder;
use crate::tower;

/// The proof's messages as input wires, in transcript order.
pub struct Inputs {
    claimed_sum: Elem,
    round_polys: Vec<[Elem; 4]>,
    values: Vec<Elem>,
    tensor: Vec<Elem>,
    successor: Option<(Vec<Elem>, Vec<Elem>)>,
    rs_sumcheck: Vec<[Elem; 2]>,
    final_eval: Elem,
    pub witness: Vec<bool>,
}

impl Inputs {
    pub fn allocate<T: ValuedBuilder>(b: &mut T, d: &Data) -> Self {
        let mut w = Vec::new();
        let claimed_sum = alloc_elem(b, &mut w, d.claimed_sum);
        let round_polys = d.round_polys.iter().map(|p| core::array::from_fn(|i| alloc_elem(b, &mut w, p[i]))).collect();
        let values = d.values.iter().map(|&x| alloc_elem(b, &mut w, x)).collect();
        let tensor = d.tensor.iter().map(|&x| alloc_elem(b, &mut w, x)).collect();
        let successor = d.successor.as_ref().map(|(c, l)| {
            (c.iter().map(|&x| alloc_elem(b, &mut w, x)).collect(), l.iter().map(|&x| alloc_elem(b, &mut w, x)).collect())
        });
        let rs_sumcheck = d.rs_sumcheck.iter().map(|p| [alloc_elem(b, &mut w, p[0]), alloc_elem(b, &mut w, p[1])]).collect();
        let final_eval = alloc_elem(b, &mut w, d.final_eval);
        Self { claimed_sum, round_polys, values, tensor, successor, rs_sumcheck, final_eval, witness: w }
    }
}

pub struct Challenges {
    pub alpha: Elem,
    pub tau: Vec<Elem>,
    pub r: Vec<Elem>,
    pub final_sum: Elem,
    pub c: Vec<Elem>,
    pub r_batch: Vec<Elem>,
    pub alpha_rs: Option<Elem>,
    pub r_prime: Vec<Elem>,
    pub surviving: Vec<Elem>,
    /// Wires that must be 1: the nonzero `tau`s and the non-Boolean column
    /// point coordinates.
    pub guards: Vec<usize>,
}

// ---------------------------------------------------------------------------
// Field helpers on wires.
// ---------------------------------------------------------------------------

fn constant<T: CircuitTrait>(b: &mut T, x: F) -> Elem {
    tower::constant(b, x.to_repr(), 128)
}

fn add<T: CircuitTrait>(b: &mut T, x: &Elem, y: &Elem) -> Elem {
    tower::add(b, x, y)
}

fn mul<T: CircuitTrait>(b: &mut T, x: &Elem, y: &Elem) -> Elem {
    tower::mul(b, x, y)
}

fn sum<T: CircuitTrait>(b: &mut T, xs: impl IntoIterator<Item = Elem>) -> Elem {
    let mut acc = zero_elem(b);
    for x in xs {
        acc = add(b, &acc, &x);
    }
    acc
}

fn product<T: CircuitTrait>(b: &mut T, xs: &[Elem]) -> Elem {
    let mut acc = one_elem(b);
    for x in xs {
        acc = mul(b, &acc, x);
    }
    acc
}

/// 1 iff `x` is nonzero.
fn nonzero<T: CircuitTrait>(b: &mut T, x: &Elem) -> usize {
    or_all(b, x)
}

/// The eq table of `point`, big-endian, `2^m` entries: one multiplication
/// per entry (`t·p`, and `t·(1+p) = t + t·p`).
pub fn eq_table<T: CircuitTrait>(b: &mut T, point: &[Elem]) -> Vec<Elem> {
    let mut table = vec![one_elem(b)];
    for p in point {
        let mut next = Vec::with_capacity(table.len() * 2);
        for t in &table {
            let tp = mul(b, t, p);
            next.push(add(b, t, &tp));
            next.push(tp);
        }
        table = next;
    }
    table
}

/// `Σ values[i] · weights[i]`.
fn dot<T: CircuitTrait>(b: &mut T, values: &[Elem], weights: &[Elem]) -> Elem {
    let terms: Vec<Elem> = values.iter().zip(weights).map(|(v, w)| mul(b, v, w)).collect();
    sum(b, terms)
}

/// The degree-4 round polynomial through the nodes `0..=4` at `r`, Lagrange
/// form with constant denominators (free) and prefix/suffix products.
fn round_poly_at<T: CircuitTrait>(b: &mut T, evals: &[Elem; 4], running: &Elem, r: &Elem) -> Elem {
    let h1 = add(b, running, &evals[0]);
    let full = [evals[0].clone(), h1, evals[1].clone(), evals[2].clone(), evals[3].clone()];
    let nodes: Vec<F> = (0..5).map(node).collect();
    // d_i = r + x_i.
    let d: Vec<Elem> = nodes
        .iter()
        .map(|&x| {
            let c = constant(b, x);
            add(b, r, &c)
        })
        .collect();
    // prefix[j] = ∏_{i<j} d_i, suffix[j] = ∏_{i>j} d_i.
    let mut prefix = vec![one_elem(b)];
    for i in 0..4 {
        let p = mul(b, &prefix[i], &d[i]);
        prefix.push(p);
    }
    let mut suffix = vec![one_elem(b); 5];
    for i in (1..5).rev() {
        suffix[i - 1] = mul(b, &suffix[i], &d[i]);
    }
    let mut out = zero_elem(b);
    for j in 0..5 {
        let mut den = F::ONE;
        for i in 0..5 {
            if i != j {
                den *= nodes[j] - nodes[i];
            }
        }
        let inv = constant(b, den.inverse());
        let num = mul(b, &prefix[j], &suffix[j]);
        let basis = mul(b, &num, &inv);
        let term = mul(b, &full[j], &basis);
        out = add(b, &out, &term);
    }
    out
}

// ---------------------------------------------------------------------------
// The tensor algebra on wires.
// ---------------------------------------------------------------------------

pub struct Tensor {
    pub rows: Vec<Elem>,
}

impl Tensor {
    fn zero<T: CircuitTrait>(b: &mut T) -> Self {
        Self { rows: (0..DIM).map(|_| zero_elem(b)).collect() }
    }

    fn one<T: CircuitTrait>(b: &mut T) -> Self {
        let mut t = Self::zero(b);
        t.rows[0] = one_elem(b);
        t
    }

    fn from_rows(rows: &[Elem]) -> Self {
        assert_eq!(rows.len(), DIM);
        Self { rows: rows.to_vec() }
    }

    /// The transposition: column `v` has bit `u` = bit `v` of row `u`.
    fn columns(&self) -> Vec<Elem> {
        (0..DIM).map(|v| self.rows.iter().map(|r| r[v]).collect()).collect()
    }

    fn from_columns(cols: &[Elem]) -> Self {
        Self::from_rows(&(0..DIM).map(|u| cols.iter().map(|c| c[u]).collect()).collect::<Vec<_>>())
    }

    /// `a ⊗ b`: row `u` is `b` gated by bit `u` of `a`.
    fn exterior<T: CircuitTrait>(b: &mut T, a: &Elem, x: &Elem) -> Self {
        Self { rows: a.iter().map(|&au| x.iter().map(|&xv| b.and_wire(au, xv)).collect()).collect() }
    }

    fn add<T: CircuitTrait>(&self, b: &mut T, other: &Self) -> Self {
        Self { rows: self.rows.iter().zip(&other.rows).map(|(x, y)| add(b, x, y)).collect() }
    }

    fn scale_rows<T: CircuitTrait>(&self, b: &mut T, y: &Elem) -> Self {
        Self { rows: self.rows.iter().map(|r| mul(b, r, y)).collect() }
    }

    fn scale_columns<T: CircuitTrait>(&self, b: &mut T, a: &Elem) -> Self {
        let cols: Vec<Elem> = self.columns().iter().map(|c| mul(b, c, a)).collect();
        Self::from_columns(&cols)
    }

    /// `(1 + a ⊗ 1 + 1 ⊗ b) · self`.
    fn mul_equality_factor<T: CircuitTrait>(&self, b: &mut T, a: &Elem, y: &Elem) -> Self {
        let cols = self.scale_columns(b, a);
        let rows = self.scale_rows(b, y);
        self.add(b, &cols).add(b, &rows)
    }

    fn batch_rows<T: CircuitTrait>(&self, b: &mut T, weights: &[Elem]) -> Elem {
        dot(b, &self.rows, weights)
    }
}

fn equality_element<T: CircuitTrait>(b: &mut T, a: &[Elem], y: &[Elem]) -> Tensor {
    assert_eq!(a.len(), y.len());
    let mut e = Tensor::one(b);
    for (x, z) in a.iter().zip(y) {
        e = e.mul_equality_factor(b, x, z);
    }
    e
}

fn successor_element<T: CircuitTrait>(b: &mut T, point: &[Elem], other: &[Elem]) -> Tensor {
    assert_eq!(point.len(), other.len());
    let one = one_elem(b);
    let mut done = Tensor::zero(b);
    let mut carry_a = one.clone();
    let mut carry_b = one.clone();
    for (a, y) in point.iter().zip(other).rev() {
        done = done.mul_equality_factor(b, a, y);
        let na = add(b, &one, a);
        let left = mul(b, &carry_a, &na);
        let right = mul(b, &carry_b, y);
        let ext = Tensor::exterior(b, &left, &right);
        done = done.add(b, &ext);
        carry_a = mul(b, &carry_a, a);
        let ny = add(b, &one, y);
        carry_b = mul(b, &carry_b, &ny);
    }
    done
}

// ---------------------------------------------------------------------------
// The AIR on wires.
// ---------------------------------------------------------------------------

struct Boundary {
    first: Elem,
    last: Elem,
    transition: Elem,
}

impl Boundary {
    fn at<T: CircuitTrait>(b: &mut T, point: &[Elem]) -> Self {
        let one = one_elem(b);
        let complements: Vec<Elem> = point.iter().map(|r| add(b, &one, r)).collect();
        let first = product(b, &complements);
        let last = product(b, point);
        let transition = add(b, &one, &last);
        Self { first, last, transition }
    }
}

fn eval_expr<T: CircuitTrait>(
    b: &mut T,
    e: &SymbolicExpression<F>,
    local: &[Elem],
    next: &[Elem],
    boundary: &Boundary,
    memo: &mut HashMap<*const SymbolicExpression<F>, Elem>,
) -> Elem {
    let key = e as *const _;
    if let Some(v) = memo.get(&key) {
        return v.clone();
    }
    let v = match e {
        SymbolicExpr::Leaf(leaf) => match leaf {
            BaseLeaf::Variable(var) => match var.entry {
                BaseEntry::Main { offset: 0 } => local[var.index].clone(),
                BaseEntry::Main { offset: 1 } => next[var.index].clone(),
                other => panic!("unsupported variable {other:?}"),
            },
            BaseLeaf::IsFirstRow => boundary.first.clone(),
            BaseLeaf::IsLastRow => boundary.last.clone(),
            BaseLeaf::IsTransition => boundary.transition.clone(),
            BaseLeaf::Constant(c) => constant(b, *c),
        },
        SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } => {
            let xv = eval_expr(b, x, local, next, boundary, memo);
            let yv = eval_expr(b, y, local, next, boundary, memo);
            add(b, &xv, &yv)
        }
        // Characteristic 2: negation is the identity.
        SymbolicExpr::Neg { x, .. } => eval_expr(b, x, local, next, boundary, memo),
        SymbolicExpr::Mul { x, y, .. } => {
            let xv = eval_expr(b, x, local, next, boundary, memo);
            let yv = eval_expr(b, y, local, next, boundary, memo);
            mul(b, &xv, &yv)
        }
    };
    memo.insert(key, v.clone());
    v
}

/// The alpha-batched constraint at the point, Horner over the constraints.
fn air_at<T: CircuitTrait>(b: &mut T, air: &Air, local: &[Elem], next: &[Elem], boundary: &Boundary, alpha: &Elem) -> Elem {
    let mut memo = HashMap::new();
    let mut acc = zero_elem(b);
    for c in &air.constraints {
        let v = eval_expr(b, c, local, next, boundary, &mut memo);
        let shifted = mul(b, &acc, alpha);
        acc = add(b, &shifted, &v);
    }
    acc
}

// ---------------------------------------------------------------------------
// The prefix: transcript, then checks.
// ---------------------------------------------------------------------------

/// The transcript between the commitment and the OOD draws, on the sponge.
pub fn prefix<T: CircuitTrait>(b: &mut T, s: &mut Sponge, cfg: &Config, inputs: &Inputs, profile: &mut Profile) -> Challenges {
    assert_eq!(cfg.pow_bits, 0, "the zerocheck sumcheck does not grind");
    let n = cfg.log_height;
    let w = cfg.width;
    let mut guards = Vec::new();

    let seed = const_bytes(b, &cfg.seeds.zerocheck);
    s.observe(&seed);
    let alpha = s.sample_elem(b);
    let _beta = s.sample_elem(b);
    let tau: Vec<Elem> = (0..n).map(|_| s.sample_elem(b)).collect();
    for t in &tau {
        guards.push(nonzero(b, t));
    }

    let seed = const_bytes(b, &cfg.seeds.generic_degree);
    s.observe(&seed);
    s.observe_elem(&inputs.claimed_sum);
    assert_eq!(inputs.round_polys.len(), n);
    let mut running = inputs.claimed_sum.clone();
    let mut r = Vec::with_capacity(n);
    for evals in &inputs.round_polys {
        for e in evals {
            s.observe_elem(e);
        }
        let ri = s.sample_elem(b);
        running = round_poly_at(b, evals, &running, &ri);
        r.push(ri);
    }
    let final_sum = running;
    profile.mark(b, "zerocheck sumcheck");

    let column_vars = cfg.column_vars();
    let seed = const_bytes(b, &cfg.seeds.column_batching);
    s.observe(&seed);
    for x in &r {
        s.observe_elem(x);
    }
    assert_eq!(inputs.values.len(), 2 * w);
    for v in &inputs.values {
        s.observe_elem(v);
    }
    let c: Vec<Elem> = (0..column_vars).map(|_| s.sample_elem(b)).collect();

    let mut point = c.clone();
    point.extend(r.iter().cloned());
    let seed = const_bytes(b, &cfg.seeds.ring_switch);
    s.observe(&seed);
    for x in &point {
        s.observe_elem(x);
    }
    for x in &inputs.tensor {
        s.observe_elem(x);
    }
    assert_eq!(inputs.successor.is_some(), cfg.sends_successor());
    if let Some((carry, last)) = &inputs.successor {
        for x in carry.iter().chain(last) {
            s.observe_elem(x);
        }
    }
    let r_batch: Vec<Elem> = (0..ABSORBED).map(|_| s.sample_elem(b)).collect();
    let alpha_rs = cfg.sends_successor().then(|| s.sample_elem(b));

    // No Boolean prefix: the leading column-point coordinates must be neither 0 nor 1.
    let packed = cfg.packed_vars();
    let prefix_limit = packed.min(point.len() - n);
    let one = one_elem(b);
    for x in &point[..prefix_limit] {
        let x1 = add(b, x, &one);
        let nz = nonzero(b, x);
        let is_zero = not(b, nz);
        let nz1 = nonzero(b, &x1);
        let is_one = not(b, nz1);
        let boolean = b.or_wire(is_zero, is_one);
        guards.push(not(b, boolean));
    }
    assert_eq!(inputs.rs_sumcheck.len(), packed);
    let seed = const_bytes(b, &cfg.seeds.quadratic);
    s.observe(&seed);
    let mut r_prime = Vec::with_capacity(packed);
    for [h0, hinf] in &inputs.rs_sumcheck {
        s.observe_elem(h0);
        s.observe_elem(hinf);
        r_prime.push(s.sample_elem(b));
    }
    s.observe_elem(&inputs.final_eval);
    profile.mark(b, "stark transcript (sponge)");

    let surviving = r_prime.clone();
    Challenges { alpha, tau, r, final_sum, c, r_batch, alpha_rs, r_prime, surviving, guards }
}

/// The arithmetic checks; each returned wire must be 1.
pub fn check<T: CircuitTrait>(
    b: &mut T,
    cfg: &Config,
    air: &Air,
    inputs: &Inputs,
    ch: &Challenges,
    profile: &mut Profile,
) -> Vec<usize> {
    let w = cfg.width;
    let one = one_elem(b);
    let mut checks = ch.guards.clone();
    let nz = nonzero(b, &inputs.claimed_sum);
    checks.push(not(b, nz));

    // The zerocheck's closing identity.
    let boundary = Boundary::at(b, &ch.r);
    let g = air_at(b, air, &inputs.values[..w], &inputs.values[w..], &boundary, &ch.alpha);
    profile.mark(b, "air constraints");
    let factors: Vec<Elem> = ch
        .tau
        .iter()
        .zip(&ch.r)
        .map(|(t, x)| {
            let tx = add(b, t, x);
            add(b, &one, &tx)
        })
        .collect();
    let eq_at = product(b, &factors);
    let expected = mul(b, &eq_at, &g);
    checks.push(equal(b, &ch.final_sum, &expected));
    profile.mark(b, "zerocheck closing");

    // The batched readings.
    let eq_c = eq_table(b, &ch.c);
    let current = dot(b, &inputs.values[..w], &eq_c);
    let next = dot(b, &inputs.values[w..], &eq_c);
    profile.mark(b, "column combination");

    // The ring switch's statement.
    let mut point = ch.c.clone();
    point.extend(ch.r.iter().cloned());
    let eq_low = eq_table(b, &point[point.len() - ABSORBED..]);
    let tensor = Tensor::from_rows(&inputs.tensor);
    let columns = tensor.columns();
    let incoming = dot(b, &columns, &eq_low);
    checks.push(equal(b, &incoming, &current));
    let tensors = inputs.successor.as_ref().map(|(c, l)| (Tensor::from_rows(c), Tensor::from_rows(l)));
    let successor = if cfg.sends_successor() {
        let mut acc = dot(b, &columns[1..], &eq_low[..DIM - 1]);
        let (carry, last) = tensors.as_ref().expect("successor tensors");
        let edge = add(b, &carry.columns()[0], &last.columns()[DIM - 1]);
        let edge = mul(b, &eq_low[DIM - 1], &edge);
        acc = add(b, &acc, &edge);
        acc
    } else {
        let last_row = (1usize << cfg.log_height) - 1;
        let weights: Vec<Elem> = (0..DIM)
            .map(|v| {
                let row = v & last_row;
                let mut acc = zero_elem(b);
                if row != 0 {
                    acc = add(b, &acc, &eq_low[v - 1]);
                }
                if row == last_row {
                    acc = add(b, &acc, &eq_low[v]);
                }
                acc
            })
            .collect();
        dot(b, &columns, &weights)
    };
    checks.push(equal(b, &successor, &next));
    profile.mark(b, "ring switch statement");

    // The batched sum through its sumcheck, against the closing weight.
    let eq_batch = eq_table(b, &ch.r_batch);
    let mut sum = tensor.batch_rows(b, &eq_batch);
    if let (Some((carry, last)), Some(a)) = (&tensors, &ch.alpha_rs) {
        let bl = last.batch_rows(b, &eq_batch);
        let bc = carry.batch_rows(b, &eq_batch);
        let inner = mul(b, a, &bl);
        let inner = add(b, &bc, &inner);
        let outer = mul(b, a, &inner);
        sum = add(b, &sum, &outer);
    }
    for ([h0, hinf], x) in inputs.rs_sumcheck.iter().zip(&ch.r_prime) {
        sum = sumcheck_round(b, &sum, h0, hinf, x);
    }
    let packed = cfg.packed_vars();
    let high = &point[..packed];
    let e = equality_element(b, high, &ch.r_prime);
    let mut closing = e.batch_rows(b, &eq_batch);
    if let (Some(_), Some(a)) = (&tensors, &ch.alpha_rs) {
        let kept = cfg.kept_rows();
        let (selector, rho) = high.split_at(high.len() - kept);
        let (r_sel, r_rows) = ch.r_prime.split_at(ch.r_prime.len() - kept);
        let mut carry = successor_element(b, rho, r_rows);
        let prho = product(b, rho);
        let prows = product(b, r_rows);
        let mut last = Tensor::exterior(b, &prho, &prows);
        for (x, y) in selector.iter().zip(r_sel) {
            carry = carry.mul_equality_factor(b, x, y);
            last = last.mul_equality_factor(b, x, y);
        }
        let bl = last.batch_rows(b, &eq_batch);
        let bc = carry.batch_rows(b, &eq_batch);
        let inner = mul(b, a, &bl);
        let inner = add(b, &bc, &inner);
        let outer = mul(b, a, &inner);
        closing = add(b, &closing, &outer);
    }
    let expected = mul(b, &closing, &inputs.final_eval);
    checks.push(equal(b, &sum, &expected));
    profile.mark(b, "ring switch closing");
    checks
}

/// The whole prefix for [`crate::circuit::build_with_prefix`]: the transcript,
/// the checks (pushed to `checks`), and the surviving claim WHIR opens.
pub fn run<T: CircuitTrait>(
    b: &mut T,
    s: &mut Sponge,
    cfg: &Config,
    air: &Air,
    inputs: &Inputs,
    checks: &mut Vec<usize>,
    profile: &mut Profile,
) -> PrefixOut {
    let ch = prefix(b, s, cfg, inputs, profile);
    let mine = check(b, cfg, air, inputs, &ch, profile);
    checks.push(and_all(b, &mine));
    PrefixOut { points: vec![ch.surviving], values: vec![vec![inputs.final_eval.clone()]] }
}
