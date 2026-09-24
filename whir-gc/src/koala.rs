//! KoalaBear (`p = 2^31 - 2^24 + 1`) and Poseidon2 over it, as boolean
//! circuits: the cost of verifying a prime-field, Poseidon2-committed proof
//! in gates, measured rather than guessed.
//!
//! An element is 31 wires, least significant first, canonical (`< p`).
//! Multi-operand sums are kept as weight-indexed columns of bits and reduced
//! by carry-save compression (one AND per full adder); modular reduction
//! folds `2^31 ≡ 2^24 - 1` and finishes with conditional subtractions.
//! Everything is checked against the `poseidon2` crate's reference, itself
//! checked against Plonky3.

use crate::gates::CircuitTrait;
use poseidon2::constants::{EXTERNAL_FINAL, EXTERNAL_INITIAL, INTERNAL, P, WIDTH};

pub const BITS: usize = 31;
/// An element: 31 wires, LSB first, canonical.
pub type Fp = Vec<usize>;

// ---------------------------------------------------------------------------
// Bit arithmetic.
// ---------------------------------------------------------------------------

/// A full adder: one AND (`maj(a,b,c) = c ⊕ ((a⊕c)·(b⊕c))`).
fn full_adder<T: CircuitTrait>(b: &mut T, x: usize, y: usize, c: usize) -> (usize, usize) {
    let xy = b.xor_wire(x, y);
    let s = b.xor_wire(xy, c);
    let xc = b.xor_wire(x, c);
    let yc = b.xor_wire(y, c);
    let t = b.and_wire(xc, yc);
    let carry = b.xor_wire(c, t);
    (s, carry)
}

/// Weight-indexed multisets of bits: the number `Σ_j Σ_{w ∈ cols[j]} w · 2^j`.
#[derive(Clone, Default)]
pub struct Cols {
    pub cols: Vec<Vec<usize>>,
}

impl Cols {
    fn push(&mut self, weight: usize, wire: usize) {
        if self.cols.len() <= weight {
            self.cols.resize(weight + 1, Vec::new());
        }
        self.cols[weight].push(wire);
    }

    fn from_bits(bits: &[usize]) -> Self {
        let mut c = Self::default();
        for (j, &w) in bits.iter().enumerate() {
            c.push(j, w);
        }
        c
    }

    fn extend(&mut self, other: &Cols, shift: usize) {
        for (j, col) in other.cols.iter().enumerate() {
            for &w in col {
                self.push(j + shift, w);
            }
        }
    }

    /// An upper bound on the value.
    fn bound(&self) -> u128 {
        self.cols.iter().enumerate().map(|(j, c)| (c.len() as u128) << j).sum()
    }

    /// The single binary number: carry-save compression to two bits per
    /// column, then a ripple.
    fn compress<T: CircuitTrait>(&self, b: &mut T) -> Vec<usize> {
        let mut cols = self.cols.clone();
        while cols.iter().any(|c| c.len() > 2) {
            let mut next: Vec<Vec<usize>> = vec![Vec::new(); cols.len() + 1];
            for (j, col) in cols.iter().enumerate() {
                let mut i = 0;
                while i + 3 <= col.len() {
                    let (s, c) = full_adder(b, col[i], col[i + 1], col[i + 2]);
                    next[j].push(s);
                    next[j + 1].push(c);
                    i += 3;
                }
                if col.len() - i == 2 {
                    let s = b.xor_wire(col[i], col[i + 1]);
                    let c = b.and_wire(col[i], col[i + 1]);
                    next[j].push(s);
                    next[j + 1].push(c);
                } else if col.len() - i == 1 {
                    next[j].push(col[i]);
                }
            }
            while next.last().is_some_and(Vec::is_empty) {
                next.pop();
            }
            cols = next;
        }
        // The ripple over at most two bits per column.
        let mut out = Vec::with_capacity(cols.len() + 1);
        let mut carry: Option<usize> = None;
        for col in &cols {
            match (col.as_slice(), carry) {
                ([], None) => out.push(b.zero()),
                ([], Some(c)) => {
                    out.push(c);
                    carry = None;
                }
                ([x], None) => out.push(*x),
                ([x], Some(c)) => {
                    out.push(b.xor_wire(*x, c));
                    carry = Some(b.and_wire(*x, c));
                }
                ([x, y], None) => {
                    out.push(b.xor_wire(*x, *y));
                    carry = Some(b.and_wire(*x, *y));
                }
                ([x, y], Some(c)) => {
                    let (s, c2) = full_adder(b, *x, *y, c);
                    out.push(s);
                    carry = Some(c2);
                }
                _ => unreachable!("compressed to two bits per column"),
            }
        }
        if let Some(c) = carry {
            out.push(c);
        }
        out
    }
}

/// `x + c` for a constant `c`, `width` bits out (the caller bounds it).
fn add_const<T: CircuitTrait>(b: &mut T, x: &[usize], c: u128, width: usize) -> Vec<usize> {
    let mut out = Vec::with_capacity(width);
    let mut carry: Option<usize> = None;
    for i in 0..width {
        let xi = x.get(i).copied();
        let ci = (c >> i) & 1 == 1;
        match (xi, ci, carry) {
            (None, false, None) => out.push(b.zero()),
            (None, false, Some(cr)) => {
                out.push(cr);
                carry = None;
            }
            (None, true, None) => out.push(b.one()),
            (None, true, Some(cr)) => {
                // 1 + carry: sum = ¬carry, carry out = carry.
                let one = b.one();
                out.push(b.xor_wire(cr, one));
                carry = Some(cr);
            }
            (Some(w), false, None) => out.push(w),
            (Some(w), false, Some(cr)) => {
                out.push(b.xor_wire(w, cr));
                carry = Some(b.and_wire(w, cr));
            }
            (Some(w), true, None) => {
                let one = b.one();
                out.push(b.xor_wire(w, one));
                carry = Some(w);
            }
            (Some(w), true, Some(cr)) => {
                // w + 1 + carry: sum = ¬(w ⊕ carry), carry out = w ∨ carry.
                let one = b.one();
                let s = b.xor_wire(w, cr);
                out.push(b.xor_wire(s, one));
                carry = Some(b.or_wire(w, cr));
            }
        }
    }
    out
}

/// `x - c` for a constant `c ≤ 2^width`: the difference modulo `2^width` and a
/// wire that is 1 iff `x ≥ c` (no borrow).
fn sub_const<T: CircuitTrait>(b: &mut T, x: &[usize], c: u128, width: usize) -> (Vec<usize>, usize) {
    // x + (2^width - c): the carry out of bit `width` is the no-borrow flag.
    let comp = (1u128 << width) - c;
    let mut out = add_const(b, x, comp, width + 1);
    let no_borrow = out.pop().expect("width + 1 bits");
    (out, no_borrow)
}

/// `x - y` for `y ≤ x` known, `width` bits: `x + ¬y + 1`.
fn sub_words<T: CircuitTrait>(b: &mut T, x: &[usize], y: &[usize], width: usize) -> Vec<usize> {
    let one = b.one();
    let ny: Vec<usize> = (0..width).map(|i| y.get(i).map_or(one, |&w| b.xor_wire(w, one))).collect();
    let mut out = Vec::with_capacity(width);
    let mut carry = one;
    for i in 0..width {
        let xi = x.get(i).copied().unwrap_or(b.zero());
        let (s, c) = full_adder(b, xi, ny[i], carry);
        out.push(s);
        carry = c;
    }
    out
}

fn mux_words<T: CircuitTrait>(b: &mut T, sel: usize, x: &[usize], y: &[usize]) -> Vec<usize> {
    x.iter()
        .zip(y)
        .map(|(&p, &q)| {
            let d = b.xor_wire(p, q);
            let t = b.and_wire(sel, d);
            b.xor_wire(p, t)
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Modular reduction.
// ---------------------------------------------------------------------------

/// The canonical residue of `pos - neg`.
pub fn reduce<T: CircuitTrait>(b: &mut T, mut pos: Cols, mut neg: Cols) -> Fp {
    let p = P as u128;
    // Fold every bit above 2^30: 2^(31+k) ≡ 2^(24+k) - 2^k.
    loop {
        let mut moved = false;
        for side in [true, false] {
            let (from, to) = if side { (&mut pos, &mut neg) } else { (&mut neg, &mut pos) };
            let high: Vec<(usize, usize)> = from
                .cols
                .iter()
                .enumerate()
                .skip(BITS)
                .flat_map(|(j, c)| c.iter().map(move |&w| (j, w)))
                .collect();
            if !high.is_empty() {
                moved = true;
                from.cols.truncate(BITS);
                for (j, w) in high {
                    let k = j - BITS;
                    from.push(24 + k, w);
                    to.push(k, w);
                }
            }
        }
        if !moved {
            break;
        }
    }
    let max_pos = pos.bound();
    let max_neg = neg.bound();
    let sum_pos = pos.compress(b);
    let sum_neg = neg.compress(b);
    // R = pos + K·p - neg ≥ 0.
    let k = max_neg.div_ceil(p);
    let bound = max_pos + k * p;
    let width = (128 - bound.leading_zeros()) as usize;
    let shifted = add_const(b, &sum_pos, k * p, width);
    let mut r = sub_words(b, &shifted, &sum_neg, width);
    // Conditional subtractions of 2^i · p, from the largest multiple down.
    let multiples = bound / p;
    let mut i = if multiples == 0 { 0 } else { 127 - multiples.leading_zeros() as usize };
    let mut r_bound = bound;
    while r_bound >= p {
        let c = p << i;
        if c <= r_bound {
            let (d, ok) = sub_const(b, &r, c, width);
            r = mux_words(b, ok, &r, &d);
            r_bound = if r_bound >= c { (r_bound - c).max(c - 1) } else { r_bound };
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }
    debug_assert!(r_bound < p);
    r.truncate(BITS);
    while r.len() < BITS {
        r.push(b.zero());
    }
    r
}

// ---------------------------------------------------------------------------
// Field operations.
// ---------------------------------------------------------------------------

pub fn constant<T: CircuitTrait>(b: &mut T, v: u32) -> Fp {
    (0..BITS).map(|i| if (v >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
}

/// `x + y mod p`: a 32-bit sum, then one conditional subtraction of `p`.
pub fn add<T: CircuitTrait>(b: &mut T, x: &Fp, y: &Fp) -> Fp {
    let mut cols = Cols::from_bits(x);
    cols.extend(&Cols::from_bits(y), 0);
    let s = cols.compress(b);
    let (d, ok) = sub_const(b, &s, P as u128, 32);
    let mut r = mux_words(b, ok, &s, &d);
    r.truncate(BITS);
    r
}

/// `x - y mod p`.
pub fn sub<T: CircuitTrait>(b: &mut T, x: &Fp, y: &Fp) -> Fp {
    // x - y + p, then subtract p if that is ≥ p (i.e. x ≥ y).
    let xp = add_const(b, x, P as u128, 32);
    let d = sub_words(b, &xp, y, 32);
    let (e, ok) = sub_const(b, &d, P as u128, 32);
    let mut r = mux_words(b, ok, &d, &e);
    r.truncate(BITS);
    r
}

pub fn double<T: CircuitTrait>(b: &mut T, x: &Fp) -> Fp {
    let mut s = vec![b.zero()];
    s.extend_from_slice(x);
    let (d, ok) = sub_const(b, &s, P as u128, 32);
    let mut r = mux_words(b, ok, &s, &d);
    r.truncate(BITS);
    r
}

/// `x / 2`: `x >> 1` if even, `(x + p) >> 1` if odd.
pub fn halve<T: CircuitTrait>(b: &mut T, x: &Fp) -> Fp {
    let xp = add_const(b, x, P as u128, 32);
    let even: Vec<usize> = x[1..].iter().copied().chain([b.zero()]).collect();
    let odd: Vec<usize> = xp[1..32].to_vec();
    mux_words(b, x[0], &even, &odd)
}

/// The partial products of `x · y`, as columns.
fn mul_cols<T: CircuitTrait>(b: &mut T, x: &[usize], y: &[usize]) -> Cols {
    let mut cols = Cols::default();
    for (i, &xi) in x.iter().enumerate() {
        for (j, &yj) in y.iter().enumerate() {
            let w = b.and_wire(xi, yj);
            cols.push(i + j, w);
        }
    }
    cols
}

/// `x · c` for a constant `c`, as columns (no gates).
fn mul_const_cols(x: &[usize], c: u32) -> Cols {
    let mut cols = Cols::default();
    for j in 0..32 {
        if (c >> j) & 1 == 1 {
            for (i, &xi) in x.iter().enumerate() {
                cols.push(i + j, xi);
            }
        }
    }
    cols
}

pub fn mul<T: CircuitTrait>(b: &mut T, x: &Fp, y: &Fp) -> Fp {
    let cols = mul_cols(b, x, y);
    reduce(b, cols, Cols::default())
}

pub fn mul_const<T: CircuitTrait>(b: &mut T, x: &Fp, c: u32) -> Fp {
    reduce(b, mul_const_cols(x, c), Cols::default())
}

/// `x / 2^k`: halvings for small `k`, a constant multiplication otherwise.
pub fn div_2exp<T: CircuitTrait>(b: &mut T, x: &Fp, k: u32) -> Fp {
    if k <= 12 {
        let mut acc = x.clone();
        for _ in 0..k {
            acc = halve(b, &acc);
        }
        acc
    } else {
        let mut inv = 1u32;
        let half = ((P as u64 + 1) / 2) as u32;
        for _ in 0..k {
            inv = poseidon2::reference::mul(inv, half);
        }
        mul_const(b, x, inv)
    }
}

pub fn sbox<T: CircuitTrait>(b: &mut T, x: &Fp) -> Fp {
    let x2 = mul(b, x, x);
    mul(b, &x2, x)
}

// ---------------------------------------------------------------------------
// Poseidon2, width 16.
// ---------------------------------------------------------------------------

fn apply_mat4<T: CircuitTrait>(b: &mut T, x: &mut [Fp]) {
    let t01 = add(b, &x[0], &x[1]);
    let t23 = add(b, &x[2], &x[3]);
    let t0123 = add(b, &t01, &t23);
    let t01123 = add(b, &t0123, &x[1]);
    let t01233 = add(b, &t0123, &x[3]);
    let d0 = double(b, &x[0]);
    let d2 = double(b, &x[2]);
    x[3] = add(b, &t01233, &d0);
    x[1] = add(b, &t01123, &d2);
    x[0] = add(b, &t01123, &t01);
    x[2] = add(b, &t01233, &t23);
}

pub fn mds_light<T: CircuitTrait>(b: &mut T, state: &mut [Fp; WIDTH]) {
    for chunk in state.chunks_exact_mut(4) {
        apply_mat4(b, chunk);
    }
    let mut sums: Vec<Fp> = Vec::new();
    for k in 0..4 {
        let mut s = state[k].clone();
        for j in (4..WIDTH).step_by(4) {
            s = add(b, &s, &state[j + k]);
        }
        sums.push(s);
    }
    for (i, e) in state.iter_mut().enumerate() {
        *e = add(b, e, &sums[i % 4]);
    }
}

pub fn internal_linear<T: CircuitTrait>(b: &mut T, state: &mut [Fp; WIDTH]) {
    let mut part_sum = state[1].clone();
    for s in state.iter().skip(2) {
        part_sum = add(b, &part_sum, s);
    }
    let full_sum = add(b, &part_sum, &state[0]);
    let s = state.clone();
    state[0] = sub(b, &part_sum, &s[0]);
    state[1] = add(b, &s[1], &full_sum);
    let d = double(b, &s[2]);
    state[2] = add(b, &d, &full_sum);
    let h = halve(b, &s[3]);
    state[3] = add(b, &h, &full_sum);
    let d = double(b, &s[4]);
    let t = add(b, &d, &s[4]);
    state[4] = add(b, &full_sum, &t);
    let d = double(b, &s[5]);
    let d = double(b, &d);
    state[5] = add(b, &full_sum, &d);
    let h = halve(b, &s[6]);
    state[6] = sub(b, &full_sum, &h);
    let d = double(b, &s[7]);
    let t = add(b, &d, &s[7]);
    state[7] = sub(b, &full_sum, &t);
    let d = double(b, &s[8]);
    let d = double(b, &d);
    state[8] = sub(b, &full_sum, &d);
    let h = div_2exp(b, &s[9], 8);
    state[9] = add(b, &h, &full_sum);
    let h = div_2exp(b, &s[10], 3);
    state[10] = add(b, &h, &full_sum);
    let h = div_2exp(b, &s[11], 24);
    state[11] = add(b, &h, &full_sum);
    let h = div_2exp(b, &s[12], 8);
    state[12] = sub(b, &full_sum, &h);
    let h = div_2exp(b, &s[13], 3);
    state[13] = sub(b, &full_sum, &h);
    let h = div_2exp(b, &s[14], 4);
    state[14] = sub(b, &full_sum, &h);
    let h = div_2exp(b, &s[15], 24);
    state[15] = sub(b, &full_sum, &h);
}

/// The permutation, as `poseidon2::reference::permute`.
pub fn permute<T: CircuitTrait>(b: &mut T, state: &mut [Fp; WIDTH]) {
    mds_light(b, state);
    for rc in EXTERNAL_INITIAL.iter() {
        for (s, &c) in state.iter_mut().zip(rc.iter()) {
            let c = constant(b, c);
            let t = add(b, s, &c);
            *s = sbox(b, &t);
        }
        mds_light(b, state);
    }
    for &c in INTERNAL.iter() {
        let c = constant(b, c);
        let t = add(b, &state[0], &c);
        state[0] = sbox(b, &t);
        internal_linear(b, state);
    }
    for rc in EXTERNAL_FINAL.iter() {
        for (s, &c) in state.iter_mut().zip(rc.iter()) {
            let c = constant(b, c);
            let t = add(b, s, &c);
            *s = sbox(b, &t);
        }
        mds_light(b, state);
    }
}

/// A Merkle compression: the two 8-element digests as the state, permuted,
/// the first 8 elements out.
pub fn compress<T: CircuitTrait>(b: &mut T, left: &[Fp; 8], right: &[Fp; 8]) -> [Fp; 8] {
    let mut state: [Fp; WIDTH] = core::array::from_fn(|i| if i < 8 { left[i].clone() } else { right[i - 8].clone() });
    permute(b, &mut state);
    core::array::from_fn(|i| state[i].clone())
}

/// `PaddingFreeSponge<_, 16, 8, 8>` over a row: each chunk of 8 overwrites
/// the rate and permutes.
pub fn hash_row<T: CircuitTrait>(b: &mut T, row: &[Fp]) -> [Fp; 8] {
    let zero = constant(b, 0);
    let mut state: [Fp; WIDTH] = core::array::from_fn(|_| zero.clone());
    for chunk in row.chunks(8) {
        for (s, x) in state.iter_mut().zip(chunk) {
            *s = x.clone();
        }
        permute(b, &mut state);
    }
    core::array::from_fn(|i| state[i].clone())
}

// ---------------------------------------------------------------------------
// The quartic extension, KoalaBear[X]/(X^4 - 3).
// ---------------------------------------------------------------------------

pub type Ext = [Fp; 4];

/// Schoolbook over unreduced products: sixteen 31×31 products accumulated
/// into four columns (the wrap-around ones tripled), one reduction each.
pub fn ext_mul<T: CircuitTrait>(b: &mut T, x: &Ext, y: &Ext) -> Ext {
    let mut acc: Vec<Cols> = (0..4).map(|_| Cols::default()).collect();
    for i in 0..4 {
        for j in 0..4 {
            let prod = mul_cols(b, &x[i], &y[j]);
            if i + j >= 4 {
                // ×3 = ×1 + ×2.
                acc[i + j - 4].extend(&prod, 0);
                acc[i + j - 4].extend(&prod, 1);
            } else {
                acc[i + j].extend(&prod, 0);
            }
        }
    }
    let mut out: Vec<Fp> = Vec::new();
    for cols in acc {
        out.push(reduce(b, cols, Cols::default()));
    }
    out.try_into().expect("four coefficients")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gates::CircuitAdapter;
    use poseidon2::reference as r;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    fn input<T: CircuitTrait>(b: &mut T, w: &mut Vec<bool>, v: u32) -> Fp {
        let wires: Fp = (0..BITS).map(|_| b.fresh_one()).collect();
        w.extend((0..BITS).map(|i| (v >> i) & 1 == 1));
        wires
    }

    fn read(values: &[bool], x: &Fp) -> u32 {
        x.iter().enumerate().fold(0u32, |acc, (i, &w)| acc | (u32::from(values[w]) << i))
    }

    fn elem(rng: &mut ChaCha20Rng) -> u32 {
        rng.random_range(0..P)
    }

    /// Every gadget against the reference, with its AND count.
    #[test]
    fn matches_the_reference_and_counts_gates() {
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let mut report = Vec::new();

        // Field operations.
        for trial in 0..3 {
            let (a, v) = (elem(&mut rng), elem(&mut rng));
            let mut b = CircuitAdapter::default();
            let mut w = Vec::new();
            let x = input(&mut b, &mut w, a);
            let y = input(&mut b, &mut w, v);
            let before = b.gate_counts().direct_and;
            let s = add(&mut b, &x, &y);
            let c_add = b.gate_counts().direct_and - before;
            let before = b.gate_counts().direct_and;
            let d = sub(&mut b, &x, &y);
            let c_sub = b.gate_counts().direct_and - before;
            let before = b.gate_counts().direct_and;
            let m = mul(&mut b, &x, &y);
            let c_mul = b.gate_counts().direct_and - before;
            let before = b.gate_counts().direct_and;
            let h = halve(&mut b, &x);
            let c_halve = b.gate_counts().direct_and - before;
            let before = b.gate_counts().direct_and;
            let h8 = div_2exp(&mut b, &x, 8);
            let c_h8 = b.gate_counts().direct_and - before;
            let before = b.gate_counts().direct_and;
            let h24 = div_2exp(&mut b, &x, 24);
            let c_h24 = b.gate_counts().direct_and - before;
            let before = b.gate_counts().direct_and;
            let cube = sbox(&mut b, &x);
            let c_sbox = b.gate_counts().direct_and - before;
            let values = b.eval_gates(&w);
            assert_eq!(read(&values, &s), r::add(a, v), "add");
            assert_eq!(read(&values, &d), r::sub(a, v), "sub");
            assert_eq!(read(&values, &m), r::mul(a, v), "mul");
            assert_eq!(read(&values, &h), r::div_2exp(a, 1), "halve");
            assert_eq!(read(&values, &h8), r::div_2exp(a, 8), "div 2^8");
            assert_eq!(read(&values, &h24), r::div_2exp(a, 24), "div 2^24");
            assert_eq!(read(&values, &cube), r::sbox(a), "sbox");
            if trial == 0 {
                report.push(format!("add {c_add}, sub {c_sub}, mul {c_mul}, halve {c_halve}, div 2^8 {c_h8}, div 2^24 {c_h24}, sbox {c_sbox}"));
            }
        }

        // Extension multiplication.
        {
            let a: [u32; 4] = core::array::from_fn(|_| elem(&mut rng));
            let v: [u32; 4] = core::array::from_fn(|_| elem(&mut rng));
            let mut b = CircuitAdapter::default();
            let mut w = Vec::new();
            let x: Ext = core::array::from_fn(|i| input(&mut b, &mut w, a[i]));
            let y: Ext = core::array::from_fn(|i| input(&mut b, &mut w, v[i]));
            let before = b.gate_counts().direct_and;
            let m = ext_mul(&mut b, &x, &y);
            let c = b.gate_counts().direct_and - before;
            let values = b.eval_gates(&w);
            let got: [u32; 4] = core::array::from_fn(|i| read(&values, &m[i]));
            assert_eq!(got, r::ext4::mul(a, v), "ext mul");
            report.push(format!("ext4 mul {c}"));
        }

        // The permutation, a compression and a row hash.
        {
            let st: [u32; WIDTH] = core::array::from_fn(|_| elem(&mut rng));
            let mut b = CircuitAdapter::default();
            let mut w = Vec::new();
            let mut state: [Fp; WIDTH] = core::array::from_fn(|i| input(&mut b, &mut w, st[i]));
            let before = b.gate_counts().direct_and;
            permute(&mut b, &mut state);
            let c_perm = b.gate_counts().direct_and - before;
            let values = b.eval_gates(&w);
            let mut expect = st;
            r::permute(&mut expect);
            let got: [u32; WIDTH] = core::array::from_fn(|i| read(&values, &state[i]));
            assert_eq!(got, expect, "permutation");
            report.push(format!("poseidon2 permutation {c_perm}"));
        }
        {
            let row: Vec<u32> = (0..64).map(|_| elem(&mut rng)).collect();
            let mut b = CircuitAdapter::default();
            let mut w = Vec::new();
            let wires: Vec<Fp> = row.iter().map(|&v| input(&mut b, &mut w, v)).collect();
            let before = b.gate_counts().direct_and;
            let digest = hash_row(&mut b, &wires);
            let c = b.gate_counts().direct_and - before;
            let values = b.eval_gates(&w);
            let got: [u32; 8] = core::array::from_fn(|i| read(&values, &digest[i]));
            assert_eq!(got, r::hash_row(&row), "row hash");
            report.push(format!("hash_row of 64 elements {c}"));
        }
        for line in report {
            eprintln!("koalabear: {line} AND");
        }
    }
}
