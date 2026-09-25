//! Arithmetic in the Wiedemann tower `GF(2) ⊂ GF(4) ⊂ … ⊂ GF(2^128)`, as gates.
//!
//! Plonky3's `p3-binary-field` defines level `k+1` as `T_k[X] / (X² + αX + 1)`
//! with `α = X_{k−1}` the generator of the level below (`α = 1` at the base),
//! and stores an element as its low half `a0` (coefficient of 1) and high half
//! `a1` (coefficient of `X`). A wire vector here is that bit pattern, wire `i`
//! being bit `i`, so a gadget's output can be read back with `from_repr`.
//!
//! Multiplication is Plonky3's `reference_mul`, Karatsuba over the tower:
//!
//! ```text
//! z0 = a0·b0    z2 = a1·b1    z1 = (a0+a1)(b0+b1) + z0 + z2
//! a·b = (z0 + z2) + (z1 + α·z2)·X
//! ```
//!
//! Additions are XOR and cost nothing under free-XOR; multiplication by `α` is
//! a shuffle and XORs. The only AND gates are the base-field products, three
//! per level, so a `2^k`-bit multiplication is `3^k` ANDs: 2,187 at 128 bits.

use garbled_snark_verifier::circuits::sect233k1::builder::CircuitTrait;

/// Fresh input wires for a `bits`-bit element, bit 0 first.
pub fn fresh<T: CircuitTrait>(b: &mut T, bits: usize) -> Vec<usize> {
    (0..bits).map(|_| b.fresh_one()).collect()
}

/// `x + y`: bitwise XOR.
pub fn add<T: CircuitTrait>(b: &mut T, x: &[usize], y: &[usize]) -> Vec<usize> {
    assert_eq!(x.len(), y.len(), "tower elements of one level");
    x.iter().zip(y).map(|(&p, &q)| b.xor_wire(p, q)).collect()
}

/// `α·c` at `c`'s level: `X·(c0 + c1·X) = c1 + (c0 + α·c1)·X`; the identity on `GF(2)`.
pub fn mul_alpha<T: CircuitTrait>(b: &mut T, c: &[usize]) -> Vec<usize> {
    let n = c.len();
    if n == 1 {
        return c.to_vec();
    }
    let (c0, c1) = c.split_at(n / 2);
    let alpha_c1 = mul_alpha(b, c1);
    let hi = add(b, c0, &alpha_c1);
    [c1.to_vec(), hi].concat()
}

/// `x·y`, Plonky3's `reference_mul`.
pub fn mul<T: CircuitTrait>(b: &mut T, x: &[usize], y: &[usize]) -> Vec<usize> {
    let n = x.len();
    assert_eq!(y.len(), n, "tower elements of one level");
    assert!(n.is_power_of_two(), "a tower level has a power-of-two width");
    if n == 1 {
        return vec![b.and_wire(x[0], y[0])];
    }
    let (a0, a1) = x.split_at(n / 2);
    let (b0, b1) = y.split_at(n / 2);
    let z0 = mul(b, a0, b0);
    let z2 = mul(b, a1, b1);
    let s = add(b, a0, a1);
    let t = add(b, b0, b1);
    let st = mul(b, &s, &t);
    let st_z0 = add(b, &st, &z0);
    let z1 = add(b, &st_z0, &z2);
    let lo = add(b, &z0, &z2);
    let alpha_z2 = mul_alpha(b, &z2);
    let hi = add(b, &z1, &alpha_z2);
    [lo, hi].concat()
}

/// `x²`: `(a0² + a1²) + α·a1²·X`, the cross term vanishing in characteristic 2;
/// no AND gates at all, since squaring `GF(2)` is the identity.
pub fn square<T: CircuitTrait>(b: &mut T, x: &[usize]) -> Vec<usize> {
    let n = x.len();
    if n == 1 {
        return x.to_vec();
    }
    let (a0, a1) = x.split_at(n / 2);
    let a0_sq = square(b, a0);
    let a1_sq = square(b, a1);
    let lo = add(b, &a0_sq, &a1_sq);
    let hi = mul_alpha(b, &a1_sq);
    [lo, hi].concat()
}

/// Wires driven by the bits of a constant.
pub fn constant<T: CircuitTrait>(b: &mut T, value: u128, bits: usize) -> Vec<usize> {
    let zero = b.zero();
    let one = b.one();
    (0..bits).map(|i| if (value >> i) & 1 == 1 { one } else { zero }).collect()
}

/// The bits of a `bits`-wide value, bit 0 first, as a witness.
pub fn witness_bits(value: u128, bits: usize) -> Vec<bool> {
    (0..bits).map(|i| (value >> i) & 1 == 1).collect()
}

/// Read a value back from evaluated wires.
pub fn read(wires: &[bool], elem: &[usize]) -> u128 {
    elem.iter().enumerate().fold(0u128, |acc, (i, &w)| acc | (u128::from(wires[w]) << i))
}

#[cfg(test)]
mod tests {
    use super::*;
    use garbled_snark_verifier::circuits::sect233k1::builder::CircuitAdapter;
    use p3_binary_field::{
        BinaryField128, BinaryField16, BinaryField2, BinaryField32, BinaryField4, BinaryField64,
        BinaryField8, Gf2, TowerLevel,
    };
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    /// Every level's multiply, square and `α` against Plonky3's, on random elements.
    fn check_level<L: TowerLevel + core::ops::Mul<Output = L> + Copy>(
        bits: usize,
        from: fn(u128) -> L,
        to: fn(L) -> u128,
        rng: &mut ChaCha20Rng,
        rounds: usize,
    ) -> usize {
        let mut ands = 0;
        for _ in 0..rounds {
            let a: u128 = rng.random::<u128>() & (u128::MAX >> (128 - bits));
            let b_: u128 = rng.random::<u128>() & (u128::MAX >> (128 - bits));
            let (fa, fb) = (from(a), from(b_));

            let mut bld = CircuitAdapter::default();
            let x = fresh(&mut bld, bits);
            let y = fresh(&mut bld, bits);
            let prod = mul(&mut bld, &x, &y);
            let sq = square(&mut bld, &x);
            let al = mul_alpha(&mut bld, &x);
            let counts = bld.gate_counts();
            ands = counts.direct_and + counts.custom_and;

            let mut witness = witness_bits(a, bits);
            witness.extend(witness_bits(b_, bits));
            let wires = bld.eval_gates(&witness);
            assert_eq!(read(&wires, &prod), to(fa * fb), "{bits}-bit product");
            assert_eq!(read(&wires, &sq), to(fa * fa), "{bits}-bit square");
            assert_eq!(read(&wires, &al), to(fa.mul_alpha()), "{bits}-bit alpha");
        }
        ands
    }

    #[test]
    fn every_level_matches_plonky3() {
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let ands = [
            check_level::<Gf2>(1, |v| Gf2::from_repr(v as u8), |x| x.to_repr() as u128, &mut rng, 8),
            check_level::<BinaryField2>(2, |v| BinaryField2::from_repr(v as u8), |x| x.to_repr() as u128, &mut rng, 16),
            check_level::<BinaryField4>(4, |v| BinaryField4::from_repr(v as u8), |x| x.to_repr() as u128, &mut rng, 32),
            check_level::<BinaryField8>(8, |v| BinaryField8::from_repr(v as u8), |x| x.to_repr() as u128, &mut rng, 32),
            check_level::<BinaryField16>(16, |v| BinaryField16::from_repr(v as u16), |x| x.to_repr() as u128, &mut rng, 32),
            check_level::<BinaryField32>(32, |v| BinaryField32::from_repr(v as u32), |x| x.to_repr() as u128, &mut rng, 32),
            check_level::<BinaryField64>(64, |v| BinaryField64::from_repr(v as u64), |x| x.to_repr() as u128, &mut rng, 32),
            check_level::<BinaryField128>(128, |v| BinaryField128::from_repr(v), |x| x.to_repr(), &mut rng, 32),
        ];
        // The AND count of one multiplication (square and alpha add none): 3^k at 2^k bits.
        for (k, &a) in ands.iter().enumerate() {
            assert_eq!(a, 3usize.pow(k as u32), "AND gates at {} bits", 1 << k);
        }
        eprintln!("GF(2^128) multiplication: {} AND gates", ands[7]);
    }
}
