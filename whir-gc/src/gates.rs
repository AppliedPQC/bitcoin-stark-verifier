//! The circuit interface and the garbling label, in place of the small part
//! of `bitvm-gc`'s `garbled-snark-verifier` this crate used.
//!
//! It is kept compatible with that crate on purpose:
//!
//! - [`CircuitTrait`] is its builder interface (wires 0 and 1 are the
//!   constants, inputs follow, gates return fresh wires) with the same
//!   constant folding, so every gadget here emits the circuit it would
//!   emit there and the counts are the counts a `bitvm-gc` build reports.
//! - [`CircuitAdapter`] is its stored-gate builder, for tests and for
//!   `garble`: the gate list and an evaluator.
//! - [`S`] is its 16-byte label, with [`S::hash_ext`] the same
//!   `Blake3(label ‖ gid)` truncated to 16 bytes as its `_blake3` feature,
//!   so a garbling produced here is one its guest (`check_guest_with_delta`)
//!   accepts.

use rand::RngCore;

/// A builder of boolean circuits over wire indices.
pub trait CircuitTrait {
    /// A fresh wire (an input, when allocated before any gate).
    fn fresh_one(&mut self) -> usize;

    fn fresh<const N: usize>(&mut self) -> [usize; N] {
        core::array::from_fn(|_| self.fresh_one())
    }

    /// The constant-0 wire.
    fn zero(&mut self) -> usize;

    /// The constant-1 wire.
    fn one(&mut self) -> usize;

    fn xor_wire(&mut self, x: usize, y: usize) -> usize;
    fn or_wire(&mut self, x: usize, y: usize) -> usize;
    fn and_wire(&mut self, x: usize, y: usize) -> usize;

    fn gate_counts(&self) -> GateCounts;

    /// The next wire index a `fresh_one` would return.
    fn next_wire(&self) -> usize;
}

/// Gates emitted so far, by kind. XOR is free under free-XOR garbling; the
/// AND and OR gates are the non-free ones.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GateCounts {
    pub direct_and: usize,
    pub direct_xor: usize,
    pub direct_or: usize,
}

impl GateCounts {
    pub fn non_free(&self) -> usize {
        self.direct_and + self.direct_or
    }
}

/// A stored gate: `(output, x, y)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    /// XOR.
    Add(usize, usize, usize),
    /// AND.
    Mul(usize, usize, usize),
    Or(usize, usize, usize),
}

/// The stored-gate builder: wires 0 and 1 are the constants, then inputs,
/// then gate outputs, and the gate list is kept for evaluation and garbling.
#[derive(Clone, Debug)]
pub struct CircuitAdapter {
    next_wire: usize,
    gates: Vec<Operation>,
}

impl Default for CircuitAdapter {
    fn default() -> Self {
        Self { next_wire: 2, gates: Vec::new() }
    }
}

impl CircuitAdapter {
    pub fn get_gates(&self) -> &Vec<Operation> {
        &self.gates
    }

    /// Every wire's value, the inputs taken from `witness` at wires `2..`.
    pub fn eval_gates(&self, witness: &[bool]) -> Vec<bool> {
        let mut w = vec![false; self.next_wire];
        w[1] = true;
        assert!(2 + witness.len() <= self.next_wire, "more witness bits than wires");
        for (i, &bit) in witness.iter().enumerate() {
            w[2 + i] = bit;
        }
        for g in &self.gates {
            match *g {
                Operation::Add(d, x, y) => w[d] = w[x] ^ w[y],
                Operation::Mul(d, x, y) => w[d] = w[x] & w[y],
                Operation::Or(d, x, y) => w[d] = w[x] | w[y],
            }
        }
        w
    }
}

impl CircuitTrait for CircuitAdapter {
    fn fresh_one(&mut self) -> usize {
        let index = self.next_wire;
        self.next_wire += 1;
        index
    }

    fn zero(&mut self) -> usize {
        0
    }

    fn one(&mut self) -> usize {
        1
    }

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
        let d = self.fresh_one();
        self.gates.push(Operation::Add(d, x, y));
        d
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
        let d = self.fresh_one();
        self.gates.push(Operation::Or(d, x, y));
        d
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
        let d = self.fresh_one();
        self.gates.push(Operation::Mul(d, x, y));
        d
    }

    fn gate_counts(&self) -> GateCounts {
        let mut c = GateCounts::default();
        for g in &self.gates {
            match g {
                Operation::Add(..) => c.direct_xor += 1,
                Operation::Mul(..) => c.direct_and += 1,
                Operation::Or(..) => c.direct_or += 1,
            }
        }
        c
    }

    fn next_wire(&self) -> usize {
        self.next_wire
    }
}

pub const LABEL_SIZE: usize = 16;

/// A garbling label: 16 bytes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct S(pub [u8; LABEL_SIZE]);

impl S {
    pub fn from_slice(bytes: &[u8]) -> Self {
        Self(bytes.try_into().expect("a 16-byte label"))
    }

    pub fn zero() -> Self {
        Self([0; LABEL_SIZE])
    }

    pub fn random() -> Self {
        Self(random_bytes())
    }

    /// The gate PRF: `Blake3(label ‖ gid as 4 little-endian bytes)`, first 16
    /// bytes, as `bitvm-gc`'s `_blake3` `hash_ext` without a salt.
    pub fn hash_ext(&self, gid: u32) -> Self {
        let mut input = [0u8; LABEL_SIZE + 4];
        input[..LABEL_SIZE].copy_from_slice(&self.0);
        input[LABEL_SIZE..].copy_from_slice(&gid.to_le_bytes());
        Self::from_slice(&blake3::hash(&input).as_bytes()[..LABEL_SIZE])
    }
}

impl core::ops::BitXor for S {
    type Output = S;
    fn bitxor(mut self, rhs: S) -> S {
        for (a, b) in self.0.iter_mut().zip(rhs.0) {
            *a ^= b;
        }
        self
    }
}

/// Fresh randomness from the thread-local CSPRNG (OS-seeded).
pub fn random_bytes<const N: usize>() -> [u8; N] {
    let mut out = [0u8; N];
    rand::rng().fill_bytes(&mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The folding rules, the evaluator and the label PRF.
    #[test]
    fn folds_evaluates_and_hashes() {
        let mut b = CircuitAdapter::default();
        let x = b.fresh_one();
        let y = b.fresh_one();
        assert_eq!(b.xor_wire(x, x), 0);
        assert_eq!(b.xor_wire(x, 0), x);
        assert_eq!(b.and_wire(x, 1), x);
        assert_eq!(b.and_wire(x, 0), 0);
        assert_eq!(b.or_wire(x, 1), 1);
        assert_eq!(b.or_wire(0, y), y);
        let xy = b.and_wire(x, y);
        let s = b.xor_wire(xy, y);
        assert_eq!(b.gate_counts(), GateCounts { direct_and: 1, direct_xor: 1, direct_or: 0 });
        for bits in 0..4u8 {
            let w = [bits & 1 == 1, bits & 2 == 2];
            let v = b.eval_gates(&w);
            assert_eq!(v[s], (w[0] & w[1]) ^ w[1]);
        }
        let l = S::from_slice(&[7u8; 16]);
        let mut input = [7u8; 20];
        input[16..].copy_from_slice(&5u32.to_le_bytes());
        assert_eq!(l.hash_ext(5).0[..], blake3::hash(&input).as_bytes()[..16]);
        assert_ne!(S::random(), S::random());
    }
}
