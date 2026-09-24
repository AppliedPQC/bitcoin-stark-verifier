//! Garbling and evaluating a built circuit, streaming over its gate list.
//!
//! `bitvm-gc` garbles through `CircuitAdapter::build`, which materialises an
//! `Rc<RefCell<Wire>>` per wire and a `Gate` per gate -- fine for its
//! sub-circuit splits, but tens of gigabytes for a verifier of 10^8 wires. This
//! walks the gate list once with one 16-byte label per wire, garbling each
//! gate through `garbled_snark_verifier::core::gate::gate_garbled_with_delta`
//! and evaluating through its `gate_evaluate`:
//!
//! - **XOR is free**: `c0 = a0 ⊕ b0`, and the evaluator XORs its labels.
//! - **AND**, one ciphertext: `c0 = H(a0)`, `ct = H(a1) ⊕ H(a0) ⊕ b0` with
//!   `a1 = a0 ⊕ Δ`; the evaluator holding `a` for `x = 0` outputs `H(a)`, for
//!   `x = 1` outputs `H(a) ⊕ ct ⊕ b`.
//! - **OR**, one ciphertext: `c0 = H(a1) ⊕ Δ`, `ct = H(a1) ⊕ H(a0) ⊕ b1`; the
//!   evaluator outputs `H(a)` for `x = 1`, `H(a) ⊕ ct ⊕ b` for `x = 0`.
//!
//! with `H(l) = Blake3(l ‖ gid)` (`S::hash_ext`, the `_blake3` PRF). This is
//! privacy-free garbling: the evaluator knows every plaintext value and uses
//! it to pick the branch, which is the BitVM3 setting, where the proof is
//! public and the point is that the *true* label of the output wire can be
//! obtained only by an accepting evaluation.
//!
//! `Δ` is drawn at random here, never upstream's default `NON_CAC_DELTA`, the
//! public constant `S::one()`: with a public `Δ` every label yields its
//! complement, so the output's true label would be free to compute.

use garbled_snark_verifier::circuits::sect233k1::builder::{CircuitAdapter, CircuitTrait, GateOperation, Operation};
use garbled_snark_verifier::core::gate::{GateType, gate_evaluate, gate_garbled_with_delta};
use garbled_snark_verifier::core::s::S;

/// A garbled circuit: what the garbler hands the evaluator, and what it keeps.
pub struct Garbled {
    /// One per AND/OR gate, in gate order.
    pub ciphertexts: Vec<S>,
    /// Kept by the garbler: the global offset.
    pub delta: S,
    /// The false labels of the constant wires 0 and 1 and of every input wire,
    /// in wire order; the evaluator receives, per wire, the label of its value.
    pub label0: Vec<S>,
    /// The false label of the output wire; the true one is `output0 ⊕ Δ`.
    pub output0: S,
    pub output: usize,
}

impl Garbled {
    /// The label of `wire` carrying `value`, for a constant or input wire.
    pub fn input_label(&self, wire: usize, value: bool) -> S {
        if value { self.label0[wire] ^ self.delta } else { self.label0[wire] }
    }

    pub fn ciphertext_bytes(&self) -> usize {
        self.ciphertexts.len() * 16
    }
}

/// Garble `circuit` with a fresh random `Δ`. `inputs` is the number of input
/// wires, which follow the two constants at wire indices `2..2 + inputs`.
pub fn garble(circuit: &CircuitAdapter, inputs: usize, output: usize) -> Garbled {
    let n = circuit.next_wire();
    let delta = S::random();
    let mut label0: Vec<S> = vec![S::from_slice(&[0u8; 16]); n];
    for l in label0.iter_mut().take(2 + inputs) {
        *l = S::random();
    }
    let mut ciphertexts = Vec::new();
    for (gid, g) in circuit.get_gates().iter().enumerate() {
        let gid = u32::try_from(gid).expect("gate ids fit in u32");
        let GateOperation::Base(op) = g else { panic!("custom gates are not used") };
        match *op {
            Operation::Add(d, x, y) => label0[d] = label0[x] ^ label0[y],
            Operation::Mul(d, x, y) | Operation::Or(d, x, y) => {
                let gate_type = if matches!(*op, Operation::Or(..)) { GateType::Or } else { GateType::And };
                let (c0, ct) = gate_garbled_with_delta(label0[x], label0[y], gid, gate_type, delta, None);
                label0[d] = c0;
                ciphertexts.push(ct.expect("AND and OR gates carry a ciphertext"));
            }
            Operation::Const(..) => panic!("constant gates are not used"),
        }
    }
    let output0 = label0[output];
    label0.truncate(2 + inputs);
    Garbled { ciphertexts, delta, label0, output0, output }
}

/// What an evaluation yields: the output's plaintext value and its label.
pub struct Evaluation {
    pub value: bool,
    pub label: S,
}

/// Evaluate the garbled circuit on `witness`, holding the labels of the
/// witness's values. Returns the output's value and label; the label is the
/// output's true label iff the value is true.
pub fn evaluate(circuit: &CircuitAdapter, garbled: &Garbled, witness: &[bool]) -> Evaluation {
    let n = circuit.next_wire();
    let mut value = vec![false; n];
    let mut label: Vec<S> = vec![S::from_slice(&[0u8; 16]); n];
    value[1] = true;
    label[0] = garbled.input_label(0, false);
    label[1] = garbled.input_label(1, true);
    for (i, &bit) in witness.iter().enumerate() {
        value[2 + i] = bit;
        label[2 + i] = garbled.input_label(2 + i, bit);
    }
    let mut next_ct = 0;
    for (gid, g) in circuit.get_gates().iter().enumerate() {
        let gid = u32::try_from(gid).expect("gate ids fit in u32");
        let GateOperation::Base(op) = g else { panic!("custom gates are not used") };
        match *op {
            Operation::Add(d, x, y) => {
                value[d] = value[x] ^ value[y];
                label[d] = label[x] ^ label[y];
            }
            Operation::Mul(d, x, y) | Operation::Or(d, x, y) => {
                let is_or = matches!(*op, Operation::Or(..));
                let gate_type = if is_or { GateType::Or } else { GateType::And };
                let ct = garbled.ciphertexts[next_ct];
                next_ct += 1;
                value[d] = if is_or { value[x] | value[y] } else { value[x] & value[y] };
                label[d] = gate_evaluate(gate_type, value[x], label[x], label[y], Some(ct), gid, None);
            }
            Operation::Const(..) => panic!("constant gates are not used"),
        }
    }
    assert_eq!(next_ct, garbled.ciphertexts.len(), "every ciphertext consumed");
    Evaluation { value: value[garbled.output], label: label[garbled.output] }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small circuit, garbled and evaluated on every input: the label
    /// obtained is the label of the value computed.
    #[test]
    fn labels_follow_values_on_a_small_circuit() {
        let mut b = CircuitAdapter::default();
        let x = b.fresh_one();
        let y = b.fresh_one();
        let z = b.fresh_one();
        let xy = b.and_wire(x, y);
        let s = b.xor_wire(xy, z);
        let out = b.or_wire(s, x);
        let g = garble(&b, 3, out);
        assert_eq!(g.ciphertexts.len(), 2);
        for bits in 0..8u8 {
            let w = [bits & 1 == 1, bits & 2 == 2, bits & 4 == 4];
            let e = evaluate(&b, &g, &w);
            let expect = ((w[0] & w[1]) ^ w[2]) | w[0];
            assert_eq!(e.value, expect);
            assert_eq!(e.label, if expect { g.output0 ^ g.delta } else { g.output0 }, "witness {w:?}");
        }
    }
}
