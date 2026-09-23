//! A WHIR verifier over the binary tower fields as a boolean circuit, built on
//! the circuit API of GOAT's `bitvm-gc` (`garbled-snark-verifier`).
//!
//! Everything here is checked against Plonky3's own field and verifier code:
//! the gadgets against `p3-binary-field`'s arithmetic, and the verifier, once
//! it exists, against proofs from Plonky3's prover.

pub mod blake3;
pub mod circuit;
pub mod garble;
pub mod pruned;
pub mod reference;
pub mod stream;
pub mod tower;
