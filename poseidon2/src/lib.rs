//! Poseidon2 over the KoalaBear field, in Bitcoin Script.
//!
//! # Why this exists
//!
//! A STARK verifier on Bitcoin has to check Merkle paths and a Fiat–Shamir
//! transcript. With a byte-oriented hash that needs `OP_CAT`, because
//! `OP_SHA256` hashes one stack item and a Merkle step hashes the concatenation
//! of two children. `OP_CAT` is disabled and re-enabling it needs a soft fork.
//!
//! An *algebraic* hash removes that dependency. A Poseidon2 digest is eight
//! field elements rather than thirty-two bytes, so compressing two children
//! means feeding sixteen field elements to a width-16 permutation — sixteen
//! stack items handed to an arithmetic routine. There is nothing to
//! concatenate; the concatenation is the order the state sits in. This crate
//! contains **no `OP_CAT`, and no disabled opcode of any kind**; there is a test
//! that asserts it.
//!
//! The arithmetic follows [`rust-bitcoin-m31`] and BitVM's `bigint`: Bitcoin has
//! no `OP_MUL` either, so multiplication is emulated. KoalaBear is a 31-bit
//! prime (`0x7f000001`), so a field element fits one four-byte script number and
//! no multi-limb representation is needed.
//!
//! # What it is for
//!
//! Sizing, primarily. The open question for a post-quantum BitVM verifier is
//! what a Poseidon2 permutation costs in script, because that number decides
//! whether a FRI verifier is affordable. [`permute`] emits the script;
//! its length is the answer.
//!
//! [`rust-bitcoin-m31`]: https://github.com/Bitcoin-Wildlife-Sanctuary/rust-bitcoin-m31

pub mod constants;
pub mod disprove;
pub mod ext4;
pub mod field;
pub mod merkle;
pub mod permutation;
pub mod reference;
pub mod winternitz;

pub(crate) mod treepp {
    pub use bitcoin_script::{define_pushable, script};
    define_pushable!();
    pub use bitcoin::ScriptBuf as Script;
}

pub use constants::{EXTERNAL_FINAL, EXTERNAL_INITIAL, INTERNAL, P, WIDTH};
pub use merkle::{merkle_path, merkle_verify};
pub use permutation::{compress, permute};
