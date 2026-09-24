//! Winternitz one-time signatures, in Bitcoin Script.
//!
//! A disprove predicate decides whether a claimed step is false. It says nothing
//! about whose claim it is, and on its own that makes it useless: a spender can
//! answer one challenge with one state and the next with a different one, and no
//! predicate over supplied values can tell. What stops that is a **commitment**
//! to each step boundary that the prover cannot open two ways.
//!
//! Winternitz fits Bitcoin exactly, because it needs only *single-item* hashing.
//! `OP_HASH160` takes one stack item and hashes it, which is all a hash chain
//! ever asks for. That is the same argument that runs through this crate: the
//! `OP_CAT` dependency belongs to hashing a *concatenation*, and a chain has
//! nothing to concatenate.
//!
//! # Why `w = 16` and not one chain per bit
//!
//! One chain per bit is the cheapest thing to *verify* — four opcodes and a
//! push — and it does not work. A committed state is sixteen field elements,
//! 496 bits, so 505 chains with the checksum, and each chain contributes a
//! signature and a digit to the witness: **1010 stack items against Bitcoin's
//! limit of 1000**. The script fails before it executes an opcode.
//!
//! So the parameter is forced from above rather than chosen. At `w = 16` a
//! digit is four bits, a state is 128 digits and 131 chains, and the witness is
//! 262 items. The cost is walking a chain of up to fifteen hashes in script
//! instead of one conditional hash, which is dearer per chain and cheaper in
//! total because there are a quarter as many.
//!
//! # The scheme
//!
//! Per digit `d`, secret `sk`, public key `pk = H^(w-1)(sk)`, signature
//! `H^d(sk)`. Verification applies `H` exactly `w-1-d` more times and compares
//! against `pk`.
//!
//! # The checksum is not optional
//!
//! The signature for a *larger* digit is further along the chain, and a chain
//! runs towards the public key — so raising a digit is free to anyone holding
//! the signature, and raising it to `w-1` is free to anyone at all. A Winternitz
//! signature is therefore never the digits alone: it carries a checksum of
//! `sum(w-1-d_i)`, whose own chains run the same way, so raising a message digit
//! forces *lowering* a checksum digit, and lowering one means inverting `H`.
//!
//! Omitting it leaves a scheme that verifies, looks like a signature, and binds
//! nothing. [`verify`] always emits it.

use crate::constants::{P, WIDTH};
use crate::treepp::*;

/// Bits per digit. Four is what keeps the witness inside the stack limit.
pub const LOG_W: usize = 4;

/// Chain length: digits run `0 ..= W - 1`.
pub const W: usize = 1 << LOG_W;

/// Digits per field element. `8 * 4 = 32 >= 31`, and the top digit is bounded
/// by the element being canonical rather than by a separate check.
pub const DIGITS_PER_ELEMENT: usize = 8;

/// Digits in one committed state.
pub const STATE_DIGITS: usize = WIDTH * DIGITS_PER_ELEMENT;

/// Checksum digits: enough for `sum(W - 1 - d_i)`, whose maximum is
/// `message_digits * (W - 1)`.
pub const fn checksum_digits(message_digits: usize) -> usize {
    let max = message_digits * (W - 1);
    let mut n = 0;
    let mut cap = 1usize;
    while cap <= max {
        cap *= W;
        n += 1;
    }
    n
}

/// Chains in a signature over `message_digits` digits.
pub const fn chains(message_digits: usize) -> usize {
    message_digits + checksum_digits(message_digits)
}

/// Verify one chain against its public key, leaving the digit.
///
/// # Stack
///
/// In: `sig(20) d`. Out: `d`. Aborts unless the signature opens to that digit.
///
/// # How a variable-length walk is done without a loop opcode
///
/// The number of hashes is `W - 1 - d`, which is not known when the script is
/// built. The walk is therefore unrolled `W - 1` times with a counter, and each
/// step hashes only while the counter is positive. Requiring the counter to
/// reach exactly zero is what rejects a digit outside `0 ..= W - 1`: a negative
/// one never decrements and a large one never finishes.
fn verify_digit(pk: &[u8; 20]) -> Script {
    script! {
        OP_DUP OP_TOALTSTACK          // keep the digit for the caller
        { W as u32 - 1 } OP_SWAP OP_SUB   // sig, k = W-1-d
        for _ in 0..(W - 1) {
            OP_DUP OP_0NOTEQUAL
            OP_IF
                OP_1SUB
                OP_SWAP OP_HASH160 OP_SWAP
            OP_ENDIF
        }
        0 OP_EQUALVERIFY              // the walk must have finished exactly
        { pk.to_vec() }
        OP_EQUALVERIFY
        OP_FROMALTSTACK
    }
}

/// Verify a signature and leave the message as field elements.
///
/// # Stack
///
/// Witness, with chain 0 **on top**: for each of the [`chains`] positions,
/// `sig(20) d` — the message digits least significant first, then the checksum.
/// Out: `n_elements` field elements, the first deepest.
///
/// # What the checksum buys, concretely
///
/// Raising any message digit lowers `sum(W - 1 - d_i)`, which lowers at least
/// one checksum digit. A chain's signature for a lower digit is *earlier* in the
/// chain, and a forger holds only what it was given plus the public key — the
/// far end. So the forgery costs a preimage of `H`.
///
/// This is why the checksum digits are verified with the same routine rather
/// than recomputed from the message: their being signed is the whole point, and
/// a recomputed checksum would be free to whoever is lying.
///
/// # Why nothing is parked while digits are still coming back
///
/// The digits live on the altstack, so a finished element cannot be parked
/// there: it would sit on top of the digits still to be read and be popped in
/// their place. Everything stays on the main stack, with the running checksum
/// sum kept directly beneath the element under construction, so the per-digit
/// juggle is at a constant depth however many elements are already finished.
pub fn verify(pks: &[[u8; 20]], n_elements: usize) -> Script {
    let message_digits = n_elements * DIGITS_PER_ELEMENT;
    let n_check = checksum_digits(message_digits);
    assert_eq!(
        pks.len(),
        message_digits + n_check,
        "one public key per chain: {message_digits} message digits and {n_check} checksum"
    );

    let verify_all: Vec<Script> = pks
        .iter()
        .map(|pk| script! { { verify_digit(pk) } OP_TOALTSTACK })
        .collect();
    script! {
        for v in verify_all { { v } }

        // The checksum the signature carries, most significant digit first.
        // There is no multiply opcode, so `W * x` is `LOG_W` doublings -- the
        // same emulation the field arithmetic in this crate is built from.
        0
        for _ in 0..n_check {
            for _ in 0..LOG_W { OP_DUP OP_ADD }
            OP_FROMALTSTACK OP_ADD
        }

        // Elements, most significant digit first, with `W - 1 - d` summed
        // alongside. The top two are always `sum, element`.
        0
        for _ in 0..n_elements {
            0
            for _ in 0..DIGITS_PER_ELEMENT {
                OP_FROMALTSTACK       // .. S E d
                OP_TUCK               // .. S d E d
                OP_SWAP               // .. S d d E
                for _ in 0..LOG_W { OP_DUP OP_ADD }
                OP_ADD                // .. S d E'      E' = W*E + d
                OP_SWAP               // .. S E' d
                OP_ROT                // .. E' d S
                OP_ADD                // .. E' S'
                OP_SWAP               // .. S' E'
            }
            OP_SWAP                   // finished element goes below the sum
        }

        // sum(d_i) + checksum == message_digits * (W - 1), which is what makes
        // a raised digit unaffordable. The checksum is under every element.
        { n_elements + 1 } OP_ROLL
        OP_ADD
        { (message_digits * (W - 1)) as u32 } OP_EQUALVERIFY

        // The elements came out last-first, because the digits did.
        for i in 1..n_elements { { i } OP_ROLL }
    }
}

/// Script bytes a signature verification costs, for the cost model.
pub fn verify_len(n_elements: usize) -> usize {
    let pks = vec![[0u8; 20]; chains(n_elements * DIGITS_PER_ELEMENT)];
    verify(&pks, n_elements).len()
}

/// Chains in a signature over one committed state.
pub fn state_chains() -> usize {
    chains(STATE_DIGITS)
}

/// Canonical base-`W` digits of a field element, least significant first.
pub fn digits_of(x: u32) -> [u32; DIGITS_PER_ELEMENT] {
    assert!(x < P, "commit canonical field elements");
    core::array::from_fn(|i| (x >> (LOG_W * i)) & (W as u32 - 1))
}
