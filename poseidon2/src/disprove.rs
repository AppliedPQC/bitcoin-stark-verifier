//! Disproving one step of the verifier, BitVM2-style.
//!
//! The verifier does not fit on Bitcoin and never will: it is 2162 Poseidon2
//! permutations, 1.24 GB, three hundred blocks. What BitVM2 does about that is
//! not to shrink it but to stop running it. The prover asserts the intermediate
//! values, and anyone who can show that *one step* is inconsistent takes their
//! bond. Only that one step is ever executed on-chain, and only when someone
//! cheats.
//!
//! So the question stops being "how big is the verifier" and becomes "how small
//! is a step, and how many are there".
//!
//! # A step is one permutation round
//!
//! The obvious unit is one Merkle level, and it is too big: 572 252 bytes
//! against `MAX_STANDARD_TX_WEIGHT`'s 400 000 weight units. A step has to be
//! *sub-permutation*, which sounds awkward until you notice the permutation is
//! already a chain of rounds, each taking a state and leaving a state.
//! [`crate::permutation::rounds`] emits them, and `rounds_compose_to_the_permutation`
//! asserts that chaining them all is `permute()` exactly.
//!
//! That makes the commitment scheme obvious too: the prover commits to the state
//! between rounds, a challenge names a round, and the disprove script runs that
//! one round against the committed input and output.
//!
//! # What this module is, and is not
//!
//! It is the *predicate*: given a claimed input and output for a step, decide
//! whether the claim is false. That is the part the chain has to execute, and
//! the part that has to be exactly right — a predicate that can be satisfied
//! for an honest step lets anyone steal the bond.
//!
//! It is **not** the commitment layer. What stops a prover equivocating —
//! answering one challenge with one state and another with a different one — is
//! a one-time signature over each committed value, Winternitz in BitVM2's case.
//! Those need only single-item hashing, so `OP_SHA256` suffices and no soft fork
//! is required, but they are a separate piece of work and nothing here provides
//! them. Without them this is a disprove predicate with no binding, which is to
//! say a check of an assertion nobody made.

use crate::constants::WIDTH;
use crate::{permutation, winternitz};
use crate::treepp::*;

/// One iff the two `n`-element vectors differ somewhere.
///
/// The verifier's own comparisons are `OP_EQUALVERIFY`, which aborts on
/// difference. A disprove wants the opposite and cannot simply negate it:
/// `OP_EQUALVERIFY` leaves nothing to negate, and aborting is a failed spend
/// rather than a `false`. So every element is compared to a boolean, the
/// booleans are folded with `OP_BOOLAND`, and the result is negated.
///
/// # Stack
///
/// In: `a(n) b(n)`, `b` on top. Consumes both.
/// Out: `1` if they differ anywhere, `0` if they are equal.
///
/// The roll depth shrinks by one each step, because each comparison removes two
/// items from the pair and the boolean it leaves goes to the altstack — the
/// same shrinking-depth pattern the root comparison in
/// [`crate::merkle::merkle_verify`] uses, for the same reason.
pub fn differs(n: usize) -> Script {
    script! {
        for j in 0..n {
            { n - j } OP_ROLL
            OP_EQUAL
            OP_TOALTSTACK
        }
        1
        for _ in 0..n { OP_FROMALTSTACK OP_BOOLAND }
        OP_NOT
    }
}

/// Rounds one permutation is made of.
pub fn rounds_per_permutation() -> usize {
    permutation::rounds().len()
}

/// The disprove script for round `i`: valid exactly when the claim is false.
///
/// # Stack
///
/// In: `claimed_out(16) state_in(16)`, the input on top — the layout the round
/// itself wants, with the value being challenged underneath it.
/// Out: `1` if the claimed output is wrong, `0` if it is right.
///
/// Leaving the boolean *is* the spending condition: a script ends valid only on
/// a truthy stack, so an honest step leaves `0` and the spend fails. Nothing
/// needs to assert anything.
///
/// # The direction matters
///
/// It would be easy to write this as `OP_EQUALVERIFY` and call the spend the
/// disprove, which is exactly backwards: that script succeeds when the prover
/// was *honest*. The predicate has to be false-on-honest, and it is worth a test
/// that runs both cases rather than only the one being hunted for.
pub fn round(i: usize) -> Script {
    let r = permutation::rounds()
        .into_iter()
        .nth(i)
        .expect("round index within the permutation");
    script! {
        { r }
        { differs(WIDTH) }
    }
}

/// The complete disprove: round `i`, with both states taken from signatures.
///
/// # Stack
///
/// Witness, in pop order: the signature over the input, then the signature over
/// the claimed output — [`crate::winternitz::verify`]'s layout twice.
/// Out: `1` if the claimed output is wrong, `0` if it is right.
///
/// # Why the input is verified first, and parked
///
/// Each verification consumes its witness from the top and leaves its state
/// there, so the second signature has to still be reachable — which it is not
/// if the first verification's output is sitting on top of it. The input is
/// therefore read first and moved to the altstack, which both frees the output's
/// witness and, because the move reverses twice, brings the state back in its
/// original order. That is also the order [`round`] wants: `claimed_out`
/// beneath `state_in`.
///
/// # What this costs, and what it buys
///
/// Two signature verifications on top of the round: at `w = 16` a state is 131
/// chains, so the pair is 262 witness items and about 44 kB of script against
/// the round's 50 kB. That is the price of the step being *the prover's* rather
/// than merely well-formed, and it is the difference between a disprove and a
/// check of an assertion nobody made.
pub fn round_committed(i: usize, pks_out: &[[u8; 20]], pks_in: &[[u8; 20]]) -> Script {
    script! {
        { winternitz::verify(pks_in, WIDTH) }
        for _ in 0..WIDTH { OP_TOALTSTACK }
        { winternitz::verify(pks_out, WIDTH) }
        for _ in 0..WIDTH { OP_FROMALTSTACK }
        { round(i) }
    }
}

/// A run of consecutive rounds, with only its two endpoints committed.
///
/// # Why a chunk is not one round
///
/// [`round_committed`] commits both sides of a single round, so the commitment
/// layer is paid once per round: 44 kB of signature against 50 kB of arithmetic,
/// and one key of 131 chains for every boundary in the schedule. That is the
/// wrong ratio, and it is not forced — a challenger only has to execute the run
/// containing the disputed round, so the intermediate states inside a run never
/// need to be committed at all.
///
/// Making the run longer therefore amortises a fixed cost against a growing
/// one, and the length is decided by what still relays:
///
/// ```text
/// len * round + signatures  <=  MAX_STANDARD_TX_WEIGHT
/// ```
///
/// [`max_chunk_len`] solves that. The saving is in the *setup*, which is what
/// BitVM2 deployments actually struggle with: committing every round boundary
/// needs one key per round, and committing every chunk boundary needs one per
/// chunk.
///
/// # Stack
///
/// As [`round_committed`], and for the same reasons: the input signature is read
/// first and parked, which frees the output's witness and returns the state in
/// the order the rounds want.
///
/// # Bounds
///
/// `first + len` must stay inside one permutation. The state between
/// permutations is not a permutation state — the sponge and the Merkle walk sit
/// in between — so a chunk that spanned two would be claiming a step the
/// schedule does not take.
pub fn chunk_committed(
    first: usize,
    len: usize,
    pks_out: &[[u8; 20]],
    pks_in: &[[u8; 20]],
) -> Script {
    let all = permutation::rounds();
    assert!(
        len >= 1 && first + len <= all.len(),
        "a chunk of {len} from {first} leaves the permutation, which has {} rounds",
        all.len()
    );
    let body: Vec<Script> = all.into_iter().skip(first).take(len).collect();
    script! {
        { winternitz::verify(pks_in, WIDTH) }
        for _ in 0..WIDTH { OP_TOALTSTACK }
        { winternitz::verify(pks_out, WIDTH) }
        for _ in 0..WIDTH { OP_FROMALTSTACK }
        for r in body { { r } }
        { differs(WIDTH) }
    }
}

/// The longest chunk that still fits a standard transaction.
///
/// Measured rather than divided: the rounds are not all the same size, and the
/// answer is the longest *run* that fits, not the budget over the mean.
pub fn max_chunk_len(budget: usize) -> usize {
    let pks = vec![[0u8; 20]; winternitz::state_chains()];
    let n = rounds_per_permutation();
    (1..=n)
        .take_while(|&len| {
            (0..=n - len).all(|first| chunk_committed(first, len, &pks, &pks).len() <= budget)
        })
        .last()
        .unwrap_or(0)
}

/// Bytes of the largest chunk of `len` rounds.
pub fn largest_chunk(len: usize) -> usize {
    let pks = vec![[0u8; 20]; winternitz::state_chains()];
    let n = rounds_per_permutation();
    (0..=n - len)
        .map(|first| chunk_committed(first, len, &pks, &pks).len())
        .max()
        .unwrap_or(0)
}

/// Bytes of the largest step, which is what decides whether a chunk relays.
pub fn largest_round() -> usize {
    (0..rounds_per_permutation()).map(|i| round(i).len()).max().unwrap_or(0)
}

/// Bytes of the largest *committed* step — the number a chunk is measured by.
pub fn largest_committed_round() -> usize {
    let pks = vec![[0u8; 20]; winternitz::state_chains()];
    (0..rounds_per_permutation())
        .map(|i| round_committed(i, &pks, &pks).len())
        .max()
        .unwrap_or(0)
}
