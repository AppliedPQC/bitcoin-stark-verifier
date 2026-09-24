//! Drawing challenges from the sponge, in Bitcoin Script.
//!
//! WHIR needs two kinds: field elements, which are rate slots taken as they
//! are, and query indices, which are `sample_bits` — a rate slot masked to the
//! log of the domain size.
//!
//! Plonky3's `sample` pops a buffered rate slot and re-duplexes when the buffer
//! empties. A script does not need that bookkeeping: the verifier's absorb and
//! squeeze schedule is fixed when the script is built, so which rate slot a
//! given challenge comes from is known at generation time and is a parameter
//! here rather than runtime state.

use crate::sponge::{RATE, WIDTH};
use crate::treepp::*;
use poseidon2::field;

/// Copy rate slot `j` of the state, leaving the state in place.
///
/// This is `sample::<F>()`, a single base element. Plonky3 uses it for query
/// indices — `sample_bits` starts from `let rand_f: F = self.sample()` — where
/// only `log(domain)` bits are wanted and a base element suffices.
pub fn sample(j: usize) -> Script {
    assert!(j < RATE);
    script! { { WIDTH - 1 - j } OP_PICK }
}

/// [`sample`] with `under` items sitting above the sponge state.
///
/// A query opening is the one place the state is not on top: the opening's root,
/// siblings and row have to be on the main stack before the index can be turned
/// into path directions, because the direction bits go on the altstack and would
/// otherwise be popped in the opening's place. Rather than shuffle the state
/// around the opening, the pick simply reaches further.
pub fn sample_at(j: usize, under: usize) -> Script {
    assert!(j < RATE);
    script! { { WIDTH - 1 - j + under } OP_PICK }
}

/// Number of extension challenges one squeeze yields.
pub const EF_PER_SQUEEZE: usize = RATE / 4;

/// Draw the `j`-th extension challenge from the rate.
///
/// This is `sample_algebra_element::<EF>()`, which is what the folding and
/// constraint challenges are: four consecutive base elements read as the
/// coefficients of one `EF` element. **This is what sets the security level.** A
/// base-field challenge caps soundness near 31 bits however many queries are
/// made; at degree four the challenge space is about 124 bits, which is what
/// Plonky3 requires and what its `WhirConfig` refuses to build without.
///
/// A rate of eight yields two extension challenges per squeeze, so the absorb
/// and squeeze schedule has to count in these, not in base elements.
///
/// Like [`poseidon2::ext4::copy`], the four picks sit at a constant depth: each
/// push shifts the remainder by exactly the step to the next coefficient.
pub fn sample_ef(j: usize) -> Script {
    assert!(j < EF_PER_SQUEEZE);
    script! {
        for _ in 0..4 { { WIDTH - 1 - 4 * j } OP_PICK }
    }
}

/// An extension challenge the way Plonky3 draws it: four rate slots from the
/// end, `rate[hi]` first, then `rate[hi-1]`, `rate[hi-2]`, `rate[hi-3]`.
///
/// [`sample_ef`] reads a group of four *forward*, which the reference sponge
/// also did; but `DuplexChallenger::sample::<EF>` `pop()`s the rate from the
/// back, so its coefficients are those four slots in descending order. `hi` is
/// the highest unread slot: `7` for the first EF drawn from a permutation, `3`
/// for the second, which is how two EFs come out of one squeeze.
///
/// Each pick reaches one slot lower and one item deeper, since the previous pick
/// left its copy on top -- the two offsets cancel, so this is four picks at a
/// walking depth rather than a constant one.
pub fn sample_ef_pop(hi: usize) -> Script {
    assert!(hi < RATE && hi >= 3);
    script! {
        { sample(hi) }
        { sample_at(hi - 1, 1) }
        { sample_at(hi - 2, 2) }
        { sample_at(hi - 3, 3) }
    }
}

/// `sample_bits`: rate slot `j`, masked to its low `bits` bits.
///
/// The mask is where an `OP_MOD` would go if script had one. It does not, so
/// the bits are peeled off by comparison and subtraction and reassembled with
/// their weights — which is also why the bits above `bits` have to be
/// subtracted away first rather than simply ignored.
pub fn sample_bits(j: usize, bits: usize) -> Script {
    script! {
        { sample(j) }
        { field::low_bits_to_altstack(bits) }
        0
        for i in 0..bits {
            OP_FROMALTSTACK
            OP_IF { 1u32 << i } OP_ADD OP_ENDIF
        }
    }
}
