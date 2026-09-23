//! The WHIR sumcheck round in Bitcoin Script.
//!
//! WHIR differs from FRI and STIR in how it folds: instead of interpolating a
//! fiber, it runs a **sumcheck** alongside the folding, and the folding
//! randomness is the sumcheck randomness. Plonky3's `SumcheckData::verify_rounds`
//! is the ground truth, and per round it does exactly this:
//!
//! ```text
//! observe(h(0), h(inf));  r = sample();
//! claim = extrapolate_01inf(h(0), claim - h(0), h(inf), r);
//! ```
//!
//! The prover sends `h(0)` and `h(inf)`; `h(1)` is not sent because the
//! sumcheck constraint `h(0) + h(1) = claim` determines it. Reconstruction uses
//! the weights from `lagrange_weights_01inf`:
//!
//! ```text
//! L_0(r) = 1 - r      L_1(r) = r      L_inf(r) = r(r - 1)
//! h(r)   = h(0)*L_0 + h(1)*L_1 + h(inf)*L_inf
//! ```
//!
//! # Why this is good news for Bitcoin
//!
//! A round is three multiplications and a handful of additions — **no field
//! inversion at all**, unlike the STIR fold which needs one per query. It is
//! also far cheaper than a Merkle level. So WHIR's advantage here is not that
//! its arithmetic is cheaper; it is that it needs fewer queries, and on Bitcoin
//! a query is a Merkle path. See `round_vs_merkle` in the tests.

pub mod challenger;
pub mod constraint;
pub mod multilinear;
pub mod proof_script;
pub mod pruned;
pub mod reference;
pub mod sponge;
pub mod sumcheck;
pub mod transcript;
pub mod verifier;

pub(crate) mod treepp {
    pub use bitcoin_script::{define_pushable, script};
    define_pushable!();
    pub use bitcoin::ScriptBuf as Script;
}
