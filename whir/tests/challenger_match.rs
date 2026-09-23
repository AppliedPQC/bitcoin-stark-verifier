//! Does `whir::reference`'s sponge reproduce Plonky3's `DuplexChallenger`?
//!
//! Everything the script re-derives -- OOD points, batching challenges, query
//! indices -- is a Fiat-Shamir sample. A real proof can only go through the
//! script verifier if the reference sponge, which the script mirrors, squeezes
//! the *same* values Plonky3's challenger does. Nothing tests that today: the
//! end-to-end tests feed the script made-up challenges and check only its
//! arithmetic, so this gap has never surfaced.
//!
//! It records what the two actually do. Plonky3 fills an output buffer with the
//! rate `[rate[0], .., rate[7]]` and `pop()`s it from the *end*: the first
//! sample is `rate[7]`, the next `rate[6]`, and so on, re-permuting only when the
//! buffer empties or a new value is observed. The reference reads the rate
//! *forward* from `rate[0]` and re-squeezes every `RATE`. The two diverge at the
//! very first sample.

use p3_challenger::{CanObserve, CanSample, DuplexChallenger};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeField32};
use p3_koala_bear::{default_koalabear_poseidon2_16, KoalaBear, Poseidon2KoalaBear};
use whir::reference;

type F = KoalaBear;
type EF = BinomialExtensionField<F, 4>;
type Perm = Poseidon2KoalaBear<16>;
type Ch = DuplexChallenger<F, Perm, 16, 8>;

fn u(x: F) -> u32 {
    x.as_canonical_u32()
}

/// Plonky3 consumes one permutation's rate from the end; the reference from the
/// start. This states the exact relationship, so a future replay can bridge it
/// rather than rediscover it.
#[test]
fn duplex_challenger_pops_the_rate_in_reverse() {
    let mut ch: Ch = DuplexChallenger::new(default_koalabear_poseidon2_16());
    let mut st = [0u32; 16];

    // One absorb of five field elements, then a permutation's worth of samples.
    let inputs: Vec<u32> = (1..=5).collect();
    for &x in &inputs {
        ch.observe(F::new(x));
    }
    reference::duplexing(&mut st, &inputs);
    let rate = st; // rate[0..8] is this permutation's output

    // Plonky3's samples, in order, are rate[7], rate[6], .. rate[0].
    // A field sample is one pop; an EF sample is four, its coefficients in pop
    // order. Eight elements exactly drain one permutation.
    let s0: F = ch.sample();
    assert_eq!(u(s0), rate[7], "first field sample is rate[7], not rate[0]");

    let e: EF = ch.sample();
    let ec: Vec<u32> = e.as_basis_coefficients_slice().iter().map(|x| u(*x)).collect();
    assert_eq!(ec, vec![rate[6], rate[5], rate[4], rate[3]], "EF coeffs are rate[6..2], reversed");

    // Three field samples drain rate[2], rate[1], rate[0]; the buffer is now empty.
    for expected in [rate[2], rate[1], rate[0]] {
        let s: F = ch.sample();
        assert_eq!(u(s), expected);
    }

    // The next sample must re-permute (empty output buffer, no new input).
    // The reference reproduces it with a bare squeeze.
    let next: F = ch.sample();
    let squeezed = reference::squeeze(&mut st);
    assert_eq!(u(next), squeezed[7], "after a drain, the next sample is the new rate[7]");

    // The mismatch, stated as an inequality so its removal is a real change:
    // the reference's forward first sample is not Plonky3's.
    let mut st2 = [0u32; 16];
    reference::duplexing(&mut st2, &inputs);
    assert_ne!(
        st2[0], rate[7],
        "reference reads rate[0] forward; Plonky3 pops rate[7]. If this ever \
         holds, the sponge was reconciled and the replay can drop the reversal."
    );
}
