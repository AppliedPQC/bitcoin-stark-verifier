//! `whir::reference::Challenger` reproduces Plonky3's `DuplexChallenger`.
//!
//! Every challenge the script re-derives -- OOD points, batching randomness,
//! query indices -- is a sponge sample, so a real proof passes the script
//! verifier only if the reference sponge, which the script mirrors, draws what
//! Plonky3 draws. The bare `duplexing`/`squeeze` primitives match the
//! permutation input but not the buffering: observes are batched, and one
//! permutation's rate is consumed from the end (`rate[7]`, `rate[6]`, ..), an EF
//! element being four such pops. `reference::Challenger` mirrors both, and this
//! checks it against a real `DuplexChallenger` over an interleaved schedule.

use p3_challenger::{CanObserve, CanSample, CanSampleBits, DuplexChallenger};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeField32};
use p3_koala_bear::{default_koalabear_poseidon2_16, KoalaBear, Poseidon2KoalaBear};
use whir::reference::Challenger;

type F = KoalaBear;
type EF = BinomialExtensionField<F, 4>;
type Perm = Poseidon2KoalaBear<16>;
type Ch = DuplexChallenger<F, Perm, 16, 8>;

fn f(x: u32) -> F {
    F::new(x)
}
fn u(x: F) -> u32 {
    x.as_canonical_u32()
}

/// The two challengers agree sample for sample over a schedule that exercises
/// every boundary: observes shorter than, equal to and longer than the rate,
/// samples that drain a permutation and force the next, EF samples that straddle
/// a refill, and query bits -- with more observes afterwards.
#[test]
fn reference_challenger_matches_plonky3() {
    let mut plonky = Ch::new(default_koalabear_poseidon2_16());
    let mut mirror = Challenger::new();

    let observe = |p: &mut Ch, m: &mut Challenger, xs: &[u32]| {
        for &x in xs {
            p.observe(f(x));
        }
        m.observe_slice(xs);
    };
    let field = |p: &mut Ch, m: &mut Challenger, tag: &str| {
        let a: F = p.sample();
        let b = m.sample();
        assert_eq!(u(a), b, "field sample disagreed ({tag})");
    };
    let ext = |p: &mut Ch, m: &mut Challenger, tag: &str| {
        let a: EF = p.sample();
        let ac: Vec<u32> = a.as_basis_coefficients_slice().iter().map(|x| u(*x)).collect();
        assert_eq!(ac, m.sample_ef().to_vec(), "EF sample disagreed ({tag})");
    };
    let bits = |p: &mut Ch, m: &mut Challenger, n: usize, tag: &str| {
        let a: usize = p.sample_bits(n);
        assert_eq!(a as u32, m.sample_bits(n), "bit sample disagreed ({tag})");
    };

    observe(&mut plonky, &mut mirror, &[1, 2, 3]); // short of the rate
    field(&mut plonky, &mut mirror, "after 3");
    ext(&mut plonky, &mut mirror, "straddles the first refill");
    observe(&mut plonky, &mut mirror, &(0..8).collect::<Vec<_>>()); // exactly the rate
    ext(&mut plonky, &mut mirror, "after a full-rate observe");
    field(&mut plonky, &mut mirror, "mid-buffer");
    bits(&mut plonky, &mut mirror, 6, "query index");
    observe(&mut plonky, &mut mirror, &(100..111).collect::<Vec<_>>()); // longer than the rate
    for i in 0..10 {
        field(&mut plonky, &mut mirror, &format!("drain {i}"));
    }
    ext(&mut plonky, &mut mirror, "final");

    // And the states themselves line up, so nothing diverged silently.
    let ps: Vec<u32> = plonky.sponge_state.iter().map(|x| u(*x)).collect();
    assert_eq!(ps, mirror.state().to_vec(), "sponge states diverged");
}
