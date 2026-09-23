//! The script transcript against the reference transcript.
//!
//! `reference::transcript` is checked against Plonky3's verifier op for op in
//! `end_to_end.rs`. Here the same function drives the script emitter, and the
//! script it emits must run the transcript to the same sponge state, checking
//! every sampled slot against the reference's draw on the way. The data is
//! synthetic: the reference is the oracle, so the shapes can go beyond what a
//! small real proof exercises — several OOD samples, PoW on, two rounds, and a
//! domain wide enough for the two-chunk uniform sampler.

use bitcoin_script::{define_pushable, script};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use whir::reference::{
    self, RoundConfig, RoundData, SumcheckRoundData, TranscriptConfig, TranscriptData,
};
use whir::transcript::{self, Mode};

define_pushable!();

fn decode(v: &[u8]) -> i64 {
    if v.is_empty() { return 0; }
    let mut n: i64 = 0;
    for (i, b) in v.iter().enumerate() { n |= ((*b as i64) & 0xff) << (8 * i); }
    if v[v.len() - 1] & 0x80 != 0 { n &= !(0x80i64 << (8 * (v.len() - 1))); return -n; }
    n
}

fn run(s: bitcoin::ScriptBuf) -> Vec<u32> {
    let info = bitcoin_scriptexec::execute_script(s);
    assert!(info.error.is_none(), "errored: {:?} at {:?}", info.error, info.last_opcode);
    (0..info.final_stack.len()).map(|i| decode(&info.final_stack.get(i)) as u32).collect()
}

/// The shape of a proof's prover messages, beyond what the config fixes.
struct Shape {
    pattern_len: usize,
    /// Evaluations absorbed per opening claim.
    openings: Vec<usize>,
    final_poly_len: usize,
}

fn six() -> (TranscriptConfig, Shape) {
    (
        TranscriptConfig {
            commitment_ood_samples: 1,
            initial_folding: 2,
            initial_folding_pow_bits: 0,
            rounds: vec![],
            final_pow_bits: 0,
            final_queries: 35,
            final_domain_bits: 6,
            final_sumcheck_rounds: 5,
            final_folding_pow_bits: 0,
        },
        Shape { pattern_len: 39, openings: vec![1], final_poly_len: 32 },
    )
}

fn eight() -> (TranscriptConfig, Shape) {
    (
        TranscriptConfig {
            commitment_ood_samples: 1,
            initial_folding: 2,
            initial_folding_pow_bits: 0,
            rounds: vec![RoundConfig {
                ood_samples: 1,
                pow_bits: 0,
                num_queries: 35,
                domain_bits: 8,
                folding: 2,
                folding_pow_bits: 0,
            }],
            final_pow_bits: 0,
            final_queries: 17,
            final_domain_bits: 7,
            final_sumcheck_rounds: 5,
            final_folding_pow_bits: 0,
        },
        Shape { pattern_len: 53, openings: vec![1], final_poly_len: 32 },
    )
}

/// Every branch the small proofs leave cold.
fn stress() -> (TranscriptConfig, Shape) {
    (
        TranscriptConfig {
            commitment_ood_samples: 2,
            initial_folding: 3,
            initial_folding_pow_bits: 3,
            rounds: vec![
                RoundConfig {
                    ood_samples: 2,
                    pow_bits: 5,
                    num_queries: 20,
                    domain_bits: 10,
                    folding: 3,
                    folding_pow_bits: 2,
                },
                RoundConfig {
                    ood_samples: 1,
                    pow_bits: 4,
                    num_queries: 10,
                    // Past `MAX_SINGLE_SAMPLE_BITS`: two chunks per draw.
                    domain_bits: 26,
                    folding: 2,
                    folding_pow_bits: 0,
                },
            ],
            final_pow_bits: 4,
            final_queries: 8,
            // Eight of sixteen: plenty of duplicates to redraw.
            final_domain_bits: 4,
            final_sumcheck_rounds: 3,
            final_folding_pow_bits: 1,
        },
        Shape { pattern_len: 60, openings: vec![2, 1], final_poly_len: 8 },
    )
}

fn field(rng: &mut ChaCha20Rng) -> u32 {
    rng.random_range(0..poseidon2::constants::P)
}

fn ef(rng: &mut ChaCha20Rng) -> [u32; 4] {
    core::array::from_fn(|_| field(rng))
}

fn sumcheck(rng: &mut ChaCha20Rng, rounds: usize) -> Vec<SumcheckRoundData> {
    (0..rounds)
        .map(|_| SumcheckRoundData { poly: [ef(rng), ef(rng)], pow_witness: field(rng) })
        .collect()
}

fn synthetic(rng: &mut ChaCha20Rng, cfg: &TranscriptConfig, shape: &Shape) -> TranscriptData {
    TranscriptData {
        pattern: (0..shape.pattern_len).map(|_| field(rng)).collect(),
        root: (0..8).map(|_| field(rng)).collect(),
        initial_ood_answers: (0..cfg.commitment_ood_samples).map(|_| ef(rng)).collect(),
        openings: shape.openings.iter().map(|&n| (0..n).map(|_| ef(rng)).collect()).collect(),
        initial_sumcheck: sumcheck(rng, cfg.initial_folding),
        rounds: cfg
            .rounds
            .iter()
            .map(|r| RoundData {
                root: (0..8).map(|_| field(rng)).collect(),
                ood_answers: (0..r.ood_samples).map(|_| ef(rng)).collect(),
                pow_witness: field(rng),
                sumcheck: sumcheck(rng, r.folding),
            })
            .collect(),
        final_poly: (0..shape.final_poly_len).map(|_| ef(rng)).collect(),
        final_pow_witness: field(rng),
        final_sumcheck: sumcheck(rng, cfg.final_sumcheck_rounds),
    }
}

/// The emitted script with its stream on the altstack over a fresh state.
fn harness(stream: &[u32], body: bitcoin::ScriptBuf) -> bitcoin::ScriptBuf {
    script! {
        for v in stream.iter().rev() { { *v } OP_TOALTSTACK }
        for _ in 0..16 { 0 }
        { body }
    }
}

#[test]
fn script_transcript_reaches_the_reference_state() {
    let mut rng = ChaCha20Rng::seed_from_u64(91);
    for (name, (cfg, shape)) in [("six", six()), ("eight", eight()), ("stress", stress())] {
        let data = synthetic(&mut rng, &cfg, &shape);

        let (emitter, challenges) = transcript::transcript(&cfg, &data, Mode::Check);
        let want = reference::transcript(&cfg, &data, &mut reference::Challenger::new());
        assert_eq!(challenges, want, "{name}: emitter draws differ from the reference's");

        let body = emitter.script();
        let got = run(harness(&emitter.stream, body.clone()));
        assert_eq!(got, emitter.state().to_vec(), "{name}: final sponge state");

        let draws = challenges.rounds.iter().map(|r| r.draws).sum::<usize>() + challenges.final_draws;
        eprintln!(
            "{name}: {} permutations, {} bytes, stream {} elements, {} query draws, pow ok {}",
            emitter.permutations,
            body.len(),
            emitter.stream.len(),
            draws,
            challenges.pow_ok
        );
    }
}

/// The check is live: one expected draw off by one and the script fails.
#[test]
fn a_wrong_expected_draw_fails_the_script() {
    let mut rng = ChaCha20Rng::seed_from_u64(92);
    let (cfg, shape) = six();
    let data = synthetic(&mut rng, &cfg, &shape);
    let (emitter, _) = transcript::transcript(&cfg, &data, Mode::Check);

    // The first draw follows the pattern and the root.
    let first_draw = shape.pattern_len + 8;
    let mut stream = emitter.stream.clone();
    stream[first_draw] = (stream[first_draw] + 1) % poseidon2::constants::P;

    let info = bitcoin_scriptexec::execute_script(harness(&stream, emitter.script()));
    assert!(info.error.is_some(), "a wrong draw must not verify");
}

/// Observing invalidates buffered output: a draw after an observe comes from a
/// fresh permutation, never from the slots left by the previous one.
#[test]
fn an_observe_between_draws_forces_a_new_permutation() {
    let mut a = transcript::Emitter::new(Mode::Check);
    let mut b = transcript::Emitter::new(Mode::Check);
    use whir::reference::Sponge;
    // Two draws from one permutation.
    a.observe(1);
    a.sample();
    a.sample();
    // The same, with an observe in between: three permutations, not two.
    b.observe(1);
    b.sample();
    b.observe(2);
    b.sample();
    assert_eq!(a.permutations, 1);
    assert_eq!(b.permutations, 2);
}
