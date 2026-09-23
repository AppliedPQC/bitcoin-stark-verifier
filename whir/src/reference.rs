//! The round in plain Rust, transcribed from Plonky3's `p3-sumcheck`.

use poseidon2::reference as f;

/// The extension element `1`.
pub const EF_ONE: [u32; 4] = [1, 0, 0, 0];

/// `lagrange_weights_01inf` over `EF`: `[1 - r, r, r*(r - 1)]`.
pub fn lagrange_weights_01inf(r: [u32; 4]) -> [[u32; 4]; 3] {
    use poseidon2::reference::ext4;
    [ext4::sub(EF_ONE, r), r, ext4::mul(r, ext4::sub(r, EF_ONE))]
}

/// `extrapolate_01inf(e0, e1, e_inf, r) = e0*w0 + e1*w1 + e_inf*w_inf`.
pub fn extrapolate_01inf(e0: [u32; 4], e1: [u32; 4], e_inf: [u32; 4], r: [u32; 4]) -> [u32; 4] {
    use poseidon2::reference::ext4;
    let [w0, w1, w_inf] = lagrange_weights_01inf(r);
    ext4::add(ext4::add(ext4::mul(e0, w0), ext4::mul(e1, w1)), ext4::mul(e_inf, w_inf))
}

/// One round of `verify_rounds`: `h(1)` comes from the sumcheck constraint, and
/// the new claim is `h(r)`.
pub fn sumcheck_round(claim: [u32; 4], c0: [u32; 4], c_inf: [u32; 4], r: [u32; 4]) -> [u32; 4] {
    use poseidon2::reference::ext4;
    extrapolate_01inf(c0, ext4::sub(claim, c0), c_inf, r)
}

/// One transcript-bound round: the mirror of [`crate::sumcheck::sumcheck_round_fs`].
///
/// Absorbs `c0 || c_inf` as eight base elements — coefficient 0 first, which is
/// the order the script's picks consume them in — permutes, and reads the
/// challenge from the first four rate slots. Returns the chained claim and the
/// challenge that produced it, so a test can check both.
pub fn sumcheck_round_fs(
    state: &mut [u32; 16],
    claim: [u32; 4],
    c0: [u32; 4],
    c_inf: [u32; 4],
) -> ([u32; 4], [u32; 4]) {
    let mut inputs = [0u32; 2 * 4];
    inputs[..4].copy_from_slice(&c0);
    inputs[4..].copy_from_slice(&c_inf);
    duplexing(state, &inputs);
    let r: [u32; 4] = state[..4].try_into().expect("rate holds four elements");
    (sumcheck_round(claim, c0, c_inf, r), r)
}

/// `eval_multilinear_recursive` from Plonky3's `multilinear-util`.
///
/// `evals` holds `2^n` values indexed big-endian by the point variables, so the
/// *last* variable pairs adjacent entries and folding runs backwards to
/// `point[0]`. Each step is `e[2j] + x*(e[2j+1] - e[2j])`.
pub fn eval_multilinear(evals: &[[u32; 4]], point: &[[u32; 4]]) -> [u32; 4] {
    use poseidon2::reference::ext4;
    assert_eq!(evals.len(), 1 << point.len());
    let mut cur = evals.to_vec();
    for &x in point.iter().rev() {
        cur = (0..cur.len() / 2)
            .map(|j| {
                let (a, b) = (cur[2 * j], cur[2 * j + 1]);
                ext4::add(a, ext4::mul(x, ext4::sub(b, a)))
            })
            .collect();
    }
    cur[0]
}

/// Sponge rate. Plonky3 uses `DuplexChallenger<_, _, 16, 8>` with this permutation.
pub const RATE: usize = 8;

/// Plonky3's `DuplexChallenger::duplexing`, for a statically known absorb count.
///
/// Overwrite the leading `k` rate slots, zero the rest of the rate, bind `k`
/// into the first capacity element so that length and zero-padding cannot
/// collide, then permute. `k == 0` is a squeeze: permute only.
pub fn duplexing(state: &mut [u32; 16], inputs: &[u32]) {
    let k = inputs.len();
    assert!(k <= RATE);
    for (i, v) in inputs.iter().enumerate() {
        state[i] = *v;
    }
    if k > 0 {
        for s in state.iter_mut().take(RATE).skip(k) {
            *s = 0;
        }
        state[RATE] = f::add(state[RATE], k as u32);
    }
    poseidon2::reference::permute(state);
}

/// The squeezed values: the rate after a duplexing.
pub fn squeeze(state: &mut [u32; 16]) -> [u32; RATE] {
    duplexing(state, &[]);
    state[..RATE].try_into().unwrap()
}

/// Plonky3's `DuplexChallenger`, buffering and all.
///
/// The bare [`duplexing`]/[`squeeze`] above match Plonky3's permutation input
/// exactly, but a real transcript's challenges depend on *when* the sponge
/// permutes and *which* rate slots a sample reads -- and those are governed by
/// two buffers, not by the permutation. This mirrors them, so a replay of a real
/// proof draws the same challenges Plonky3 drew.
///
/// The two things the bare functions leave out:
/// - **Observes are buffered.** They accumulate until the rate is full or a
///   sample forces a permutation, so several observes fold into one absorb.
/// - **Samples pop the rate from the end.** One permutation's output is consumed
///   `rate[7]`, `rate[6]`, .. down to `rate[0]` before the next permutation, and
///   an EF element is four such pops, its coefficients in that order.
#[derive(Clone, Debug)]
pub struct Challenger {
    state: [u32; 16],
    input: Vec<u32>,
    output: Vec<u32>,
}

impl Default for Challenger {
    fn default() -> Self {
        Self::new()
    }
}

impl Challenger {
    /// A challenger over the zero state, as `DuplexChallenger::new` starts.
    pub fn new() -> Self {
        Self { state: [0u32; 16], input: Vec::new(), output: Vec::new() }
    }

    /// The current sponge state, for tests that compare against Plonky3's.
    pub fn state(&self) -> [u32; 16] {
        self.state
    }

    /// Absorb one field element. Buffered outputs are now stale.
    pub fn observe(&mut self, value: u32) {
        self.output.clear();
        self.input.push(value);
        if self.input.len() == RATE {
            self.duplex();
        }
    }

    /// Absorb a slice, one element at a time (the buffering is what matters).
    pub fn observe_slice(&mut self, values: &[u32]) {
        for &v in values {
            self.observe(v);
        }
    }

    /// Absorb the buffered inputs (or, with none, squeeze) and refill the output.
    fn duplex(&mut self) {
        duplexing(&mut self.state, &self.input);
        self.input.clear();
        self.output.clear();
        self.output.extend_from_slice(&self.state[..RATE]);
    }

    /// One field-element challenge: the next rate slot from the end.
    pub fn sample(&mut self) -> u32 {
        if !self.input.is_empty() || self.output.is_empty() {
            self.duplex();
        }
        self.output.pop().expect("output refilled by duplex")
    }

    /// An EF element: four field samples, its coefficients in pop order.
    pub fn sample_ef(&mut self) -> [u32; 4] {
        [self.sample(), self.sample(), self.sample(), self.sample()]
    }

    /// A query index: the low `bits` of one field sample.
    pub fn sample_bits(&mut self, bits: usize) -> u32 {
        sample_bits(self.sample(), bits)
    }
}

/// `DuplexChallenger::sample_bits`: take a squeezed field element and keep its
/// low `bits` bits. Plonky3 asserts `2^bits < |F|`, so no reduction is needed.
pub fn sample_bits(rate_element: u32, bits: usize) -> u32 {
    assert!((1u64 << bits) < poseidon2::constants::P as u64);
    rate_element & ((1 << bits) - 1)
}

/// `sigma' = base + sum_{i=0}^{t} gamma^(i+1) * y_i`: the mirror of
/// [`crate::constraint::combine_answers`].
///
/// Written as the sum rather than as Horner, on purpose. The script uses Horner
/// because multiplications are expensive there; the reference should state what
/// is being computed, so that a mistake in the rearrangement shows up as a
/// disagreement rather than being copied into both.
pub fn combine_answers(base: [u32; 4], gamma: [u32; 4], answers: &[[u32; 4]]) -> [u32; 4] {
    use poseidon2::reference::ext4;
    let mut acc = base;
    let mut power = gamma; // gamma^(i+1), starting at i = 0
    for y in answers {
        acc = ext4::add(acc, ext4::mul(power, *y));
        power = ext4::mul(power, gamma);
    }
    acc
}

/// `eq(z, r)`: the mirror of [`crate::constraint::eq_eval`].
///
/// Written as the definition — a product of `z_i*r_i + (1-z_i)*(1-r_i)` — rather
/// than as the one-multiplication rearrangement the script uses. The script is
/// allowed to be clever because a multiplication over `EF` is sixteen base
/// multiplications; the reference should say what is meant, so that an error in
/// the rearrangement shows up as a disagreement instead of being copied into
/// both.
pub fn eq_eval(z: &[[u32; 4]], r: &[[u32; 4]]) -> [u32; 4] {
    use poseidon2::reference::ext4;
    assert_eq!(z.len(), r.len(), "eq is a product over matching coordinates");
    let mut acc = EF_ONE;
    for (&a, &b) in z.iter().zip(r) {
        let term = ext4::add(
            ext4::mul(a, b),
            ext4::mul(ext4::sub(EF_ONE, a), ext4::sub(EF_ONE, b)),
        );
        acc = ext4::mul(acc, term);
    }
    acc
}

/// `expand_from_univariate`: the mirror of [`crate::constraint::expand_univariate`].
///
/// `[u^(2^(m-1)), ..., u^2, u]` — the multilinear point whose `eq` picks out the
/// univariate evaluation at `u`.
pub fn expand_univariate(u: [u32; 4], m: usize) -> Vec<[u32; 4]> {
    use poseidon2::reference::ext4;
    let mut out = vec![[0u32; 4]; m];
    let mut cur = u;
    for i in (0..m).rev() {
        out[i] = cur;
        cur = ext4::mul(cur, cur);
    }
    out
}

/// `evaluation_of_weights`: the mirror of [`crate::constraint::constraint_eval`].
///
/// `randomness` is the concatenation of every round's folding randomness. Each
/// constraint reads the **last** `z.len()` coordinates of it, which is what
/// Plonky3's `eval_constraints_poly` does by reversing, slicing to the
/// constraint's arity, and reversing back.
pub fn constraint_eval(
    randomness: &[[u32; 4]],
    groups: &[Vec<([u32; 4], Vec<[u32; 4]>)>],
) -> [u32; 4] {
    use poseidon2::reference::ext4;
    let mut acc = [0u32; 4];
    for group in groups {
        for (w, z) in group {
            assert!(z.len() <= randomness.len(), "constraint arity exceeds the randomness");
            let local = &randomness[randomness.len() - z.len()..];
            acc = ext4::add(acc, ext4::mul(*w, eq_eval(z, local)));
        }
    }
    acc
}

/// The mirror of [`crate::constraint::constraint_eval_batched`].
///
/// Written as the sum with the powers spelled out, not as Horner: the script is
/// allowed to rearrange because multiplications are expensive there, and the
/// reference should say what is meant so a mistake in the rearrangement shows up
/// as a disagreement. The powers start at `chi^0 = 1`, which is Plonky3's
/// `shifted_powers` convention and not the `gamma^(i+1)` of the paper's
/// `sigma'`.
pub fn constraint_eval_batched(
    randomness: &[[u32; 4]],
    groups: &[([u32; 4], Vec<[u32; 4]>, usize)],
) -> [u32; 4] {
    use poseidon2::reference::ext4;
    let mut acc = [0u32; 4];
    for (chi, scalars, arity) in groups {
        let local = &randomness[randomness.len() - arity..];
        let mut power = EF_ONE;
        for u in scalars {
            let point = expand_univariate(*u, *arity);
            acc = ext4::add(acc, ext4::mul(power, eq_eval(&point, local)));
            power = ext4::mul(power, *chi);
        }
    }
    acc
}

/// `sum_j w_j * f_M(z_j)`: the mirror of [`crate::constraint::closing_check`].
///
/// Returns the accumulated left-hand side, so a test can compare it with the
/// target rather than only observing that the script accepted.
pub fn closing_sum(evals: &[[u32; 4]], points: &[([u32; 4], Vec<[u32; 4]>)]) -> [u32; 4] {
    use poseidon2::reference::ext4;
    let mut acc = [0u32; 4];
    for (w, z) in points {
        acc = ext4::add(acc, ext4::mul(*w, eval_multilinear(evals, z)));
    }
    acc
}

// ---------------------------------------------------------------------------
// The WHIR verifier's transcript, as Plonky3 executes it.
//
// Plonky3's `DomainSeparator` declares an observe/sample pattern; the
// verifier then runs a sequence of calls whose every sampler
// (`sample_algebra_element`, `sample_bits`, `sample_uniform_bits`,
// `check_witness`) is a trait default over one primitive `sample()`, and
// whose every observer bottoms out in `observe(F)`. `transcript` is that
// executed sequence, written over the two primitives, so that anything able
// to observe and sample (the reference sponge, a log of Plonky3's own calls,
// a script) can be driven through the same schedule.
//
// Plonky3 0.7 layers its transcript: the commitment, each out-of-domain
// virtual claim, each opening claim, the WHIR run, the batching draw and
// every sumcheck delegate run as their own sub-transcript, and each *seeds*
// the sponge with its domain separator (a constant of the configuration)
// before its first interaction. Those seeds are inputs here; the test bed
// reads them off a logged run and cross-checks the WHIR one against the API.
//
// The order, per `WhirVerifier::verify` and the PCS adapter around it:
//
//   1. the commitment seed, then the root
//   2. per commitment OOD sample: its seed, draw the point, absorb the answer
//   3. per opening claim: its seed, draw the point, absorb the evaluations
//   4. the WHIR seed, the batching seed, draw the batching randomness
//   5. the initial sumcheck: its seed, then per round absorb `[c0, c_inf]`,
//      PoW, draw
//   6. per intermediate round: absorb the root; per OOD draw and absorb;
//      PoW; the STIR queries, a fixed `num_queries` uniform draws (every
//      position when the domain is no larger), duplicates kept, in draw
//      order; draw the combination randomness; the round's sumcheck as in 5
//   7. absorb the final polynomial; PoW; the final STIR queries; the final
//      sumcheck as in 5
// ---------------------------------------------------------------------------

/// What a transcript needs of its challenger: the two primitives every
/// Plonky3 sampler and observer reduces to, and the derived draws.
pub trait Sponge {
    fn observe(&mut self, value: u32);
    fn sample(&mut self) -> u32;

    fn observe_ef(&mut self, x: &[u32; 4]) {
        for &c in x {
            self.observe(c);
        }
    }

    /// An EF element: four base samples, coefficients in draw order.
    fn sample_ef(&mut self) -> [u32; 4] {
        let a = self.sample();
        let b = self.sample();
        let c = self.sample();
        let d = self.sample();
        [a, b, c, d]
    }

    /// `DuplexChallenger::sample_bits`: one draw, the low `bits` bits kept.
    fn sample_bits(&mut self, bits: usize) -> u32 {
        sample_bits(self.sample(), bits)
    }

    /// `check_witness`: absorb the witness, then `bits` sampled bits must be zero.
    fn check_witness(&mut self, bits: usize, witness: u32) -> bool {
        if bits == 0 {
            return true;
        }
        self.observe(witness);
        self.sample_bits(bits) == 0
    }

    /// `DuplexChallenger::sample_uniform_bits::<true>`: draw until the
    /// element is below `m_k = floor(P / 2^k) * 2^k`, keep its low `k` bits;
    /// past 24 bits, two half-width draws are combined.
    fn sample_uniform_bits(&mut self, bits: usize) -> u32 {
        if bits == 0 {
            return 0;
        }
        if bits <= MAX_SINGLE_SAMPLE_BITS {
            return self.uniform_chunk(bits);
        }
        let half1 = bits / 2;
        let half2 = bits - half1;
        let chunk1 = self.uniform_chunk(half1);
        let chunk2 = self.uniform_chunk(half2);
        chunk1 | (chunk2 << half1)
    }

    /// One rejection-sampled chunk of `bits` uniform bits.
    fn uniform_chunk(&mut self, bits: usize) -> u32 {
        let m = (poseidon2::constants::P >> bits) << bits;
        loop {
            let v = self.sample();
            if v < m {
                return v & ((1 << bits) - 1);
            }
        }
    }
}

/// KoalaBear's `UniformSamplingField::MAX_SINGLE_SAMPLE_BITS`.
pub const MAX_SINGLE_SAMPLE_BITS: usize = 24;

impl Sponge for Challenger {
    fn observe(&mut self, value: u32) {
        Challenger::observe(self, value);
    }

    fn sample(&mut self) -> u32 {
        Challenger::sample(self)
    }
}

/// One intermediate round's public parameters, as the transcript needs them.
#[derive(Clone, Debug)]
pub struct RoundConfig {
    pub ood_samples: usize,
    pub pow_bits: usize,
    pub num_queries: usize,
    /// log2 of the folded domain the queries index (`domain_size >> folding`).
    pub domain_bits: usize,
    /// Sumcheck rounds after this round's commitment: the next folding factor.
    pub folding: usize,
    pub folding_pow_bits: usize,
}

/// The public parameters that shape the transcript.
#[derive(Clone, Debug)]
pub struct TranscriptConfig {
    pub commitment_ood_samples: usize,
    pub initial_folding: usize,
    pub initial_folding_pow_bits: usize,
    pub rounds: Vec<RoundConfig>,
    pub final_pow_bits: usize,
    pub final_queries: usize,
    pub final_domain_bits: usize,
    pub final_sumcheck_rounds: usize,
    pub final_folding_pow_bits: usize,
}

/// One sumcheck round as sent: `[c0, c_inf]` and, with PoW on, a witness.
#[derive(Clone, Debug)]
pub struct SumcheckRoundData {
    pub poly: [[u32; 4]; 2],
    pub pow_witness: u32,
}

/// One intermediate round's prover messages.
#[derive(Clone, Debug)]
pub struct RoundData {
    /// The Merkle cap, every root's eight elements in order.
    pub root: Vec<u32>,
    pub ood_answers: Vec<[u32; 4]>,
    pub pow_witness: u32,
    /// The round's sumcheck delegate's seed.
    pub seed_sumcheck: Vec<u32>,
    pub sumcheck: Vec<SumcheckRoundData>,
}

/// Everything the transcript absorbs: the sub-transcripts' seeds (constants
/// of the configuration) and the prover's messages.
#[derive(Clone, Debug)]
pub struct TranscriptData {
    pub seed_commitment: Vec<u32>,
    /// One per commitment OOD sample.
    pub seed_virtual: Vec<Vec<u32>>,
    /// One per opening claim.
    pub seed_claim: Vec<Vec<u32>>,
    pub seed_whir: Vec<u32>,
    pub seed_batching: Vec<u32>,
    pub seed_initial_sumcheck: Vec<u32>,
    pub seed_final_sumcheck: Vec<u32>,
    pub root: Vec<u32>,
    pub initial_ood_answers: Vec<[u32; 4]>,
    /// Per opening claim, the evaluations in the order they are absorbed.
    pub openings: Vec<Vec<[u32; 4]>>,
    pub initial_sumcheck: Vec<SumcheckRoundData>,
    pub rounds: Vec<RoundData>,
    pub final_poly: Vec<[u32; 4]>,
    pub final_pow_witness: u32,
    pub final_sumcheck: Vec<SumcheckRoundData>,
}

/// The challenges one intermediate round draws.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoundChallenges {
    pub ood_points: Vec<[u32; 4]>,
    /// In draw order, duplicates kept, as the verifier consumes them.
    pub queries: Vec<u32>,
    pub combination: [u32; 4],
    pub folding: Vec<[u32; 4]>,
}

/// Every challenge the verifier draws, in draw order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Challenges {
    pub initial_ood_points: Vec<[u32; 4]>,
    pub opening_points: Vec<[u32; 4]>,
    pub alpha: [u32; 4],
    pub initial_folding: Vec<[u32; 4]>,
    pub rounds: Vec<RoundChallenges>,
    pub final_queries: Vec<u32>,
    pub final_folding: Vec<[u32; 4]>,
    /// Whether every PoW witness passed.
    pub pow_ok: bool,
}

/// `SumcheckData::verify_rounds`' transcript: absorb, PoW, draw, per round.
fn sumcheck_rounds<S: Sponge>(
    s: &mut S,
    rounds: &[SumcheckRoundData],
    expected: usize,
    pow_bits: usize,
    pow_ok: &mut bool,
) -> Vec<[u32; 4]> {
    assert_eq!(rounds.len(), expected, "sumcheck round count");
    rounds
        .iter()
        .map(|r| {
            s.observe_ef(&r.poly[0]);
            s.observe_ef(&r.poly[1]);
            *pow_ok &= s.check_witness(pow_bits, r.pow_witness);
            s.sample_ef()
        })
        .collect()
}

/// `assemble_query_indices` for a non-stratified domain: `num_queries`
/// uniform `bits`-bit draws in draw order, duplicates kept; every position,
/// with no draw at all, when the domain is no larger than that.
pub fn stir_queries<S: Sponge>(s: &mut S, bits: usize, num_queries: usize) -> Vec<u32> {
    if num_queries >= 1 << bits {
        return (0..1u32 << bits).collect();
    }
    (0..num_queries).map(|_| s.sample_uniform_bits(bits)).collect()
}

/// Drive `s` through the verifier's transcript and collect what it draws.
pub fn transcript<S: Sponge>(cfg: &TranscriptConfig, data: &TranscriptData, s: &mut S) -> Challenges {
    let mut pow_ok = true;
    let observe_all = |s: &mut S, values: &[u32]| {
        for &v in values {
            s.observe(v);
        }
    };

    // 1. The commitment's seed, then the root.
    observe_all(s, &data.seed_commitment);
    observe_all(s, &data.root);

    // 2. Commitment OOD samples, each its own seeded sub-transcript.
    assert_eq!(data.initial_ood_answers.len(), cfg.commitment_ood_samples);
    assert_eq!(data.seed_virtual.len(), data.initial_ood_answers.len(), "one seed per OOD claim");
    let initial_ood_points = data
        .initial_ood_answers
        .iter()
        .zip(&data.seed_virtual)
        .map(|(answer, seed)| {
            observe_all(s, seed);
            let point = s.sample_ef();
            s.observe_ef(answer);
            point
        })
        .collect();

    // 3. Opening claims, likewise.
    assert_eq!(data.seed_claim.len(), data.openings.len(), "one seed per opening claim");
    let opening_points = data
        .openings
        .iter()
        .zip(&data.seed_claim)
        .map(|(evals, seed)| {
            observe_all(s, seed);
            let point = s.sample_ef();
            for e in evals {
                s.observe_ef(e);
            }
            point
        })
        .collect();

    // 4. The WHIR run's seed, then the batching draw's.
    observe_all(s, &data.seed_whir);
    observe_all(s, &data.seed_batching);
    let alpha = s.sample_ef();

    // 5. Initial sumcheck.
    observe_all(s, &data.seed_initial_sumcheck);
    let initial_folding = sumcheck_rounds(
        s,
        &data.initial_sumcheck,
        cfg.initial_folding,
        cfg.initial_folding_pow_bits,
        &mut pow_ok,
    );

    // 6. Intermediate rounds.
    assert_eq!(data.rounds.len(), cfg.rounds.len(), "round count");
    let rounds = cfg
        .rounds
        .iter()
        .zip(&data.rounds)
        .map(|(rc, rd)| {
            for &v in &rd.root {
                s.observe(v);
            }
            assert_eq!(rd.ood_answers.len(), rc.ood_samples);
            let ood_points = rd
                .ood_answers
                .iter()
                .map(|answer| {
                    let point = s.sample_ef();
                    s.observe_ef(answer);
                    point
                })
                .collect();
            pow_ok &= s.check_witness(rc.pow_bits, rd.pow_witness);
            let queries = stir_queries(s, rc.domain_bits, rc.num_queries);
            let combination = s.sample_ef();
            observe_all(s, &rd.seed_sumcheck);
            let folding =
                sumcheck_rounds(s, &rd.sumcheck, rc.folding, rc.folding_pow_bits, &mut pow_ok);
            RoundChallenges { ood_points, queries, combination, folding }
        })
        .collect();

    // 7. Final polynomial, final queries, final sumcheck.
    for e in &data.final_poly {
        s.observe_ef(e);
    }
    pow_ok &= s.check_witness(cfg.final_pow_bits, data.final_pow_witness);
    let final_queries = stir_queries(s, cfg.final_domain_bits, cfg.final_queries);
    observe_all(s, &data.seed_final_sumcheck);
    let final_folding = sumcheck_rounds(
        s,
        &data.final_sumcheck,
        cfg.final_sumcheck_rounds,
        cfg.final_folding_pow_bits,
        &mut pow_ok,
    );

    Challenges {
        initial_ood_points,
        opening_points,
        alpha,
        initial_folding,
        rounds,
        final_queries,
        final_folding,
        pow_ok,
    }
}

// ---------------------------------------------------------------------------
// The WHIR verifier's arithmetic, on top of the transcript.
//
// `WhirVerifier::verify` and the PCS adapter around it, in plain Rust over the
// crate's `u32`/`[u32; 4]` arithmetic. The transcript is run first
// ([`transcript`]); the arithmetic only consumes challenges, never feeds the
// sponge, so the two passes are independent.
//
//   1. Initial constraint. One `Eq` statement per opening claim: each current
//      opening's point is the claim's row point `expand(y, row_vars)` with its
//      column selector's coordinates appended (`PrefixProver` reverses the
//      selectors and lifts them as a suffix). Then one `Eq` statement of
//      the commitment's OOD claims at `expand(y, k)`. Batched by `alpha`:
//      `claim = sum_i alpha^i eval_i` in that order.
//   2. Initial sumcheck: `claim = h(r)` per round.
//   3. Per intermediate round: the previous commitment is opened at the
//      round's queries (Merkle paths from the pruned multi-proof), each row
//      folds to `eval_multilinear(row, previous folding randomness)`, the query
//      index `q` becomes the point `z = g^q`; a new constraint
//      `[Eq(ood), Select(z, folds)]` with challenge `gamma` is combined into
//      the claim -- its powers start at `gamma^1`, the existing claim being
//      the `gamma^0` term (`Constraint::new_with_existing_claim`), which is
//      the paper's `sigma = claim + gamma*y_0 + sum gamma^(j+1) g(z_j)` --
//      then the round's sumcheck runs.
//   4. Final: the last commitment's rows fold likewise and must equal the
//      final polynomial's Horner evaluation at `z`; the final sumcheck runs;
//      with `R` the concatenation of all folding randomness, the weights
//      `w(R) = sum_c sum_i chi_c^i weight_{c,i}(last arity_c coords of R)`
//      and the closing identity `claim == w(R) * eval_multilinear(final, r_fin)`.
//
// `Eq` weights are `eq(point, .)`; `Select` weights are Plonky3's
// `eval_select`, the multilinear extension of `b -> z^b`.
// ---------------------------------------------------------------------------

use crate::pruned::{self, Digest};

/// A claim's shape: the row point's arity and, per current opening, the
/// column selector's hypercube coordinates that prefix it.
#[derive(Clone, Debug)]
pub struct ClaimShape {
    pub row_vars: usize,
    pub selectors: Vec<Vec<[u32; 4]>>,
}

/// One intermediate round's arithmetic parameters.
#[derive(Clone, Debug)]
pub struct RoundMath {
    /// Variables of the folded polynomial this round commits to.
    pub num_variables: usize,
    /// Generator of the folded domain the queries index.
    pub folded_domain_gen: u32,
}

/// Everything the verifier's arithmetic needs beyond the transcript's config.
#[derive(Clone, Debug)]
pub struct VerifyConfig {
    pub transcript: TranscriptConfig,
    /// Variables of the committed (stacked) polynomial.
    pub num_variables: usize,
    pub claims: Vec<ClaimShape>,
    pub rounds: Vec<RoundMath>,
    pub final_folded_domain_gen: u32,
}

/// A commitment opened at the transcript's queries.
#[derive(Clone, Debug)]
pub struct Opening {
    /// Rows hold extension elements, four base coefficients each.
    pub extension: bool,
    /// Per query in ascending index order, the row as the base elements the
    /// leaf hash absorbs.
    pub rows: Vec<Vec<u32>>,
    /// The pruned multi-proof's boundary digests.
    pub boundaries: Vec<Digest>,
}

/// The proof's prover messages, transcript data included.
#[derive(Clone, Debug)]
pub struct VerifyData {
    pub transcript: TranscriptData,
    /// Per intermediate round, the *previous* commitment's opening.
    pub round_openings: Vec<Opening>,
    pub final_opening: Opening,
}

/// Why a proof was rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Pow,
    /// A query's Merkle path did not reach the root. `round` counts the final
    /// opening as one past the last intermediate round.
    Merkle { round: usize, query: usize },
    /// Query count or pruned proof shape did not match the transcript.
    Opening { round: usize },
    /// A final query's fold disagreed with the final polynomial.
    FinalStir { query: usize },
    Closing { claimed: [u32; 4], expected: [u32; 4] },
}

/// What an accepted proof pinned down, for tests that check the parts.
#[derive(Clone, Debug)]
pub struct Verified {
    pub challenges: Challenges,
    /// The claim after every combination and sumcheck round.
    pub claimed: [u32; 4],
    pub weights: [u32; 4],
    pub final_value: [u32; 4],
}

/// One statement's contribution to the weights: its points and how they weigh.
#[derive(Clone, Debug)]
enum Statement {
    Eq(Vec<Vec<[u32; 4]>>),
    Select(Vec<u32>),
}

/// A batched constraint: its challenge, arity and statements in power order,
/// the powers starting at `challenge^initial_power`.
#[derive(Clone, Debug)]
struct Constraint {
    challenge: [u32; 4],
    num_variables: usize,
    initial_power: usize,
    statements: Vec<Statement>,
}

fn lift(x: u32) -> [u32; 4] {
    [x, 0, 0, 0]
}

/// `x^e` over the base field.
pub fn base_pow(x: u32, e: u64) -> u32 {
    let (mut acc, mut base, mut e) = (1u32, x, e);
    while e > 0 {
        if e & 1 == 1 {
            acc = f::mul(acc, base);
        }
        base = f::mul(base, base);
        e >>= 1;
    }
    acc
}

/// Plonky3's `eval_select(var, point)`: the multilinear extension of
/// `b -> var^b`, read highest coordinate first with `var` squared per step.
pub fn select_eval(var: u32, point: &[[u32; 4]]) -> [u32; 4] {
    use poseidon2::reference::ext4;
    let mut var = var;
    let mut acc = EF_ONE;
    for &r in point.iter().rev() {
        let term = ext4::add(ext4::mul(r, lift(f::sub(var, 1))), EF_ONE);
        acc = ext4::mul(acc, term);
        var = f::mul(var, var);
    }
    acc
}

/// `sum_j p_j var^j` with a base-field `var`.
pub fn horner(coeffs: &[[u32; 4]], var: u32) -> [u32; 4] {
    use poseidon2::reference::ext4;
    let var = lift(var);
    coeffs.iter().rev().fold([0u32; 4], |acc, &c| ext4::add(ext4::mul(acc, var), c))
}

/// `sum_i chi^(shift + i) e_i`, added into `claim`.
fn combine_into(claim: &mut [u32; 4], chi: [u32; 4], shift: usize, evals: &[[u32; 4]]) {
    use poseidon2::reference::ext4;
    let mut power = EF_ONE;
    for _ in 0..shift {
        power = ext4::mul(power, chi);
    }
    for &e in evals {
        *claim = ext4::add(*claim, ext4::mul(power, e));
        power = ext4::mul(power, chi);
    }
}

/// The rows of an opening as extension elements, for folding.
fn rows_as_ef(opening: &Opening) -> Vec<Vec<[u32; 4]>> {
    opening
        .rows
        .iter()
        .map(|row| {
            if opening.extension {
                row.chunks(4).map(|c| [c[0], c[1], c[2], c[3]]).collect()
            } else {
                row.iter().map(|&x| lift(x)).collect()
            }
        })
        .collect()
}

/// Every query's Merkle path of `opening` must reach `root`.
fn check_opening(
    opening: &Opening,
    root: &[u32],
    indices: &[u32],
    depth: usize,
    round: usize,
) -> Result<(), VerifyError> {
    if opening.rows.len() != indices.len() || root.len() != 8 {
        return Err(VerifyError::Opening { round });
    }
    let root: Digest = root.try_into().expect("checked above");
    let leaves: Vec<Digest> = opening.rows.iter().map(|r| poseidon2::reference::hash_row(r)).collect();
    let indices: Vec<usize> = indices.iter().map(|&i| i as usize).collect();
    let paths = pruned::expand(&opening.boundaries, &indices, &leaves, depth)
        .map_err(|_| VerifyError::Opening { round })?;
    for (query, path) in paths.iter().enumerate() {
        let bits: Vec<bool> = (0..depth).map(|i| (path.index >> i) & 1 == 1).collect();
        if poseidon2::reference::merkle_root(path.leaf, &path.siblings, &bits) != root {
            return Err(VerifyError::Merkle { round, query });
        }
    }
    Ok(())
}

/// Fold each opened row at the folding randomness, and the query points.
fn folds_and_points(
    opening: &Opening,
    folding_randomness: &[[u32; 4]],
    queries: &[u32],
    gen: u32,
) -> (Vec<[u32; 4]>, Vec<u32>) {
    let folds = rows_as_ef(opening)
        .iter()
        .map(|row| eval_multilinear(row, folding_randomness))
        .collect();
    let points = queries.iter().map(|&q| base_pow(gen, u64::from(q))).collect();
    (folds, points)
}

/// The batched weights at `randomness`: `eval_constraints_poly`, prefix order.
fn weights(constraints: &[Constraint], randomness: &[[u32; 4]]) -> [u32; 4] {
    use poseidon2::reference::ext4;
    let mut total = [0u32; 4];
    for c in constraints {
        assert!(c.num_variables <= randomness.len());
        let local = &randomness[randomness.len() - c.num_variables..];
        let mut shift = c.initial_power;
        for s in &c.statements {
            let ws: Vec<[u32; 4]> = match s {
                Statement::Eq(points) => points.iter().map(|p| eq_eval(p, local)).collect(),
                Statement::Select(vars) => vars.iter().map(|&v| select_eval(v, local)).collect(),
            };
            let mut acc = [0u32; 4];
            combine_into(&mut acc, c.challenge, shift, &ws);
            total = ext4::add(total, acc);
            shift += ws.len();
        }
    }
    total
}

/// Run the verifier: the transcript, then the arithmetic.
pub fn verify(cfg: &VerifyConfig, data: &VerifyData) -> Result<Verified, VerifyError> {
    let t = &cfg.transcript;
    let ch = transcript(t, &data.transcript, &mut Challenger::new());
    if !ch.pow_ok {
        return Err(VerifyError::Pow);
    }

    // 1. The initial constraint and claim.
    let mut statements = Vec::new();
    let mut evals = Vec::new();
    assert_eq!(cfg.claims.len(), data.transcript.openings.len(), "claim count");
    for ((shape, point), opening_evals) in
        cfg.claims.iter().zip(&ch.opening_points).zip(&data.transcript.openings)
    {
        assert_eq!(shape.selectors.len(), opening_evals.len(), "openings per claim");
        let row = expand_univariate(*point, shape.row_vars);
        // `PrefixProver` reverses its selectors and lifts them as a *suffix*
        // (`LayoutStrategy::new(true, Prefix)`): the row point comes first.
        let points = shape
            .selectors
            .iter()
            .map(|sel| row.iter().copied().chain(sel.iter().copied()).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for p in &points {
            assert_eq!(p.len(), cfg.num_variables, "lifted claim point arity");
        }
        statements.push(Statement::Eq(points));
        evals.push(opening_evals.clone());
    }
    let ood_points: Vec<Vec<[u32; 4]>> = ch
        .initial_ood_points
        .iter()
        .map(|&y| expand_univariate(y, cfg.num_variables))
        .collect();
    if !ood_points.is_empty() {
        statements.push(Statement::Eq(ood_points));
        evals.push(data.transcript.initial_ood_answers.clone());
    }
    let mut claimed = [0u32; 4];
    let mut shift = 0;
    for group in &evals {
        combine_into(&mut claimed, ch.alpha, shift, group);
        shift += group.len();
    }
    let mut constraints = vec![Constraint {
        challenge: ch.alpha,
        num_variables: cfg.num_variables,
        initial_power: 0,
        statements,
    }];

    // 2. The initial sumcheck.
    for (round, &r) in data.transcript.initial_sumcheck.iter().zip(&ch.initial_folding) {
        claimed = sumcheck_round(claimed, round.poly[0], round.poly[1], r);
    }
    let mut randomness: Vec<[u32; 4]> = ch.initial_folding.clone();
    let mut prev_root: &[u32] = &data.transcript.root;
    let mut prev_folding: Vec<[u32; 4]> = ch.initial_folding.clone();

    // 3. Intermediate rounds.
    assert_eq!(cfg.rounds.len(), t.rounds.len());
    assert_eq!(data.round_openings.len(), t.rounds.len());
    for (i, ((rm, rt), rc)) in cfg.rounds.iter().zip(&t.rounds).zip(&ch.rounds).enumerate() {
        let opening = &data.round_openings[i];
        check_opening(opening, prev_root, &rc.queries, rt.domain_bits, i)?;
        let (folds, points) =
            folds_and_points(opening, &prev_folding, &rc.queries, rm.folded_domain_gen);
        let ood: Vec<Vec<[u32; 4]>> =
            rc.ood_points.iter().map(|&y| expand_univariate(y, rm.num_variables)).collect();
        let rd = &data.transcript.rounds[i];
        combine_into(&mut claimed, rc.combination, 1, &rd.ood_answers);
        combine_into(&mut claimed, rc.combination, 1 + rd.ood_answers.len(), &folds);
        constraints.push(Constraint {
            challenge: rc.combination,
            num_variables: rm.num_variables,
            initial_power: 1,
            statements: vec![Statement::Eq(ood), Statement::Select(points)],
        });
        for (round, &r) in rd.sumcheck.iter().zip(&rc.folding) {
            claimed = sumcheck_round(claimed, round.poly[0], round.poly[1], r);
        }
        randomness.extend_from_slice(&rc.folding);
        prev_root = &rd.root;
        prev_folding = rc.folding.clone();
    }

    // 4. The final polynomial, queries, sumcheck and closing identity.
    let final_round = t.rounds.len();
    check_opening(&data.final_opening, prev_root, &ch.final_queries, t.final_domain_bits, final_round)?;
    let (folds, points) = folds_and_points(
        &data.final_opening,
        &prev_folding,
        &ch.final_queries,
        cfg.final_folded_domain_gen,
    );
    for (query, (&fold, &z)) in folds.iter().zip(&points).enumerate() {
        if horner(&data.transcript.final_poly, z) != fold {
            return Err(VerifyError::FinalStir { query });
        }
    }
    for (round, &r) in data.transcript.final_sumcheck.iter().zip(&ch.final_folding) {
        claimed = sumcheck_round(claimed, round.poly[0], round.poly[1], r);
    }
    randomness.extend_from_slice(&ch.final_folding);
    let weights = weights(&constraints, &randomness);
    let final_value = eval_multilinear(&data.transcript.final_poly, &ch.final_folding);
    let expected = poseidon2::reference::ext4::mul(weights, final_value);
    if claimed != expected {
        return Err(VerifyError::Closing { claimed, expected });
    }
    Ok(Verified { challenges: ch, claimed, weights, final_value })
}
