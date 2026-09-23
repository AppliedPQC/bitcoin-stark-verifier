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
