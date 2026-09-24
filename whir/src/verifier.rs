//! The WHIR verifier, composed.
//!
//! Follows `WhirVerifier::verify` in Plonky3's `whir/src/pcs/verifier/mod.rs`:
//!
//! ```text
//! initial sumcheck rounds                     (folding factor of round 0)
//! for each round:
//!     absorb the round commitment and OOD answers
//!     sample query indices, open Merkle paths, fold each answer
//!     sample the constraint challenge, combine
//!     sumcheck rounds                         (folding factor of round i+1)
//! observe the final polynomial in the clear
//! open the final round's queries
//! final sumcheck rounds
//! check  claimed_eval == weights * f(final_randomness)
//! ```
//!
//! Every step below is one of the primitives this crate already checks against
//! Plonky3. What this module adds is the schedule: how many permutations a
//! given [`Config`] actually costs, which is the number that decides whether a
//! WHIR verifier fits on Bitcoin.

use crate::sponge::RATE;
use crate::treepp::*;
use crate::{challenger, constraint, sponge, sumcheck};
use poseidon2::ext4;
use poseidon2::field;
use poseidon2::merkle;

/// One round of the WHIR schedule.
#[derive(Clone, Debug)]
pub struct Round {
    /// Sumcheck rounds this round runs, i.e. the next folding factor.
    pub folding_factor: usize,
    /// In-domain queries opened against the previous commitment.
    pub num_queries: usize,
    /// Merkle depth of the codeword being opened.
    pub log_domain_size: usize,
    /// Out-of-domain samples absorbed with the commitment.
    pub ood_samples: usize,
    /// Field elements in one opened row — the `2^folding_factor` values of the
    /// fibre a shift query reads, which is what a Merkle leaf commits to.
    pub row_len: usize,
    /// Generator of the folded evaluation domain. A shift query's constraint
    /// point is the square-power expansion of `domain_gen^index`, so the
    /// verifier needs the generator to turn a sampled index into a point.
    pub domain_gen: u32,
}

/// A WHIR instance, mirroring the fields of `WhirConfig` this verifier reads.
#[derive(Clone, Debug)]
pub struct Config {
    /// Sumcheck rounds before the first folding round.
    pub initial_folding_factor: usize,
    /// Out-of-domain samples taken with the *initial* commitment, in the commit
    /// phase before the protocol proper.
    pub initial_ood_samples: usize,
    pub rounds: Vec<Round>,
    /// The final round's queries.
    pub final_round: Round,
    /// Sumcheck rounds after the last folding round.
    pub final_sumcheck_rounds: usize,
    /// Variables of the final polynomial sent in the clear.
    pub final_poly_vars: usize,
}

impl Config {
    /// Coordinates of folding randomness the whole schedule produces: one per
    /// sumcheck round, which is what [`sumcheck::sumcheck_rounds_fs_keep`]
    /// leaves on the stack.
    pub fn total_folding_vars(&self) -> usize {
        self.initial_folding_factor
            + self.rounds.iter().map(|r| r.folding_factor).sum::<usize>()
            + self.final_sumcheck_rounds
    }

    /// Coordinates accumulated by the time the final polynomial is absorbed —
    /// everything except the final sumcheck rounds, which come after it.
    pub fn randomness_before_final(&self) -> usize {
        self.total_folding_vars() - self.final_sumcheck_rounds
    }
}

/// Absorb `n` field elements taken from the altstack, splitting across
/// rate-sized blocks as the duplex does. Each block is one permutation.
///
/// The values come from the altstack because a script's witness is its initial
/// stack: everything the spender supplies is present from the first opcode, and
/// only the altstack lets the verifier consume it in transcript order without
/// burying the sponge state.
///
/// No trailing squeeze. Absorbing already permutes, which is exactly what
/// Plonky3's `DuplexChallenger` does — `observe` buffers, and the `sample` that
/// follows duplexes once. The previous version emitted `absorb` *and* `squeeze`,
/// paying two permutations per round for one round's worth of transcript.
fn absorb_n_from_altstack(n: usize) -> Script {
    // The block sizes are known at generation time, so build them here rather
    // than trying to bind a local inside `script!`.
    let blocks: Vec<Script> = (0..n.div_ceil(RATE))
        .map(|chunk| {
            let block = core::cmp::min(RATE, n - chunk * RATE);
            script! {
                for _ in 0..block { OP_FROMALTSTACK }
                { sponge::absorb(block) }
            }
        })
        .collect();
    script! { for b in blocks { { b } } }
}

/// Absorb `n` elements from the altstack, keeping a copy beneath the randomness.
///
/// The final polynomial is the one transcript item the verifier needs *twice*:
/// once absorbed, so the challenges depend on it, and once evaluated, because
/// the closing identity is `claimed == w(R) * f_M(r_fin)`. Supplying it twice in
/// the witness would be the cheaper-looking option and a hole — the two copies
/// could differ, so the transcript would commit to one polynomial while the
/// check used another. The copy is therefore made in script.
///
/// `r_len` is how many extension elements of folding randomness are already
/// accumulated. The copy is buried *below* them rather than directly under the
/// claim, which is what keeps `R` contiguous: a later sumcheck round buries its
/// challenge directly under the claim, and if the polynomial sat there too it
/// would land in the middle of the randomness and `constraint_eval` could no
/// longer read a suffix.
///
/// # Stack
///
/// In: `F(prev) R(4*r_len) claim(4) state(16)`, the values on the altstack.
/// Out: `F(prev) F(new) R(4*r_len) claim(4) state'(16)`.
///
/// # Cost
///
/// Unchanged: one permutation per rate block. The burial and the copy are rolls
/// and picks at a constant depth — around three bytes a slot against 572 228 for
/// the block's permutation.
fn absorb_n_from_altstack_keep(n: usize, r_len: usize) -> Script {
    // Everything that has to end up above the buried block: the randomness, the
    // claim and the sponge state.
    let region = ext4::D * r_len + ext4::D + sponge::WIDTH;
    let blocks: Vec<Script> = (0..n.div_ceil(RATE))
        .map(|chunk| {
            let b = core::cmp::min(RATE, n - chunk * RATE);
            // The deepest slot of the region while the block sits above it, and
            // — the same number — the deepest slot of the block once the region
            // is back above it. Both stay constant as their loop runs, because
            // each step removes one item from below and adds one above.
            let depth = b + region - 1;
            script! {
                for _ in 0..b { OP_FROMALTSTACK }
                // Sink the block beneath the randomness.
                for _ in 0..region { { depth } OP_ROLL }
                // Copy it back up to be absorbed.
                for _ in 0..b { { depth } OP_PICK }
                { sponge::absorb(b) }
            }
        })
        .collect();
    script! { for b in blocks { { b } } }
}

/// Open one query: derive its index from the transcript, then authenticate the
/// opening against the committed root.
///
/// The query index *is* the path. Sampling it and feeding those bits to the walk
/// is what binds the opening: the spender picks neither which leaf is opened nor
/// where it sits.
///
/// `slot` selects which rate element the index is read from. One squeeze yields
/// `RATE` of them and the caller must re-squeeze once they are spent — see
/// [`queries_per_squeeze`]. The first version hardcoded slot 0, and since
/// [`challenger::sample`] is a bare `OP_PICK` that neither permutes nor advances
/// any buffer, every query in a round derived the *same* index and opened the
/// *same* leaf. However many queries were configured, the soundness was that of
/// one.
///
/// The opening is one unit: the **row** goes in, the root is checked, and no
/// leaf digest is taken on trust in between. [`merkle::hash_row`] reproduces the
/// `PaddingFreeSponge` the commitment was built with, so the walk authenticates
/// the values themselves.
///
/// That matters because the two halves of a query are separable and only one of
/// them used to be checked. Walking the path proves that *some* committed leaf
/// sits at the sampled index; if the leaf arrives as a hint alongside the row,
/// nothing stops a spender authenticating the real leaf and folding a different
/// row into the constraint. Hashing in script removes the seam.
///
/// # The root is not the spender's to supply
///
/// The first version took the root from the witness alongside the siblings, so
/// a spender could commit to one tree and open a path in another: any root with
/// any consistent path would pass, and the round's commitment — the thing the
/// transcript absorbed — was never compared against. The root is now copied
/// from that absorbed commitment, kept on the stack for the round by
/// [`absorb_n_from_altstack_keep`], which is the third time in this crate a
/// value has turned out to be absorbed and then not retained.
///
/// # Stack
///
/// In: `... commit(8) claim(4) state(16)`, the sponge on top as everywhere else
/// and the round's commitment beneath the claim.
/// Altstack: the opening, in pop order — the siblings deepest last, then the
/// row. No root: it comes from the commitment.
/// Out: unchanged. The spend is invalid unless the walk reaches that root.
///
/// # Why the opening comes from the altstack, and in that order
///
/// The first version took the opening from the main stack and sampled the index
/// with [`challenger::sample`], which picks within the top sixteen slots. With
/// an opening on top of the state those picks land in the row, so the contract
/// could not hold — and nothing caught it, because the builder had no test that
/// executed it. It is the same shape as the defect that made `verify` a cost
/// model: a script that is measured but never run.
///
/// The order is forced. The direction bits go on the altstack, so the opening
/// has to come off it first or the bits would be popped in the opening's place;
/// and the index has to be sampled with the opening already above the state,
/// which is what [`challenger::sample_at`] is for.
pub fn open_query(
    slot: usize,
    log_domain_size: usize,
    row_len: usize,
    commit_depth: usize,
) -> Script {
    let witness = merkle::DIGEST * log_domain_size + row_len;
    let opening = merkle::DIGEST + witness;
    script! {
        // The root the walk has to reach, taken from the commitment rather than
        // from the spender, and placed where `merkle_verify` expects it.
        for _ in 0..merkle::DIGEST { { commit_depth } OP_PICK }
        for _ in 0..witness { OP_FROMALTSTACK }
        { challenger::sample_at(slot, opening) }
        { field::low_bits_to_altstack(log_domain_size) }
        { merkle::hash_row(row_len) }
        { merkle::merkle_verify_from_altstack(log_domain_size) }
    }
}

/// Every query of one round, with the re-squeezes its indices need.
///
/// A squeeze yields [`queries_per_squeeze`] rate slots, so a round with more
/// queries than that has to permute again part-way through. That cost is real —
/// it is in [`permutation_count`] — and it is the only thing in the schedule
/// whose permutation count is not one per absorb.
///
/// # Stack
///
/// In and out: `... commit(8) claim(4) state(16)`. Altstack: the openings back
/// to back, in query order.
fn open_round_queries(r: &Round, commit_depth: usize) -> Script {
    let queries: Vec<Script> = (0..r.num_queries)
        .map(|q| {
            let slot = q % queries_per_squeeze();
            script! {
                // A fresh squeeze once the previous batch of slots is spent.
                if q > 0 && slot == 0 { { sponge::squeeze() } }
                { open_query(slot, r.log_domain_size, r.row_len, commit_depth) }
            }
        })
        .collect();
    script! { for q in queries { { q } } }
}

/// Sink the top `n` slots to just below the folding randomness.
///
/// The same manoeuvre [`absorb_n_from_altstack_keep`] performs, for a value that
/// is already on the stack rather than arriving from the altstack: lift the
/// randomness, the claim and the sponge over it, deepest slot first, at a depth
/// that stays constant because each roll removes one item from below and adds
/// one above.
///
/// Anything buried earlier stays beneath, so the carried region grows in the
/// order the transcript produces it — which is the order the closing check
/// wants to read it back in.
fn sink_below_randomness(n: usize, r_len: usize) -> Script {
    let region = ext4::D * r_len + ext4::D + sponge::WIDTH;
    let depth = n + region - 1;
    script! { for _ in 0..region { { depth } OP_ROLL } }
}

/// A shift query's constraint scalar: `domain_gen^index`, as an `EF` element.
///
/// The index is re-sampled rather than kept from [`open_query`], which is free:
/// [`challenger::sample`] is a pick, so reading the same rate slot again gives
/// the same value, and the sponge has not moved in between. Keeping it instead
/// would mean carrying it past a Merkle walk that uses the altstack.
///
/// `pow_const_base` squares the generator at build time, so the exponentiation
/// costs one multiply-by-constant per bit of the index and no permutation.
fn shift_scalar(slot: usize, log_domain_size: usize, domain_gen: u32) -> Script {
    script! {
        { challenger::sample(slot) }
        { field::pow_const_base(domain_gen, log_domain_size) }
        // Embed in the extension: coefficient zero is the base element, and the
        // rest are zero, with `a0` deepest as everywhere else.
        0 0 0
    }
}

/// Depth of a commitment's deepest slot, given what is stacked above it.
///
/// A commitment is buried *below* the folding randomness rather than under the
/// claim, and this is not a matter of taste: a sumcheck round buries its
/// challenge directly under the claim, so a commitment parked there would land
/// inside `R` and stop [`crate::constraint::constraint_eval`] reading a suffix.
/// Below `R` it survives the round's sumcheck rounds untouched, which is what a
/// commitment has to do — its queries are opened after them.
const fn commitment_depth(r_len: usize, above: usize) -> usize {
    sponge::WIDTH + ext4::D + ext4::D * r_len + above + merkle::DIGEST - 1
}

/// Drop the round's commitment from under the claim and the sponge.
///
/// Rolled up one slot at a time rather than parked on the altstack: the altstack
/// holds the rest of the transcript, and anything pushed there would be popped
/// in its place.
fn drop_commitment(depth: usize) -> Script {
    script! { for j in 0..merkle::DIGEST { { depth - j } OP_ROLL OP_DROP } }
}

/// Query indices available from one squeeze.
///
/// Each index is masked out of a single base element, so the rate yields `RATE`
/// of them before the sponge has to be permuted again.
pub const fn queries_per_squeeze() -> usize {
    RATE
}

/// The final consistency check: `claimed_eval == weight * f(r)`, over `EF`.
///
/// Input, bottom to top: `claimed_eval(4) weight(4) f_at_r(4)`. Leaves nothing;
/// the spend is invalid unless the identity holds in all four coefficients.
///
/// This is the linear `Z * eq(X, z)` case of WHIR's closing condition
/// `sum_b w(f_M(b), alpha, b) = h_M(alpha)`, which is the shape a multilinear
/// evaluation query takes.
///
/// It has to be an extension-field comparison. Checking one coefficient would
/// leave a base-field equality worth at most `log2(P) ~ 31` bits — a prover
/// could hit it by chance far too often — against the ~124 bits the quartic
/// extension exists to provide.
pub fn final_check() -> Script {
    script! {
        { ext4::mul() }
        // Product on top, claimed value beneath it. Each comparison removes two
        // items, so the claimed value rises by one and the roll depth shrinks
        // with it — the same pattern `merkle_verify` uses for roots.
        for i in 0..ext4::D {
            { ext4::D - i } OP_ROLL
            OP_EQUALVERIFY
        }
    }
}

/// Emit the transcript spine of the verifier for `cfg`.
///
/// Every opcode this emits is wired and executable: the sumcheck chains derive
/// their own challenges through [`sumcheck::sumcheck_rounds_fs`], and the round
/// commitments, out-of-domain answers and final polynomial are absorbed into the
/// same sponge, so the challenges are a function of the proof rather than of the
/// spender's choosing. `whir/tests/verifier.rs` runs the result.
///
/// # Stack
///
/// In: `claim(4) state(16)` on the main stack, with the transcript on the
/// altstack in consumption order — for each sumcheck round `c_inf` then `c0`,
/// and each absorbed block in the order it is read.
/// Out: `R(4m) claim(4) state(16)`, where `R` is every round's folding
/// randomness concatenated in round order — the point the accumulated
/// constraints are evaluated at.
///
/// # What this does not cover
///
/// Two links remain outside the script, and neither is a matter of wiring:
///
/// - **The query openings are not composed into the schedule.** [`open_query`]
///   authenticates one, and [`permutation_count`] prices them all, but the
///   spine does not yet emit them. That is what still stands between this and a
///   verifier: the openings are where the constraints other than the statement
///   come from, and the batching challenge `gamma` that weights them is sampled
///   from the transcript position they occupy. Until they are in the spine there
///   is no `gamma` in it to derive those weights from, which is why [`close`]
///   takes its constraint list rather than building it.
///
/// So this is the part of the verifier that is *checked*, not the whole
/// verifier. [`permutation_count`] prices the whole schedule including queries;
/// the two numbers are deliberately different and the doc comment on each says
/// which it is.
pub fn verify(cfg: &Config) -> Script {
    let m = cfg.total_folding_vars();
    // The carried region below the randomness, bottom to top, in slots. New
    // burials go on top of it, so it ends up in transcript order -- which is the
    // order `constraint_eval_batched` reads its groups back in.
    let mut below: Vec<usize> = Vec::new();
    let mut r_len = 0usize;
    let mut out: Vec<Script> = Vec::new();

    // Depth of the deepest slot of segment `i`, from the top of the stack.
    let depth_of = |below: &[usize], i: usize, r_len: usize| -> usize {
        let above: usize = below[i + 1..].iter().sum();
        sponge::WIDTH + ext4::D + ext4::D * r_len + above + below[i] - 1
    };

    // --- commit phase: the initial codeword, and its out-of-domain samples ---
    out.push(script! { { absorb_n_from_altstack_keep(merkle::DIGEST, r_len) } });
    below.push(merkle::DIGEST);
    let commit_init = below.len() - 1;
    for _ in 0..cfg.initial_ood_samples {
        out.push(script! {
            { challenger::sample_ef(0) }
            { sink_below_randomness(ext4::D, r_len) }
            { absorb_n_from_altstack(ext4::D) }
        });
        below.push(ext4::D);
    }
    // The group's batching challenge. A fresh squeeze rather than a leftover
    // rate slot: which slots the queries have spent is known here, but relying
    // on that would couple the challenge's position to the query count for the
    // sake of one permutation in the whole schedule.
    out.push(script! {
        { sponge::squeeze() }
        { challenger::sample_ef(0) }
        { sink_below_randomness(ext4::D, r_len) }
    });
    below.push(ext4::D);
    out.push(script! { { sumcheck::sumcheck_rounds_fs_keep(cfg.initial_folding_factor) } });
    r_len += cfg.initial_folding_factor;

    // --- rounds ----------------------------------------------------------
    let mut opened = commit_init;
    for r in cfg.rounds.iter() {
        // A constraint born here is over the new commitment's variables, and the
        // randomness that binds them is everything from this round onwards --
        // the last `m - r_len` coordinates of `R`.
        let arity = m - r_len;
        out.push(script! { { absorb_n_from_altstack_keep(merkle::DIGEST, r_len) } });
        below.push(merkle::DIGEST);
        let this_commit = below.len() - 1;

        for _ in 0..r.ood_samples {
            out.push(script! {
                { challenger::sample_ef(0) }
                { sink_below_randomness(ext4::D, r_len) }
                { absorb_n_from_altstack(ext4::D) }
            });
            below.push(ext4::D);
        }
        for q in 0..r.num_queries {
            let slot = q % queries_per_squeeze();
            let d = depth_of(&below, opened, r_len);
            out.push(script! {
                if q > 0 && slot == 0 { { sponge::squeeze() } }
                { open_query(slot, r.log_domain_size, r.row_len, d) }
                { shift_scalar(slot, r.log_domain_size, r.domain_gen) }
                { sink_below_randomness(ext4::D, r_len) }
            });
            below.push(ext4::D);
        }
        out.push(script! {
            { sponge::squeeze() }
            { challenger::sample_ef(0) }
            { sink_below_randomness(ext4::D, r_len) }
        });
        below.push(ext4::D);
        let _ = arity; // recorded by `constraint_groups`, which close() reads

        // The opened commitment has done its work. Dropping it from the middle
        // of the carried region shifts everything above it up, which is why the
        // model is kept rather than the depths hard-coded.
        let d = depth_of(&below, opened, r_len);
        out.push(script! { { drop_commitment(d) } });
        below.remove(opened);
        let this_commit = if this_commit > opened { this_commit - 1 } else { this_commit };
        opened = this_commit;

        out.push(script! { { sumcheck::sumcheck_rounds_fs_keep(r.folding_factor) } });
        r_len += r.folding_factor;
    }

    // --- the final polynomial, the final queries, the final sumcheck ------
    out.push(script! {
        { absorb_n_from_altstack_keep(ext4::D << cfg.final_poly_vars, r_len) }
    });
    below.push(ext4::D << cfg.final_poly_vars);

    // The final proximity test checks its answers against the final polynomial
    // directly rather than accumulating a constraint -- Plonky3's
    // `stir_statement.verify(final_evaluations)` -- so these queries carry
    // nothing, and the polynomial stays the topmost carried segment.
    for q in 0..cfg.final_round.num_queries {
        let slot = q % queries_per_squeeze();
        let d = depth_of(&below, opened, r_len);
        out.push(script! {
            if q > 0 && slot == 0 { { sponge::squeeze() } }
            { open_query(slot, cfg.final_round.log_domain_size, cfg.final_round.row_len, d) }
        });
    }
    let d = depth_of(&below, opened, r_len);
    out.push(script! { { drop_commitment(d) } });
    below.remove(opened);

    out.push(script! { { sumcheck::sumcheck_rounds_fs_keep(cfg.final_sumcheck_rounds) } });

    script! { for b in out { { b } } }
}

/// The constraint groups [`verify`] accumulates: `(constraints, arity)` per
/// group, in the order the closing check reads them.
///
/// One group for the commit phase and one per round, each holding that
/// commitment's out-of-domain samples, that round's shift queries and the
/// batching challenge that weights them. A group's arity is the commitment's
/// variable count, which is `m` minus the randomness accumulated before it —
/// so it reads exactly the suffix of `R` drawn from that point onwards.
pub fn constraint_groups(cfg: &Config) -> Vec<(usize, usize)> {
    let m = cfg.total_folding_vars();
    let mut groups = vec![(cfg.initial_ood_samples, m)];
    let mut r_len = cfg.initial_folding_factor;
    for r in cfg.rounds.iter() {
        groups.push((r.ood_samples + r.num_queries, m - r_len));
        r_len += r.folding_factor;
    }
    groups
}

/// Extension elements the schedule carries down to the closing check.
///
/// One per constraint, plus one batching challenge per group — the challenge is
/// carried alongside the scalars but is not itself a constraint, which is an
/// easy off-by-one and was one.
pub fn carried_scalars(cfg: &Config) -> usize {
    constraint_groups(cfg).iter().map(|&(n, _)| n + 1).sum()
}

/// The closing identity, on the stack [`verify`] leaves.
///
/// ```text
/// claimed_eval == w(R) * f_M(r_fin)
/// ```
///
/// This is where the transcript stops being a transcript and becomes a check.
/// Everything it multiplies together is derived: `R` is accumulated by the
/// sumcheck rounds, `f_M` is the copy [`absorb_n_from_altstack_keep`] kept of
/// the polynomial that was absorbed, and `r_fin` is the tail of `R`.
///
/// # Stack
///
/// In: `F(4*2^v) R(4m) claim(4) state(16)` — exactly [`verify`]'s output.
/// Altstack: the constraint list, laid out as [`constraint::constraint_eval`]
/// expects. It has to be pushed *first* by the spender, beneath the whole
/// transcript, so that it is what remains once the transcript is consumed.
///
/// # What the constraint list may contain
///
/// For a plain evaluation opening the list is a single entry of weight one --
/// the statement `f(z) = sigma` itself, whose point is public and whose weight
/// needs no batching challenge. That case is complete: nothing in the identity
/// is the spender's to choose.
///
/// The out-of-domain and shift constraints are weighted by powers of a `gamma`
/// sampled after each round's answers are absorbed. Those weights must be
/// derived in script for the same reason the sumcheck challenges must be, and
/// they cannot be until [`verify`] composes the query openings that fix where
/// `gamma` sits in the transcript. Passing them in here would be the same defect
/// as supplying a sumcheck challenge.
/// Out: nothing. The spend is invalid unless the identity holds in all four
/// coefficients.
///
/// # Why the sponge is simply dropped
///
/// Its work is done: every challenge has been squeezed out of it, and each one
/// is already baked into `R` and into the chained claim. Nothing downstream
/// reads it, and keeping it would only mean carrying sixteen slots through the
/// closing arithmetic.
///
/// # Cost
///
/// No permutation at all. One multilinear evaluation of `v` variables, one
/// `eq` per constraint, and rolls. The closing identity is arithmetic, and at
/// this resolution arithmetic is free — which is worth stating plainly, because
/// it means the reason a WHIR verifier does not fit on Bitcoin is entirely the
/// Merkle openings and not the algebra.
pub fn close(cfg: &Config, statement: &[(usize, usize)]) -> Script {
    // In Plonky3 these are the same quantity: the final polynomial has one
    // variable per final sumcheck round, and is evaluated at that round's
    // randomness. Splitting them into two fields is this crate's own doing, so
    // the closing check is where the two have to be reconciled.
    assert_eq!(
        cfg.final_poly_vars, cfg.final_sumcheck_rounds,
        "the final polynomial is evaluated at the final sumcheck randomness, so it has one \
         variable per final sumcheck round"
    );
    let v = cfg.final_sumcheck_rounds;
    let m = cfg.total_folding_vars();
    let n_evals = 1usize << cfg.final_poly_vars;
    let groups = constraint_groups(cfg);
    let carried = carried_scalars(cfg);
    // The stack below the sponge, bottom to top: the carried scalars, the final
    // polynomial, the randomness, the claim.
    let lift_poly = ext4::D * n_evals + ext4::D * m + ext4::D - 1;
    // Once the polynomial has been lifted out and collapsed to one value, the
    // scalars sit under the randomness, the claim and that value.
    let lift_scalars = ext4::D * carried + ext4::D * m + 2 * ext4::D - 1;
    script! {
        // The sponge has nothing left to say.
        for _ in 0..sponge::WIDTH { OP_DROP }

        // Bring the final polynomial up over `R` and the claim.
        for _ in 0..(ext4::D * n_evals) { { lift_poly } OP_ROLL }

        // The point it is evaluated at is the *final* sumcheck randomness, the
        // tail of `R`. `eval_multilinear` pops the last variable first, and the
        // altstack is last-in-first-out, so the last variable has to be pushed
        // *last* -- the copy runs from the deepest coordinate upwards, not from
        // the top down. The `+ 1` steps over the claim, which the lift left
        // between the polynomial and the randomness.
        for i in (0..v).rev() { { ext4::copy(n_evals + 1 + i) } { ext4::to_altstack() } }
        { crate::multilinear::eval_multilinear(cfg.final_poly_vars) }

        // The statement's own constraint, first, because it reads the
        // randomness without consuming it and the batched evaluation does not.
        // Its point is public: it *is* the statement, and a different point is a
        // different claim, so the spender supplying it is not a choice. Its
        // pairs are the only thing on the altstack until the scalars join them,
        // which is why this has to run before they do.
        for st in statement.iter() {
            { constraint::weights_at_under(st.0, st.1, 2) }
        }
        for _ in 0..statement.len() { { ext4::to_altstack() } }

        // Bring the carried scalars up, then hand them to the altstack. Rolling
        // deepest-first preserves their order; moving top-first reverses it
        // again, so what pops is the order they were sampled in.
        for _ in 0..(ext4::D * carried) { { lift_scalars } OP_ROLL }
        for _ in 0..carried { { ext4::to_altstack() } }

        // w(R) from everything the transcript produced. The claim and
        // f_M(r_fin) sit above the randomness and are both still needed, so
        // they are stepped over rather than parked.
        { constraint::constraint_eval_batched_at(m, &groups, 2) }
        for _ in 0..statement.len() {
            { ext4::from_altstack() }
            { ext4::add() }
        }

        // final_check wants `claimed weight f_at_r`; lift the value over the
        // weight, deepest slot first.
        for _ in 0..ext4::D { { 2 * ext4::D - 1 } OP_ROLL }
        { final_check() }
    }
}

/// [`verify`] followed by [`close`]: the whole transcript and the identity it
/// exists to reach.
pub fn verify_and_close(cfg: &Config, statement: &[(usize, usize)]) -> Script {
    script! {
        { verify(cfg) }
        { close(cfg, statement) }
    }
}

/// Count the permutations `cfg` costs, including the query openings that
/// [`verify`] does not yet compose.
///
/// Script weight is very nearly this number times the permutation size, because
/// nothing else is within 1% of one.
///
/// Corrections against the original accounting, in both directions:
///
/// - a sumcheck round is **one** permutation, not two — the absorb *is* the
///   duplexing, and the extra squeeze was never needed;
/// - a round absorbs two *extension* elements, so eight base elements, which
///   still fits one rate block;
/// - query indices are drawn `RATE` at a time, so a round with more queries than
///   that has to re-squeeze;
/// - each constraint group ends with a squeeze for its batching challenge,
///   rather than reading a rate slot the query indices happen to have left --
///   one permutation per round, traded for not coupling the challenge's position
///   to the query count;
/// - out-of-domain answers and the final polynomial are **extension** elements.
///   Counting them as base elements under-absorbed by a factor of four, and the
///   out-of-domain points are sampled one at a time between the answers rather
///   than once after them, which is one duplexing per sample and not one per
///   rate block.
pub fn permutation_count(cfg: &Config) -> usize {
    // Absorb-and-sample is a single duplexing.
    let sumcheck_perms = |rounds: usize| rounds;
    // Indices come `RATE` per squeeze; the first batch rides the preceding
    // absorb, so only the batches after it cost a permutation.
    let index_squeezes = |queries: usize| queries.div_ceil(queries_per_squeeze()).saturating_sub(1);
    // A leaf hash is the row absorbed `HASH_RATE` at a time -- the same
    // `PaddingFreeSponge` the commitment was built with.
    let leaf_hash = |row_len: usize| row_len.div_ceil(merkle::HASH_RATE);

    // The commit phase: the initial root, one duplexing per OOD sample, and the
    // squeeze that produces the group's batching challenge.
    let mut n = merkle::DIGEST.div_ceil(RATE) + cfg.initial_ood_samples + 1;
    n += sumcheck_perms(cfg.initial_folding_factor);
    for r in cfg.rounds.iter() {
        n += merkle::DIGEST.div_ceil(RATE); // the commitment
        // One duplexing per out-of-domain sample: the answer is absorbed and the
        // next point is read from the rate that absorb produced.
        n += r.ood_samples;
        n += index_squeezes(r.num_queries);
        n += r.num_queries * (r.log_domain_size + leaf_hash(r.row_len));
        n += 1; // the round's batching challenge
        n += sumcheck_perms(r.folding_factor);
    }
    n += (ext4::D << cfg.final_poly_vars).div_ceil(RATE);
    n += index_squeezes(cfg.final_round.num_queries);
    n += cfg.final_round.num_queries
        * (cfg.final_round.log_domain_size + leaf_hash(cfg.final_round.row_len));
    n += sumcheck_perms(cfg.final_sumcheck_rounds);
    n
}
