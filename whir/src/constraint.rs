//! Batching a round's answers into the next target, in Bitcoin Script.
//!
//! A WHIR round ends by folding its out-of-domain answer and its `t` shift
//! answers into the *next* round's constraint. Following the paper's §2.1.3:
//!
//! ```text
//! w'(Z, X) := w(Z, alpha, X) + Z * sum_{i=0}^{t} gamma^(i+1) * eq(z_i, X)
//! sigma'   := h_k(alpha_k)   +     sum_{i=0}^{t} gamma^(i+1) * y_i
//! ```
//!
//! The two halves are not equally hard. `sigma'` is plain extension-field
//! arithmetic on values the verifier already holds, and that is what
//! [`combine_answers`] computes. `w'` is carried *symbolically* — it is never
//! evaluated during a round — and the question is what happens to it at the end.
//!
//! # Two readings of the closing identity, and which one Plonky3 uses
//!
//! The paper's reading folds the weight against the polynomial's evaluations:
//!
//! ```text
//! sum_b f_M(b) * gamma^e * eq(z, b)  =  gamma^e * f_M(z)
//! ```
//!
//! so each accumulated term collapses into an evaluation of `f_M` and no `eq`
//! is ever computed. That is what [`closing_check`] does, and an earlier version
//! of this module claimed it was the whole story.
//!
//! It is not the shape Plonky3's verifier has. There, `w` and `f_M` are kept
//! apart and each is evaluated at its own point:
//!
//! ```text
//! claimed_eval == evaluation_of_weights * final_value
//!     evaluation_of_weights = eval_constraints_poly(&constraints, &folding_randomness)
//!     final_value           = final_evaluations.eval_ext(&final_sumcheck_randomness)
//! ```
//!
//! and `eval_constraints_poly` evaluates every accumulated `eq(z, .)` explicitly.
//! Since this crate is checked against Plonky3, that is the shape the script has
//! to produce, and it needs an `eq` primitive after all — [`eq_eval`].
//!
//! # Threading, and why it needs no per-round work
//!
//! The natural guess is that a carried pair has to be rewritten every round, its
//! weight picking up a factor as the sumcheck binds variables. It does not. The
//! constraints are simply *accumulated*, and at the end each is evaluated
//! against the concatenation of every round's folding randomness:
//!
//! ```text
//! R = alpha^(0) || alpha^(1) || ... || alpha^(final)
//! ```
//!
//! A constraint created at round `i` is over `n_c` variables, and the randomness
//! that binds those variables is everything from round `i` onwards — the **last
//! `n_c` coordinates of `R`**. That is exactly `get_subpoint_over_range(..n_c)`
//! on the reversed point, reversed back.
//!
//! On a stack this rule costs nothing to implement. Push `R` with `R[0]` deepest
//! and the last `n_c` coordinates are the *topmost* `n_c` elements, so every
//! constraint reads from the top and a longer one simply reaches further down.
//! No slicing, no arithmetic on offsets, and no per-round rewriting: see
//! [`constraint_eval`].
//!
//! Together with the row-to-leaf binding in [`poseidon2::merkle::hash_row`] and
//! [`combine_answers`], this is what makes a query *constrain* something. Before,
//! an answer was authenticated against the commitment and then dropped; now it
//! reaches the claim, and the claim reaches the closing identity.

use crate::treepp::*;
use poseidon2::ext4;

/// `sigma' = base + sum_{i=0}^{t} gamma^(i+1) * y_i`, over `EF`.
///
/// # Horner, not powers
///
/// Forming `gamma, gamma^2, ..., gamma^(t+1)` and then taking the inner product
/// costs `2t` multiplications. Horner from the top costs `t + 1`:
///
/// ```text
/// S := y_t;  S := S*gamma + y_i  for i = t-1 .. 0;  sigma' := base + gamma*S
/// ```
///
/// which expands to `sum_i gamma^(i+1) y_i` because the outer `gamma` shifts
/// every exponent up by one — the `+1` in the paper's `gamma^(i+1)`. Each
/// extension multiplication is sixteen base multiplications, so halving them is
/// worth the slightly denser code.
///
/// # Stack
///
/// In: `base(4) gamma(4)`, with the answers on the altstack, `y_t` on top
/// (Horner consumes them highest index first).
/// Out: `sigma'(4)`.
///
/// # Cost
///
/// `t + 1` extension multiplications and `t + 1` additions — no permutation at
/// all, so against the `depth` permutations each answer already cost to
/// authenticate this is free. Batching answers into the constraint is not what
/// makes a WHIR verifier expensive; opening them is.
pub fn combine_answers(t: usize) -> Script {
    script! {
        // S := y_t
        { ext4::from_altstack() }
        for _ in 0..t {
            // S := S * gamma + y_i
            { ext4::copy(1) }           // gamma sits directly under S
            { ext4::mul() }
            { ext4::from_altstack() }
            { ext4::add() }
        }
        // sigma' := base + gamma * S
        { ext4::copy(1) }
        { ext4::mul() }
        // Drop gamma from under the product, then add the base.
        { ext4::to_altstack() }
        { ext4::drop_n(1) }
        { ext4::from_altstack() }
        { ext4::add() }
    }
}

/// `eq(z, r)` over `EF`, with `under` extension elements sitting above `r`.
///
/// # The identity
///
/// The equality polynomial is a product of one factor per coordinate:
///
/// ```text
/// eq(z, r) = prod_i ( z_i * r_i + (1 - z_i) * (1 - r_i) )
///          = prod_i ( 1 + 2*z_i*r_i - z_i - r_i )
/// ```
///
/// The second form is what Plonky3's `Point::eval_eq` uses, and it is worth a
/// line of explanation because it is not a cosmetic rewrite: the first form is
/// two multiplications per coordinate, the second is one. Over the quartic
/// extension a multiplication is sixteen base multiplications, so halving them
/// halves the dominant cost of this routine.
///
/// # Stack
///
/// The challenge `r` is the top `n` extension elements *underneath* `under`
/// unrelated ones — `r[0]` deepest of the block, `r[n-1]` closest to the top.
/// It is **copied, not consumed**, because several constraint groups read
/// overlapping suffixes of the same randomness.
///
/// Altstack: the point `z`, popped `z[n-1]` first — the same order
/// [`crate::multilinear::eval_multilinear`] consumes a point in, so one loader
/// serves both and a point can be laid out once.
///
/// Out: the scalar, pushed on top.
///
/// # Why the challenge is read from the top
///
/// A constraint of arity `n` reads the *last* `n` coordinates of the total
/// folding randomness (see the module docs). With `R[0]` deepest those are the
/// topmost `n` elements, so the depth of `r[i]` is a function of `n` and `i`
/// alone — the total length never enters. A group of larger arity reaches
/// further down and needs no different code.
pub fn eq_eval_at(n: usize, under: usize) -> Script {
    script! {
        { ext4::push_one() }
        for i in (0..n).rev() {
            { ext4::from_altstack() }            // z_i
            // r_i, with the accumulator, z_i and `under` others above it.
            { ext4::copy(under + n - i + 1) }
            // 1 + 2*z_i*r_i - z_i - r_i, built above the two operands.
            { ext4::copy(1) }                    // z_i
            { ext4::copy(1) }                    // r_i
            { ext4::mul() }
            { ext4::copy(0) } { ext4::add() }    // doubled
            { ext4::copy(2) } { ext4::sub() }    // - z_i
            { ext4::copy(1) } { ext4::sub() }    // - r_i
            { ext4::push_one() } { ext4::add() }
            // Drop the two operands from under the factor, then fold it in.
            { ext4::to_altstack() }
            { ext4::drop_n(2) }
            { ext4::from_altstack() }
            { ext4::mul() }
        }
    }
}

/// [`eq_eval_at`] with the challenge on top of the stack.
pub fn eq_eval(n: usize) -> Script {
    eq_eval_at(n, 0)
}

/// A constraint point from a single field element: Plonky3's
/// `Point::expand_from_univariate`.
///
/// Out-of-domain samples and shift queries are scalars, but a constraint's point
/// is a vector. The expansion is the square-power vector
///
/// ```text
/// expand(u, m) = [ u^(2^(m-1)), ..., u^4, u^2, u ]
/// ```
///
/// which is the multilinear point whose `eq` picks out the univariate evaluation
/// at `u` — the same `pow(x, m)` that turns a Reed-Solomon codeword into a
/// multilinear one.
///
/// # Stack
///
/// In: `u(4)`. Out: nothing on the stack; the `m` coordinates are left on the
/// altstack laid out exactly as [`eq_eval`] consumes them.
///
/// # Why no reordering is needed
///
/// Repeated squaring produces `u` first and `u^(2^(m-1))` last, so the powers
/// land on the stack with `u` deepest. Moving the block to the altstack top
/// first reverses it, which puts `u` — the point's *last* coordinate — on top,
/// and that is the coordinate `eq_eval` pops first. The two conventions meet
/// without a single extra roll.
///
/// # Cost
///
/// `m - 1` extension multiplications and no permutation.
pub fn expand_univariate(m: usize) -> Script {
    assert!(m >= 1, "a constraint point has at least one coordinate");
    script! {
        // u, u^2, u^4, ... with u deepest.
        for _ in 1..m {
            { ext4::copy(0) }
            { ext4::copy(1) }
            { ext4::mul() }
        }
        for _ in 0..m { { ext4::to_altstack() } }
    }
}

/// `sum_j w_j * eq(z_j, r)` for one group of constraints sharing an arity.
///
/// This is the script form of Plonky3's
/// `dot_product(eq_statement.weights_at(&local_challenge), challenge_powers(shift))`.
/// The weights arrive as values rather than as powers of a batching challenge,
/// so the same routine serves any group whose weights the caller has already
/// formed — [`combine_answers`] forms them the same way for `sigma'`.
///
/// # Stack
///
/// In: the challenge, its top `n_vars` extension elements being this group's
/// local point. Preserved.
/// Altstack, per constraint in order: the weight `w_j`, then the `n_vars`
/// coordinates of `z_j` — the layout [`closing_check`] already takes, where the
/// coordinates pop first and the weight is underneath them.
/// Out: the accumulated scalar, pushed above the challenge.
///
/// # Cost
///
/// `2 * n_vars + 2` extension multiplications per constraint and no permutation.
/// Against the `depth` permutations each constraint's answer already cost to
/// authenticate, threading is free; opening is what a WHIR verifier pays for.
pub fn weights_at(n_points: usize, n_vars: usize) -> Script {
    weights_at_under(n_points, n_vars, 0)
}

/// [`weights_at`] with `under` unrelated extension elements above the challenge.
pub fn weights_at_under(n_points: usize, n_vars: usize, under: usize) -> Script {
    script! {
        { ext4::push_zero() }
        for _ in 0..n_points {
            { eq_eval_at(n_vars, 1 + under) }    // the accumulator, and the caller's
            { ext4::from_altstack() }            // w_j, underneath its coordinates
            { ext4::mul() }
            { ext4::add() }
        }
    }
}

/// `evaluation_of_weights`: the accumulated constraint polynomial at the folding
/// point, the script form of Plonky3's `eval_constraints_poly`.
///
/// # What this closes
///
/// [`combine_answers`] carries each round's answers into the next target and
/// this carries each round's *points* to the end, so the closing identity is
/// checked against the constraints the transcript actually accumulated rather
/// than against a list supplied by the spender. That was the last link outside
/// the script.
///
/// # Stack
///
/// In: the total folding randomness `R`, `total_vars` extension elements with
/// `R[0]` deepest — the concatenation of every round's sumcheck randomness in
/// round order, which is the order the rounds produced it in.
/// Altstack: the groups in the order given, each laid out as [`weights_at`]
/// expects.
/// Out: the single scalar. `R` is consumed.
///
/// `groups` is `(constraints, arity)` per round, arity being the number of
/// variables that round's commitment had. Nothing requires the arities to be
/// sorted: each group reads its own suffix of `R` by reading that many elements
/// from the top.
///
/// The result is the `weight` that [`crate::verifier::final_check`] multiplies
/// against `f_M` at the final sumcheck randomness.
pub fn constraint_eval(total_vars: usize, groups: &[(usize, usize)]) -> Script {
    constraint_eval_at(total_vars, groups, 0)
}

/// [`constraint_eval`] with `under` unrelated extension elements above `R`.
///
/// The composed verifier reaches the closing identity holding the chained claim
/// and the final polynomial's value, both of which sit above the randomness and
/// both of which are still needed afterwards. Parking them on the altstack is
/// not an option — the constraint list is down there, and anything pushed above
/// it would be popped in its place — so the offset is threaded through instead.
///
/// # Stack
///
/// In: `R(4*total_vars) X(4*under)`.
/// Out: `X(4*under) w`, with `R` consumed.
pub fn constraint_eval_at(total_vars: usize, groups: &[(usize, usize)], under: usize) -> Script {
    // `script!` takes no local bindings, so the per-group blocks are built here.
    let blocks: Vec<Script> = groups
        .iter()
        .map(|&(n_points, n_vars)| {
            assert!(
                n_vars <= total_vars,
                "a constraint of arity {n_vars} cannot read a suffix of {total_vars} coordinates"
            );
            script! {
                for _ in 0..n_points {
                    // The accumulator, plus whatever the caller left above `R`.
                    { eq_eval_at(n_vars, 1 + under) }
                    { ext4::from_altstack() }
                    { ext4::mul() }
                    { ext4::add() }
                }
            }
        })
        .collect();
    // Slots standing above `R` once the accumulator exists.
    let above = ext4::D * (under + 1);
    let r_slots = ext4::D * total_vars;
    script! {
        { ext4::push_zero() }
        for b in blocks { { b } }
        // The randomness has done its work. It is at the bottom with live values
        // above it, so each slot is rolled up and dropped rather than parked:
        // parking would reverse the order of what sits above.
        for j in 0..r_slots { { r_slots + above - 1 - j } OP_ROLL OP_DROP }
    }
}

/// The accumulated weight with the constraints *derived* rather than supplied.
///
/// [`constraint_eval`] takes a list of `(weight, point)` pairs. Both halves can
/// be built from far less: a round's constraints are all weighted by powers of
/// one batching challenge, and each of their points is the square-power
/// expansion of a single scalar. So a round is described by `1 + n` extension
/// elements — the challenge and the scalars — rather than by `n * (1 + arity)`.
///
/// # The weights are Horner, and the challenge arrives last
///
/// Plonky3's `Constraint::challenge_powers(shift)` is
/// `challenge.shifted_powers(challenge^shift)`, so within a constraint the
/// weights run `chi^0, chi^1, chi^2, ...` — starting at **one**, not at `chi`.
/// That is worth pinning down, because it differs from the `gamma^(i+1)` of the
/// paper's `sigma'` update that [`combine_answers`] implements, and getting it
/// wrong would produce a value that looks right and is not.
///
/// Starting at one makes the group a plain polynomial in `chi`, which Horner
/// evaluates from the top in `n - 1` multiplications:
///
/// ```text
/// S := e_{n-1};   S := S*chi + e_j   for j = n-2 .. 0
/// ```
///
/// Horner wants the *last* term first, and a round produces its scalars in
/// order and its challenge only afterwards — the two orders disagree. Rather
/// than reverse one of them, the `eq` values are built up on the stack as the
/// scalars arrive and Horner runs over them once `chi` appears. That costs `n`
/// extension elements of stack for the length of a group and nothing else, and
/// it is what lets a round bury its scalars in the order it samples them.
///
/// # Stack
///
/// In: the total folding randomness `R`, `total_vars` extension elements with
/// `R[0]` deepest.
/// Altstack, per group in order: the scalars **in order**, then the batching
/// challenge.
/// Out: the single scalar. `R` is consumed.
///
/// `groups` is `(constraints, arity)` per round.
///
/// # Cost
///
/// Per constraint: `arity - 1` multiplications to expand the point, `2 * arity`
/// to evaluate `eq`, and one for the Horner step. No permutation anywhere — the
/// whole of the weight polynomial is arithmetic, which is why it stays a
/// rounding error against the query openings.
pub fn constraint_eval_batched(total_vars: usize, groups: &[(usize, usize)]) -> Script {
    constraint_eval_batched_at(total_vars, groups, 0)
}

/// [`constraint_eval_batched`] with `under` unrelated elements above `R`.
pub fn constraint_eval_batched_at(
    total_vars: usize,
    groups: &[(usize, usize)],
    under: usize,
) -> Script {
    let blocks: Vec<Script> = groups
        .iter()
        .map(|&(n, n_vars)| {
            assert!(n >= 1, "a constraint group with no constraints has no challenge");
            assert!(
                n_vars <= total_vars,
                "a constraint of arity {n_vars} cannot read a suffix of {total_vars} coordinates"
            );
            // Everything to discard once the group's total exists: its `n` eq
            // values and the challenge.
            let spent = ext4::D * (n + 1);
            script! {
                // e_j = eq(expand(u_j), R), left on the stack in order. While
                // e_j is being built, the accumulator, whatever the caller left
                // above `R`, and e_0..e_{j-1} are all above it.
                for j in 0..n {
                    { ext4::from_altstack() }
                    { expand_univariate(n_vars) }
                    { eq_eval_at(n_vars, 1 + under + j) }
                }
                { ext4::from_altstack() }        // chi, above e_{n-1}
                { ext4::copy(1) }                // S := e_{n-1}
                for j in (0..n - 1).rev() {
                    { ext4::copy(1) }            // chi
                    { ext4::mul() }
                    { ext4::copy(n + 1 - j) }    // e_j
                    { ext4::add() }
                }
                // Drop the eq values and the challenge from under the total.
                for i in 0..spent { { spent + ext4::D - 1 - i } OP_ROLL OP_DROP }
                { ext4::add() }
            }
        })
        .collect();
    let r_slots = ext4::D * total_vars;
    let above = ext4::D * (under + 1);
    script! {
        { ext4::push_zero() }
        for b in blocks { { b } }
        for j in 0..r_slots { { r_slots + above - 1 - j } OP_ROLL OP_DROP }
    }
}

/// The closing check: `sum_j w_j * f_M(z_j) == sigma`, over `EF`.
///
/// # Why this is the whole of `w'`
///
/// A round never evaluates its weight polynomial; it carries it. After `M`
/// rounds `w'` is a sum of terms `Z * gamma^e * eq(z, X)`, and the closing check
/// asks for
///
/// ```text
/// sum_b w'(f_M(b), b) = sigma
/// ```
///
/// Each term collapses, because summing an evaluation against `eq` *is*
/// evaluation:
///
/// ```text
/// sum_b f_M(b) * gamma^e * eq(z, b) = gamma^e * f_M(z)
/// ```
///
/// So the accumulated symbolic polynomial is exactly a list of
/// `(weight, point)` pairs, and checking it is evaluating the final polynomial
/// at each point and taking the weighted sum. That is why no `eq` primitive is
/// needed anywhere in this verifier: `eq` appears only inside something that is
/// never touched until it turns into an evaluation.
///
/// # Stack
///
/// In: `sigma(4) evals(4 * 2^n_vars)`, the final polynomial's evaluations with
/// `e[0]` deepest. Altstack, per point in consumption order: the weight `w_j`,
/// then the point's coordinates ordered so the *last* variable pops first —
/// which is what [`crate::multilinear::eval_multilinear`] expects.
/// Out: nothing. The spend is invalid unless the identity holds in all four
/// coefficients.
///
/// # Cost
///
/// `n_points` multilinear evaluations of `n_vars` variables. The evaluations are
/// copied rather than re-pushed, so the witness carries the final polynomial
/// once. No permutation — this is arithmetic, and it is the reason
/// `final_poly_vars` wants to stay small: the cost is
/// `n_points * 2^n_vars` extension operations, exponential in the wrong variable
/// if the folding schedule leaves too much to the end.
pub fn closing_check(n_points: usize, n_vars: usize) -> Script {
    let n = 1usize << n_vars; // evaluations in the final polynomial
    script! {
        // acc := 0
        { ext4::push_zero() }
        for _ in 0..n_points {
            // Copy the evaluation block above the accumulator. The block's
            // deepest element sits at a constant depth of `n` while the copy is
            // being built: each push shifts the remainder by one, which cancels
            // the step to the next element — the same cancellation
            // `ext4::copy` relies on internally.
            for _ in 0..n { { ext4::copy(n) } }
            { crate::multilinear::eval_multilinear(n_vars) }
            { ext4::from_altstack() }   // w_j
            { ext4::mul() }
            { ext4::add() }
        }
        // Compare the accumulator with sigma, which is beneath the evaluations.
        { ext4::to_altstack() }
        { ext4::drop_n(n) }
        { ext4::from_altstack() }
        for i in 0..ext4::D {
            { ext4::D - i } OP_ROLL
            OP_EQUALVERIFY
        }
    }
}
