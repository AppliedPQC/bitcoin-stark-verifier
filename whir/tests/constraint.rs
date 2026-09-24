//! Batching answers into the next target.
//!
//! The script computes the sum by Horner because extension multiplications are
//! expensive; the reference computes it as written. They agree only if the
//! rearrangement is right, which is the point of testing them against each other
//! rather than against a shared helper.

use bitcoin_script::{define_pushable, script};
use poseidon2::reference as pf;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use whir::{constraint, reference};

define_pushable!();

fn decode(v: &[u8]) -> i64 {
    if v.is_empty() {
        return 0;
    }
    let mut n: i64 = 0;
    for (i, b) in v.iter().enumerate() {
        n |= ((*b as i64) & 0xff) << (8 * i);
    }
    if v[v.len() - 1] & 0x80 != 0 {
        n &= !(0x80i64 << (8 * (v.len() - 1)));
        return -n;
    }
    n
}

fn run(s: bitcoin::ScriptBuf) -> Vec<u32> {
    let info = bitcoin_scriptexec::execute_script(s);
    assert!(info.error.is_none(), "errored: {:?} at {:?}", info.error, info.last_opcode);
    (0..info.final_stack.len()).map(|i| decode(&info.final_stack.get(i)) as u32).collect()
}

fn rand_ef(rng: &mut ChaCha20Rng) -> [u32; 4] {
    core::array::from_fn(|_| rng.random_range(0..poseidon2::constants::P))
}

fn push_ef(v: [u32; 4]) -> bitcoin::ScriptBuf {
    script! { for x in v { {x} } }
}

/// Load the answers so Horner pops `y_t` first.
fn answers_to_altstack(answers: &[[u32; 4]]) -> bitcoin::ScriptBuf {
    script! {
        for y in answers.iter() {
            { push_ef(*y) }
            for _ in 0..4 { OP_TOALTSTACK }
        }
    }
}

#[test]
fn combine_matches_the_reference() {
    let mut rng = ChaCha20Rng::seed_from_u64(41);
    // t = 0 is the out-of-domain answer alone; the rest add shift answers.
    for t in 0..6usize {
        let base = rand_ef(&mut rng);
        let gamma = rand_ef(&mut rng);
        let answers: Vec<[u32; 4]> = (0..=t).map(|_| rand_ef(&mut rng)).collect();
        let want = reference::combine_answers(base, gamma, &answers);

        let got = run(script! {
            { answers_to_altstack(&answers) }
            { push_ef(base) }
            { push_ef(gamma) }
            { constraint::combine_answers(t) }
        });

        assert_eq!(got.len(), 4, "t = {t}: expected a single EF element");
        assert_eq!(got, want.to_vec(), "t = {t}: Horner disagrees with the sum");
    }
}

/// The exponents are right, not merely consistent.
///
/// Both implementations could share an off-by-one in the power of `gamma` and
/// still agree. Pinning `t = 1` against the expression written out by hand —
/// `base + gamma*y0 + gamma^2*y1` — catches that.
#[test]
fn combine_uses_the_stated_powers() {
    let mut rng = ChaCha20Rng::seed_from_u64(42);
    let base = rand_ef(&mut rng);
    let gamma = rand_ef(&mut rng);
    let y0 = rand_ef(&mut rng);
    let y1 = rand_ef(&mut rng);

    let g2 = pf::ext4::mul(gamma, gamma);
    let by_hand = pf::ext4::add(
        base,
        pf::ext4::add(pf::ext4::mul(gamma, y0), pf::ext4::mul(g2, y1)),
    );

    let got = run(script! {
        { answers_to_altstack(&[y0, y1]) }
        { push_ef(base) }
        { push_ef(gamma) }
        { constraint::combine_answers(1) }
    });
    assert_eq!(got, by_hand.to_vec(), "gamma is raised to the wrong power somewhere");
}

/// Every answer reaches the target.
///
/// An answer that could be changed without moving `sigma'` would be
/// authenticated and then ignored — exactly the state this module exists to
/// leave behind.
#[test]
fn every_answer_reaches_the_target() {
    let mut rng = ChaCha20Rng::seed_from_u64(43);
    let t = 4usize;
    let base = rand_ef(&mut rng);
    let gamma = rand_ef(&mut rng);
    let answers: Vec<[u32; 4]> = (0..=t).map(|_| rand_ef(&mut rng)).collect();

    let run_with = |answers: &[[u32; 4]]| {
        run(script! {
            { answers_to_altstack(answers) }
            { push_ef(base) }
            { push_ef(gamma) }
            { constraint::combine_answers(t) }
        })
    };
    let want = run_with(&answers);

    for i in 0..=t {
        for c in 0..4 {
            let mut bad = answers.clone();
            bad[i][c] = pf::add(bad[i][c], 1);
            assert_ne!(
                run_with(&bad),
                want,
                "answer {i} coefficient {c} did not affect sigma'"
            );
        }
    }
}

/// A different batching challenge gives a different target.
///
/// This is what stops a prover trading one wrong answer against another: the
/// combination is a random linear one, so cancelling in the sum means hitting a
/// root of a degree-`t+1` polynomial in `gamma`.
#[test]
fn the_batching_challenge_matters() {
    let mut rng = ChaCha20Rng::seed_from_u64(44);
    let t = 3usize;
    let base = rand_ef(&mut rng);
    let answers: Vec<[u32; 4]> = (0..=t).map(|_| rand_ef(&mut rng)).collect();

    let with = |gamma: [u32; 4]| {
        run(script! {
            { answers_to_altstack(&answers) }
            { push_ef(base) }
            { push_ef(gamma) }
            { constraint::combine_answers(t) }
        })
    };

    let g = rand_ef(&mut rng);
    let mut g2 = g;
    g2[0] = pf::add(g2[0], 1);
    assert_ne!(with(g), with(g2), "sigma' is independent of gamma");
}

// ---------------------------------------------------------------------------
// The closing check
// ---------------------------------------------------------------------------

/// Load one point: the weight first, then coordinates so the last variable pops
/// first — the order `eval_multilinear` consumes them in.
fn point_to_altstack(w: [u32; 4], z: &[[u32; 4]]) -> bitcoin::ScriptBuf {
    script! {
        { push_ef(w) } for _ in 0..4 { OP_TOALTSTACK }
        for c in z.iter() { { push_ef(*c) } for _ in 0..4 { OP_TOALTSTACK } }
    }
}

fn closing_script(
    sigma: [u32; 4],
    evals: &[[u32; 4]],
    pts: &[([u32; 4], Vec<[u32; 4]>)],
    n_vars: usize,
) -> bitcoin::ScriptBuf {
    script! {
        for (w, z) in pts.iter().rev() { { point_to_altstack(*w, z) } }
        { push_ef(sigma) }
        for e in evals.iter() { { push_ef(*e) } }
        { constraint::closing_check(pts.len(), n_vars) }
        OP_TRUE
    }
}

#[test]
fn closing_check_accepts_the_accumulated_sum() {
    let mut rng = ChaCha20Rng::seed_from_u64(45);
    for (n_vars, n_points) in [(1usize, 1usize), (2, 3), (3, 5), (4, 2)] {
        let evals: Vec<[u32; 4]> = (0..(1 << n_vars)).map(|_| rand_ef(&mut rng)).collect();
        let pts: Vec<([u32; 4], Vec<[u32; 4]>)> = (0..n_points)
            .map(|_| (rand_ef(&mut rng), (0..n_vars).map(|_| rand_ef(&mut rng)).collect()))
            .collect();
        let sigma = reference::closing_sum(&evals, &pts);

        let ok = bitcoin_scriptexec::execute_script(closing_script(sigma, &evals, &pts, n_vars));
        assert!(
            ok.error.is_none(),
            "{n_vars} vars, {n_points} points: rejected: {:?}",
            ok.error
        );
    }
}

/// Wrong target, wrong weight, wrong point, wrong polynomial — all rejected.
///
/// Each of these is a distinct way for the closing check to be vacuous, and the
/// previous incarnation of `final_check` was vacuous in the first way.
#[test]
fn closing_check_rejects_every_perturbation() {
    let mut rng = ChaCha20Rng::seed_from_u64(46);
    let (n_vars, n_points) = (3usize, 4usize);
    let evals: Vec<[u32; 4]> = (0..(1 << n_vars)).map(|_| rand_ef(&mut rng)).collect();
    let pts: Vec<([u32; 4], Vec<[u32; 4]>)> = (0..n_points)
        .map(|_| (rand_ef(&mut rng), (0..n_vars).map(|_| rand_ef(&mut rng)).collect()))
        .collect();
    let sigma = reference::closing_sum(&evals, &pts);

    let rejects = |s: bitcoin::ScriptBuf, why: &str| {
        assert!(bitcoin_scriptexec::execute_script(s).error.is_some(), "{why}: accepted");
    };

    for c in 0..4 {
        let mut bad = sigma;
        bad[c] = pf::add(bad[c], 1);
        rejects(closing_script(bad, &evals, &pts, n_vars), &format!("sigma coefficient {c}"));
    }
    for j in 0..n_points {
        let mut bad = pts.clone();
        bad[j].0[0] = pf::add(bad[j].0[0], 1);
        rejects(closing_script(sigma, &evals, &bad, n_vars), &format!("weight {j}"));

        let mut bad = pts.clone();
        bad[j].1[0][0] = pf::add(bad[j].1[0][0], 1);
        rejects(closing_script(sigma, &evals, &bad, n_vars), &format!("point {j}"));
    }
    for i in 0..evals.len() {
        let mut bad = evals.clone();
        bad[i][0] = pf::add(bad[i][0], 1);
        rejects(closing_script(sigma, &bad, &pts, n_vars), &format!("final polynomial coeff {i}"));
    }
}

/// What the closing check costs, so the folding schedule can be argued about.
#[test]
fn report_closing_check_size() {
    println!("\n  closing check: n_points x eval_multilinear(n_vars)");
    println!("  ------------------------------------------------");
    for n_vars in [2usize, 3, 4, 5] {
        let one = constraint::closing_check(1, n_vars).len();
        let ten = constraint::closing_check(10, n_vars).len();
        println!(
            "  n_vars = {n_vars}:  1 point {one:>10} B   10 points {ten:>11} B   per point {:>10} B",
            (ten - one) / 9
        );
    }
    println!();
}

// ---------------------------------------------------------------------------
// Threading: eq, and the accumulated constraint polynomial
// ---------------------------------------------------------------------------

/// Load a point so `eq_eval` pops `z[n-1]` first -- the coordinate order
/// `point_to_altstack` already uses, and the one `eval_multilinear` expects.
fn point_coords_to_altstack(z: &[[u32; 4]]) -> bitcoin::ScriptBuf {
    script! {
        for c in z.iter() { { push_ef(*c) } for _ in 0..4 { OP_TOALTSTACK } }
    }
}

/// The challenge on the stack, `r[0]` deepest.
fn push_randomness(r: &[[u32; 4]]) -> bitcoin::ScriptBuf {
    script! { for c in r.iter() { { push_ef(*c) } } }
}

#[test]
fn eq_eval_matches_the_reference() {
    let mut rng = ChaCha20Rng::seed_from_u64(47);
    for n in 1..6usize {
        let z: Vec<[u32; 4]> = (0..n).map(|_| rand_ef(&mut rng)).collect();
        let r: Vec<[u32; 4]> = (0..n).map(|_| rand_ef(&mut rng)).collect();
        let want = reference::eq_eval(&z, &r);

        let got = run(script! {
            { point_coords_to_altstack(&z) }
            { push_randomness(&r) }
            { constraint::eq_eval(n) }
        });
        // The challenge is preserved beneath the result.
        assert_eq!(got.len(), 4 * (n + 1), "n = {n}: eq_eval disturbed the challenge");
        assert_eq!(&got[4 * n..], want.as_slice(), "n = {n}: eq disagrees with the product");
        assert_eq!(&got[..4 * n], r.concat().as_slice(), "n = {n}: the challenge moved");
    }
}

/// The rearrangement is Plonky3's, so check it against Plonky3.
///
/// The script uses `1 + 2*z*r - z - r` and the reference uses
/// `z*r + (1-z)*(1-r)`. Both could be a consistent misreading of what the
/// verifier this crate targets actually computes; `Point::eval_eq` is that
/// verifier's own routine.
#[test]
fn eq_eval_matches_plonky3() {
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
    use p3_koala_bear::KoalaBear;
    use p3_multilinear_util::point::Point;

    type EF = BinomialExtensionField<KoalaBear, 4>;

    let coeffs = |x: EF| -> [u32; 4] {
        let s: &[KoalaBear] = x.as_basis_coefficients_slice();
        core::array::from_fn(|i| s[i].as_canonical_u32())
    };
    let of = |c: [u32; 4]| -> EF {
        EF::from_basis_coefficients_fn(|i| KoalaBear::from_u32(c[i]))
    };

    let mut rng = ChaCha20Rng::seed_from_u64(48);
    for n in 1..6usize {
        let z: Vec<[u32; 4]> = (0..n).map(|_| rand_ef(&mut rng)).collect();
        let r: Vec<[u32; 4]> = (0..n).map(|_| rand_ef(&mut rng)).collect();

        let zp: Vec<EF> = z.iter().map(|c| of(*c)).collect();
        let rp: Vec<EF> = r.iter().map(|c| of(*c)).collect();
        let want = coeffs(Point::eval_eq::<EF>(&zp, &rp));

        assert_eq!(reference::eq_eval(&z, &r), want, "n = {n}: reference disagrees with Plonky3");

        let got = run(script! {
            { point_coords_to_altstack(&z) }
            { push_randomness(&r) }
            { constraint::eq_eval(n) }
        });
        assert_eq!(&got[4 * n..], want.as_slice(), "n = {n}: script disagrees with Plonky3");
    }
}

/// `eq` factorises across a split, which is why threading needs no per-round work.
///
/// If this failed, a constraint could not simply be evaluated at a suffix of the
/// accumulated randomness at the end -- its weight would have to be rewritten
/// every round with the prefix folded in. The whole design of
/// `constraint_eval` rests on this line.
#[test]
fn eq_factorises_across_a_split() {
    use poseidon2::reference::ext4;
    let mut rng = ChaCha20Rng::seed_from_u64(49);
    for (k, m) in [(1usize, 2usize), (2, 3), (3, 1)] {
        let z: Vec<[u32; 4]> = (0..k + m).map(|_| rand_ef(&mut rng)).collect();
        let r: Vec<[u32; 4]> = (0..k + m).map(|_| rand_ef(&mut rng)).collect();
        assert_eq!(
            reference::eq_eval(&z, &r),
            ext4::mul(
                reference::eq_eval(&z[..k], &r[..k]),
                reference::eq_eval(&z[k..], &r[k..]),
            ),
            "eq does not factorise at {k} | {m}"
        );
    }
}

/// A point of every arity reads its own suffix of the same randomness.
#[test]
fn constraint_eval_matches_the_reference() {
    let mut rng = ChaCha20Rng::seed_from_u64(50);
    let total = 5usize;
    let r: Vec<[u32; 4]> = (0..total).map(|_| rand_ef(&mut rng)).collect();

    // One group per round, arities shrinking the way the rounds do -- and one
    // out of order, because nothing requires them to be sorted.
    let shape = [(2usize, 5usize), (3, 3), (1, 4), (2, 1)];
    let groups: Vec<Vec<([u32; 4], Vec<[u32; 4]>)>> = shape
        .iter()
        .map(|&(n_points, n_vars)| {
            (0..n_points)
                .map(|_| (rand_ef(&mut rng), (0..n_vars).map(|_| rand_ef(&mut rng)).collect()))
                .collect()
        })
        .collect();
    let want = reference::constraint_eval(&r, &groups);

    let got = run(script! {
        { groups_to_altstack(&groups) }
        { push_randomness(&r) }
        { constraint::constraint_eval(total, &shape) }
    });
    assert_eq!(got.len(), 4, "constraint_eval left the randomness behind");
    assert_eq!(got, want.to_vec(), "the accumulated weight disagrees");
}

/// Load every group so the script pops weight then coordinates, group by group.
fn groups_to_altstack(groups: &[Vec<([u32; 4], Vec<[u32; 4]>)>]) -> bitcoin::ScriptBuf {
    let mut flat: Vec<([u32; 4], Vec<[u32; 4]>)> = Vec::new();
    for g in groups {
        flat.extend(g.iter().cloned());
    }
    script! {
        for (w, z) in flat.iter().rev() { { point_to_altstack(*w, z) } }
    }
}

/// Every carried point and weight reaches the accumulated weight.
///
/// A constraint that could be changed without moving the result would have been
/// accumulated and then ignored -- the state this module exists to leave behind,
/// one level up from `every_answer_reaches_the_target`.
#[test]
fn every_constraint_reaches_the_weight() {
    let mut rng = ChaCha20Rng::seed_from_u64(51);
    let total = 4usize;
    let r: Vec<[u32; 4]> = (0..total).map(|_| rand_ef(&mut rng)).collect();
    let shape = [(2usize, 4usize), (2, 2)];
    let groups: Vec<Vec<([u32; 4], Vec<[u32; 4]>)>> = shape
        .iter()
        .map(|&(n_points, n_vars)| {
            (0..n_points)
                .map(|_| (rand_ef(&mut rng), (0..n_vars).map(|_| rand_ef(&mut rng)).collect()))
                .collect()
        })
        .collect();

    let eval = |gs: &[Vec<([u32; 4], Vec<[u32; 4]>)>]| {
        run(script! {
            { groups_to_altstack(gs) }
            { push_randomness(&r) }
            { constraint::constraint_eval(total, &shape) }
        })
    };
    let want = eval(&groups);

    for gi in 0..groups.len() {
        for pi in 0..groups[gi].len() {
            let mut bad = groups.to_vec();
            bad[gi][pi].0[0] = pf::add(bad[gi][pi].0[0], 1);
            assert_ne!(eval(&bad), want, "group {gi} point {pi}: the weight was ignored");

            for c in 0..groups[gi][pi].1.len() {
                let mut bad = groups.to_vec();
                bad[gi][pi].1[c][0] = pf::add(bad[gi][pi].1[c][0], 1);
                assert_ne!(eval(&bad), want, "group {gi} point {pi} coord {c}: ignored");
            }
        }
    }
}

/// The randomness a constraint reads is the *suffix*, not the prefix.
///
/// Reading the first `n_c` coordinates instead of the last would still produce a
/// value, agree with a reference that made the same choice, and be wrong. The
/// two differ as soon as an arity is shorter than the total, so perturbing a
/// coordinate that only the suffix rule reaches pins the direction.
#[test]
fn a_short_constraint_reads_the_end_of_the_randomness() {
    let mut rng = ChaCha20Rng::seed_from_u64(52);
    let total = 4usize;
    let r: Vec<[u32; 4]> = (0..total).map(|_| rand_ef(&mut rng)).collect();
    // One constraint over two variables: it must see r[2] and r[3] only.
    let shape = [(1usize, 2usize)];
    let groups = vec![vec![(rand_ef(&mut rng), vec![rand_ef(&mut rng), rand_ef(&mut rng)])]];

    let eval = |r: &[[u32; 4]]| {
        run(script! {
            { groups_to_altstack(&groups) }
            { push_randomness(r) }
            { constraint::constraint_eval(total, &shape) }
        })
    };
    let want = eval(&r);

    for i in 0..total {
        let mut bad = r.clone();
        bad[i][0] = pf::add(bad[i][0], 1);
        if i < total - 2 {
            assert_eq!(eval(&bad), want, "r[{i}] is outside the suffix but changed the result");
        } else {
            assert_ne!(eval(&bad), want, "r[{i}] is in the suffix but was ignored");
        }
    }
    // And the reference agrees about which coordinates matter.
    assert_eq!(reference::constraint_eval(&r, &groups).to_vec(), want);
}

/// What threading costs, so it can be compared with the queries it constrains.
#[test]
fn report_constraint_eval_size() {
    println!("\n  eq_eval(n): the accumulated weight, per constraint");
    println!("  ------------------------------------------------");
    for n in [1usize, 2, 4, 8, 16] {
        println!("  n_vars = {n:>2}:  eq_eval {:>9} B", constraint::eq_eval(n).len());
    }
    let one = constraint::constraint_eval(8, &[(1, 8)]).len();
    let ten = constraint::constraint_eval(8, &[(10, 8)]).len();
    println!(
        "  constraint_eval, 8 vars: 1 point {one} B, 10 points {ten} B, per point {} B",
        (ten - one) / 9
    );
    println!();
}

/// The square-power expansion, against Plonky3's own.
///
/// The order matters twice over: it has to be Plonky3's, and it has to reach the
/// altstack in the order `eq_eval` pops coordinates. Checking the value of
/// `eq(expand(u), r)` catches a reversal that checking the coordinates alone
/// would not, because a reversed point is still a point.
#[test]
fn expand_univariate_matches_plonky3() {
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
    use p3_koala_bear::KoalaBear;
    use p3_multilinear_util::point::Point;

    type EF = BinomialExtensionField<KoalaBear, 4>;
    let coeffs = |x: EF| -> [u32; 4] {
        let s: &[KoalaBear] = x.as_basis_coefficients_slice();
        core::array::from_fn(|i| s[i].as_canonical_u32())
    };
    let of = |c: [u32; 4]| -> EF { EF::from_basis_coefficients_fn(|i| KoalaBear::from_u32(c[i])) };

    let mut rng = ChaCha20Rng::seed_from_u64(53);
    for m in 1..6usize {
        let u = rand_ef(&mut rng);
        let want: Vec<[u32; 4]> =
            Point::expand_from_univariate(of(u), m).into_iter().map(coeffs).collect();
        assert_eq!(reference::expand_univariate(u, m), want, "m = {m}: reference expansion");

        // The script leaves the point on the altstack, so read it back through
        // the routine that consumes it.
        let r: Vec<[u32; 4]> = (0..m).map(|_| rand_ef(&mut rng)).collect();
        let got = run(script! {
            { push_ef(u) }
            { constraint::expand_univariate(m) }
            { push_randomness(&r) }
            { constraint::eq_eval(m) }
        });
        assert_eq!(
            &got[4 * m..],
            reference::eq_eval(&want, &r).as_slice(),
            "m = {m}: the expansion reached eq_eval in the wrong order"
        );
    }
}

/// Isolate `constraint_eval_at` with values above the randomness.
#[test]
fn constraint_eval_at_steps_over_what_sits_above() {
    let mut rng = ChaCha20Rng::seed_from_u64(60);
    let total = 4usize;
    let r: Vec<[u32; 4]> = (0..total).map(|_| rand_ef(&mut rng)).collect();
    let shape = [(1usize, 4usize)];
    let groups = vec![vec![(rand_ef(&mut rng), (0..4).map(|_| rand_ef(&mut rng)).collect::<Vec<_>>())]];
    let want = reference::constraint_eval(&r, &groups);

    for under in 0..3usize {
        let above: Vec<[u32; 4]> = (0..under).map(|_| rand_ef(&mut rng)).collect();
        let got = run(script! {
            { groups_to_altstack(&groups) }
            { push_randomness(&r) }
            for x in above.iter() { { push_ef(*x) } }
            { constraint::constraint_eval_at(total, &shape, under) }
        });
        assert_eq!(got.len(), 4 * (under + 1), "under = {under}: wrong stack shape");
        assert_eq!(&got[..4 * under], above.concat().as_slice(),
                   "under = {under}: the values above the randomness were disturbed");
        assert_eq!(&got[4 * under..], want.as_slice(), "under = {under}: wrong weight");
    }
}

// ---------------------------------------------------------------------------
// Deriving the constraints instead of being handed them
// ---------------------------------------------------------------------------

/// One group: the scalars in order, then the challenge -- the order a round
/// samples them in, and so the order it can bury them in.
fn batched_group_to_altstack(chi: [u32; 4], scalars: &[[u32; 4]]) -> bitcoin::ScriptBuf {
    script! {
        { push_ef(chi) } for _ in 0..4 { OP_TOALTSTACK }
        for u in scalars.iter().rev() { { push_ef(*u) } for _ in 0..4 { OP_TOALTSTACK } }
    }
}

fn batched_groups_to_altstack(
    groups: &[([u32; 4], Vec<[u32; 4]>, usize)],
) -> bitcoin::ScriptBuf {
    script! {
        for (chi, scalars, _) in groups.iter().rev() {
            { batched_group_to_altstack(*chi, scalars) }
        }
    }
}

#[test]
fn batched_matches_the_reference() {
    let mut rng = ChaCha20Rng::seed_from_u64(61);
    let total = 6usize;
    let r: Vec<[u32; 4]> = (0..total).map(|_| rand_ef(&mut rng)).collect();

    // Rounds shrinking the way a schedule does, and one out of order.
    let shape = [(3usize, 6usize), (2, 4), (4, 5), (1, 1)];
    let groups: Vec<([u32; 4], Vec<[u32; 4]>, usize)> = shape
        .iter()
        .map(|&(n, arity)| {
            (rand_ef(&mut rng), (0..n).map(|_| rand_ef(&mut rng)).collect(), arity)
        })
        .collect();
    let want = reference::constraint_eval_batched(&r, &groups);

    let shape_pairs: Vec<(usize, usize)> = shape.to_vec();
    let got = run(script! {
        { batched_groups_to_altstack(&groups) }
        { push_randomness(&r) }
        { constraint::constraint_eval_batched(total, &shape_pairs) }
    });
    assert_eq!(got.len(), 4, "the randomness was not consumed");
    assert_eq!(got, want.to_vec(), "the derived weight disagrees with the reference");
}

/// The powers start at one, which is Plonky3's convention and not the paper's.
///
/// `Constraint::challenge_powers` is `shifted_powers(chi^shift)`, so the first
/// constraint in a group is weighted by `chi^0 = 1`. The `sigma'` update in the
/// same protocol uses `gamma^(i+1)`, starting at the challenge itself. Two
/// conventions in one protocol is exactly the sort of thing both a script and a
/// reference written by the same hand would get wrong together, so this pins the
/// two-constraint case against the expression by hand.
#[test]
fn batched_weights_start_at_one() {
    let mut rng = ChaCha20Rng::seed_from_u64(62);
    let arity = 3usize;
    let r: Vec<[u32; 4]> = (0..arity).map(|_| rand_ef(&mut rng)).collect();
    let chi = rand_ef(&mut rng);
    let u0 = rand_ef(&mut rng);
    let u1 = rand_ef(&mut rng);

    let e0 = reference::eq_eval(&reference::expand_univariate(u0, arity), &r);
    let e1 = reference::eq_eval(&reference::expand_univariate(u1, arity), &r);
    // e0 * chi^0 + e1 * chi^1, written out.
    let by_hand = pf::ext4::add(e0, pf::ext4::mul(chi, e1));

    let got = run(script! {
        { batched_group_to_altstack(chi, &[u0, u1]) }
        { push_randomness(&r) }
        { constraint::constraint_eval_batched(arity, &[(2, arity)]) }
    });
    assert_eq!(got, by_hand.to_vec(), "the first weight is not one");
}

/// Every scalar and every challenge reaches the accumulated weight.
#[test]
fn every_derived_constraint_reaches_the_weight() {
    let mut rng = ChaCha20Rng::seed_from_u64(63);
    let total = 4usize;
    let r: Vec<[u32; 4]> = (0..total).map(|_| rand_ef(&mut rng)).collect();
    let shape = [(2usize, 4usize), (3, 2)];
    let groups: Vec<([u32; 4], Vec<[u32; 4]>, usize)> = shape
        .iter()
        .map(|&(n, arity)| {
            (rand_ef(&mut rng), (0..n).map(|_| rand_ef(&mut rng)).collect(), arity)
        })
        .collect();
    let shape_pairs: Vec<(usize, usize)> = shape.to_vec();

    let eval = |gs: &[([u32; 4], Vec<[u32; 4]>, usize)]| {
        run(script! {
            { batched_groups_to_altstack(gs) }
            { push_randomness(&r) }
            { constraint::constraint_eval_batched(total, &shape_pairs) }
        })
    };
    let want = eval(&groups);

    for gi in 0..groups.len() {
        let mut bad = groups.to_vec();
        bad[gi].0[0] = pf::add(bad[gi].0[0], 1);
        // A single-constraint group is weighted by chi^0 only, so its challenge
        // genuinely does not matter -- stating that is better than asserting a
        // sensitivity that does not exist.
        if groups[gi].1.len() > 1 {
            assert_ne!(eval(&bad), want, "group {gi}: the batching challenge was ignored");
        }
        for j in 0..groups[gi].1.len() {
            let mut bad = groups.to_vec();
            bad[gi].1[j][0] = pf::add(bad[gi].1[j][0], 1);
            assert_ne!(eval(&bad), want, "group {gi} scalar {j}: ignored");
        }
    }
}

/// What deriving the constraints costs, against being handed them.
#[test]
fn report_batched_size() {
    println!("\n  constraint_eval, supplied pairs vs derived from scalars");
    println!("  ------------------------------------------------------");
    for arity in [4usize, 8, 16] {
        let supplied = constraint::constraint_eval(arity, &[(10, arity)]).len();
        let derived = constraint::constraint_eval_batched(arity, &[(10, arity)]).len();
        println!(
            "  arity {arity:>2}, 10 constraints:  supplied {supplied:>10} B   derived {derived:>10} B   \
             ({:+.1}%)",
            100.0 * (derived as f64 - supplied as f64) / supplied as f64
        );
    }
    println!();
}

/// The batched form with values above the randomness, as `close` calls it.
#[test]
fn batched_steps_over_what_sits_above() {
    let mut rng = ChaCha20Rng::seed_from_u64(64);
    let total = 4usize;
    let r: Vec<[u32; 4]> = (0..total).map(|_| rand_ef(&mut rng)).collect();
    let shape = [(2usize, 4usize), (3, 2)];
    let groups: Vec<([u32; 4], Vec<[u32; 4]>, usize)> = shape
        .iter()
        .map(|&(n, arity)| {
            (rand_ef(&mut rng), (0..n).map(|_| rand_ef(&mut rng)).collect(), arity)
        })
        .collect();
    let want = reference::constraint_eval_batched(&r, &groups);
    let shape_pairs: Vec<(usize, usize)> = shape.to_vec();

    for under in 0..3usize {
        let above: Vec<[u32; 4]> = (0..under).map(|_| rand_ef(&mut rng)).collect();
        let got = run(script! {
            { batched_groups_to_altstack(&groups) }
            { push_randomness(&r) }
            for x in above.iter() { { push_ef(*x) } }
            { constraint::constraint_eval_batched_at(total, &shape_pairs, under) }
        });
        assert_eq!(got.len(), 4 * (under + 1), "under = {under}: wrong stack shape");
        assert_eq!(&got[..4 * under], above.concat().as_slice(),
                   "under = {under}: the values above the randomness were disturbed");
        assert_eq!(&got[4 * under..], want.as_slice(), "under = {under}: wrong weight");
    }
}
