//! The composed verifier: the transcript spine runs, and the closing identity
//! rejects.
//!
//! Both properties are new. The spine used to be emitted and measured but never
//! executed, and the closing identity used to be applied to a product the test
//! had just computed, so it could not fail.

use bitcoin_script::{define_pushable, script};
use poseidon2::reference as pf;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use whir::reference;
use whir::verifier::{self, Config, Round};

define_pushable!();

fn rand_f(rng: &mut ChaCha20Rng) -> u32 {
    rng.random_range(0..poseidon2::constants::P)
}
fn rand_ef(rng: &mut ChaCha20Rng) -> [u32; 4] {
    core::array::from_fn(|_| rand_f(rng))
}
fn push_ef(v: [u32; 4]) -> bitcoin::ScriptBuf {
    script! { for x in v { {x} } }
}

/// Load the altstack so that `items` pops in the order given.
///
/// The altstack is LIFO, so the first value consumed has to be pushed last.
fn push_altstack(items: &[u32]) -> bitcoin::ScriptBuf {
    script! { for x in items.iter().rev() { {*x} OP_TOALTSTACK } }
}

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

fn run_ok(s: bitcoin::ScriptBuf) -> Vec<u32> {
    let info = bitcoin_scriptexec::execute_script(s);
    assert!(info.error.is_none(), "errored: {:?} at {:?}", info.error, info.last_opcode);
    (0..info.final_stack.len()).map(|i| decode(&info.final_stack.get(i)) as u32).collect()
}

fn run_rejects(s: bitcoin::ScriptBuf, why: &str) {
    let info = bitcoin_scriptexec::execute_script(s);
    assert!(info.error.is_some(), "{why}: the script accepted");
}

// ---------------------------------------------------------------------------
// The closing identity
// ---------------------------------------------------------------------------

/// `claimed == weight * f(r)` over the quartic extension, and nothing else.
///
/// The previous version of this test pushed `a`, `b` and `a*b` and then checked
/// `a*b == a*b`, which holds for every proof there is. It also compared a single
/// coefficient, leaving a base-field equality worth ~31 bits where the extension
/// exists to provide ~124.
#[test]
fn final_check_accepts_only_the_right_value() {
    let mut rng = ChaCha20Rng::seed_from_u64(21);
    for _ in 0..8 {
        let weight = rand_ef(&mut rng);
        let f_at_r = rand_ef(&mut rng);
        let claimed = pf::ext4::mul(weight, f_at_r);

        run_ok(script! {
            { push_ef(claimed) } { push_ef(weight) } { push_ef(f_at_r) }
            { verifier::final_check() }
            OP_TRUE
        });

        // Every coefficient is load-bearing: perturbing any one must abort.
        for i in 0..4 {
            let mut bad = claimed;
            bad[i] = pf::add(bad[i], 1);
            run_rejects(
                script! {
                    { push_ef(bad) } { push_ef(weight) } { push_ef(f_at_r) }
                    { verifier::final_check() }
                    OP_TRUE
                },
                &format!("claimed coefficient {i} was perturbed"),
            );
        }

        // And the weight is not decorative.
        let mut bad_w = weight;
        bad_w[0] = pf::add(bad_w[0], 1);
        run_rejects(
            script! {
                { push_ef(claimed) } { push_ef(bad_w) } { push_ef(f_at_r) }
                { verifier::final_check() }
                OP_TRUE
            },
            "the batching weight was perturbed",
        );
    }
}

// ---------------------------------------------------------------------------
// The transcript spine
// ---------------------------------------------------------------------------

/// A small instance, chosen so the whole transcript fits in a test.
fn small() -> Config {
    Config {
        initial_folding_factor: 2,
        initial_ood_samples: 1,
        rounds: vec![Round { folding_factor: 2, num_queries: 3, log_domain_size: 6, ood_samples: 1, row_len: 4, domain_gen: 7 }],
        final_round: Round { folding_factor: 2, num_queries: 3, log_domain_size: 4, ood_samples: 0, row_len: 4, domain_gen: 11 },
        final_sumcheck_rounds: 2,
        final_poly_vars: 2,
    }
}

/// The transcript that `verify` consumes, and the state and claim it should
/// A committed tree, and the openings the verifier will ask it for.
///
/// The script now checks a query against the *absorbed commitment*, so the test
/// can no longer hand it a root and a matching path: every query in a round has
/// to reach the same root, which means building an actual tree.
struct Tree {
    root: [u32; 8],
    leaves: Vec<[u32; 8]>,
    /// `levels[0]` is the leaves; the last level is the pair under the root.
    levels: Vec<Vec<[u32; 8]>>,
    rows: Vec<Vec<u32>>,
}

/// A config whose single main-loop round has no shift queries.
///
/// WHIR's per-round combination is
/// `sigma_i = h_{i-1,k}(alpha) + gamma_i*y_{i,0} + sum_j gamma_i^{j+1}*g_{i-1}(z_{i,j})`.
/// Dropping the shift queries leaves exactly the OOD batch, which the mirror can
/// compute exactly -- the `g(z_j)` terms would need a fold of the queried rows.
/// Two OOD samples per commitment keep the derived constraints non-trivial.
fn query_free() -> Config {
    Config {
        initial_folding_factor: 2,
        initial_ood_samples: 2,
        rounds: vec![Round { folding_factor: 2, num_queries: 0, log_domain_size: 6, ood_samples: 2, row_len: 4, domain_gen: 7 }],
        final_round: Round { folding_factor: 2, num_queries: 0, log_domain_size: 4, ood_samples: 0, row_len: 4, domain_gen: 11 },
        final_sumcheck_rounds: 2,
        final_poly_vars: 2,
    }
}

fn build_tree(depth: usize, row_len: usize, rng: &mut ChaCha20Rng) -> Tree {
    let rows: Vec<Vec<u32>> = (0..(1usize << depth))
        .map(|_| (0..row_len).map(|_| rand_f(rng)).collect())
        .collect();
    let leaves: Vec<[u32; 8]> = rows.iter().map(|r| poseidon2::reference::hash_row(r)).collect();
    let mut levels = vec![leaves.clone()];
    while levels.last().expect("non-empty").len() > 1 {
        let below = levels.last().expect("non-empty");
        let up: Vec<[u32; 8]> = below
            .chunks(2)
            .map(|p| poseidon2::reference::compress(&p[0], &p[1]))
            .collect();
        levels.push(up);
    }
    let root = levels.last().expect("non-empty")[0];
    Tree { root, leaves, levels, rows }
}

impl Tree {
    /// The siblings for `index`, deepest level first — the order the walk reads.
    fn siblings(&self, index: usize) -> Vec<[u32; 8]> {
        let mut out = Vec::new();
        let mut i = index;
        for level in self.levels.iter().take(self.levels.len() - 1) {
            out.push(level[i ^ 1]);
            i >>= 1;
        }
        out
    }
}

/// The coordinates of folding randomness a schedule produces: one per sumcheck
/// round, which is what `sumcheck_rounds_fs_keep` leaves on the stack.
fn total_folding_vars(cfg: &Config) -> usize {
    cfg.initial_folding_factor
        + cfg.rounds.iter().map(|r| r.folding_factor).sum::<usize>()
        + cfg.final_sumcheck_rounds
}

/// reach. Mirrors the script step for step in plain Rust.
struct Spine {
    items: Vec<u32>,
    claim: [u32; 4],
    state: [u32; 16],
    /// Every round's folding randomness, concatenated in round order.
    randomness: Vec<[u32; 4]>,
    /// The final polynomial, which `verify` keeps a copy of because the closing
    /// identity evaluates it.
    final_poly: Vec<[u32; 4]>,
    /// The constraint groups the schedule derives: per group, its batching
    /// challenge, its scalars in sampling order, and its arity.
    groups: Vec<([u32; 4], Vec<[u32; 4]>, usize)>,
    /// The same chain, threaded the way WHIR's decision phase 2(c) requires:
    /// before each main-loop round's sumcheck the claim becomes
    /// `sigma_i = h_{i-1,k}(alpha) + gamma_i*y_{i,0} + sum_j gamma_i^{j+1}*g(z_j)`.
    /// `verify` never performs that combination, so this differs from `claim`.
    /// Only faithful for rounds with no shift queries: the `g(z_j)` terms need a
    /// fold the mirror does not compute, so the paper-faithful test uses a
    /// query-free round where the combination is exactly the OOD batch.
    paper_claim: [u32; 4],
}

fn build_spine(cfg: &Config, rng: &mut ChaCha20Rng, state0: [u32; 16], claim0: [u32; 4]) -> Spine {
    let mut items = Vec::new();
    let mut state = state0;
    let mut claim = claim0;
    let mut paper_claim = claim0;

    let mut randomness: Vec<[u32; 4]> = Vec::new();
    let sumcheck = |n: usize, items: &mut Vec<u32>, state: &mut [u32; 16], claim: &mut [u32; 4], paper_claim: &mut [u32; 4], rng: &mut ChaCha20Rng, randomness: &mut Vec<[u32; 4]>| {
        for _ in 0..n {
            let (c0, c_inf) = (rand_ef(rng), rand_ef(rng));
            items.extend_from_slice(&c0);
            items.extend_from_slice(&c_inf);
            let (next, r) = reference::sumcheck_round_fs(state, *claim, c0, c_inf);
            *claim = next;
            // The paper-faithful chain runs over the same emitted polynomials and
            // the same challenge; only the claim it starts from differs.
            *paper_claim = reference::sumcheck_round(*paper_claim, c0, c_inf, r);
            randomness.push(r);
        }
    };
    let absorb = |n: usize, items: &mut Vec<u32>, state: &mut [u32; 16], rng: &mut ChaCha20Rng| -> Vec<u32> {
        let vals: Vec<u32> = (0..n).map(|_| rand_f(rng)).collect();
        items.extend_from_slice(&vals);
        for block in vals.chunks(reference::RATE) {
            reference::duplexing(state, block);
        }
        vals
    };

    // Every query in a round has to reach a committed root, so the mirror builds
    // actual trees. There is one more commitment than there are rounds: the
    // initial codeword, which round 0 opens, and then one per round, the last of
    // which the final proximity test opens. `trees[i]` is the codeword *opened*
    // at step `i`, and it is absorbed one step earlier.
    let mut trees: Vec<Tree> = Vec::with_capacity(cfg.rounds.len() + 1);
    for r in cfg.rounds.iter().chain(core::iter::once(&cfg.final_round)) {
        trees.push(build_tree(r.log_domain_size, r.row_len, rng));
    }

    // The openings for one round: indices sampled from the rate, `RATE` of them
    // per squeeze, then the siblings deepest-last and the row.
    // A query opening, and the constraint scalar it produces: the folded domain
    // generator raised to the sampled index, embedded in the extension.
    let queries = |r: &Round,
                   tree: &Tree,
                   items: &mut Vec<u32>,
                   state: &mut [u32; 16],
                   scalars: &mut Vec<[u32; 4]>| {
        for q in 0..r.num_queries {
            let slot = q % reference::RATE;
            if q > 0 && slot == 0 {
                reference::squeeze(state);
            }
            let index = reference::sample_bits(state[slot], r.log_domain_size) as usize;
            for sib in tree.siblings(index).iter().rev() {
                items.extend_from_slice(sib);
            }
            items.extend_from_slice(&tree.rows[index]);
            let mut g = 1u32;
            for _ in 0..index {
                g = poseidon2::reference::mul(g, r.domain_gen);
            }
            scalars.push([g, 0, 0, 0]);
        }
    };

    // A group's batching challenge: a fresh squeeze, then the first four rate
    // slots, matching what the script emits.
    let batching = |state: &mut [u32; 16]| -> [u32; 4] {
        let rate = reference::squeeze(state);
        [rate[0], rate[1], rate[2], rate[3]]
    };

    // Commit phase: the initial root and its out-of-domain samples.
    let commit = |t: &Tree, items: &mut Vec<u32>, state: &mut [u32; 16]| {
        items.extend_from_slice(&t.root);
        for block in t.root.chunks(reference::RATE) {
            reference::duplexing(state, block);
        }
    };
    let m = total_folding_vars(cfg);
    let mut groups: Vec<([u32; 4], Vec<[u32; 4]>, usize)> = Vec::new();

    commit(&trees[0], &mut items, &mut state);
    let mut scalars: Vec<[u32; 4]> = Vec::new();
    for _ in 0..cfg.initial_ood_samples {
        // The point is sampled from the rate the previous absorb produced, and
        // only then is the answer absorbed. Sampling reads the state without
        // permuting, so the mirror only has to keep the order -- and to record
        // the point, which is now a constraint the closing check will evaluate.
        scalars.push([state[0], state[1], state[2], state[3]]);
        let _ = absorb(4, &mut items, &mut state, rng);
    }
    // The initial commitment has every variable, so its constraint reads all of R.
    let chi = batching(&mut state);
    scalars.push(chi);
    groups.push((chi, scalars[..scalars.len() - 1].to_vec(), m));
    sumcheck(cfg.initial_folding_factor, &mut items, &mut state, &mut claim, &mut paper_claim, rng, &mut randomness);
    let mut r_len = cfg.initial_folding_factor;

    for (i, r) in cfg.rounds.iter().enumerate() {
        let arity = m - r_len;
        // Absorb the *next* codeword's root, then open the previous one.
        commit(&trees[i + 1], &mut items, &mut state);
        let mut scalars: Vec<[u32; 4]> = Vec::new();
        let mut ood_answers: Vec<[u32; 4]> = Vec::new();
        for _ in 0..r.ood_samples {
            scalars.push([state[0], state[1], state[2], state[3]]);
            // The absorbed value *is* the round's OOD reply y_{i,0}.
            let y = absorb(4, &mut items, &mut state, rng);
            ood_answers.push([y[0], y[1], y[2], y[3]]);
        }
        queries(r, &trees[i], &mut items, &mut state, &mut scalars);
        let chi = batching(&mut state);
        // WHIR decision phase 2(c): the claim entering this round's sumcheck is
        // the previous round's ending value batched with the OOD reply (and, for
        // a round with shift queries, the folded shift answers -- which is why
        // the paper-faithful instance uses a query-free round).
        paper_claim = reference::combine_answers(paper_claim, chi, &ood_answers);
        groups.push((chi, scalars, arity));
        sumcheck(r.folding_factor, &mut items, &mut state, &mut claim, &mut paper_claim, rng, &mut randomness);
        r_len += r.folding_factor;
    }
    let poly_start = items.len();
    let _ = absorb(4 << cfg.final_poly_vars, &mut items, &mut state, rng);
    let final_poly: Vec<[u32; 4]> = items[poly_start..]
        .chunks(4)
        .map(|c| [c[0], c[1], c[2], c[3]])
        .collect();
    // The final proximity test checks its answers against the final polynomial
    // directly rather than accumulating a constraint, so its scalars go nowhere.
    let mut unused = Vec::new();
    queries(
        &cfg.final_round,
        trees.last().expect("one per round plus one"),
        &mut items,
        &mut state,
        &mut unused,
    );
    sumcheck(cfg.final_sumcheck_rounds, &mut items, &mut state, &mut claim, &mut paper_claim, rng, &mut randomness);

    Spine { items, claim, state, randomness, final_poly, groups, paper_claim }
}

/// The spine executes, and lands where the reference does.
///
/// This is the property the module previously lacked entirely: `verify` was
/// emitted, measured with `.len()`, and never handed to the interpreter. It
/// could not have run — an `absorb` leaves the sixteen-element state where the
/// old `sumcheck_round` expected `claim c0 c_inf r`, so the schedule would have
/// consumed sponge state as sumcheck operands.
#[test]
fn transcript_spine_executes_and_matches_the_reference() {
    let mut rng = ChaCha20Rng::seed_from_u64(22);
    let cfg = small();
    let state0: [u32; 16] = core::array::from_fn(|_| rand_f(&mut rng));
    let claim0 = rand_ef(&mut rng);
    let want = build_spine(&cfg, &mut rng, state0, claim0);

    let got = run_ok(script! {
        { push_altstack(&want.items) }
        { push_ef(claim0) }
        for s in state0 { {s} }
        { verifier::verify(&cfg) }
    });

    let m = total_folding_vars(&cfg);
    let f = 4 * (1usize << cfg.final_poly_vars);
    let carried = 4 * verifier::carried_scalars(&cfg);
    assert_eq!(got.len(), carried + f + 4 * m + 4 + 16, "unexpected stack shape");

    // The carried constraint scalars, in the order the transcript sampled them:
    // per group, its scalars and then its batching challenge.
    let mut want_scalars: Vec<u32> = Vec::new();
    for (chi, scalars, _) in want.groups.iter() {
        for u in scalars {
            want_scalars.extend_from_slice(u);
        }
        want_scalars.extend_from_slice(chi);
    }
    assert_eq!(&got[..carried], want_scalars.as_slice(),
               "the carried constraint scalars are wrong, or in the wrong order");
    assert_eq!(&got[carried..carried + f], want.final_poly.concat().as_slice(),
               "the kept final polynomial is wrong, or in the wrong place");
    assert_eq!(&got[carried + f..carried + f + 4 * m], want.randomness.concat().as_slice(),
               "the folding randomness is not contiguous beneath the claim");
    assert_eq!(&got[carried + f + 4 * m..carried + f + 4 * m + 4], &want.claim, "claim disagrees");
    assert_eq!(&got[carried + f + 4 * m + 4..], &want.state, "sponge state disagrees");
}

/// Changing one byte of the transcript changes the claim the spine reaches.
///
/// A verifier that ended on an equality against this claim would therefore
/// reject the tampered proof. That is the property the derived challenges buy;
/// with challenges supplied as hints the prover could restore any target.
#[test]
fn transcript_spine_is_sensitive_to_every_absorbed_value() {
    let mut rng = ChaCha20Rng::seed_from_u64(23);
    let cfg = small();
    let state0: [u32; 16] = core::array::from_fn(|_| rand_f(&mut rng));
    let claim0 = rand_ef(&mut rng);
    let want = build_spine(&cfg, &mut rng, state0, claim0);

    // Probe a spread of positions rather than all of them; the transcript is
    // long and each run executes a full schedule of permutations.
    let probes = [0usize, 7, want.items.len() / 2, want.items.len() - 1];
    for &i in probes.iter() {
        let mut items = want.items.clone();
        items[i] = pf::add(items[i], 1);

        let info = bitcoin_scriptexec::execute_script(script! {
            { push_altstack(&items) }
            { push_ef(claim0) }
            for s in state0 { {s} }
            { verifier::verify(&cfg) }
        });
        // Two ways for the transcript to notice, and which one applies depends
        // on what was perturbed. A value inside a Merkle opening breaks the walk
        // and the script aborts; a value that is only absorbed moves a squeezed
        // challenge, which moves the chained claim. Accepting *either* is the
        // honest assertion -- demanding only the second would have failed the
        // moment the query openings were composed in, for the good reason that
        // the tamper is now caught earlier.
        if info.error.is_some() {
            continue;
        }
        let got: Vec<u32> = (0..info.final_stack.len())
            .map(|k| decode(&info.final_stack.get(k)) as u32)
            .collect();
        let m = total_folding_vars(&cfg);
        let f = 4 * (1usize << cfg.final_poly_vars) + 4 * verifier::carried_scalars(&cfg);
        assert_ne!(
            &got[f + 4 * m..f + 4 * m + 4],
            &want.claim,
            "perturbing transcript position {i} was neither rejected nor moved the claim"
        );
    }
}

/// The count matches what the spine actually emits, for the part it covers.
///
/// `permutation_count` prices the whole schedule including the query openings
/// the spine does not yet compose, so the comparison is against the spine's
/// share: absorbs and sumcheck rounds, one permutation each.
///
/// # Why this is a difference and not a division
///
/// The obvious test is `verify(&cfg).len() / one`, and it worked until the
/// arithmetic grew. A sumcheck round is one permutation *plus* about 95 kB of
/// extension-field arithmetic, and six rounds of that is itself more than a
/// permutation -- so the quotient started reporting one too many and would have
/// been "fixed" by adjusting the prediction, which is exactly the wrong
/// direction. Differences isolate the permutation from the arithmetic around it:
/// two configurations that differ by one absorb differ in length by one
/// permutation and nothing else.
#[test]
fn one_more_absorb_is_one_more_permutation() {
    let one = poseidon2::permutation::permute().len();

    let bump = |mutate: &dyn Fn(&mut Config), what: &str, expect: usize| {
        let base = small();
        let mut grown = small();
        mutate(&mut grown);
        assert_eq!(
            verifier::permutation_count(&grown) - verifier::permutation_count(&base),
            expect,
            "{what}: the accounting predicts a different number of permutations"
        );
        let delta = verifier::verify(&grown).len() - verifier::verify(&base).len();
        let arithmetic = delta - expect * one;
        assert!(
            delta >= expect * one && arithmetic < one / 4,
            "{what}: emitted {delta} B for {expect} permutation(s), \
             which is {arithmetic} B of arithmetic -- too much to be bookkeeping"
        );
    };

    // An out-of-domain sample is a squeeze off the current rate and a
    // four-element absorb, so exactly one duplexing.
    bump(&|c| c.rounds[0].ood_samples += 1, "one more OOD sample", 1);
    // Doubling the final polynomial doubles the blocks it takes to absorb it.
    bump(
        &|c| {
            c.final_poly_vars += 1;
            c.final_sumcheck_rounds += 1;
        },
        "one more final variable",
        // Twice the evaluations is twice the rate blocks, and one more sumcheck
        // round to bind the new variable.
        (4usize << small().final_poly_vars).div_ceil(reference::RATE) + 1,
    );
}

/// The absolute count, with the arithmetic stated rather than hidden.
///
/// Now that the query openings are composed, this covers the whole verifier and
/// not just its transcript -- which is why the arithmetic share drops: the
/// sumcheck rounds are the same size, but there is far more permutation around
/// them.
///
/// `permutation_count` is what decides whether a WHIR verifier fits on Bitcoin,
/// so it is worth knowing how much of the emitted script it fails to describe.
#[test]
fn report_verifier_arithmetic() {
    let cfg = small();
    let one = poseidon2::permutation::permute().len();
    let sumcheck_rounds =
        cfg.initial_folding_factor + cfg.rounds.iter().map(|r| r.folding_factor).sum::<usize>()
            + cfg.final_sumcheck_rounds;
    // One squeeze per constraint group, for its batching challenge.
    let challenges = 1 + cfg.rounds.len();
    let absorbs: usize = poseidon2::merkle::DIGEST.div_ceil(reference::RATE)
        + cfg.initial_ood_samples
        + cfg
            .rounds
            .iter()
            .map(|r| poseidon2::merkle::DIGEST.div_ceil(reference::RATE) + r.ood_samples)
            .sum::<usize>()
        + (4usize << cfg.final_poly_vars).div_ceil(reference::RATE);
    // The queries are the rest, and they are the reason any of this is
    // expensive: a Merkle level and a leaf hash each, per query.
    let queries: usize = cfg
        .rounds
        .iter()
        .chain(core::iter::once(&cfg.final_round))
        .map(|r| {
            r.num_queries.div_ceil(reference::RATE).saturating_sub(1)
                + r.num_queries * (r.log_domain_size + r.row_len.div_ceil(8))
        })
        .sum();
    let predicted = sumcheck_rounds + absorbs + queries + challenges;
    let emitted = verifier::verify(&cfg).len();
    let arithmetic = emitted - predicted * one;
    println!(
        "\n  verifier: {predicted} permutations = {} B, emitted {emitted} B\n  \
         ({sumcheck_rounds} sumcheck, {absorbs} absorb, {queries} query, \
{challenges} challenge)\n  \
         arithmetic and bookkeeping: {arithmetic} B ({:.1}% of the whole)\n",
        predicted * one,
        100.0 * arithmetic as f64 / emitted as f64
    );
    assert!(
        arithmetic < emitted / 8,
        "arithmetic is now more than an eighth of the spine; the cost law needs revisiting"
    );
}

/// A realistic instance: a 2^20 trace, rate 1/2, folding factor 4, ~20 queries.
fn example() -> Config {
    let mut rounds = Vec::new();
    let mut log_domain = 21usize;
    for _ in 0..4 {
        rounds.push(Round {
            folding_factor: 4,
            num_queries: 20,
            log_domain_size: log_domain,
            ood_samples: 2,
            // 2^folding_factor extension elements: the fibre a shift query reads.
            row_len: 4 * (1 << 4),
            domain_gen: 7,
        });
        log_domain -= 4;
    }
    Config {
        initial_folding_factor: 4,
        initial_ood_samples: 2,
        rounds,
        final_round: Round {
            folding_factor: 4,
            num_queries: 20,
            log_domain_size: log_domain,
            ood_samples: 0,
            row_len: 4 * (1 << 4),
            domain_gen: 11,
        },
        final_sumcheck_rounds: 4,
        final_poly_vars: 4,
    }
}

#[test]
fn report_verifier_size() {
    let cfg = example();
    let perms = verifier::permutation_count(&cfg);
    let one = poseidon2::permutation::permute().len();

    const BLOCK: usize = 4_000_000;

    let (mut paths, mut leaves) = (0usize, 0usize);
    for r in cfg.rounds.iter().chain(core::iter::once(&cfg.final_round)) {
        paths += r.num_queries * r.log_domain_size;
        leaves += r.num_queries * r.row_len.div_ceil(poseidon2::merkle::HASH_RATE);
    }
    let queries = paths + leaves;

    println!("\n  WHIR verifier for a 2^20 trace, 20 queries, folding factor 4");
    println!("  -----------------------------------------------------------");
    println!("  permutations                 {perms:>12}");
    println!("    of which Merkle paths      {paths:>12}");
    println!("    of which leaf hashing      {leaves:>12}");
    println!("    of which transcript        {:>12}", perms - queries);
    println!("  bytes                        {:>12}", perms * one);
    println!("  blocks                       {:>12.1}", (perms * one) as f64 / BLOCK as f64);
    println!("\n  query share                  {:>11.1}%", 100.0 * queries as f64 / perms as f64);
    println!("  transcript share             {:>11.1}%", 100.0 * (perms - queries) as f64 / perms as f64);
    println!();
}

/// Binding a row to its leaf is not free, and was never priced.
///
/// The row-to-leaf hash closed a real gap -- without it a spender could
/// authenticate the committed leaf and fold a different row -- but the
/// accounting only ever counted the path. At folding factor 4 a row is sixteen
/// extension elements, so sixty-four base elements, so eight permutations per
/// query on top of the twenty-one the path costs. That deserves its own number
/// rather than hiding inside a total.
#[test]
fn report_leaf_hashing_cost() {
    let cfg = example();
    let one = poseidon2::permutation::permute().len();
    let leaves: usize = cfg
        .rounds
        .iter()
        .chain(core::iter::once(&cfg.final_round))
        .map(|r| r.num_queries * r.row_len.div_ceil(poseidon2::merkle::HASH_RATE))
        .sum();
    let perms = verifier::permutation_count(&cfg);
    println!(
        "\n  leaf hashing: {leaves} permutations = {} B, {:.1}% of the verifier\n  \
         (a row of {} base elements is {} permutations, per query)\n",
        leaves * one,
        100.0 * leaves as f64 / perms as f64,
        cfg.final_round.row_len,
        cfg.final_round.row_len.div_ceil(poseidon2::merkle::HASH_RATE)
    );
}

// ---------------------------------------------------------------------------
// The closing identity, on the stack the spine leaves
// ---------------------------------------------------------------------------

/// An `EF` element as Plonky3 sees it, so the test can use its inverse.
fn to_ef(c: [u32; 4]) -> Ef {
    use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
    Ef::from_basis_coefficients_fn(|i| p3_koala_bear::KoalaBear::from_u32(c[i]))
}

type Ef = p3_field::extension::BinomialExtensionField<p3_koala_bear::KoalaBear, 4>;

fn of_ef(x: Ef) -> [u32; 4] {
    use p3_field::{BasedVectorSpace, PrimeField32};
    let s: &[p3_koala_bear::KoalaBear] = x.as_basis_coefficients_slice();
    core::array::from_fn(|i| s[i].as_canonical_u32())
}

/// Lay one constraint on the altstack: the weight, then the coordinates.
fn constraint_to_altstack(w: [u32; 4], z: &[[u32; 4]]) -> bitcoin::ScriptBuf {
    script! {
        { push_ef(w) } for _ in 0..4 { OP_TOALTSTACK }
        for c in z.iter() { { push_ef(*c) } for _ in 0..4 { OP_TOALTSTACK } }
    }
}

/// Build a spend that satisfies the closing identity, and the pieces of it.
struct Closing {
    spine: Spine,
    weight: [u32; 4],
    point: Vec<[u32; 4]>,
}

fn build_closing(cfg: &Config, rng: &mut ChaCha20Rng, state0: [u32; 16], claim0: [u32; 4]) -> Closing {
    build_closing_for(cfg, rng, state0, claim0, false)
}

/// Build a closing instance whose statement is solved against one of the two
/// chains: the one `verify` actually produces (`paper == false`), or the one
/// WHIR's decision phase 2(c) requires (`paper == true`).
///
/// The emitted transcript is identical either way -- the combination changes how
/// a verifier *threads* the claim, not what the prover sends -- so the two
/// instances differ only in which claim the constraint was solved to satisfy.
fn build_closing_for(cfg: &Config, rng: &mut ChaCha20Rng, state0: [u32; 16], claim0: [u32; 4], paper: bool) -> Closing {
    let spine = build_spine(cfg, rng, state0, claim0);
    let m = total_folding_vars(cfg);
    assert_eq!(spine.randomness.len(), m);

    // The final polynomial is evaluated at the tail of the randomness.
    let v = cfg.final_poly_vars;
    let r_fin = &spine.randomness[m - v..];
    let f_at_r = reference::eval_multilinear(&spine.final_poly, r_fin);

    // Everything the transcript produced, evaluated at the randomness it also
    // produced. Nothing here is supplied.
    let derived = reference::constraint_eval_batched(&spine.randomness, &spine.groups);
    // If this were zero the composed test would still pass and would be saying
    // nothing about the derived half of the weight.
    assert_ne!(derived, [0u32; 4], "the derived constraints contribute nothing");
    assert!(
        spine.groups.iter().map(|(_, s, _)| s.len()).sum::<usize>() >= 4,
        "too few derived constraints for the test to mean much"
    );

    // On top of it, one constraint over every variable: the evaluation query
    // the whole protocol exists to answer. Its point is the statement, not a
    // prover choice; its weight is solved for so that the instance is a *valid*
    // one, the same way a prover would produce a proof that verifies.
    let point: Vec<[u32; 4]> = (0..m).map(|_| rand_ef(rng)).collect();
    let e = reference::eq_eval(&point, &spine.randomness);
    let denom = to_ef(e) * to_ef(f_at_r);
    assert_ne!(
        denom,
        <Ef as p3_field::PrimeCharacteristicRing>::ZERO,
        "degenerate instance: eq or the final evaluation vanished"
    );
    // claim = (derived + weight*e) * f_at_r  =>  weight = (claim/f_at_r - derived)/e
    let against = if paper { spine.paper_claim } else { spine.claim };
    let target = to_ef(against) * p3_field::Field::inverse(&to_ef(f_at_r));
    let weight = of_ef((target - to_ef(derived)) * p3_field::Field::inverse(&to_ef(e)));

    // The reference agrees the identity holds, independently of any script.
    let supplied = reference::constraint_eval(&spine.randomness, &[vec![(weight, point.clone())]]);
    let total = pf::ext4::add(derived, supplied);
    assert_eq!(
        of_ef(to_ef(total) * to_ef(f_at_r)),
        against,
        "the constructed instance does not satisfy w(R) * f_M(r_fin) == claim"
    );

    Closing { spine, weight, point }
}

fn closing_spend(
    cfg: &Config,
    c: &Closing,
    state0: [u32; 16],
    claim0: [u32; 4],
    items: &[u32],
) -> bitcoin::ScriptBuf {
    let m = total_folding_vars(cfg);
    script! {
        // The constraint list goes down first, beneath the whole transcript, so
        // that it is what remains once the transcript has been consumed.
        { constraint_to_altstack(c.weight, &c.point) }
        { push_altstack(items) }
        { push_ef(claim0) }
        for s in state0 { {s} }
        { verifier::verify_and_close(cfg, &[(1, m)]) }
        OP_TRUE
    }
}

/// The composed verifier runs to completion on a satisfying instance.
///
/// This is the first time the schedule ends in a *check* rather than in a
/// transcript: every value the identity multiplies together is derived inside
/// the script -- `R` from the sumcheck rounds, `f_M` from the copy the absorb
/// kept, `r_fin` from the tail of `R` -- and the only thing the spender chooses
/// is the constraint, which is the statement being proved.
#[test]
fn the_composed_verifier_closes() {
    let mut rng = ChaCha20Rng::seed_from_u64(24);
    let cfg = small();
    let state0: [u32; 16] = core::array::from_fn(|_| rand_f(&mut rng));
    let claim0 = rand_ef(&mut rng);
    let c = build_closing(&cfg, &mut rng, state0, claim0);

    let info = bitcoin_scriptexec::execute_script(closing_spend(&cfg, &c, state0, claim0, &c.spine.items));
    assert!(
        info.error.is_none(),
        "the closing identity was rejected: {:?} at {:?}",
        info.error,
        info.last_opcode
    );
}

/// The per-round combination WHIR's decision phase 2(c) requires is missing.
///
/// A round ends by folding its out-of-domain reply into the *next* target:
///
/// ```text
/// sigma_i := h_{i-1,k}(alpha_{i-1,k}) + gamma_i*y_{i,0} + sum_j gamma_i^{j+1}*g_{i-1}(z_{i,j})
/// ```
///
/// That is what `constraint::combine_answers` computes, and `verify` never calls
/// it: the claim carries over from one round's sumcheck to the next untouched,
/// while the OOD reply is absorbed and then dropped. The two instances below
/// share one transcript and differ only in which chain their statement was
/// solved against, so the pair isolates exactly that combination.
///
/// The control passes because the mirror reproduces `verify`'s own arithmetic.
/// The paper-faithful instance is rejected -- and a real proof is a
/// paper-faithful instance, which is why this is a completeness failure rather
/// than a soundness gap. Tracked as AppliedPQC/pqc-research#39.
#[test]
fn the_per_round_combination_is_missing() {
    let cfg = query_free();

    // Control: the statement is solved against the chain `verify` produces.
    let mut rng = ChaCha20Rng::seed_from_u64(31);
    let state0: [u32; 16] = core::array::from_fn(|_| rand_f(&mut rng));
    let claim0 = rand_ef(&mut rng);
    let control = build_closing_for(&cfg, &mut rng, state0, claim0, false);
    let info = bitcoin_scriptexec::execute_script(closing_spend(&cfg, &control, state0, claim0, &control.spine.items));
    assert!(
        info.error.is_none(),
        "the control instance must close: {:?} at {:?}",
        info.error,
        info.last_opcode
    );

    // The same transcript, with the statement solved against the paper's chain.
    let mut rng = ChaCha20Rng::seed_from_u64(31);
    let state0: [u32; 16] = core::array::from_fn(|_| rand_f(&mut rng));
    let claim0 = rand_ef(&mut rng);
    let paper = build_closing_for(&cfg, &mut rng, state0, claim0, true);

    // Same bytes on the wire: the combination is a verifier-side step.
    assert_eq!(paper.spine.items, control.spine.items, "the transcript must be identical");
    // ...and the combination has to actually move the claim, or this says nothing.
    assert_ne!(
        paper.spine.paper_claim, paper.spine.claim,
        "the OOD batch did not move the claim; the instance would be vacuous"
    );

    let info = bitcoin_scriptexec::execute_script(closing_spend(&cfg, &paper, state0, claim0, &paper.spine.items));
    assert!(
        info.error.is_some(),
        "verify_and_close accepted a paper-faithful instance -- the per-round \
         combination is present after all, and this test is obsolete"
    );
}

/// Everything the identity rests on is load-bearing.
///
/// The point of listing these separately is that each one is a distinct way for
/// the check to be vacuous, and this crate has shipped two of them before: a
/// closing check that compared a value with itself, and a chain whose challenges
/// the prover supplied.
#[test]
fn the_closing_identity_rejects_every_perturbation() {
    let mut rng = ChaCha20Rng::seed_from_u64(25);
    let cfg = small();
    let state0: [u32; 16] = core::array::from_fn(|_| rand_f(&mut rng));
    let claim0 = rand_ef(&mut rng);
    let c = build_closing(&cfg, &mut rng, state0, claim0);

    let rejects = |s: bitcoin::ScriptBuf, why: &str| {
        assert!(bitcoin_scriptexec::execute_script(s).error.is_some(), "{why}: accepted");
    };

    // The weight, and every coordinate of the point.
    for i in 0..4 {
        let mut bad = c.weight;
        bad[i] = pf::add(bad[i], 1);
        rejects(
            closing_spend(&cfg, &Closing { weight: bad, ..clone_closing(&c) }, state0, claim0, &c.spine.items),
            &format!("weight coefficient {i}"),
        );
    }
    for j in 0..c.point.len() {
        let mut bad = c.point.clone();
        bad[j][0] = pf::add(bad[j][0], 1);
        rejects(
            closing_spend(&cfg, &Closing { point: bad, ..clone_closing(&c) }, state0, claim0, &c.spine.items),
            &format!("point coordinate {j}"),
        );
    }
    // The initial claim, which the whole chain hangs from.
    let mut bad_claim = claim0;
    bad_claim[0] = pf::add(bad_claim[0], 1);
    rejects(closing_spend(&cfg, &c, state0, bad_claim, &c.spine.items), "the initial claim");

    // Any transcript value: it moves a squeezed challenge, which moves both the
    // chained claim and the randomness the constraint is evaluated at.
    for &i in [0usize, 7, c.spine.items.len() / 2, c.spine.items.len() - 1].iter() {
        let mut items = c.spine.items.clone();
        items[i] = pf::add(items[i], 1);
        rejects(closing_spend(&cfg, &c, state0, claim0, &items), &format!("transcript position {i}"));
    }
}

fn clone_closing(c: &Closing) -> Closing {
    Closing {
        spine: Spine {
            items: c.spine.items.clone(),
            claim: c.spine.claim,
            state: c.spine.state,
            randomness: c.spine.randomness.clone(),
            final_poly: c.spine.final_poly.clone(),
            groups: c.spine.groups.clone(),
            paper_claim: c.spine.paper_claim,
        },
        weight: c.weight,
        point: c.point.clone(),
    }
}

/// What closing costs, against the verifier it closes.
///
/// Priced from `permutation_count` rather than by building the script: now that
/// the query openings are composed, `verify(&example())` is three quarters of a
/// gigabyte of Bitcoin Script, and materialising it to call `.len()` is not a
/// reasonable thing for a test to do.
#[test]
fn report_closing_size() {
    let cfg = example();
    let m = cfg.total_folding_vars();
    let one = poseidon2::permutation::permute().len();
    let whole = verifier::permutation_count(&cfg) * one;
    let closing = verifier::close(&cfg, &[(1, m)]).len();
    println!(
        "\n  whole verifier ~{whole} B, closing {closing} B \
         ({:.3}% of it, 0 permutations)\n",
        100.0 * closing as f64 / whole as f64
    );
}

/// The closing check's inputs, before it multiplies them.
///
/// A single `OP_EQUALVERIFY` at the end says only that something disagreed.
/// Pinning `f_M(r_fin)` on its own -- and that the claim and the randomness are
/// where they were -- turns that into a location. It found the bug it was
/// written for: the coordinates were copied from the top down, and the altstack
/// being last-in-first-out meant `eval_multilinear` then read the point
/// backwards.
#[test]
fn the_closing_inputs_match_the_reference() {
    let mut rng = ChaCha20Rng::seed_from_u64(24);
    let cfg = small();
    let state0: [u32; 16] = core::array::from_fn(|_| rand_f(&mut rng));
    let claim0 = rand_ef(&mut rng);
    let c = build_closing(&cfg, &mut rng, state0, claim0);
    let m = total_folding_vars(&cfg);
    let v = cfg.final_poly_vars;
    let n_evals = 1usize << v;
    let lift = 4 * n_evals + 4 * m + 4 - 1;
    let carried = 4 * verifier::carried_scalars(&cfg);

    let got = run_ok(script! {
        { constraint_to_altstack(c.weight, &c.point) }
        { push_altstack(&c.spine.items) }
        { push_ef(claim0) }
        for s in state0 { {s} }
        { verifier::verify(&cfg) }
        for _ in 0..16 { OP_DROP }
        for _ in 0..(4 * n_evals) { { lift } OP_ROLL }
        for i in (0..v).rev() {
            { poseidon2::ext4::copy(n_evals + 1 + i) } { poseidon2::ext4::to_altstack() }
        }
        { whir::multilinear::eval_multilinear(v) }
    });
    let f_at_r = reference::eval_multilinear(&c.spine.final_poly, &c.spine.randomness[m - v..]);
    assert_eq!(&got[got.len() - 4..], &f_at_r, "f_M(r_fin) disagrees");
    assert_eq!(&got[got.len() - 8..got.len() - 4], &c.spine.claim, "the claim moved");
    assert_eq!(&got[carried..carried + 4 * m], c.spine.randomness.concat().as_slice(),
               "the randomness moved");
}

/// One query opening, in the position the schedule puts it in.
///
/// `open_query` had no test at all until now, which is how its stack contract
/// came to be unsatisfiable: it sampled the index with a pick that reaches into
/// the top sixteen slots while an opening sat on top of them.
#[test]
fn one_opening_authenticates_against_the_commitment() {
    let mut rng = ChaCha20Rng::seed_from_u64(30);
    let depth = 4usize;
    let row_len = 4usize;
    let tree = build_tree(depth, row_len, &mut rng);
    let state: [u32; 16] = core::array::from_fn(|_| rand_f(&mut rng));
    // Stand-ins for the randomness and the claim the commitment is buried under.
    let r_len = 2usize;
    let commit_depth = 16 + 4 + 4 * r_len + 8 - 1;

    for slot in [0usize, 3, 7] {
        let index = reference::sample_bits(state[slot], depth) as usize;
        let mut opening = Vec::new();
        for sib in tree.siblings(index).iter().rev() {
            opening.extend_from_slice(sib);
        }
        opening.extend_from_slice(&tree.rows[index]);

        let accepted = |root: [u32; 8], opening: &[u32]| {
            bitcoin_scriptexec::execute_script(script! {
                { push_altstack(opening) }
                for x in root { {x} }
                for _ in 0..(4 * r_len) { 7 }
                for _ in 0..4 { 9 }
                for s in state { {s} }
                { verifier::open_query(slot, depth, row_len, commit_depth) }
                OP_TRUE
            })
            .error
            .is_none()
        };

        assert!(accepted(tree.root, &opening), "slot {slot} (index {index}) was rejected");

        // A different committed root is what the walk is checked against, so
        // opening the same path under it must fail -- this is the property that
        // was missing when the root came from the witness.
        let mut wrong = tree.root;
        wrong[0] = pf::add(wrong[0], 1);
        assert!(!accepted(wrong, &opening), "slot {slot}: a wrong commitment was accepted");

        // And the row is bound to the leaf, not merely alongside it.
        let mut tampered = opening.clone();
        let last = tampered.len() - 1;
        tampered[last] = pf::add(tampered[last], 1);
        assert!(!accepted(tree.root, &tampered), "slot {slot}: a tampered row was accepted");
    }
}
