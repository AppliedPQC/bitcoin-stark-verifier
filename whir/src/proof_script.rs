//! The WHIR verifier for one proof, as a single Bitcoin Script.
//!
//! [`crate::reference::verify`] is the verifier in Rust, checked against
//! Plonky3's on real proofs. This builds the script that performs the same
//! verification: the transcript through the sponge, then the arithmetic on the
//! challenges the sponge produced. It is built *from* the proof: the schedule
//! of a transcript is data-dependent (STIR queries are drawn until enough are
//! distinct), and the openings' shape is the proof's, so the script is
//! specific to the proof it verifies. What it must not do is trust the proof:
//! every challenge is drawn from the script's own sponge, every opened row is
//! hashed and walked to the committed root, every rejected query draw is
//! checked to be one, and the closing identity is computed in full.
//!
//! # Stack
//!
//! The proof's data is pushed first and stays at the bottom, read by depth:
//! the transcript's inputs in consumption order (first consumed shallowest),
//! then the openings. Above it a *kept* region grows: every challenge the
//! sponge draws is buried there as it is drawn, and every value the arithmetic
//! wants back later (the running claim, the query indices, the folds, the STIR
//! points) is left there as it is computed. During the transcript the sponge
//! state sits on top of the kept region with its pending inputs above; once the
//! transcript is done the state is dropped and the arithmetic works on top of
//! the kept region with short-lived temporaries. The builder tracks the size of
//! each of these so a value's depth is always a computed number.
//!
//! The proof's size makes the stack far larger than Bitcoin's 1000-item limit
//! allows; a deployment would chunk the verification across transactions. That
//! constraint is orthogonal to whether the script verifies, which is what is
//! established here.

use crate::challenger;
use crate::constraint;
use crate::multilinear;
use crate::pruned::{self, Digest};
use crate::reference::{self, Challenges, Opening, Sponge, VerifyConfig, VerifyData};
use crate::sponge::{self, RATE, WIDTH};
use crate::sumcheck;
use crate::treepp::*;
use poseidon2::{ext4, field, merkle};

/// The built verifier.
pub struct Built {
    pub script: Script,
    /// The proof's data as the script reads it, `data[0]` shallowest.
    pub data: Vec<u32>,
    /// Permutations the transcript costs; the openings add `depth + 1` each.
    pub transcript_permutations: usize,
    pub challenges: Challenges,
}

/// Where the transcript put each prover message (stream index) and each
/// challenge (kept entry), walked in transcript order.
#[derive(Default, Debug)]
struct Layout {
    root: usize,
    ood_answers: Vec<usize>,
    evals: Vec<Vec<usize>>,
    initial_sumcheck: Vec<(usize, usize)>,
    rounds: Vec<RoundLayout>,
    final_poly: usize,
    final_sumcheck: Vec<(usize, usize)>,
    k_ood: Vec<usize>,
    k_claim: Vec<usize>,
    k_alpha: usize,
    k_initial_fold: Vec<usize>,
    k_final_draws: Vec<usize>,
    k_final_fold: Vec<usize>,
}

#[derive(Default, Debug)]
struct RoundLayout {
    root: usize,
    ood_answers: Vec<usize>,
    sumcheck: Vec<(usize, usize)>,
    k_ood: Vec<usize>,
    k_draws: Vec<usize>,
    k_combination: usize,
    k_fold: Vec<usize>,
}

/// One STIR query, with the draw that produced it and the index it became.
#[derive(Clone, Copy, Debug)]
struct Query {
    index: u32,
    /// Kept entry of the masked index, once the draw checks have run.
    entry: usize,
}

struct Builder {
    reference: reference::Challenger,
    pending: usize,
    available: usize,
    parts: Vec<Script>,
    data: Vec<u32>,
    /// Every sample the sponge drew, in order; one kept entry each.
    samples: Vec<u32>,
    /// Slots in the kept region.
    kept: usize,
    state: bool,
    /// Slots above the kept region (and the state, while present).
    temps: usize,
    permutations: usize,
}

const COMPARE_EF: usize = 4;

impl Builder {
    fn new() -> Self {
        Self {
            reference: reference::Challenger::new(),
            pending: 0,
            available: 0,
            parts: Vec::new(),
            data: Vec::new(),
            samples: Vec::new(),
            kept: 0,
            state: false,
            temps: 0,
            permutations: 0,
        }
    }

    fn emit(&mut self, s: Script) {
        self.parts.push(s);
    }

    /// Slots above the kept region.
    fn above(&self) -> usize {
        (if self.state { WIDTH + self.pending } else { 0 }) + self.temps
    }

    /// Depth of kept entry `e` (0 deepest).
    fn kept_depth(&self, e: usize) -> usize {
        assert!(e < self.kept, "kept entry {e} of {}", self.kept);
        self.kept - 1 - e + self.above()
    }

    /// Depth of data element `i`.
    fn data_depth(&self, i: usize) -> usize {
        assert!(i < self.data.len());
        i + self.kept + self.above()
    }

    // -- the sponge, as `transcript::Emitter` but keeping every draw --------

    fn duplex(&mut self) {
        let k = self.pending;
        self.emit(sponge::absorb(k));
        self.permutations += 1;
        self.pending = 0;
        self.available = RATE;
    }

    fn end_transcript(&mut self) {
        assert_eq!(self.pending, 0, "the transcript ends on a draw");
        assert_eq!(self.temps, 0);
        self.emit(script! { for _ in 0..WIDTH / 2 { OP_2DROP } });
        self.state = false;
    }

    // -- stack movement, after the transcript ---------------------------------

    /// Copy data elements `i..i+n` to the top, `data[i]` deepest.
    fn push_data(&mut self, i: usize, n: usize) {
        let base = self.data_depth(i);
        // Each pick raises the stack by one and targets one element deeper.
        self.emit(script! { for k in 0..n { { base + 2 * k } OP_PICK } });
        self.temps += n;
    }

    /// Copy kept entries `e..e+n` to the top, entry `e` deepest.
    fn push_kept(&mut self, e: usize, n: usize) {
        assert!(e + n <= self.kept);
        let d = self.kept_depth(e);
        self.emit(script! { for _ in 0..n { { d } OP_PICK } });
        self.temps += n;
    }

    /// Adopt the top `n` temporaries into the kept region; returns the entry
    /// of the deepest of them.
    fn bury(&mut self, n: usize) -> usize {
        assert!(!self.state, "burying is bookkeeping only once the state is gone");
        assert!(self.temps >= n);
        self.temps -= n;
        self.kept += n;
        self.kept - n
    }

    fn drop(&mut self, n: usize) {
        assert!(self.temps >= n);
        self.emit(script! { for _ in 0..n / 2 { OP_2DROP } if n % 2 == 1 { OP_DROP } });
        self.temps -= n;
    }

    fn push_ef_const(&mut self, x: [u32; 4]) {
        self.emit(script! { { x[0] } { x[1] } { x[2] } { x[3] } });
        self.temps += 4;
    }

    /// Lift the base element on top to the extension.
    fn lift(&mut self) {
        self.emit(script! { 0 0 0 });
        self.temps += 3;
    }

    fn ef_mul(&mut self) {
        self.emit(ext4::mul());
        self.temps -= 4;
    }

    fn ef_add(&mut self) {
        self.emit(ext4::add());
        self.temps -= 4;
    }

    /// `[a(4) b(1)] -> [a * b (4)]`, the base element scaling each coefficient.
    fn ef_mul_base(&mut self) {
        self.emit(script! {
            OP_TOALTSTACK
            for _ in 0..4 {
                3 OP_ROLL
                OP_FROMALTSTACK OP_DUP OP_TOALTSTACK
                { field::mul() }
            }
            OP_FROMALTSTACK OP_DROP
        });
        self.temps -= 1;
    }

    /// Require the two extension elements on top to be equal; both consumed.
    fn equal_verify_ef(&mut self) {
        self.emit(script! { for i in 0..COMPARE_EF { { COMPARE_EF - i } OP_ROLL OP_EQUALVERIFY } });
        self.temps -= 2 * COMPARE_EF;
    }

    // -- arithmetic on kept and data values ----------------------------------

    /// `sum_i chi^i e_i` by Horner, `chi` a kept EF and each `e_i` a data EF.
    fn batch(&mut self, chi: usize, evals: &[usize]) {
        let last = *evals.last().expect("a batch has a term");
        self.push_data(last, 4);
        for &e in evals.iter().rev().skip(1) {
            self.push_kept(chi, 4);
            self.ef_mul();
            self.push_data(e, 4);
            self.ef_add();
        }
    }

    /// One sumcheck round on the kept claim: `claim <- h(r)`.
    fn sumcheck_round(&mut self, claim: usize, c0: usize, c_inf: usize, r: usize) -> usize {
        self.push_kept(claim, 4);
        self.push_data(c0, 4);
        self.push_data(c_inf, 4);
        self.push_kept(r, 4);
        self.emit(sumcheck::sumcheck_round());
        self.temps -= 12;
        self.bury(4)
    }

    /// The draw checks of one query block: every sample below the rejection
    /// threshold is masked to an index and kept, in draw order, duplicates
    /// and all; one at or above it is verified to be and skipped. When the
    /// domain is no larger than the query count there are no draws and the
    /// queries are every position.
    fn query_draws(&mut self, draws: &[usize], bits: usize, num_queries: usize) -> Vec<Query> {
        assert!(bits <= reference::MAX_SINGLE_SAMPLE_BITS, "one draw per index");
        if num_queries >= 1 << bits {
            assert!(draws.is_empty());
            return (0..1u32 << bits)
                .map(|index| {
                    self.emit(script! { { index } });
                    self.temps += 1;
                    Query { index, entry: self.bury(1) }
                })
                .collect();
        }
        let m = (poseidon2::constants::P >> bits) << bits;
        let mask = (1u32 << bits) - 1;
        let mut accepted: Vec<Query> = Vec::new();
        for &e in draws {
            let v = self.samples[e];
            self.push_kept(e, 1);
            if v >= m {
                self.emit(script! { { m } OP_GREATERTHANOREQUAL OP_VERIFY });
                self.temps -= 1;
                continue;
            }
            self.emit(script! {
                OP_DUP { m } OP_LESSTHAN OP_VERIFY
                { field::low_bits_to_altstack(bits) }
                0
                for i in 0..bits { OP_FROMALTSTACK OP_IF { 1u32 << i } OP_ADD OP_ENDIF }
            });
            let index = v & mask;
            let entry = self.bury(1);
            accepted.push(Query { index, entry });
        }
        assert_eq!(accepted.len(), num_queries, "query count");
        accepted
    }

    /// Append an opening's paths and rows to the data; per query, the
    /// siblings top level first then the row, so one copy lays them out as
    /// `merkle_verify_from_altstack` wants.
    fn append_opening(
        &mut self,
        opening: &Opening,
        queries: &[Query],
        depth: usize,
    ) -> Result<Vec<usize>, pruned::Error> {
        let leaves: Vec<Digest> = opening.rows.iter().map(|r| poseidon2::reference::hash_row(r)).collect();
        let indices: Vec<usize> = queries.iter().map(|q| q.index as usize).collect();
        if opening.rows.len() != indices.len() {
            return Err(pruned::Error::MissingLeaf { index: opening.rows.len().min(indices.len()) });
        }
        let paths = pruned::expand(&opening.boundaries, &indices, &leaves, depth)?;
        Ok(paths
            .iter()
            .zip(&opening.rows)
            .map(|(path, row)| {
                let start = self.data.len();
                for level in (0..depth).rev() {
                    self.data.extend_from_slice(&path.siblings[level]);
                }
                self.data.extend_from_slice(row);
                start
            })
            .collect())
    }

    /// Authenticate each query's row against the root at `root` (a data
    /// digest), fold it at `fold_point` (kept EFs), and turn the index into
    /// the STIR point `gen^index`. Returns the kept folds (EF) and points (base).
    fn stir(
        &mut self,
        opening: &Opening,
        queries: &[Query],
        starts: &[usize],
        root: usize,
        depth: usize,
        fold_point: &[usize],
        gen: u32,
    ) -> (Vec<usize>, Vec<usize>) {
        let row_len = opening.rows[0].len();
        let folding = fold_point.len();
        let ef_per_row = if opening.extension { row_len / 4 } else { row_len };
        assert_eq!(ef_per_row, 1 << folding, "a row folds over the folding randomness");
        let mut folds = Vec::new();
        let mut points = Vec::new();
        for (q, &start) in queries.iter().zip(starts) {
            // The Merkle path: root, siblings, row; directions from the index.
            self.push_data(root, merkle::DIGEST);
            self.push_data(start, merkle::DIGEST * depth + row_len);
            self.push_kept(q.entry, 1);
            self.emit(field::low_bits_to_altstack(depth));
            self.temps -= 1;
            self.emit(merkle::hash_row(row_len));
            self.temps = self.temps - row_len + merkle::DIGEST;
            self.emit(merkle::merkle_verify_from_altstack(depth));
            self.temps -= merkle::DIGEST * (depth + 2);

            // The fold: the row as EF evaluations, the point on the altstack.
            let row_start = start + merkle::DIGEST * depth;
            for t in 0..ef_per_row {
                if opening.extension {
                    self.push_data(row_start + 4 * t, 4);
                } else {
                    self.push_data(row_start + t, 1);
                    self.lift();
                }
            }
            for &r in fold_point {
                self.push_kept(r, 4);
                self.emit(ext4::to_altstack());
                self.temps -= 4;
            }
            self.emit(multilinear::eval_multilinear(folding));
            self.temps = self.temps - 4 * ef_per_row + 4;
            folds.push(self.bury(4));

            // The point.
            self.push_kept(q.entry, 1);
            self.emit(field::pow_const_base(gen, depth));
            points.push(self.bury(1));
        }
        (folds, points)
    }

    /// `claim <- claim + sum_i gamma^(i+1) y_i` over the OOD answers (data)
    /// then the folds (kept): Plonky3's `combine_evals` for a constraint made
    /// `with_existing_claim`, which is exactly `combine_answers`.
    fn combine(&mut self, claim: usize, gamma: usize, ood: &[usize], folds: &[usize]) -> usize {
        self.push_kept(claim, 4);
        self.push_kept(gamma, 4);
        let t = ood.len() + folds.len();
        for &e in ood {
            self.push_data(e, 4);
            self.emit(ext4::to_altstack());
            self.temps -= 4;
        }
        for &f in folds {
            self.push_kept(f, 4);
            self.emit(ext4::to_altstack());
            self.temps -= 4;
        }
        self.emit(constraint::combine_answers(t - 1));
        self.temps -= 4;
        self.bury(4)
    }

    /// Plonky3's `eval_select(z, local)` with the local randomness the top
    /// `n` EFs of the stack under `under` EFs, and `z` a kept base element.
    fn select_weight(&mut self, z: usize, n: usize, under: usize) {
        // acc = 1, var = z
        self.push_ef_const(reference::EF_ONE);
        self.push_kept(z, 1);
        for i in (0..n).rev() {
            // (var - 1), then r_i, then r_i * (var - 1) + 1
            self.emit(script! { OP_DUP 1 { field::sub() } });
            self.temps += 1;
            // r_i's top slot: below the `under` EFs and this routine's
            // acc(4) var(1) (var-1)(1), i.e. n-1-i EFs into the block.
            let d = 4 * under + 6 + 4 * (n - 1 - i);
            self.emit(script! { for _ in 0..4 { { d + 3 } OP_PICK } });
            self.temps += 4;
            self.emit(script! { 4 OP_ROLL });
            self.ef_mul_base();
            self.push_ef_const(reference::EF_ONE);
            self.ef_add();
            // acc *= term, keeping var aside; then var = var^2.
            self.emit(script! { 4 OP_ROLL OP_TOALTSTACK });
            self.temps -= 1;
            self.ef_mul();
            self.emit(script! { OP_FROMALTSTACK OP_DUP { field::mul() } });
            self.temps += 1;
        }
        self.drop(1);
    }

    /// `eq(point, local)` for a point that is `expand(u, m)` with `suffix`
    /// hypercube coordinates appended; `u` a kept EF.
    fn eq_weight(&mut self, u: usize, m: usize, suffix: &[[u32; 4]], under: usize) {
        self.push_kept(u, 4);
        self.emit(constraint::expand_univariate(m));
        self.temps -= 4;
        for &c in suffix {
            self.push_ef_const(c);
            self.emit(ext4::to_altstack());
            self.temps -= 4;
        }
        self.emit(constraint::eq_eval_at(m + suffix.len(), under));
        self.temps += 4;
    }
}

impl Sponge for Builder {
    fn observe(&mut self, value: u32) {
        assert!(self.state && self.temps == 0);
        self.reference.observe(value);
        let i = self.data.len();
        self.data.push(value);
        let d = self.data_depth(i);
        self.emit(script! { { d } OP_PICK });
        self.available = 0;
        self.pending += 1;
        if self.pending == RATE {
            self.duplex();
        }
    }

    fn sample(&mut self) -> u32 {
        assert!(self.state && self.temps == 0);
        let value = self.reference.sample();
        if self.pending > 0 || self.available == 0 {
            self.duplex();
        }
        self.available -= 1;
        let slot = self.available;
        // Read the slot, then bury it under the state.
        self.emit(script! {
            { challenger::sample(slot) }
            for _ in 0..WIDTH { { WIDTH } OP_ROLL }
        });
        self.samples.push(value);
        self.kept += 1;
        value
    }
}

/// The kept entries one query block consumed: `stir_queries` replayed on the
/// recorded samples, since a sample at or above the rejection threshold costs
/// a further one and the shape counts draws, not samples.
fn draw_block(samples: &[u32], k: &mut usize, bits: usize, num_queries: usize) -> Vec<usize> {
    if num_queries >= 1 << bits {
        return Vec::new();
    }
    let m = (poseidon2::constants::P >> bits) << bits;
    let mut entries = Vec::new();
    let mut accepted = 0;
    while accepted < num_queries {
        let v = samples[*k];
        entries.push(*k);
        *k += 1;
        if v < m {
            accepted += 1;
        }
    }
    entries
}

fn stream(s: &mut usize, n: usize) -> usize {
    let at = *s;
    *s += n;
    at
}

fn kept(k: &mut usize, n: usize) -> usize {
    let at = *k;
    *k += n;
    at
}

/// The transcript's layout, walked in the order `reference::transcript` runs.
fn layout(cfg: &VerifyConfig, data: &VerifyData, ch: &Challenges, samples: &[u32]) -> Layout {
    let t = &cfg.transcript;
    let d = &data.transcript;
    let mut s = d.seed_commitment.len();
    let mut k = 0;
    let mut l = Layout::default();
    l.root = stream(&mut s, d.root.len());
    for seed in &d.seed_virtual {
        stream(&mut s, seed.len());
        l.k_ood.push(kept(&mut k, 4));
        l.ood_answers.push(stream(&mut s, 4));
    }
    for (evals, seed) in d.openings.iter().zip(&d.seed_claim) {
        stream(&mut s, seed.len());
        l.k_claim.push(kept(&mut k, 4));
        l.evals.push(evals.iter().map(|_| stream(&mut s, 4)).collect());
    }
    stream(&mut s, d.seed_whir.len() + d.seed_batching.len());
    l.k_alpha = kept(&mut k, 4);
    stream(&mut s, d.seed_initial_sumcheck.len());
    for _ in 0..d.initial_sumcheck.len() {
        l.initial_sumcheck.push((stream(&mut s, 4), stream(&mut s, 4)));
        l.k_initial_fold.push(kept(&mut k, 4));
    }
    for (rd, rt) in d.rounds.iter().zip(&t.rounds) {
        let mut r = RoundLayout { root: stream(&mut s, rd.root.len()), ..Default::default() };
        for _ in 0..rd.ood_answers.len() {
            r.k_ood.push(kept(&mut k, 4));
            r.ood_answers.push(stream(&mut s, 4));
        }
        r.k_draws = draw_block(samples, &mut k, rt.domain_bits, rt.num_queries);
        r.k_combination = kept(&mut k, 4);
        stream(&mut s, rd.seed_sumcheck.len());
        for _ in 0..rd.sumcheck.len() {
            r.sumcheck.push((stream(&mut s, 4), stream(&mut s, 4)));
            r.k_fold.push(kept(&mut k, 4));
        }
        l.rounds.push(r);
    }
    l.final_poly = stream(&mut s, 4 * d.final_poly.len());
    l.k_final_draws = draw_block(samples, &mut k, t.final_domain_bits, t.final_queries);
    stream(&mut s, d.seed_final_sumcheck.len());
    for _ in 0..d.final_sumcheck.len() {
        l.final_sumcheck.push((stream(&mut s, 4), stream(&mut s, 4)));
        l.k_final_fold.push(kept(&mut k, 4));
    }
    assert_eq!(k, samples.len(), "every sample is accounted for");
    let _ = ch;
    assert!(t.rounds.iter().all(|r| r.pow_bits == 0 && r.folding_pow_bits == 0));
    assert!(t.initial_folding_pow_bits == 0 && t.final_pow_bits == 0 && t.final_folding_pow_bits == 0);
    l
}

/// Build the verifier script for `data` under `cfg`.
///
/// Fails when the openings cannot be laid out against the transcript's
/// queries (a proof whose messages were changed after the openings were made,
/// or one with the wrong number of them): the reference verifier rejects such
/// a proof at the openings too. A well-formed but false proof builds, and its
/// script fails when run.
pub fn build(cfg: &VerifyConfig, data: &VerifyData) -> Result<Built, pruned::Error> {
    let mut b = Builder::new();

    // 1. The transcript: every input picked from the data, every draw kept.
    //    A fresh `DuplexChallenger` starts from the zero state.
    b.emit(script! { for _ in 0..WIDTH { 0 } });
    b.state = true;
    let ch = reference::transcript(&cfg.transcript, &data.transcript, &mut b);
    b.end_transcript();
    let l = layout(cfg, data, &ch, &b.samples);
    assert_eq!(b.data.len(), l.final_sumcheck.last().map_or(l.final_poly + 4 * data.transcript.final_poly.len(), |&(_, c)| c + 4));
    assert_eq!(b.kept, b.samples.len());
    let transcript_permutations = b.permutations;

    // 2. The initial claim: the openings' evaluations, then the OOD answers.
    let mut evals: Vec<usize> = l.evals.iter().flatten().copied().collect();
    evals.extend_from_slice(&l.ood_answers);
    b.batch(l.k_alpha, &evals);
    let mut claim = b.bury(4);

    // 3. The initial sumcheck.
    for (&(c0, c_inf), &r) in l.initial_sumcheck.iter().zip(&l.k_initial_fold) {
        claim = b.sumcheck_round(claim, c0, c_inf, r);
    }

    // 4. Intermediate rounds: draws, openings of the previous commitment,
    //    folds, the combination, the round's sumcheck.
    let mut prev_root = l.root;
    let mut prev_fold: Vec<usize> = l.k_initial_fold.clone();
    let mut round_points: Vec<Vec<usize>> = Vec::new();
    let mut all_fold: Vec<usize> = l.k_initial_fold.clone();
    for (i, (rl, rc)) in l.rounds.iter().zip(&cfg.transcript.rounds).enumerate() {
        let queries = b.query_draws(&rl.k_draws, rc.domain_bits, rc.num_queries);
        assert_eq!(
            queries.iter().map(|q| q.index).collect::<Vec<_>>(),
            ch.rounds[i].queries,
            "round {i}: the script's queries are the transcript's"
        );
        let opening = &data.round_openings[i];
        let starts = b.append_opening(opening, &queries, rc.domain_bits)?;
        let gen = cfg.rounds[i].folded_domain_gen;
        let (folds, points) = b.stir(opening, &queries, &starts, prev_root, rc.domain_bits, &prev_fold, gen);
        claim = b.combine(claim, rl.k_combination, &rl.ood_answers, &folds);
        for (&(c0, c_inf), &r) in rl.sumcheck.iter().zip(&rl.k_fold) {
            claim = b.sumcheck_round(claim, c0, c_inf, r);
        }
        round_points.push(points);
        prev_root = rl.root;
        prev_fold = rl.k_fold.clone();
        all_fold.extend_from_slice(&rl.k_fold);
    }

    // 5. The final openings: each fold must be the final polynomial at the
    //    STIR point.
    let t = &cfg.transcript;
    let queries = b.query_draws(&l.k_final_draws, t.final_domain_bits, t.final_queries);
    assert_eq!(queries.iter().map(|q| q.index).collect::<Vec<_>>(), ch.final_queries);
    let starts = b.append_opening(&data.final_opening, &queries, t.final_domain_bits)?;
    let (folds, points) = b.stir(
        &data.final_opening,
        &queries,
        &starts,
        prev_root,
        t.final_domain_bits,
        &prev_fold,
        cfg.final_folded_domain_gen,
    );
    let n_final = data.transcript.final_poly.len();
    for (&fold, &z) in folds.iter().zip(&points) {
        // Horner over the final polynomial's coefficients at z.
        b.push_data(l.final_poly + 4 * (n_final - 1), 4);
        for j in (0..n_final - 1).rev() {
            b.push_kept(z, 1);
            b.ef_mul_base();
            b.push_data(l.final_poly + 4 * j, 4);
            b.ef_add();
        }
        b.push_kept(fold, 4);
        b.equal_verify_ef();
    }

    // 6. The final sumcheck.
    for (&(c0, c_inf), &r) in l.final_sumcheck.iter().zip(&l.k_final_fold) {
        claim = b.sumcheck_round(claim, c0, c_inf, r);
    }
    all_fold.extend_from_slice(&l.k_final_fold);

    // 7. The weights: per constraint, its local randomness on the stack, each
    //    statement's weights above it, Horner in the constraint's challenge.
    b.push_ef_const([0, 0, 0, 0]);
    let total = 4;
    // (challenge, arity, weights) per constraint; a weight is a closure over
    // the builder producing one EF above `under` EFs.
    enum W {
        Eq { u: usize, m: usize, suffix: Vec<[u32; 4]> },
        Select { z: usize },
    }
    // (challenge, arity, powers start at 1, weights) per constraint.
    let mut constraints: Vec<(usize, usize, bool, Vec<W>)> = Vec::new();
    let mut ws = Vec::new();
    for (shape, &u) in cfg.claims.iter().zip(&l.k_claim) {
        for sel in &shape.selectors {
            ws.push(W::Eq { u, m: shape.row_vars, suffix: sel.clone() });
        }
    }
    for &u in &l.k_ood {
        ws.push(W::Eq { u, m: cfg.num_variables, suffix: vec![] });
    }
    constraints.push((l.k_alpha, cfg.num_variables, false, ws));
    for (i, rl) in l.rounds.iter().enumerate() {
        let n = cfg.rounds[i].num_variables;
        let mut ws: Vec<W> = rl.k_ood.iter().map(|&u| W::Eq { u, m: n, suffix: vec![] }).collect();
        ws.extend(round_points[i].iter().map(|&z| W::Select { z }));
        constraints.push((rl.k_combination, n, true, ws));
    }
    for (chi, n, shifted, ws) in &constraints {
        let n = *n;
        assert!(n <= all_fold.len());
        for &r in &all_fold[all_fold.len() - n..] {
            b.push_kept(r, 4);
        }
        for (i, w) in ws.iter().enumerate() {
            match w {
                W::Eq { u, m, suffix } => b.eq_weight(*u, *m, suffix, i),
                W::Select { z } => b.select_weight(*z, n, i),
            }
        }
        for _ in 0..ws.len() - 1 {
            b.push_kept(*chi, 4);
            b.ef_mul();
            b.ef_add();
        }
        // A round constraint's powers start at chi^1: one more factor.
        if *shifted {
            b.push_kept(*chi, 4);
            b.ef_mul();
        }
        // [total R(n) value] -> [total value] -> [total]
        b.emit(ext4::to_altstack());
        b.emit(ext4::drop_n(n));
        b.emit(ext4::from_altstack());
        b.temps -= 4 * n;
        b.ef_add();
    }
    assert_eq!(b.temps, total);

    // 8. The closing identity: claim == weights * final(r_fin).
    b.push_data(l.final_poly, 4 * n_final);
    for &r in &l.k_final_fold {
        b.push_kept(r, 4);
        b.emit(ext4::to_altstack());
        b.temps -= 4;
    }
    b.emit(multilinear::eval_multilinear(l.k_final_fold.len()));
    b.temps = b.temps - 4 * n_final + 4;
    b.ef_mul();
    b.push_kept(claim, 4);
    b.equal_verify_ef();
    assert_eq!(b.temps, 0);

    let data_out = b.data.clone();
    let parts = &b.parts;
    let script = script! {
        for v in data_out.iter().rev() { { *v } }
        for p in parts { { p.clone() } }
    };
    Ok(Built { script, data: data_out, transcript_permutations, challenges: ch })
}
