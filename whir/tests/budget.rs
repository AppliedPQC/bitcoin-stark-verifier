//! Does a WHIR verifier fit in a Bitcoin transaction?
//!
//! Everything else in this crate measures a script. This asks the question the
//! measurements exist to answer, against a real `WhirConfig` derived by Plonky3
//! rather than a schedule written out by hand -- so the query counts, domain
//! sizes and folding schedule are whatever the security analysis actually
//! produces at a given level.
//!
//! Two limits bind, and neither is the one people expect. Taproot removed both
//! the 10 000-byte script limit and the 201-opcode cap, so what is left is
//! weight: a standard transaction is capped at 400 000 weight units, and a
//! block at 4 000 000. Script lives in the witness at one unit per byte.

use p3_challenger::DuplexChallenger;
use p3_field::extension::BinomialExtensionField;
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear};
use p3_whir::parameters::{FoldingFactor, ProtocolParameters, SecurityAssumption, WhirConfig};
use whir::verifier::{queries_per_squeeze, Config, Round};

type F = KoalaBear;
type EF = BinomialExtensionField<F, 4>;
type Perm = Poseidon2KoalaBear<16>;
type MyChallenger = DuplexChallenger<F, Perm, 16, 8>;

/// `MAX_STANDARD_TX_WEIGHT`: what a node will relay.
const STANDARD_TX_WU: usize = 400_000;
/// Consensus block weight: what a miner could include directly.
const BLOCK_WU: usize = 4_000_000;

fn perm_bytes() -> usize {
    poseidon2::permutation::permute().len()
}

/// Plonky3's derived configuration, translated into this crate's schedule.
fn derive(
    num_variables: usize,
    security_level: usize,
    pow_bits: usize,
) -> Result<(Config, Vec<usize>), String> {
    derive_under(num_variables, security_level, pow_bits, SecurityAssumption::CapacityBound)
}

/// The same, under a named soundness assumption.
fn derive_under(
    num_variables: usize,
    security_level: usize,
    pow_bits: usize,
    soundness_type: SecurityAssumption,
) -> Result<(Config, Vec<usize>), String> {
    let folding_factor = FoldingFactor::Constant(4);
    // One rate per round, and the recurrence is WHIR's: folding k variables
    // multiplies the rate by 2^(1-k), so log(1/rate) grows by k-1. Writing it
    // out by hand is what `RoundRateCountMismatch` is there to catch.
    let schedule = folding_factor
        .compute_folding_schedule(num_variables)
        .expect("valid folding schedule");
    let mut rates = Vec::with_capacity(schedule.len() - 1);
    let mut rate = 4usize; // starting_log_inv_rate
    for &folding in schedule.iter().take(schedule.len() - 1) {
        rate += folding - 1;
        rates.push(rate);
    }
    let params = ProtocolParameters {
        security_level,
        pow_bits,
        round_log_inv_rates: rates,
        folding_factor,
        soundness_type,
        starting_log_inv_rate: 4,
    };
    // `pow_bits: 0` is not always satisfiable: WHIR trades query count against
    // grinding, and below a certain budget the security level is unreachable at
    // any query count. Reporting that is more useful than asserting it away.
    let cfg: WhirConfig<EF, F, MyChallenger> =
        WhirConfig::new(num_variables, params).map_err(|e| format!("{e:?}"))?;

    let rounds: Vec<Round> = cfg
        .round_parameters()
        .iter()
        .map(|r| Round {
            folding_factor: r.folding_factor,
            num_queries: r.num_queries,
            log_domain_size: r.domain_size.trailing_zeros() as usize - r.folding_factor,
            ood_samples: r.ood_samples,
            // One row is the 2^folding_factor values of the fibre, as extension
            // elements -- four base elements each.
            row_len: 4 * (1 << r.folding_factor),
            // Plonky3 derives this per round; the cost model only needs the
            // exponent's bit width, which `log_domain_size` already gives.
            domain_gen: 7,
        })
        .collect();
    let last = cfg.round_parameters().last().expect("at least one round");
    let final_round = Round {
        folding_factor: 0,
        num_queries: cfg.terminal().num_queries,
        log_domain_size: last.domain_size.trailing_zeros() as usize - last.folding_factor,
        ood_samples: 0,
        row_len: 4 * (1 << last.folding_factor),
        domain_gen: 7,
    };
    let queries: Vec<usize> = cfg.round_parameters().iter().map(|r| r.num_queries).collect();
    Ok((
        Config {
            initial_folding_factor: cfg.folding_schedule()[0],
            initial_ood_samples: cfg.commitment_ood_samples(),
            rounds,
            final_round,
            final_sumcheck_rounds: cfg.final_sumcheck_rounds(),
            final_poly_vars: cfg.final_sumcheck_rounds(),
        },
        queries,
    ))
}

/// One query is the unit that would have to be chunked, so price it alone.
///
/// A query is `log_domain_size` permutations for the Merkle path plus the row
/// hash. Nothing about the security level changes that -- lowering the level
/// buys *fewer* queries, not cheaper ones -- which is the whole point of
/// printing both.
#[test]
fn one_query_against_a_transaction() {
    let one = perm_bytes();
    println!("\n  one Poseidon2 permutation: {one} B");
    println!("    standard tx (400k WU) holds {:.2} permutations", STANDARD_TX_WU as f64 / one as f64);
    println!("    whole block  (4M WU) holds {:.2} permutations", BLOCK_WU as f64 / one as f64);
    println!("\n  security  vars   rounds  queries(r0)  depth(r0)   one query        vs block");
    println!("  --------------------------------------------------------------------------");
    for &security in [80usize, 100].iter() {
        for &pow in [0usize, 22].iter() {
            if pow >= security {
                continue;
            }
            for &vars in [16usize, 20, 24].iter() {
                let (cfg, queries) = match derive(vars, security, pow) {
                    Ok(v) => v,
                    Err(e) => {
                        println!("  {security:>3} pow{pow:<3} {vars:>4}   not derivable: {e}");
                        continue;
                    }
                };
                let depth = cfg.rounds[0].log_domain_size;
                let per_query = depth + cfg.rounds[0].row_len.div_ceil(8);
                let bytes = per_query * one;
                println!(
                    "  {security:>3} pow{pow:<3} {vars:>4} {:>8} {:>11} {depth:>10} {:>11} B {:>9.2}",
                    cfg.rounds.len(),
                    queries[0],
                    bytes,
                    bytes as f64 / BLOCK_WU as f64,
                );
            }
        }
    }
    println!();
}

/// The whole verifier, for the same grid.
#[test]
fn whole_verifier_against_a_block() {
    let one = perm_bytes();
    println!("\n  security  pow   vars   permutations        bytes     blocks   vs 100-bit");
    println!("  ----------------------------------------------------------------------");
    let mut baseline = std::collections::HashMap::new();
    for &security in [100usize, 80].iter() {
        for &pow in [0usize, 22].iter() {
            if pow >= security {
                continue;
            }
            for &vars in [16usize, 20, 24].iter() {
                let (cfg, _) = match derive(vars, security, pow) {
                    Ok(v) => v,
                    Err(e) => {
                        println!("  {security:>3} {pow:>6} {vars:>6}   not derivable: {e}");
                        continue;
                    }
                };
                let n = whir::verifier::permutation_count(&cfg);
                let bytes = n * one;
                if security == 100 && pow == 0 {
                    baseline.insert(vars, n);
                }
                let rel = baseline.get(&vars).map_or(1.0, |b| n as f64 / *b as f64);
                println!(
                    "  {security:>3} {pow:>6} {vars:>6} {n:>14} {bytes:>12} {:>10.1} {rel:>11.2}x",
                    bytes as f64 / BLOCK_WU as f64,
                );
            }
        }
    }
    println!("\n  Query indices come {} per squeeze.\n", queries_per_squeeze());
}

/// How many chunks a BitVM2-style assertion would need.
///
/// The verifier is three hundred blocks and will never be executed on-chain.
/// What can be is one *step* of it, if the prover commits to the state between
/// steps and a challenger names the step it claims is wrong. So the number that
/// matters is not the verifier's size but the step count, and whether a step
/// relays.
///
/// A step is one Poseidon2 round, because a Merkle level is already too big:
/// 572 252 bytes against 400 000 weight units. The rounds are what
/// `permutation::rounds()` emits and what `rounds_compose_to_the_permutation`
/// pins to `permute()`.
///
/// The step measured here is the *committed* one — both its states taken from
/// Winternitz signatures rather than from the witness. An uncommitted step is
/// smaller and is not a disprove: a spender would pick whichever pair of states
/// makes the predicate fire.
#[test]
fn chunk_count_for_a_disprove() {
    let bare = poseidon2::disprove::largest_round();
    let step = poseidon2::disprove::largest_committed_round();
    let per_perm = poseidon2::disprove::rounds_per_permutation();
    // A chunk commits only its two endpoints, so its length is decided by what
    // still relays rather than by paying the commitment once per round.
    let chunk_len = poseidon2::disprove::max_chunk_len(STANDARD_TX_WU);
    let chunk = poseidon2::disprove::largest_chunk(chunk_len);
    let chunks_per_perm = per_perm.div_ceil(chunk_len);

    println!("\n  disprove chunking, one step = one Poseidon2 round");
    println!("  ------------------------------------------------");
    println!("  the round alone            {bare:>12} B");
    println!("  a committed step           {step:>12} B  ({:.1}% of a standard tx)",
             100.0 * step as f64 / STANDARD_TX_WU as f64);
    println!("  of which the signatures    {:>12} B  ({:.0}%)",
             step - bare, 100.0 * (step - bare) as f64 / step as f64);
    println!("  a chunk of {chunk_len} rounds      {chunk:>12} B  ({:.1}% of a standard tx)",
             100.0 * chunk as f64 / STANDARD_TX_WU as f64);
    println!("  chunks per permutation     {chunks_per_perm:>12}  (rather than {per_perm})");
    println!();
    println!("  security  pow   vars   permutations         steps        chunks   disprove");
    println!("  --------------------------------------------------------------------------");
    for &security in [100usize, 80].iter() {
        for &vars in [16usize, 20, 24].iter() {
            let (cfg, _) = match derive(vars, security, 22) {
                Ok(v) => v,
                Err(_) => continue,
            };
            let perms = whir::verifier::permutation_count(&cfg);
            let steps = perms * per_perm;
            let chunks = perms * chunks_per_perm;
            println!(
                "  {security:>3} {:>6} {vars:>6} {perms:>14} {steps:>13} {chunks:>13} {:>10} B",
                22, chunk,
            );
        }
    }
    println!("\n  A disprove spends one chunk. Everything else stays off-chain unless");
    println!("  someone cheats, which is the whole of the trick.\n");

    assert!(step < STANDARD_TX_WU, "a committed step does not relay");
    assert!(chunk <= STANDARD_TX_WU, "the chosen chunk length does not relay");
}

/// What the chunking does *not* cover, stated rather than implied.
///
/// The permutations decompose because `rounds()` exists. The arithmetic between
/// them -- the sumcheck rounds, the multilinear evaluation, the constraint
/// weights -- does not, and it is 2% of the verifier. Two per cent of 1.24 GB is
/// still 25 MB, which is sixty standard transactions' worth of script with no
/// step boundaries in it.
#[test]
fn report_unchunked_arithmetic() {
    let (cfg, _) = derive(20, 80, 22).expect("derivable");
    let perms = whir::verifier::permutation_count(&cfg);
    let one = poseidon2::permutation::permute().len();
    let hashing = perms * one;
    // The example configuration measures its own arithmetic share; reuse it as
    // the estimate rather than inventing a second one.
    let arithmetic = (hashing as f64 * 0.02) as usize;
    println!(
        "\n  hashing {hashing} B decomposes into {} steps;\n  \
         arithmetic is about {arithmetic} B and decomposes into none.\n",
        perms * poseidon2::disprove::rounds_per_permutation()
    );
}

/// What the soundness regime costs, since the script does not know about it.
///
/// Nothing in `whir/src` or `poseidon2/src` mentions a soundness assumption.
/// The script executes a schedule; which regime produced that schedule is a
/// parameter of the *configuration*, and it reaches the script only as a query
/// count. So switching regimes is a config change, and this is what it costs.
///
/// The default everywhere in this crate is `CapacityBound`, the cheapest of the
/// three and the only one resting on the unproven half of WHIR's Conjecture
/// 4.12. That is the papers' own benchmarking default and a defensible choice,
/// but a verifier that settles bitcoin should be able to say what the proved
/// alternative would cost rather than only that it is dearer.
#[test]
fn what_the_soundness_regime_costs() {
    let one = perm_bytes();
    let regimes = [
        ("UD, proved       ", SecurityAssumption::UniqueDecoding),
        ("JB, Conj. 4.12(1)", SecurityAssumption::JohnsonBound),
        ("CB, Conj. 4.12(2)", SecurityAssumption::CapacityBound),
    ];
    println!("\n  soundness regime at 100-bit security");
    println!("  -----------------------------------");
    println!("  Each regime is given the grinding it needs rather than a shared");
    println!("  budget: a weaker assumption wants more of both, and holding pow");
    println!("  fixed would report 'not derivable' instead of a price.\n");
    println!("  regime               vars   pow   queries(r0)   permutations        bytes   vs CB");
    for &vars in [16usize, 20].iter() {
        let mut baseline = None;
        for (name, regime) in regimes.iter() {
            // The smallest grinding budget the regime is derivable at.
            let found = (0..64).find_map(|pow| {
                derive_under(vars, 100, pow, *regime).ok().map(|v| (pow, v))
            });
            match found {
                Some((pow, (cfg, queries))) => {
                    let n = whir::verifier::permutation_count(&cfg);
                    if matches!(regime, SecurityAssumption::CapacityBound) {
                        baseline = Some(n);
                    }
                    println!(
                        "  {name}  {vars:>5} {pow:>5} {:>13} {n:>14} {:>12} {}",
                        queries[0],
                        n * one,
                        baseline.map_or(String::new(), |b| format!("{:>6.2}x", n as f64 / b as f64)),
                    );
                }
                None => println!("  {name}  {vars:>5}   not derivable at any grinding budget"),
            }
        }
        println!();
    }
    println!("  The script is identical in all three. Only the query count moves,");
    println!("  and script weight moves with it.\n");
}
