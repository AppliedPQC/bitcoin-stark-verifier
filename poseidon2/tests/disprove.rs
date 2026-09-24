//! The disprove predicate: valid exactly when the prover lied.
//!
//! Every other test here asks whether a script accepts a correct value. These
//! ask the opposite, and the opposite has its own way of being vacuous: a
//! predicate that is always true lets anyone take the bond, and one that is
//! always false makes the bond unclaimable. Both cases are run.

use bitcoin_script::{define_pushable, script};
use poseidon2::constants::WIDTH;
use poseidon2::{disprove, permutation, reference};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

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

fn rand_state(rng: &mut ChaCha20Rng) -> [u32; WIDTH] {
    core::array::from_fn(|_| rng.random_range(0..poseidon2::constants::P))
}

#[test]
fn differs_is_the_negation_of_equality() {
    let mut rng = ChaCha20Rng::seed_from_u64(70);
    for n in [1usize, 4, 16] {
        let a: Vec<u32> = (0..n).map(|_| rng.random_range(0..poseidon2::constants::P)).collect();

        let same = run(script! {
            for x in a.iter() { {*x} }
            for x in a.iter() { {*x} }
            { disprove::differs(n) }
        });
        assert_eq!(same, vec![0], "n = {n}: equal vectors reported as differing");

        // Every position on its own has to be enough.
        for i in 0..n {
            let mut b = a.clone();
            b[i] = reference::add(b[i], 1);
            let got = run(script! {
                for x in a.iter() { {*x} }
                for x in b.iter() { {*x} }
                { disprove::differs(n) }
            });
            assert_eq!(got, vec![1], "n = {n}: a difference at {i} went unnoticed");
        }
    }
}

/// The honest step is *not* disprovable, and every wrong one is.
///
/// The first half is the half that matters. A predicate that fires on an honest
/// step is not a weak disprove, it is a way to take a bond from someone who did
/// nothing wrong.
#[test]
fn a_round_is_disprovable_exactly_when_it_is_wrong() {
    let mut rng = ChaCha20Rng::seed_from_u64(71);
    let n_rounds = disprove::rounds_per_permutation();

    for i in [0usize, 1, n_rounds / 2, n_rounds - 1] {
        let state = rand_state(&mut rng);
        // The honest output of round `i`, from the reference by way of the
        // script itself: `rounds()` is checked against `permute()` elsewhere,
        // so running it here is the definition of what the prover owes.
        let honest = run(script! {
            for x in state { {x} }
            { permutation::rounds().into_iter().nth(i).expect("round") }
        });
        assert_eq!(honest.len(), WIDTH);

        let got = run(script! {
            for x in honest.iter() { {*x} }
            for x in state { {x} }
            { disprove::round(i) }
        });
        assert_eq!(got, vec![0], "round {i}: an honest step was disprovable");

        for j in [0usize, WIDTH / 2, WIDTH - 1] {
            let mut lie = honest.clone();
            lie[j] = reference::add(lie[j], 1);
            let got = run(script! {
                for x in lie.iter() { {*x} }
                for x in state { {x} }
                { disprove::round(i) }
            });
            assert_eq!(got, vec![1], "round {i}: a lie about element {j} was not disprovable");
        }
    }
}

/// What a step costs, and what that means for the chunk count.
///
/// Two limits: 400 000 weight units for a transaction a node will relay, and
/// 4 000 000 for a block. Script is witness data, so one byte is one unit.
#[test]
fn report_step_size() {
    const STANDARD_TX_WU: usize = 400_000;
    let n_rounds = disprove::rounds_per_permutation();
    let one = permutation::permute().len();
    let largest = disprove::largest_round();

    println!("\n  a step is one permutation round");
    println!("  -------------------------------");
    println!("  rounds per permutation       {n_rounds:>12}");
    println!("  one permutation              {one:>12} B");
    println!("  largest disprove step        {largest:>12} B");
    println!("  as a share of a standard tx  {:>11.1}%", 100.0 * largest as f64 / STANDARD_TX_WU as f64);
    println!("  steps that fit in one        {:>12}", STANDARD_TX_WU / largest);
    println!();

    assert!(
        largest < STANDARD_TX_WU,
        "a disprove step is {largest} B, past the {STANDARD_TX_WU} weight units a node will relay: \
         the chunking has to go finer than one permutation round"
    );
}

// ---------------------------------------------------------------------------
// The complete disprove: states taken from signatures, not from the witness
// ---------------------------------------------------------------------------

use bitcoin::hashes::{hash160, Hash};
use poseidon2::winternitz::{self, DIGITS_PER_ELEMENT, W};

fn h160(x: &[u8; 20]) -> [u8; 20] {
    hash160::Hash::hash(x).to_byte_array()
}

struct Key {
    secrets: Vec<[u8; 20]>,
    pks: Vec<[u8; 20]>,
}

fn keygen(rng: &mut ChaCha20Rng) -> Key {
    let n = winternitz::state_chains();
    let secrets: Vec<[u8; 20]> = (0..n).map(|_| rng.random::<[u8; 20]>()).collect();
    let pks = secrets.iter().map(|sk| (0..W - 1).fold(*sk, |a, _| h160(&a))).collect();
    Key { secrets, pks }
}

fn sign(key: &Key, state: &[u32]) -> bitcoin::ScriptBuf {
    let mut ds: Vec<u32> = Vec::new();
    for &x in state {
        ds.extend_from_slice(&winternitz::digits_of(x));
    }
    let sum: u32 = ds.iter().sum();
    let check = (ds.len() * (W - 1)) as u32 - sum;
    for j in 0..winternitz::checksum_digits(ds.len()) {
        ds.push((check >> (winternitz::LOG_W * j)) & (W as u32 - 1));
    }
    let sigs: Vec<(Vec<u8>, u32)> = ds
        .iter()
        .enumerate()
        .map(|(i, &d)| ((0..d).fold(key.secrets[i], |a, _| h160(&a)).to_vec(), d))
        .collect();
    script! { for (s, d) in sigs.into_iter().rev() { { s } { d } } }
}

/// The complete predicate: honest is not disprovable, wrong is, unsigned aborts.
///
/// The third case is the one the commitment layer exists for. Without it a
/// spender picks whatever pair of states makes the predicate fire.
#[test]
fn a_committed_round_is_disprovable_exactly_when_the_prover_lied() {
    let mut rng = ChaCha20Rng::seed_from_u64(90);
    let i = disprove::rounds_per_permutation() / 2;
    let state = rand_state(&mut rng);
    let honest = run(script! {
        for x in state { {x} }
        { permutation::rounds().into_iter().nth(i).expect("round") }
    });

    let key_in = keygen(&mut rng);
    let key_out = keygen(&mut rng);

    let spend = |out: &[u32], sig_out_key: &Key| {
        script! {
            { sign(sig_out_key, out) }
            { sign(&key_in, &state) }
            { disprove::round_committed(i, &key_out.pks, &key_in.pks) }
        }
    };

    // The prover signed the honest output: nothing to disprove.
    let got = run(spend(&honest, &key_out));
    assert_eq!(got, vec![0], "an honest committed step was disprovable");

    // The prover signed a wrong output: the bond is claimable.
    let mut lie = honest.clone();
    lie[3] = reference::add(lie[3], 1);
    let got = run(spend(&lie, &key_out));
    assert_eq!(got, vec![1], "a signed lie was not disprovable");

    // A state nobody signed: the spend does not even run to a verdict.
    let other = keygen(&mut rng);
    let info = bitcoin_scriptexec::execute_script(spend(&lie, &other));
    assert!(
        info.error.is_some(),
        "a state signed with the wrong key was accepted -- the predicate is unbound"
    );
}

/// What a committed step costs, which is what a chunk is measured by.
#[test]
fn report_committed_step_size() {
    const STANDARD_TX_WU: usize = 400_000;
    let bare = disprove::largest_round();
    let committed = disprove::largest_committed_round();
    println!("\n  a step, bare and committed");
    println!("  --------------------------");
    println!("  round alone                  {bare:>10} B");
    println!("  with both states signed      {committed:>10} B");
    println!("  the commitment layer         {:>10} B  ({:.0}% of the step)",
             committed - bare, 100.0 * (committed - bare) as f64 / committed as f64);
    println!("  as a share of a standard tx  {:>9.1}%", 100.0 * committed as f64 / STANDARD_TX_WU as f64);
    println!("  committed steps per tx       {:>10}", STANDARD_TX_WU / committed);
    println!("  witness items                {:>10}  (limit 1000)", 4 * winternitz::state_chains());
    println!();
    assert!(committed < STANDARD_TX_WU, "a committed step does not relay");
    assert!(
        4 * winternitz::state_chains() < 1000,
        "two signatures do not fit the stack limit"
    );
}

/// A chunk of several rounds, committed only at its ends.
#[test]
fn a_committed_chunk_is_disprovable_exactly_when_the_prover_lied() {
    let mut rng = ChaCha20Rng::seed_from_u64(91);
    let len = disprove::max_chunk_len(400_000);
    assert!(len >= 2, "a chunk of one round is no better than a step");
    let first = 1usize;

    let state = rand_state(&mut rng);
    let honest = run(script! {
        for x in state { {x} }
        for r in permutation::rounds().into_iter().skip(first).take(len) { { r } }
    });
    assert_eq!(honest.len(), WIDTH);

    let key_in = keygen(&mut rng);
    let key_out = keygen(&mut rng);
    let spend = |out: &[u32], out_key: &Key| {
        script! {
            { sign(out_key, out) }
            { sign(&key_in, &state) }
            { disprove::chunk_committed(first, len, &key_out.pks, &key_in.pks) }
        }
    };

    assert_eq!(run(spend(&honest, &key_out)), vec![0], "an honest chunk was disprovable");

    let mut lie = honest.clone();
    lie[9] = reference::add(lie[9], 1);
    assert_eq!(run(spend(&lie, &key_out)), vec![1], "a signed lie was not disprovable");

    let other = keygen(&mut rng);
    assert!(
        bitcoin_scriptexec::execute_script(spend(&lie, &other)).error.is_some(),
        "a state signed with the wrong key was accepted"
    );
}

/// What chunking buys, which is setup rather than on-chain cost.
#[test]
fn report_chunk_length() {
    const STANDARD_TX_WU: usize = 400_000;
    let round = disprove::largest_round();
    let len = disprove::max_chunk_len(STANDARD_TX_WU);
    let per_perm = disprove::rounds_per_permutation();

    println!("\n  how long a chunk can be");
    println!("  -----------------------");
    println!("  len   bytes      of a standard tx   commitments per permutation");
    for l in [1usize, 2, 4, len, len + 1] {
        if l == 0 || l > per_perm {
            continue;
        }
        let b = disprove::largest_chunk(l);
        let fits = if b <= STANDARD_TX_WU { "" } else { "   (does not relay)" };
        println!(
            "  {l:>3} {b:>10} B {:>15.1}% {:>25}{fits}",
            100.0 * b as f64 / STANDARD_TX_WU as f64,
            per_perm.div_ceil(l),
        );
    }
    println!(
        "\n  longest chunk that relays: {len} rounds, so {} commitments per\n  \
         permutation rather than {per_perm} -- a {:.1}x cut in setup.\n",
        per_perm.div_ceil(len),
        per_perm as f64 / per_perm.div_ceil(len) as f64,
    );
    let _ = round;
}
