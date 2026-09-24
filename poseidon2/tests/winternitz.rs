//! The commitment layer: what stops a prover opening a step two ways.
//!
//! The disprove predicate decides whether a claimed step is false. These check
//! the other half — that the claim is *bound*, so a spender cannot answer one
//! challenge with one state and another with a different one.

use bitcoin::hashes::{hash160, Hash};
use bitcoin_script::{define_pushable, script};
use poseidon2::constants::WIDTH;
use poseidon2::winternitz::{self, DIGITS_PER_ELEMENT, W};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

define_pushable!();

fn h(x: &[u8; 20]) -> [u8; 20] {
    hash160::Hash::hash(x).to_byte_array()
}

/// A one-time key: one chain per bit, plus the checksum chains.
struct Key {
    secrets: Vec<[u8; 20]>,
    pks: Vec<[u8; 20]>,
}

fn keygen(n_elements: usize, rng: &mut ChaCha20Rng) -> Key {
    let n = winternitz::chains(n_elements * DIGITS_PER_ELEMENT);
    let secrets: Vec<[u8; 20]> = (0..n).map(|_| rng.random::<[u8; 20]>()).collect();
    // pk is the far end of the chain: H applied W-1 times.
    let pks = secrets
        .iter()
        .map(|sk| (0..W - 1).fold(*sk, |acc, _| h(&acc)))
        .collect();
    Key { secrets, pks }
}

/// `H^d(sk)`: the signature for digit `d`.
fn chain(sk: &[u8; 20], d: usize) -> [u8; 20] {
    (0..d).fold(*sk, |acc, _| h(&acc))
}

/// Message digits, least significant first, then the checksum digits.
fn digits(elements: &[u32]) -> Vec<u32> {
    let mut ds: Vec<u32> = Vec::new();
    for &x in elements {
        ds.extend_from_slice(&winternitz::digits_of(x));
    }
    let sum: u32 = ds.iter().sum();
    let check = (ds.len() * (W - 1)) as u32 - sum;
    let n_check = winternitz::checksum_digits(ds.len());
    for j in 0..n_check {
        ds.push((check >> (winternitz::LOG_W * j)) & (W as u32 - 1));
    }
    ds
}

/// The witness: chain 0 on top, so pairs are pushed in reverse.
fn sign(key: &Key, elements: &[u32]) -> bitcoin::ScriptBuf {
    let ds = digits(elements);
    assert_eq!(ds.len(), key.secrets.len());
    let sigs: Vec<(Vec<u8>, u32)> = ds
        .iter()
        .enumerate()
        .map(|(i, &d)| (chain(&key.secrets[i], d as usize).to_vec(), d))
        .collect();
    script! {
        for (s, d) in sigs.into_iter().rev() { { s } { d } }
    }
}

fn rand_elements(n: usize, rng: &mut ChaCha20Rng) -> Vec<u32> {
    (0..n).map(|_| rng.random_range(0..poseidon2::constants::P)).collect()
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

#[test]
fn a_signature_opens_to_the_committed_state() {
    let mut rng = ChaCha20Rng::seed_from_u64(80);
    for n in [1usize, 4, WIDTH] {
        let key = keygen(n, &mut rng);
        let msg = rand_elements(n, &mut rng);
        let info = bitcoin_scriptexec::execute_script(script! {
            { sign(&key, &msg) }
            { winternitz::verify(&key.pks, n) }
        });
        assert!(info.error.is_none(), "n = {n}: rejected: {:?}", info.error);
        let got: Vec<u32> = (0..info.final_stack.len())
            .map(|i| decode(&info.final_stack.get(i)) as u32)
            .collect();
        assert_eq!(got, msg, "n = {n}: the recovered state is not the signed one");
    }
}

/// The property the whole layer exists for: a state nobody signed does not open.
///
/// Without this the disprove predicate is a check of an assertion nobody made —
/// a spender could answer one challenge with one state and the next with
/// another, and no predicate over supplied values could tell.
#[test]
fn a_state_nobody_signed_does_not_open() {
    let mut rng = ChaCha20Rng::seed_from_u64(81);
    let n = 2usize;
    let key = keygen(n, &mut rng);
    let msg = rand_elements(n, &mut rng);

    let run_with = |ds: Vec<u32>| {
        let sigs: Vec<(Vec<u8>, u32)> = ds
            .iter()
            .enumerate()
            .map(|(i, &d)| (chain(&key.secrets[i], d as usize).to_vec(), d))
            .collect();
        bitcoin_scriptexec::execute_script(script! {
            for (s, d) in sigs.into_iter().rev() { { s } { d } }
            { winternitz::verify(&key.pks, n) }
        })
    };

    // Changing a message digit without touching the checksum: the sum no longer
    // matches, which is the arithmetic the checksum exists to enforce.
    let message_digits = n * DIGITS_PER_ELEMENT;
    for i in [0usize, 3, 7, 8, 15] {
        let mut ds = digits(&msg);
        ds[i] = (ds[i] + 1) % W as u32;
        assert!(run_with(ds).error.is_some(), "digit {i} changed, checksum untouched: accepted");
    }

    // A consistently re-signed message *does* verify, and that is correct: it is
    // a valid signature over a different state, which only the key holder can
    // make. What stops a forger is the next test, not this one.
    let mut other = msg.clone();
    other[0] ^= 1;
    let ds = digits(&other);
    assert!(
        run_with(ds).error.is_none(),
        "a consistently re-signed message should verify"
    );
    let _ = message_digits;
}

/// Raising a digit with only the public keys is what a forger can actually try.
///
/// This is the attack the checksum blocks, run as a forger would run it: a
/// signature for a *larger* digit is further along the chain, so raising one is
/// free to anyone holding the signature. Lowering the checksum to match cannot
/// be done without going backwards along a chain.
#[test]
fn a_forger_cannot_raise_a_digit() {
    let mut rng = ChaCha20Rng::seed_from_u64(82);
    let n = 2usize;
    let key = keygen(n, &mut rng);
    let msg = rand_elements(n, &mut rng);
    let honest = digits(&msg);
    let message_digits = n * DIGITS_PER_ELEMENT;

    // Pick a message digit the forger can raise, and raise it.
    let target = (0..message_digits)
        .find(|&i| honest[i] + 1 < W as u32)
        .expect("some digit is raisable");
    let mut forged = honest.clone();
    forged[target] += 1;

    // The checksum must fall by one. The forger can only move *forward* along a
    // chain from what it holds, so every checksum digit it can produce is at
    // least the honest one. Model that: it tries the honest checksum, and it
    // tries raising the checksum, and neither is what the sum now requires.
    for attempt in [honest[message_digits..].to_vec(), {
        let mut c = honest[message_digits..].to_vec();
        c[0] = (c[0] + 1).min(W as u32 - 1);
        c
    }] {
        let mut ds = forged.clone();
        ds.truncate(message_digits);
        ds.extend_from_slice(&attempt);
        let sigs: Vec<(Vec<u8>, u32)> = ds
            .iter()
            .enumerate()
            .map(|(i, &d)| (chain(&key.secrets[i], d as usize).to_vec(), d))
            .collect();
        let info = bitcoin_scriptexec::execute_script(script! {
            for (s, d) in sigs.into_iter().rev() { { s } { d } }
            { winternitz::verify(&key.pks, n) }
        });
        assert!(
            info.error.is_some(),
            "a forger raised a message digit and the signature still verified"
        );
    }
}

#[test]
fn report_commitment_size() {
    let one = poseidon2::permutation::permute().len();
    let state = winternitz::verify_len(WIDTH);
    let step = poseidon2::disprove::largest_round();
    println!("\n  committing one state");
    println!("  --------------------");
    println!("  chains per state             {:>10}", winternitz::state_chains());
    println!("  verification                 {:>10} B", state);
    println!("  a committed step (2 states)  {:>10} B", 2 * state + step);
    println!("  as a share of a standard tx  {:>9.1}%", 100.0 * (2 * state + step) as f64 / 400_000.0);
    println!("  the round alone              {:>10} B  ({:.1}%)", step, 100.0 * step as f64 / (2.0 * state as f64 + step as f64));
    println!("  one permutation, for scale   {:>10} B\n", one);
}
