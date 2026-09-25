use bitcoin::hashes::{hash160, Hash};
use bitcoin_script::{define_pushable, script};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
define_pushable!();

fn h(x: &[u8]) -> [u8; 20] { hash160::Hash::hash(x).to_byte_array() }

#[test]
fn lamport_bit_reveal_cost() {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    for n in [1usize, 997, 998] {
        let keys: Vec<([u8; 16], [u8; 16])> = (0..n).map(|_| (rng.random(), rng.random())).collect();
        let bits: Vec<bool> = (0..n).map(|_| rng.random()).collect();
        let lock = script! {
            for (k0, k1) in keys.iter() {
                OP_HASH160 OP_DUP { h(k0).to_vec() } OP_EQUAL OP_SWAP { h(k1).to_vec() } OP_EQUAL OP_BOOLOR OP_VERIFY
            }
            OP_TRUE
        };
        let wit = script! { for (i, (k0, k1)) in keys.iter().enumerate().rev() { { if bits[i] { k1.to_vec() } else { k0.to_vec() } } } };
        let lock_len = lock.len();
        let wit_len = wit.len();
        let info = bitcoin_scriptexec::execute_script(script! { { wit } { lock } });
        eprintln!("{n} bits: script {lock_len} B ({:.2}/bit), witness pushes {wit_len} B, ok={} err={:?}", lock_len as f64 / n as f64, info.success, info.error);
        let bad = script! { for _ in 0..n { { vec![7u8; 16] } } };
        let info = bitcoin_scriptexec::execute_script(script! { { bad } { script! { for (k0, k1) in keys.iter() { OP_HASH160 OP_DUP { h(k0).to_vec() } OP_EQUAL OP_SWAP { h(k1).to_vec() } OP_EQUAL OP_BOOLOR OP_VERIFY } OP_TRUE } } });
        eprintln!("  wrong preimages rejected: {}", !info.success);
    }
}
