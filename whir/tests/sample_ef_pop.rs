//! `challenger::sample_ef_pop` matches `reference::Challenger`'s EF draw.
use bitcoin_script::{define_pushable, script};
use whir::{challenger, reference::Challenger};
define_pushable!();

fn decode(v: &[u8]) -> u32 {
    let mut a = 0u32; for (i,&b) in v.iter().enumerate() { a |= (b as u32) << (8*i); } a
}
fn run(s: bitcoin::ScriptBuf) -> Vec<u32> {
    let info = bitcoin_scriptexec::execute_script(s);
    assert!(info.error.is_none(), "err: {:?} at {:?}", info.error, info.last_opcode);
    (0..info.final_stack.len()).map(|i| decode(&info.final_stack.get(i))).collect()
}

/// One permutation's rate yields two EFs: pop from hi=7, then hi=3. Both must
/// equal what the reference challenger draws from the same state.
#[test]
fn two_efs_per_squeeze_match_the_reference() {
    // Drive the reference challenger to a permuted state, and read its two EFs.
    let mut ch = Challenger::new();
    ch.observe_slice(&(1..=8).collect::<Vec<_>>()); // a full-rate observe -> one permute
    let state = ch.state(); // rate[0..8] is this permutation's output
    let ef0 = ch.sample_ef(); // pops rate[7,6,5,4]
    let ef1 = ch.sample_ef(); // pops rate[3,2,1,0]

    // The script reads the same two EFs off the same state on the stack.
    let with_state = |s: bitcoin::ScriptBuf| script! { for x in state.iter() { {*x} } { s } };
    let got0 = &run(with_state(script! { { challenger::sample_ef_pop(7) } }))[16..];
    let got1 = &run(with_state(script! { { challenger::sample_ef_pop(3) } }))[16..];

    assert_eq!(got0, ef0, "first EF (hi=7)");
    assert_eq!(got1, ef1, "second EF (hi=3)");
}
