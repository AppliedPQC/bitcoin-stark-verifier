# whir-gc

A WHIR verifier over the binary tower fields as a boolean circuit, to be
garbled: the on-chain cost of a garbled-circuit dispute (BitVM3 and its
successors) does not depend on the verifier's size, and a hash-based verifier
garbled instead of a Groth16 one keeps the whole construction post-quantum.

Built on the circuit API of GOAT's [`bitvm-gc`](https://github.com/GOATNetwork/bitvm-gc)
(`garbled-snark-verifier`, a modification of BitVM's), with Blake3 as the
garbling PRF (`_blake3`); the proofs are Plonky3's, over `BinaryField128` on
the additive Cantor domain with Blake3 commitments.

## What is here, measured

| gadget | AND gates | checked against |
| --- | ---: | --- |
| `tower::mul`, `GF(2^128)` | **2,187** (`3^7`) | `p3-binary-field`, every level, random elements |
| `tower::square`, `tower::mul_alpha` | 0 | same |
| `blake3::hash_bytes`, 64 bytes (a Merkle compression) | **10,281** | the `blake3` crate |
| `blake3::hash_bytes`, 256 bytes (a leaf row of 16 elements) | **41,511** | same |

XOR is free under half-gates, so only AND gates are counted. The Blake3
gadget is `bitvm-gc`'s (`circuits/sect233k1/blake3_ckt.rs`, MIT OR
Apache-2.0, vendored because it is `pub(crate)` there) with its 32-bit adder
rewritten to one AND per bit (`maj(a, b, c) = c ⊕ ((a⊕c)·(b⊕c))`), which
halved it from 20,657.

`tests/binary_whir.rs` produces a real WHIR proof over `BinaryField128`
(`WhirProver` on `BooleanWhirDomain`, `SuffixProver` binding, Blake3 MMCS —
as `examples/prove_hash_binary` configures it, minus the boolean-trace front
end), has Plonky3's own verifier accept it through a challenger that logs
every byte observed and sampled, and prints the executed byte schedule. That
schedule is what the circuit's transcript must reproduce.

```
cargo test -p whir-gc --release -- --nocapture
```

## Plan

1. `reference`: the transcript and the verifier over the additive domain in
   plain Rust, checked op for op against the logged run and accepting the real
   proofs — the method `whir/` used for the prime-field verifier.
2. The verifier as a `CircuitTrait` component mirroring it, run in Execute
   mode on the real proofs.
3. Garble and evaluate the 100-bit schedules; measure.
