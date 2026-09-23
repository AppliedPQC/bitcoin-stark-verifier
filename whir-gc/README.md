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

## The verifier as a circuit, measured

`circuit::build` is `reference::verify` as gates -- the transcript on a
wire-level `HashChallenger` over the Blake3 gadget, every opened row hashed
and walked to the absorbed root, the folds, the STIR checks and the closing
identity -- with one output wire. Its shape depends only on the configuration
(the schedule has no data-dependent branch), so one circuit serves every proof
of a configuration. On real Plonky3 proofs, single-root commitments, rate 1/8,
folding 4, terminal security 110 (composed ≥ 103 bits):

| proof | queries | non-free gates | free XOR | inputs | garbled at 16 B/gate |
| --- | --- | ---: | ---: | ---: | ---: |
| 8 variables, no round | 72 final | **11,473,018** | 69.0M | 281,856 bits | ~184 MB |
| 12 variables, one round | 68 + 33 final | **21,980,196** | 128.2M | 490,368 bits | ~352 MB |

Each accepts the proof it was built from and rejects it with any single input
bit flipped, evaluated in Execute mode. For scale, `bitvm-gc`'s Groth16
verifier circuit is 2.72 × 10^9 non-free gates.

## Garbled, measured

`garble` streams over the gate list with one label per wire -- the same
formulas as `bitvm-gc`'s `gate_garbled`/`Gate::e` (privacy-free: one 16-byte
ciphertext per AND/OR, free XOR, `H(l) = Blake3(l ‖ gid)`), without
materialising a `Wire` per wire -- and `evaluate` walks it with the proof's
values, which is the BitVM3 setting: the proof is public, and the point is
that the output's *true* label comes out only of an accepting evaluation.
Single thread:

| circuit | garbled | garbling | evaluation |
| --- | ---: | ---: | ---: |
| 8 variables, 72 queries, 11.47M non-free gates | **183 MB** | 3.2 s (25M wires/s) | 2.2 s |
| 12 variables, 68 + 33 queries, 21.98M non-free gates | **351 MB** | 6.9 s | 7.4 s |

Each valid proof yields the true output label; with one input bit flipped,
the false one. Upstream's `DELTA` is the fixed public constant `S::one()`
(its own `FIXME`), under which any label yields its complement; `garble`
draws `Δ` at random, as a deployment must.

## Plan

1. Done: `reference`, checked op for op against the logged run and accepting
   the real proofs; `circuit`, accepting them in Execute mode; `garble`, the
   true label only for a valid proof.
2. Multi-chunk Blake3 in the gadget, so the commitment can be a Merkle cap
   (64 roots absorb 2 KB but save six compressions per query).
3. The 2^18 schedule (84 queries over three rounds), and the on-chain side:
   BitVM3's transaction structure takes this circuit as a drop-in.
