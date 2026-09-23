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
| `blake3::hash_bytes`, 1,072 bytes (two chunks: a flush with the 64-coefficient final polynomial) | 186,125 | same |

XOR is free under half-gates, so only AND gates are counted. The Blake3
gadget is `bitvm-gc`'s (`circuits/sect233k1/blake3_ckt.rs`, MIT OR
Apache-2.0, vendored because it is `pub(crate)` there) with its 32-bit adder
rewritten to one AND per bit (`maj(a, b, c) = c ⊕ ((a⊕c)·(b⊕c))`), which
halved it from 20,657, and with the reference implementation's tree mode
added (chunk chaining values on a stack, parent nodes, the root at the top),
since the transcript of the 2^18 schedule absorbs more than one chunk between
samples.

`tests/binary_whir.rs` produces a real WHIR proof over `BinaryField128`
(`WhirProver` on `BooleanWhirDomain`, `SuffixProver` binding, Blake3 MMCS —
as `examples/prove_hash_binary` configures it, minus the boolean-trace front
end), has Plonky3's own verifier accept it through a challenger that logs
every byte observed and sampled, and prints the executed byte schedule. That
schedule is what the circuit's transcript must reproduce.

```
cargo test -p whir-gc --release -- --nocapture
```

The suite peaks at 3.5 GB (the stored-gate build of the 8-variable circuit);
the 2^18 case is `#[ignore]`d and run on its own. Run both under a cap, so a
regression kills the test and not the machine:

```
(ulimit -v 7340032; cargo test -p whir-gc --release -- --nocapture)
(ulimit -v 6291456; cargo test -p whir-gc --release -- --ignored --nocapture)
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

`Inputs` are the constants and the inputs of the proof: the roots, the OOD
answers, the sumcheck polynomials, the grinding witnesses, the opened rows
and their Merkle siblings (expanded for the queries of the proof's own
transcript), the final polynomial.

## Garbled, measured

`garble` walks a stored gate list with one label per wire -- the same
formulas as `bitvm-gc`'s `gate_garbled`/`Gate::e` (privacy-free: one 16-byte
ciphertext per AND/OR, free XOR, `H(l) = Blake3(l ‖ gid)`), without
materialising a `Wire` per wire -- and `evaluate` walks it with the proof's
values, which is the BitVM3 setting: the proof is public, and the point is
that the output's *true* label comes out only of an accepting evaluation.
Single thread, on the stored 8- and 12-variable circuits:

| circuit | garbled | garbling | evaluation |
| --- | ---: | ---: | ---: |
| 8 variables, 72 queries, 11.47M non-free gates | **183 MB** | 3.2 s (25M wires/s) | 2.2 s |
| 12 variables, 68 + 33 queries, 21.98M non-free gates | **351 MB** | 6.9 s | 7.4 s |

Each valid proof yields the true output label; with one input bit flipped,
the false one. Upstream's `DELTA` is the fixed public constant `S::one()`
(its own `FIXME`), under which any label yields its complement; `garble`
draws `Δ` at random, as a deployment must.

## Streamed, measured: the 2^18 schedule

A stored gate list is the limit: the 12-variable circuit's is 10 GB, and
garbling it needs a label per wire on top. `stream::Streaming` is a
`CircuitTrait` backend that garbles, evaluates and checks each gate as the
builder emits it (the evaluator's formula on the held labels must give the
held output label), with the same folding as `CircuitAdapter` so that the two
emit the same circuit, gate for gate. `stream::Plan` is a first pass of the
same builder that records each wire's number of uses (one byte per wire);
the garbling pass then releases a wire's slot after its last use, so what is
held is the live wires, not the circuit. Single thread, peak RSS of the
whole process in the last column:

| proof | queries | non-free gates | wires | live at peak | garbled | plan | garble | RSS |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 8 variables, rate 1/8 | 72 | 11,473,018 | 80.8M | 0.94M | 183 MB | 1.6 s | 5.5 s | — |
| 12 variables, rate 1/8 | 68 + 33 | 21,980,196 | 150.7M | 1.06M | 351 MB | 2.8 s | 10.1 s | — |
| **18 variables, rate 1/32, folding 4, terminal security 110** | 35 + 22 + 16 | **24,269,949** | 165.5M | 1.28M | **388 MB** | 3.1 s | 11.1 s | 250 MB |

The 2^18 proof (a 2^18-row table, the commitment on a 2^23-point domain,
composed security ≥ 103 bits) takes Plonky3 217 s to produce, nearly all of
it grinding, and has 507,136 input bits. Its verifier is 24.3M non-free
gates: ~110× smaller than `bitvm-gc`'s Groth16 verifier, and its garbled
form is 388 MB. Both smaller circuits come out identical to their stored
builds, and every case rejects the proof with an opened row changed.

## With a Merkle cap, measured

A cap of `2^h` roots costs the transcript one flush of `32 · 2^h` bytes per
commitment and each query a selection of its root by the top `h` index bits
(a mux tree, `256 · (2^h − 1)` AND), and saves each query `h` compressions
(10,281 AND each). The same proofs with Plonky3's `recommended_cap_height`
(the log of the most draws in a round, capped by the shallowest tree):

| proof | cap | non-free gates | against a single root | garbled | garble |
| --- | ---: | ---: | ---: | ---: | ---: |
| 8 variables, rate 1/8, 72 queries | 64 roots | **7,478,776** | −35% | 119 MB | 4.0 s |
| 12 variables, rate 1/8, 68 + 33 queries | 64 roots | **16,758,412** | −24% | 268 MB | 8.2 s |
| 18 variables, rate 1/32, 35 + 22 + 16 queries | 32 roots | **21,200,494** | −13% | **339 MB** | 10.0 s |

`streaming_garbler_on_the_2_18_schedule` takes `WHIR_GC_CAP=<height>` to
try another height.

## Plan

1. Done: `reference`, checked op for op against the logged run and accepting
   the real proofs; `circuit`, accepting them in Execute mode; `garble`, the
   true label only for a valid proof; `stream`, the 2^18 schedule garbled in
   250 MB of memory; multi-chunk Blake3; the Merkle cap.
2. The on-chain side waits for a design. Then the evaluator's half: the
   ciphertexts streamed to it, and the garbling made verifiable
   (cut-and-choose or a proof of correct garbling), which is what the fixed
   public `Δ` upstream stands in for.
