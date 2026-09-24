# whir-gc

A binary-field STARK verifier -- Plonky3's `p3-multi-stark` over the WHIR
polynomial commitment, all over the `GF(2^128)` tower -- as a boolean
circuit, to be garbled: the on-chain cost of a garbled-circuit dispute
(BitVM3 and its successors) does not depend on the verifier's size, and a
hash-based verifier garbled instead of a Groth16 one keeps the whole
construction post-quantum.

In one line: a full verifier for a 2^16-row, 1,625-column Keccak-f trace at
104 bits of soundness is 88.7M non-free gates, 1.4 GB garbled, one minute to
garble or evaluate on one core, against 2.72 × 10^9 gates for `bitvm-gc`'s
Groth16 verifier. The tables below say where every gate goes.

Built on the circuit API of GOAT's [`bitvm-gc`](https://github.com/GOATNetwork/bitvm-gc)
(`garbled-snark-verifier`, a modification of BitVM's), with Blake3 as the
garbling PRF (`_blake3`); the proofs are Plonky3's, over `BinaryField128` on
the additive Cantor domain with Blake3 commitments.

## What is here, measured

| gadget | AND gates | checked against |
| --- | ---: | --- |
| `tower::mul`, `GF(2^128)` | **2,187** (`3^7`) | `p3-binary-field`, every level, random elements |
| `tower::square`, `tower::mul_alpha` | 0 | same |
| `blake3_ckt::hash_bytes`, 64 bytes (a Merkle compression) | **10,281** | the `blake3` crate |
| `blake3_ckt::hash_bytes`, 256 bytes (a leaf row of 16 elements) | **41,511** | same |
| `blake3_ckt::hash_bytes`, 1,072 bytes (two chunks: a flush with the 64-coefficient final polynomial) | 186,125 | same |

XOR is free under half-gates, so only AND gates are counted. The Blake3
gadget is `bitvm-gc`'s (`circuits/sect233k1/blake3_ckt.rs`), made public
upstream with its 32-bit adder rewritten to one AND per bit (`maj(a, b, c) = c ⊕ ((a⊕c)·(b⊕c))`), which
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

`garble` walks a stored gate list with one label per wire -- each gate
garbled by `bitvm-gc`'s own `gate_garbled_with_delta` (privacy-free: one
16-byte ciphertext per AND/OR, free XOR, `H(l) = Blake3(l ‖ gid)`), without
materialising a `Wire` per wire -- and `evaluate` walks it with the proof's
values through `bitvm-gc`'s `gate_evaluate`, which is the BitVM3 setting: the proof is public, and the point is
that the output's *true* label comes out only of an accepting evaluation.
Single thread, on the stored 8- and 12-variable circuits:

| circuit | garbled | garbling | evaluation |
| --- | ---: | ---: | ---: |
| 8 variables, 72 queries, 11.47M non-free gates | **183 MB** | 3.2 s (25M wires/s) | 2.2 s |
| 12 variables, 68 + 33 queries, 21.98M non-free gates | **351 MB** | 6.9 s | 7.4 s |

Each valid proof yields the true output label; with one input bit flipped,
the false one. `garble` draws `Δ` at random, as a deployment must, never
upstream's default `NON_CAC_DELTA` (the public `S::one()`, under which any
label yields its complement).

## Streamed, measured: the 2^18 schedule

A stored gate list is the limit: the 12-variable circuit's is 10 GB, and
garbling it needs a label per wire on top. `bitvm-gc`'s
`circuits/sect233k1/stream.rs` (written for this crate, upstreamed with a
secret random `Δ` per garbling) has `Streaming`, a
`CircuitTrait` backend that garbles, evaluates and checks each gate as the
builder emits it (the evaluator's formula on the held labels must give the
held output label), with the same folding as `CircuitAdapter` so that the two
emit the same circuit, gate for gate, and `Plan`, a first pass of the
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
try another height. On the 2^18 schedule the recommendation is the optimum:
the cap is shared by all three trees, so every commitment pays the flush
and every query the selection, while only the deep paths save much.

| cap on the 2^18 schedule | 1 | 32 | 64 | 128 | 256 |
| --- | ---: | ---: | ---: | ---: | ---: |
| non-free gates | 24,269,949 | **21,200,494** | 21,540,757 | 23,009,172 | 26,733,891 |

## Where the gates go, and the parameter sweep

`circuit::Profile` charges every non-free gate to the phase that emits it;
the streaming test prints it. The 2^18 schedule at rate 1/32, folding 4,
cap of 32, 21,200,494 non-free gates:

| phase | non-free gates | share |
| --- | ---: | ---: |
| Merkle paths (compressions, 10,281 each) | 10,447,624 | 49.3% |
| leaf hashes (256-byte rows, 41,511 each) | 3,030,303 | 14.3% |
| query folds (15 multiplications each, 2,187 per multiplication) | 2,394,765 | 11.3% |
| closing query weights | 1,903,719 | 9.0% |
| transcript (the sponge's flushes) | 1,475,727 | 7.0% |
| final polynomial at the final queries | 655,216 | 3.1% |
| claim combination | 564,236 | 2.7% |
| cap selection | 217,015 | 1.0% |
| closing eq weights, sumcheck rounds, closing identity, initial claim | 511,889 | 2.4% |

Three quarters is hashing, and the rest is `GF(2^128)` multiplication. The
same table for the other parameters of the 2^18 schedule
(`WHIR_GC_RATE`, `WHIR_GC_FOLDING`; each is one proof and its grinding time
is one draw of a lottery, so the proving times are indicative only):

| rate | folding | queries | cap | non-free gates | garbled | proving |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 1/16 | 4 | 45 + 26 + 18 | 32 | 24,560,837 | 393 MB | 38 s |
| 1/32 | 2 | 37 + 31 + 26 + 23 + 20 + 18 | 32 | 36,327,977 | 581 MB | 39 s |
| 1/32 | 3 | 35 + 25 + 20 + 16 | 32 | 24,548,531 | 393 MB | 142 s |
| **1/32** | **4** | **35 + 22 + 16** | **32** | **21,200,494** | **339 MB** | 150 s |
| 1/32 | 5 | 34 + 19 + 13 | 32 | 22,808,713 | 364 MB | 926 s |
| 1/64 | 4 | 28 + 19 + 14 | 16 | 18,988,736 | 304 MB | 1,102 s |

Folding trades leaf width against path count: at folding 2 the paths are
64% of the circuit, at folding 5 the 512-byte leaves and the 31
multiplications per fold overtake the shorter paths. Halving the rate buys
10% fewer gates for a prover domain twice the size and much more grinding.
Rate 1/32 with folding 4 is the configuration to carry forward.

## The full STARK verifier, measured

`stark` and `stark_circuit` put Plonky3's `p3-multi-stark` layers in front of
the WHIR opening, as the Boolean WHIR trace commitment runs them: the
zerocheck of the AIR (alpha, beta, tau; a degree-4 generic sumcheck over the
row variables; the constraints evaluated at the bound point from the opened
current and next rows, Horner-batched under alpha, against `eq(tau, r)`), the
batching of the opened columns into one bit-level claim (the column point,
`combine_columns` on both rows), and the bit ring switch (the 128-row tensor
and, above 2^7 rows, its carry and last tensors; the batched sumcheck; the
closing weight from the tensor algebra's equality and successor elements)
whose surviving point WHIR then opens as a given claim. The AIR comes in as
Plonky3's symbolic constraints and is evaluated on wires.

`tests/keccak_stark.rs` proves Keccak-f permutations (the 1,625-column
characteristic-2 AIR, booleanity assumed since the commitment is to bits)
through this crate's own `MultiStarkConfig` under a byte-logging challenger,
has the reference replay Plonky3's verifier byte for byte, then streams the
full circuit through the garbler. Rate 1/32, folding 4, terminal security
110, Blake3 everywhere:

| trace | packed variables | non-free gates | garbled | garble | peak RSS | inputs | proving |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^5 rows (1 Keccak-f) | 9 | 44,573,121 | 713 MB | 25 s | | 586,240 bits | 0.1 s |
| 2^8 rows (10 Keccak-f) | 12 | 66,459,859 | 1,063 MB | 37 s | | 743,808 bits | 1.2 s |
| 2^12 rows (163 Keccak-f) | 16 | 77,736,394 | 1,243 MB | 43 s | 616 MB | 874,240 bits | 75 s |
| **2^16 rows (2,621 Keccak-f)** | 20 | **88,680,747** | **1,418 MB** | 61 s | 1.5 GB | 997,760 bits | 44 min |

Each accepts its proof and rejects it with an opened value changed. The
2^18 case is not yet measured (about +5M gates per two variables from the
slope above, so ~95M); it is the `#[ignore]`d test, a few hours of proving
on one core with a 6 GB peak:

```
WHIR_GC_LOG_HEIGHT=18 cargo test -p whir-gc --release --test keccak_stark \
    full_verifier_circuit_on_the_2_18 -- --ignored --nocapture
```

Where the 2^16 circuit's gates go:

| phase | non-free gates | share |
| --- | ---: | ---: |
| ring switch closing (equality, carry and last elements: 256 multiplications per coordinate) | 29,318,218 | 33.1% |
| WHIR Merkle paths | 13,048,737 | 14.7% |
| column combination (a 2^11 eq table and two 1,625-term dot products) | 11,582,352 | 13.1% |
| AIR constraints (1,650 constraints, Horner under alpha) | 10,727,362 | 12.1% |
| STARK transcript (absorbing 3,250 opened values and the tensors) | 10,500,208 | 11.8% |
| WHIR leaves, folds, weights, transcript, rest | 11,500,000 | 13.0% |
| zerocheck sumcheck, ring switch statement, closing checks | 2,000,000 | 2.2% |

The column count sets three of the big items: the STARK transcript, the
combination and the constraints all grow with it. The ring switch closing
grows with the packed variables (256 multiplications each) plus a fixed
11 × 512 for the column selector, and is the first place to optimise.

## Security

Plonky3's own assessment of the configurations above
(`security_of_the_measured_configurations`), every term a proven bound in the
Johnson list-decoding regime, nothing unassessed:

| trace | 2^5 | 2^8 | 2^12 | 2^16 | 2^18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| composed soundness, bits | 106.1 | 105.2 | 104.7 | 104.3 | 104.3 |

The terms at 2^18: WHIR opening 104.3 (the binding term; 110 bits per term,
rate 1/32, folding 4, grinding up to 32 bits), constraint batching 109.0,
zerocheck 114.5 and its sumcheck 113.5, bit ring switch 114.0, column
batching 115.2, commitment and transcript collision 128 (Blake3). The
garbling adds 128-bit labels under a random secret `Δ` with Blake3 as the
PRF; it is privacy-free, which the BitVM setting allows since the proof is
public. Two of Plonky3's data-dependent branches are fixed in the circuit
and guarded by checks (nonzero `tau` draws, no Boolean prefix on the column
point), each rejecting where Plonky3 would continue with probability
~2^-127 per coordinate, never the reverse.

## KoalaBear and Poseidon2, measured

The question this crate exists to answer for the other half of the repository:
what would the KoalaBear, Poseidon2-committed verifier of the `whir` and
`poseidon2` crates cost as a garbled circuit? `koala` implements KoalaBear
(`p = 2^31 − 2^24 + 1`) and Poseidon2 over it on wires -- 31-bit elements,
carry-save compression at one AND per full adder, reduction by folding
`2^31 ≡ 2^24 − 1` and conditional subtractions -- checked against the
`poseidon2` crate's reference, which is checked against Plonky3:

| gadget | AND gates | for comparison |
| --- | ---: | --- |
| `koala::add` / `sub` | 70 / 94 | |
| `koala::mul` (31-bit modular) | **3,451** | `GF(2^128)` multiplication: 2,187 |
| `koala::sbox` (`x^3`) | 6,871 | |
| `koala::div_2exp` by 2, 2^8, 2^24 | 54, 432, 2,128 | |
| `koala::ext_mul`, degree-4 extension, schoolbook | **60,615** | `GF(2^128)` multiplication: 2,187 |
| `koala::permute`, Poseidon2 width 16 | **1,240,747** | Blake3 compression: 10,281 |
| `koala::hash_row`, 64 elements (8 permutations) | 9,924,068 | Blake3 of 256 bytes: 41,511 |

A Poseidon2 permutation is 120 Blake3 compressions; the 148 S-boxes are 1.0M
of it and the linear layers, with their halvings, 0.2M. An extension
multiplication is 28 tower multiplications (a Karatsuba version would be
about 40,000, still 18×). Applied to the `whir` crate's 2^20 KoalaBear
configuration (2,157 permutations: 1,300 in paths, 800 in leaves, 57 in the
transcript; about 7,500 extension multiplications):

| the same WHIR opening as a circuit | hashing | arithmetic | total |
| --- | ---: | ---: | ---: |
| KoalaBear, Poseidon2 (as the `whir` crate verifies it) | 2.68G | ~0.45G | **~3.1G**, above `bitvm-gc`'s Groth16 verifier |
| KoalaBear, Blake3 in place of Poseidon2 | 19M | ~0.45G (~0.3G with Karatsuba) | **~0.3G to 0.5G** |
| `GF(2^128)`, Blake3 (measured, 2^18) | 16M | 5M | **21M** |

Poseidon2 alone puts the KoalaBear verifier at the Groth16 circuit's size;
with the hash swapped, the extension arithmetic still leaves it 15 to 20×
the binary-field verifier, and in a full STARK every opened extension value
costs about 125,000 gates against 4,400. The proof handed to a garbled
verifier should be binary-field native.

## Layout

| module | what |
| --- | --- |
| `tower` | `GF(2^128)` tower arithmetic on wires, level by level against `p3-binary-field` |
| `pruned` | expansion of Plonky3's pruned Merkle proofs into per-query paths |
| `reference` | the WHIR verifier on field elements, op for op with Plonky3 |
| `circuit` | the WHIR verifier on wires, with a prefix hook and a gate profile |
| `stark`, `stark_circuit` | the multi-STARK layers (zerocheck, column batching, bit ring switch) as reference and as wires |
| `koala` | KoalaBear and Poseidon2 on wires, for the comparison above |
| `garble` | garbling and evaluation of a stored gate list |
| `tests/binary_whir.rs` | real WHIR proofs; `tests/keccak_stark.rs` real Keccak-f STARK proofs |

## Plan

1. Done: the WHIR verifier and the full multi-STARK verifier, each checked
   op for op against Plonky3's run and accepting real proofs; garbled and
   evaluated by streaming in live-wire memory; multi-chunk Blake3; the
   Merkle cap; profiles and parameter sweeps.
2. Circuit size: the ring switch closing (a third of the full verifier), a
   sub-Karatsuba `GF(2^128)` multiplier (a quarter of every circuit is
   multiplication), per-tree cap heights (a Plonky3 change), and the trace
   width of the statement that will actually be verified, which sets three
   of the big items.
3. The on-chain side waits for a design. Verifiable garbling comes from
   `bitvm-gc`'s zkVM proof of garbling (its `check_guest` uses the same gate
   formulas; with Blake3 as the PRF the guest needs the `blake3` feature
   rather than the Poseidon2 or AES precompiles), not from cut-and-choose.
