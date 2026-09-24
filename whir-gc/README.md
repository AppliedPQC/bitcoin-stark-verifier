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
Groth16 verifier.

Built on the circuit API of GOAT's [`bitvm-gc`](https://github.com/GOATNetwork/bitvm-gc)
(`garbled-snark-verifier`), with Blake3 as the garbling PRF (`_blake3`): its
Blake3 gadget (`blake3_ckt`, 10,281 AND per compression), its streaming
garbler (`stream`) and its gate garbling and evaluation
(`gate_garbled_with_delta`, `gate_evaluate`). The proofs are Plonky3's, over
`BinaryField128` on the additive Cantor domain with Blake3 commitments.

## The full STARK verifier, garbled

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
full circuit through the garbler: each gate garbled under a secret random
`Δ` and checked by the evaluator's formula on the held labels, one label per
live wire. Rate 1/32, folding 4, terminal security 110, Blake3 everywhere:

| trace | packed variables | non-free gates | garbled | garble | peak RSS | inputs | proving |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^5 rows (1 Keccak-f) | 9 | 44,573,121 | 713 MB | 25 s | | 586,240 bits | 0.1 s |
| 2^8 rows (10 Keccak-f) | 12 | 66,459,859 | 1,063 MB | 37 s | | 743,808 bits | 1.2 s |
| 2^12 rows (163 Keccak-f) | 16 | 77,736,394 | 1,243 MB | 43 s | 616 MB | 874,240 bits | 75 s |
| **2^16 rows (2,621 Keccak-f)** | 20 | **88,680,747** | **1,418 MB** | 61 s | 1.5 GB | 997,760 bits | 44 min |

Each accepts its proof and rejects it with an opened value changed. The
2^18 case is not yet measured (about +5M gates per two variables from the
slope above, so ~95M); it is the `#[ignore]`d test, a few hours of proving
on one core with a 6 GB peak.

## Running

```
(ulimit -v 7340032; cargo test -p whir-gc --release --test keccak_stark -- --nocapture)
(ulimit -v 10485760; WHIR_GC_LOG_HEIGHT=18 cargo test -p whir-gc --release --test keccak_stark \
    full_verifier_circuit_on_the_2_18 -- --ignored --nocapture)
```

Run under a cap, so a regression kills the test and not the machine.
`reference_verifies_real_keccak_stark_proofs` checks the reference against
Plonky3's verifier, `full_verifier_circuit_accepts_real_keccak_stark_proofs`
garbles the circuit at 2^5 to 2^16 rows, and
`security_of_the_measured_configurations` prints Plonky3's soundness report.

## Where the gates go

The 2^16 circuit, by the phase that emits each non-free gate:

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

## Layout

| module | what |
| --- | --- |
| `tower` | `GF(2^128)` tower arithmetic on wires, level by level against `p3-binary-field` |
| `pruned` | expansion of Plonky3's pruned Merkle proofs into per-query paths |
| `reference` | the WHIR verifier on field elements, op for op with Plonky3 |
| `circuit` | the WHIR verifier on wires, with a prefix hook and a gate profile |
| `stark`, `stark_circuit` | the multi-STARK layers (zerocheck, column batching, bit ring switch) as reference and as wires |
| `garble` | garbling and evaluation of a stored gate list |
| `tests/keccak_stark.rs` | real Keccak-f STARK proofs, verified by the reference and garbled |

## Plan

1. Done: the full multi-STARK verifier, checked op for op against Plonky3's
   run and accepting real proofs, garbled and evaluated by streaming in
   live-wire memory.
2. Circuit size: the ring switch closing (a third of the verifier), a
   sub-Karatsuba `GF(2^128)` multiplier, per-tree cap heights (a Plonky3
   change), and the trace width of the statement that will actually be
   verified, which sets three of the big items.
3. The on-chain side is on hold until there is a design.
