# whir-gc

A binary-field STARK verifier as a Boolean circuit, to be garbled. It is
Plonky3's `p3-multi-stark` over the WHIR polynomial commitment, with every field
in the `GF(2^128)` tower and Blake3 for commitments, transcript and garbling.
The paper, [`paper/garbled-stark-verifier.pdf`](../paper/garbled-stark-verifier.pdf), covers the design, the
security and post-quantum analysis, the on-chain protocol and its cost, and the
full measurements.

Built on the circuit API of GOAT's [`bitvm-gc`](https://github.com/GOATNetwork/bitvm-gc)
(`garbled-snark-verifier`), using:
- its Blake3 gadget (`blake3_ckt`, 10,281 AND per compression);
- its streaming garbler (`stream`);
- its gate garbling and evaluation (`gate_garbled_with_delta`, `gate_evaluate`).

## Results

The trace is Keccak-f with 1,625 columns. The WHIR parameters are rate 1/32,
folding 4 and 110 bits per term. Each circuit accepts its real proof. At 2^5 and
2^8 rows, the test also checks that the circuit rejects the proof with one
opened value changed.

| trace | non-free gates | garbled | bytes per committed cell | garbler memory | input bits | soundness |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 2^5 rows | 44,573,121 | 713 MB | 13,715 | 0.32 GiB | 586,240 | 106.1 |
| 2^8 rows | 66,459,859 | 1,063 MB | 2,556 | 0.46 GiB | 743,808 | 105.2 |
| 2^12 rows | 77,736,394 | 1,243 MB | 186.9 | 0.54 GiB | 874,240 | 104.7 |
| 2^16 rows | 88,680,747 | 1,418 MB | 13.32 | 0.61 GiB | 997,760 | 104.3 |
| **2^18 rows** | **94,069,548** | **1,505 MB** | **3.53** | 0.65 GiB | 1,041,024 | 104.3 |
| 2^20 rows | 99,613,898 | 1,593 MB | 0.94 | 0.68 GiB | 1,108,992 | 103.95 |

- **Garbled size** is 16 bytes per non-free gate. Garbling takes under a minute
  on one core.
- **Garbler memory** is the plan (one byte per wire) plus 18 bytes per live
  wire.
- **Whole-process peak.** The 2^18 run peaks at 5.82 GiB, almost all of it
  proof generation, which took 87 min on 8 cores.
- **Soundness** is Plonky3's composed bound, in bits.

## Running

```
LIMIT="systemd-run --user --scope -q -p MemoryMax=32G -p MemorySwapMax=0 taskset -c 0-7"
RAYON_NUM_THREADS=8 $LIMIT cargo test -p whir-gc --release --test keccak_stark -- --nocapture
WHIR_GC_LOG_HEIGHT=18 RAYON_NUM_THREADS=8 $LIMIT cargo test -p whir-gc --release --test keccak_stark \
    full_verifier_circuit_on_the_2_18 -- --ignored --nocapture
```

Every test runs in 32 GB of RAM on 8 cores, so a regression kills the test and
not the machine. The default tests do three things:
- check the reference against Plonky3's verifier;
- garble the full circuit at 2^5 and 2^8 rows;
- print Plonky3's soundness report.

The ignored tests are:

| test | what it does |
| --- | --- |
| `full_verifier_circuit_on_the_2_18_schedule` | any height from `WHIR_GC_LOG_HEIGHT` |
| `stored_build_of_the_full_verifier` | the memory comparison |
| `whir_schedule_of_the_measured_configurations` | queries and grinding per round |
| `input_bits_of_whir_configurations` | the input-size sweep |
| `garbled_before_the_proof_evaluates_real_proofs` | garbles with every input at 0, then evaluates the stored garbling on a real proof (label of 1) and on a changed proof (label of 0) |

## Layout

| module | what |
| --- | --- |
| `tower` | `GF(2^128)` tower arithmetic on wires, checked against `p3-binary-field` |
| `pruned` | expansion of Plonky3's pruned Merkle proofs into per-query paths |
| `reference` | the WHIR verifier on field elements, op for op with Plonky3 |
| `circuit` | the WHIR verifier on wires, with a prefix hook and a gate profile |
| `stark`, `stark_circuit` | the multi-STARK layers (zerocheck, column batching, bit ring switch), as reference and as wires |
| `garble` | garbling and evaluation of a stored gate list |
| `tests/keccak_stark.rs` | real Keccak-f STARK proofs, verified by the reference and garbled |
