# bitcoin-stark-verifier

Two ways to verify a STARK on Bitcoin as it is today, using **no `OP_CAT`** and
no other disabled opcode:
- **in Bitcoin Script**, with Poseidon2 over KoalaBear and WHIR;
- **as a garbled circuit**, with Plonky3's multi-STARK over binary-field WHIR,
  whose verifier is garbled off-chain and evaluated in a dispute.

| Crate | What it is |
| --- | --- |
| [`poseidon2`](poseidon2/) | Poseidon2 over KoalaBear in Script: the permutation, the degree-4 extension field, row hashing and Merkle path verification |
| [`whir`](whir/) | The WHIR verifier in Script on top of it, run end to end against Plonky3's prover |
| [`whir-gc`](whir-gc/) | Plonky3's full multi-STARK verifier over `GF(2^128)` and Blake3 as a Boolean circuit, garbled by streaming on GOAT's [`bitvm-gc`](https://github.com/GOATNetwork/bitvm-gc) |

| Document | What it covers |
| --- | --- |
| 📄 [Algorithm and implementation review](docs/whir-review.pdf) | The STIR and WHIR proximity tests, and what the Script verifier checks and does not |
| 📄 [Paper: Garbling a Post-Quantum STARK Verifier for Bitcoin](paper/garbled-stark-verifier.pdf) | The garbled verifier, its security and post-quantum analysis, a BitVM3-style protocol with its on-chain cost, and the measurements |

```
cargo test                              # everything: 131 tests, 6 more ignored as heavy
```

Run the tests under a memory cap; [`whir-gc/README.md`](whir-gc/README.md)
gives the command.

## The Script verifier

Script has no byte concatenation, so a SHA256 Merkle step needs `OP_CAT`. A
Poseidon2 digest is field elements, which Script can pass to an arithmetic
routine with nothing to concatenate. On that basis [`whir`](whir/) verifies a
real Plonky3 WHIR proof entirely in Script.

The cost is the obstacle:
- **Total size:** the 2^20 example configuration is 2,162 Poseidon2
  permutations, 1.24 GB of script, or 309 blocks.
- **One permutation doesn't fit a transaction:** a standard transaction holds
  0.70 of one permutation.
- **So it runs as a dispute:** the verifier executes as a dispute over
  committed sub-query chunks, about 2,000 of them for the 80-bit, 20-variable
  configuration.

Details, measurements and the soundness regimes are in
[`whir/README.md`](whir/README.md) and [`poseidon2/README.md`](poseidon2/README.md).

## The garbled verifier

The whole verifier for a 2^18-row, 1,625-column Keccak-f trace at 104 bits of
soundness is a circuit of 94.1M non-free gates. It garbles to 1.5 GB in under a
minute on one core and needs under 0.7 GiB of memory. That is about 30× fewer
non-free gates than the Boolean-garbled Groth16 verifier, with no pairing and no
trusted setup. The circuit is garbled before any proof exists. A challenger
evaluates the stored garbling on the operator's proof: a valid proof yields the
accept label, and a changed one yields the reject label that disproves it.

The price is on-chain. A dispute publishes the proof's million input bits,
which is 2.5 MvB with adaptor signatures and 12 to 17 MvB with hash-based keys.
Tuning the proof removes a fifth of that. Details are in
[`whir-gc/README.md`](whir-gc/README.md) and the paper.

## Credits

[Plonky3](https://github.com/Plonky3/Plonky3) for the specification and the
prover, [BitVM](https://github.com/bitvm/bitvm) and
[`rust-bitcoin-m31`](https://github.com/Bitcoin-Wildlife-Sanctuary/rust-bitcoin-m31)
for the Bitcoin Script field-arithmetic technique, and GOAT's
[`bitvm-gc`](https://github.com/GOATNetwork/bitvm-gc) for the garbling code.
