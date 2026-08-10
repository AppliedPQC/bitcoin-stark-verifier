# bitcoin-stark-verifier

A STARK verifier in Bitcoin Script, using **no `OP_CAT`** and no other disabled
opcode.

| Crate | What it is |
| --- | --- |
| [`poseidon2`](poseidon2/) | Poseidon2 over KoalaBear — the permutation, the degree-4 extension field, row hashing and Merkle path verification |
| [`whir`](whir/) | The WHIR verifier on top of it — Fiat–Shamir sponge, challenger, sumcheck rounds, multilinear evaluation, query openings, constraint batching and the closing identity |

📄 **[Algorithm and implementation review](docs/whir-review.pdf)** — a formal
account of the STIR and WHIR proximity tests, what this implementation checks,
what it does not, and why. Source: [`docs/whir-review.tex`](docs/whir-review.tex).

```
cargo test                              # everything, 107 tests
cargo test -p whir --test end_to_end    # a real Plonky3 proof, in script
cargo test -p whir --test budget        # what it would cost on-chain
```

## Why no `OP_CAT`

`OP_SHA256` hashes one stack item, while a Merkle step hashes two children
concatenated — so a byte hash needs `OP_CAT`, which is disabled, and re-enabling
it means a soft fork ([BIP-347](https://github.com/bitcoin/bips/blob/master/bip-0347.mediawiki)
is `Complete` but not deployed).

An **algebraic** hash removes the dependency. A Poseidon2 digest is eight field
elements rather than thirty-two bytes, so compressing two children hands sixteen
field elements to a width-16 permutation — sixteen stack items passed to an
arithmetic routine, with nothing to concatenate. It is also the hash
[Ziren](https://github.com/ProjectZKM/Ziren) commits with.

## What the verifier does

`verifier::verify_and_close` emits the whole schedule and ends on the identity
the protocol exists to reach:

```
claimed_eval == w(R) · f_M(r_fin)
```

Every value in it is derived inside the script. `R` is each round's folding
randomness, accumulated by the sumcheck rounds rather than discarded; `w(R)` is
the accumulated constraints evaluated at `R`; `f_M` is a copy the absorb kept of
the final polynomial, and `r_fin` is the tail of `R`.

Per round the schedule absorbs the commitment, alternates out-of-domain samples
with their answers, opens the round's queries against the **previous** round's
commitment, and runs its sumcheck rounds. Query indices are squeezed from the
sponge, and the index *is* the Merkle path: the spender picks neither which leaf
is opened nor where it sits.

### What is checked

- **Challenges are unchooseable.** Every one is squeezed after the values it
  depends on are absorbed. Supplying them instead is not a shortcut but a
  soundness error of exactly one — the review works out why.
- **An opening is one unit.** The row is bound to its leaf by
  `merkle::hash_row` (Plonky3's `PaddingFreeSponge`, checked against it on a row
  from a real proof), the path recomputes the root, and that root is the
  **absorbed commitment** rather than a value taken from the witness.
- **The closing identity is real.** All four extension coefficients, against a
  claim the transcript produced.

- **The constraints are derived, not supplied.** Each round buries the
  out-of-domain scalars it samples, the shift points its queries produce
  (`domain_gen^index`) and its batching challenge below the folding randomness;
  the closing check lifts them back out and evaluates the whole weight
  polynomial from them. A round costs `1 + n` extension elements to carry rather
  than `n · (1 + arity)`, because its constraints share a challenge and each
  point is the square-power expansion of one scalar.

### What is not

The **statement** is supplied, and always will be: its point is public because
it *is* the claim being proved, and a different point is a different statement
rather than a cheaper proof of the same one.

Two fidelity items remain against Plonky3. Each constraint group ends with a
fresh squeeze for its batching challenge rather than reading whichever rate slot
the query indices happened to leave — one permutation per round, traded for not
coupling the challenge's position to the query count. And Plonky3 folds the
statement and the commit phase's out-of-domain samples into one
`initial_constraint` with a shared challenge, where this treats them as two
groups.


## End to end

`whir/tests/end_to_end.rs` runs [Plonky3](https://github.com/Plonky3/Plonky3)'s
actual WHIR prover over KoalaBear, verifies the proof with **Plonky3's own
verifier**, then re-derives the same claims in Bitcoin Script and executes it.

The native verification comes first on purpose. Every other test compares a
script against a Rust reference, which establishes that the two agree — not that
either is right. Where a primitive exists in Plonky3, it is checked against
Plonky3 directly: `eq_eval` against `Point::eval_eq`, `expand_univariate`
against `Point::expand_from_univariate`, the leaf hash against
`PaddingFreeSponge`.

No hand-built vectors are involved. Perturbing any evaluation moves the squeezed
challenge, which moves the chained claim, which breaks the closing identity —
asserted for every evaluation in the proof.

## Measured cost

Everything follows from one constant: a Poseidon2 permutation is **572,228
bytes**, and nothing else is within 1% of it. Each figure below is the length of
a script some test executes.

| | bytes |
| --- | ---: |
| one Poseidon2 permutation | 572,228 |
| one Merkle level | 572,252 *(24 bytes of ordering overhead)* |
| Merkle path at depth 21 | 12,017,292 — **3.0 blocks** |
| `sumcheck_round()` | 95,100 |
| `sumcheck_round_fs()` | 667,539 |
| …keeping its challenge for the closing check | 667,615 — **+76 B, 0.011%** |
| `eval_multilinear(4)` | 358,048 |
| `eq_eval(4)` | 190,780 |
| `constraint_eval`, 10 constraints of arity 8 | 4,053,279 |
| …derived from scalars instead | 5,687,109 — **+40%** |
| the whole closing check, example config | 92,801,911 — **7.5%, 0 permutations** |
| **composed sumcheck chain, one real proof** | **8,967,342** |

For the 2²⁰ example configuration — 20 queries, folding factor 4 —
`whir/tests/verifier.rs` reports:

| | permutations |
| --- | ---: |
| Merkle paths | 1,300 |
| leaf hashing | 800 |
| transcript | 62 |
| **total** | **2,162** = 1.24 GB = **309.3 blocks** |
| **query share** | **97.1%** |

Leaf hashing is 37% of that on its own: a row at folding factor 4 is sixteen
extension elements, so sixty-four base elements, so eight permutations per query
on top of the twenty-one the path costs. It buys the binding — without it a
spender could authenticate the committed leaf and fold a different row.

The closing identity is **92,801,911 bytes — 7.5% of the verifier, and no
permutation at all**, evaluating 110 constraints derived from the transcript.
Against a supplied list it is 1.5 MB; deriving is what stops a spender choosing
them. Arithmetic is the cheap part without being a free one.

## Does it fit in a transaction?

No, and the wall is lower than a query. Taproot removed the 10,000-byte script
limit and the 201-opcode cap, so what binds is weight: 400,000 units for a
standard transaction, 4,000,000 for a block, witness bytes counting one each.

**A standard transaction holds 0.70 of a single permutation.** One *hash* does
not fit, let alone one query — which is 3.4 to 4.6 blocks across every
configuration `whir/tests/budget.rs` derives.

Lowering the security level does not change that. It buys **fewer queries, not
cheaper ones**: at 16 variables a query costs the same 13.7 MB at 80 and 100
bits, because depth is set by the domain size and not by λ. What moves is the
total:

| λ | pow | vars | permutations | blocks |
| ---: | ---: | ---: | ---: | ---: |
| 100 | 22 | 16 | 976 | 139.6 |
| 80 | 22 | 16 | 740 | **105.9** |
| 80 | 22 | 20 | 991 | 141.8 |
| 80 | 22 | 24 | 1,249 | 178.7 |

Chunking is therefore not optional, and its unit has to be *sub-query*.

## Chunks

The verifier is never executed on-chain. What can be is one **step** of it, if
the prover commits to the state between steps and a challenger names the step it
claims is wrong — so what matters is the step count and whether a step relays.

A step cannot be one Merkle level (572,252 bytes against 400,000 weight units),
so it has to be sub-permutation. That is less awkward than it sounds: a
permutation is already a chain of rounds, each taking a state and leaving a
state, and `permutation::rounds()` emits them with a test pinning their
composition to `permute()`.

A step also has to be *bound*. A predicate over supplied states decides nothing
about whose claim it is — a spender answers one challenge with one state and the
next with another — so both states come from Winternitz one-time signatures.
Those fit Bitcoin for the same reason the rest of this does: a hash chain only
ever hashes a single item, so `OP_HASH160` suffices and no soft fork is needed.

The Winternitz parameter is forced from above rather than chosen. One chain per
bit is the cheapest thing to verify and does not work: a state is 496 bits, so
505 chains, so **1,010 witness items against Bitcoin's 1,000-item stack limit**
— the script fails before executing an opcode. At `w = 16` a state is 131 chains
and two signatures are 524 items.

The last saving is to commit at *chunk* boundaries rather than every round,
since a challenger only executes the run containing the disputed round:

| | bytes | of a standard tx | commitments per permutation |
| --- | ---: | ---: | ---: |
| one committed round | 94,020 | 23.5% | 29 |
| a **22-round chunk** | 395,916 | 99.0% | **2** |

22 is longer than dividing the budget by a round suggests, because the rounds
differ by 6×: an external round applies the S-box to all sixteen state elements
(50,028 B), an internal round to one (8,434 B), and the eight external rounds
sit at opposite ends so no window of 22 holds more than four. `max_chunk_len`
takes the length whose *worst* window fits, not the budget over the mean.

The 80-bit, 20-variable verifier is then **≈2,000 chunks**, the same order as
BitVM2's own leaf count — and because the commitments *are* the setup, that
figure bounds setup as well as the spend.

**What the count leaves out.** Generating the keys: 2,000 boundaries at 131
chains each is roughly a quarter of a million hash chains, which is the cost
BitVM2 deployments actually struggle with. And the arithmetic between
permutations does not decompose — 2% of the verifier, still 25 MB with no step
boundaries in it, and so not counted in the 2,000.


## Security parameters

`pow_bits: 0` is not a conservative choice; it is a configuration that mostly
does not exist. Neither security level is derivable past a toy instance without
grinding: 100-bit at 16 variables already requires 19 bits, 20 variables
requires 28, and 24 requires 37. Even 80-bit needs 8 bits at 20 variables.
KoalaBear gives log₂(p) = 30.989 and degree 4, so 123.955 bits are available and
the field is never what binds.

The soundness regime is `SecurityAssumption::CapacityBound`, the cheapest of the
three and the only one resting on the unproven half of WHIR's Conjecture 4.12.
Nothing in the implementation mentions a soundness assumption — the script
executes a schedule, and the regime reaches it only as a query count — so the
choice is a config change. `cargo test -p whir --test budget` prices it, giving
each regime the grinding it needs:

| regime | vars | pow | queries | permutations | vs CB |
| --- | ---: | ---: | ---: | ---: | ---: |
| UD, proved | 16 | 0 | 110 | 7,376 | **7.18×** |
| JB, Conj. 4.12(1) | 16 | 26 | 39 | 1,853 | 1.80× |
| CB, Conj. 4.12(2) | 16 | 19 | 21 | 1,027 | 1.00× |
| UD, proved | 20 | 0 | 110 | 11,171 | **9.01×** |
| JB | 20 | 33 | 35 | 2,222 | 1.79× |
| CB | 20 | 28 | 19 | 1,240 | 1.00× |

UD wants no grinding at all and pays entirely in queries, capped at 110
regardless of size — so the gap widens with the witness rather than staying
fixed. JB wants *more* grinding than CB, which is the direction a weaker
assumption should push. A verifier that settles bitcoin should say out loud
which assumption it stands on, and what the proved one would cost.

## Credits

[Plonky3](https://github.com/Plonky3/Plonky3) for the specification and the
prover, [BitVM](https://github.com/bitvm/bitvm) and
[`rust-bitcoin-m31`](https://github.com/Bitcoin-Wildlife-Sanctuary/rust-bitcoin-m31)
for the Bitcoin Script field-arithmetic technique.
