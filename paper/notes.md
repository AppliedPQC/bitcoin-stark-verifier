# Literature notes for the whir-gc paper

These are working notes, one section per source, kept alongside `garbled-stark-verifier.tex`. Each
number is quoted from the source, with its section, table or figure. Anything
marked **[ours]** is our own reading or measurement and not a claim the source
makes. PDFs are in `refs/`, which is git-ignored.

The last section lists errors and open points to fix before release.

---

## 1. BABE: *Verifying Proofs on Bitcoin Made 1000x Cheaper* — ePrint 2026/065

Garg, Kolonelos (UC Berkeley), Sergeevitch (Babylon Labs), Sridhar (Byzantine
Research), Tse (Byzantine Research, Stanford). 61 pp.

- **Problem.** Verify Groth16 proofs on Bitcoin in the BitVM setting (Prover and
  Verifier, hashlocks and timelocks only). BitVM2's unhappy path costs over
  $14,000 on-chain. BitVM3's garbled Groth16 verifier costs little on-chain but
  is 42 GiB per garbled circuit (Abstract, Sec. 1.2).
- **BitVM3 baseline, as they report it.** They cite BitVM/garbled-snark-verifier
  [Bit25b]: about 10B gates and 3B non-free, with free-XOR and privacy-free half
  gates, giving a 42 GiB garbled circuit and 6 minutes to garble one circuit on
  one core (Sec. 1.2.2). The storage figure in Fig. 2 is 2.7B non-free gates at
  16 B each, about 41,200 MiB (Sec. 9.1). Cut-and-choose setup at
  (N_CC, M_CC) = (181, 7) is 3:24:24, estimated as twice the garbling time
  (Tab. 3).
- **Alternatives they mention.**
  - Eagen's Glock [Eag25] uses a designated-verifier SNARK on a binary curve,
    giving a 12 MB garbled circuit. BABE says that "the security of binary curves
    is not widely accepted", so the approach "is not currently pursued in
    practice".
  - [FBFL25] garbles the verifier with arithmetic circuits: "still expected to be
    100 million ciphertexts (a few GBs)" (Sec. 1.2.2).
- **Idea.** Witness encryption for *linear* pairing relations
  [BC16, GKPW24]. For `e(w1,x1)+e(x2,w2)=x3` the ciphertext is
  `(r x1, r x2, r x3 + msg)` (Sec. 1.3.2). Groth16 is quadratic because of
  `e(π1, π2)`, so they treat π1 as a public input:
  `e(x0,π2)+e(π3,x1)=x2`, with `x0 := π1`. The ciphertext needs `r·π1`, which is
  unknown at setup. A maliciously secure 2PC gives it: the Verifier garbles a
  circuit computing `r·π1` with `r` hard-coded, and the Prover's input labels
  are the Lamport signature on π1 (Sec. 1.3.2, Fig. 4).
- **Roles are reversed relative to BitVM3.** In BitVM3 the garbled circuit
  releases the secret on an *invalid* proof (the Verifier wins). In BABE's WE
  view, the Prover decrypts with a *valid* proof and opens the hashlock
  (Figs. 1 and 3).
- **Garbling r·π1.** Builds on Argo MAC [EL26]. Decomposable randomized
  encodings (DRE, [IK00, Ish13]) reduce the BN254 scalar multiplication to a
  254-dimensional vector homomorphic MAC. Each component is linearised by
  feeding in the monomials `(x, y, x², y², xy)`, making it an inner product. A
  small Boolean Yao circuit computes the monomials and checks the point
  (Sec. 1.3.3, Sec. 5).
- **Sizes (Sec. 9.1).**
  - Per-instance artifact: **22.16 MiB**. That is 6.35 MiB of Boolean Yao gadgets
    (π1 validation and the feature vector), plus 15.77 MiB of DRE selection
    tables (n(8n+3) = 516,890 field elements of 32 B), plus 480 B of WE
    ciphertext.
  - Setup: 174.9 ms. Decryption: 126.5 ms, single-threaded on a Ryzen 7 7840U.
- **On-chain (Tab. 1, mainnet experiment).** Assert 9,240 vB, ChallengeAssert
  17,400 vB, WronglyChallenged 149 vB. That is **$56.90** at 2.2 sat/vB and
  BTC = $95,500. BitVM3 is $37.65 and BitVM2 $14,211 (Fig. 2).
- **Malicious setup (Sec. 9.2–9.4).**
  - Cut-and-choose with soundness error at most 2^-40. Setup time by
    (N_CC, M_CC): 0:06 at (78, 10), 0:09 at (181, 7), 1:37 at (2,268, 4). Peak
    RAM stays around 1–2 GB.
  - zk-SNARK soldering (an SP1 zkVM prototype) reduces the on-chain input-label
    sets from M_CC to one. It takes 745.5 s at M_CC = 4 for BABE (508 labels),
    and 1,529–1,977 s for BitVM3 (1,019 labels) (Tabs. 4–6).
  - Verifiable Shamir secret sharing (the Glock-inspired alternative) adds
    33–333 s (Tab. 7). Its on-chain integration isn't done yet.
- **Security.**
  - The BitVM-core primitive (Sec. 3) has two properties. u-Robustness: an
    honest Prover with a valid witness wins. Knowledge soundness: a Prover wins
    only if the witness can be extracted.
  - Honest-setup security: Thms. 6–8, assuming a ledger with safety, liveness
    and chain growth. The WE part uses the generic bilinear group model and a
    random oracle (Sec. 2.2.1, Sec. 4).
  - Groth16 knowledge soundness is Thm. 2.
- **[ours] Relevance.**
  - Post-quantum: no. It uses BN254 pairings and Groth16, with a trusted setup
    per circuit.
  - The statement must be Groth16, so any other proof system has to be wrapped
    in Groth16.
  - On-chain cost is the same order as garbled-circuit BitVM3.
  - Its 22 MiB beats our 1.5 GB of garbled circuit by about 70×. We verify a
    STARK directly, post-quantum, with no wrapping and no trusted setup.

## 2. Partial-binding WE over Groth16 — bitvm-gc `docs/partial_binding_we.tex`

Stephen Duan, 2026-04-19. Internal note, built on BABE.

- **Problem.** BABE's `Enc` needs the *whole* public-input vector at encryption
  time, which is peg-in for a bridge. Some inputs (the chain tip, a watchtower
  bitmap) are only known at dispute time.
- **Construction.** Split the public inputs into a static part `x_S`, fixed at
  encryption, and a dynamic part `x_D`, fixed at dispute time.
  - Encrypt under `Y_S = e(α,β)·e(P_S,γ)`, blinded by `e(B,γ)^{-1}`.
  - A **Dual-Scalar Garbled Circuit** outputs `r·π1` and `r·P_D + r·B`, with
    `r·L_j` and `r·B` baked in as constants.
  - The `x_D` input wires are Lamport-soldered, so only the on-chain-committed
    `x_D` can be fed in.
  - The construction relies on Groth16's *linear* public-input aggregation
    `vk_x = Σ x_j L_j`.
- **Security.** `Adv ≤ Adv_BABE + Adv_DLog(G1)`, plus garbling security and
  Lamport one-wayness. There is a sketch of a UC proof (App. A).
- **Cost.** Each dynamic slot adds about 1.5·10^8 gates to the garbled circuit.
  The note gives BABE's base garbled circuit as about 4.7·10^8 gates. For the
  BitVM2 bridge with |D| = 4, the circuit is about 1.1·10^9 gates. Lamport
  witness: +|D|·254 bits.
- **In code.** `verifiable-circuit-babe`: `gc/circuit.rs` has "Circuit 1 / FGC"
  computing ū(π) and "SGC Part 1" computing `Q = x_d·L_2 + B`. `dre/` holds the
  DRE, and `babe-programs/soldering` is a Ziren (zkm) guest for soldering.
  `N_CC = 181` and `M_CC = 7` are the production values in the comments; the
  code sets 4 and 2 for tests.
- **[ours] Inconsistency to resolve.** The note's 4.7·10^8-gate figure for the
  basic BABE garbled circuit doesn't match BABE's own 22 MiB artifact, which is
  6.35 MiB of Yao gadgets plus DRE tables. The note seems to count a Boolean
  scalar-multiplication circuit (GOAT's implementation?), while BABE garbles
  most of the work through DRE. Check which one GOAT deploys before quoting
  either.

## 3. Bitcoin PIPEs v2 — ePrint 2026/186

Abdalla, Carmer, El Gebali, Kilinc-Alper, Komarov, Rebenko, Soukhanov, Tairi,
Tatuzova, Towa (alloc init). 22 pp.

- **Idea.** Witness-encrypt a Schnorr signing key under an NP statement x. A
  valid witness decrypts the key, and the spend is an ordinary Schnorr/P2TR
  signature, so there is no soft fork (Sec. 1, Fig. 1).
- **Witness Signature (WS) primitive** (Sec. 3): Setup, OutVerify, WSign.
  Properties: correctness, WS-EUF-CMA and verifiability.
  - The construction (Sec. 4) is `ct = WE.Enc(x, sk)` plus a NIZK that `ct`
    encrypts the `sk` for `pk`.
  - Security (Thms. 1–3) rests on Schnorr EUF-CMA, a hard relation, NIZK zero
    knowledge and *extractable* WE.
- **Limits they state.**
  - The key is released once, not per transaction ("binary NP covenant",
    Def. 1.1). There is no template enforcement like `OP_CTV` (footnote 2).
  - In BitVM-PIPE the statement includes `h = Hash(w)`, so the operator must
    know w at setup. GC setup doesn't need w (Sec. 6).
- **WE instantiation.** AADP, the next section. The ciphertext is estimated at
  about **338 TB** for a SNARK verifier (Sec. 5.3.1). Security is heuristic
  (Sec. 5.2).
- **BitVM mapping (Sec. 6).** The relation is `R = (f(w) = 0) ∧ (h = Hash(w))`.
  AssertTx carries one hash and DisproveTx one signature. The signer committee
  is n-of-n, and one honest challenger suffices.
- **[ours]** "Any NP relation" holds in theory. In practice only statements
  proven in their custom small-verifier SNARK qualify, because the ciphertext
  grows cubically. It isn't post-quantum.

## 4. AADP witness encryption — ePrint 2026/175

Soukhanov, Rebenko, El Gebali, Komarov, Kilinc-Alper, Abdalla, Towa (alloc
init). 38 pp.

- **Arithmetic ADPs.** Constraints have the form `(Ax)∘(Bx) = (Cx)∘(Dx)` over a
  large field. Each constraint is a 4×4 block `U_i`, of rank 2 if it holds and
  rank 4 otherwise. The blocks are randomised as `L_i U_i R_i` and summed into a
  `(2m+1)×(2m+1)` matrix, which has rank 2m exactly on solutions (Alg. 1,
  Thm. 1).
  - Encryption adds msg to the bottom-right entry of `M^0`. Decryption solves
    `det(E − t e eᵀ) = 0` for t (Algs. 2–3).
- **Projective safety** (Def. 3): every variable needs a certificate
  `x_i² = a(x_0..x_{i−1})·b(x)`, which rules out solutions at infinity.
  Otherwise the correlated span attack recovers the randomness (Sec. 3.1–3.2).
- **Cryptanalysis.**
  - A parametric rank-drop attack **broke an earlier version**, the one with
    bit-check matrices (Sec. 3.3).
  - For the linearization attack they estimate at least `k^28` time and call the
    evidence "inconclusive" (Sec. 3.4).
  - Assumption 1 is extractable WE, which they acknowledge is non-falsifiable.
    It needs `g(x) > m^ε`, i.e. gates repeated.
  - Assumption 2 claims 100-bit concrete security, capped by BN254.
- **Gadgets** (Sec. 4). General multiplication costs `O(log|F|)`
  certification. Instead they build everything from "multiply and square root"
  steps `c² = ab` in the odd-order subgroup: exponentiation, the Miller loop with
  fixed G2 points, and Poseidon with an x^5 S-box.
  - "20,000 witness, 20,000 constraint system yield ciphertext sizes ≈ 1 PB";
    one 256-bit scalar multiplication would be "several exabytes" (Sec. 4.2).
- **SNARK** (Sec. 4.3). A modified squaring QAP with batched KZG and one pairing
  equation. The G2 points are fixed, rewritten from Pari's (Sec. 4.3 opening
  argument). The setup is circuit-specific. It is knowledge-sound in the
  generic group model plus the random oracle model (Thm. 3).
- **Cost** (Sec. 4.10, from a modelling script, github.com/alloc-init/adp-estimates):

  | subroutine | variables | gates |
  | --- | ---: | ---: |
  | extension basis | 11 | 22 |
  | glue | 1,265 | 1,270 |
  | hash | 1,017 | 1,192 |
  | non-native arithmetic | 3,578 | 3,580 |
  | pairing equation | 8,212 | 8,307 |
  | **total** | **14,083** | **14,371** |

  The ciphertext is `v(2g+1)²|F|`, about **338 TB**. That is cubic in circuit
  size since v ≈ g; the paper calls it "cubic scaling". There is no
  implementation.
- **[ours]** The gadgets need odd characteristic (square roots in the
  odd-order subgroup, Fermat certification), so binary-field arithmetic doesn't
  fit. Our 94M-gate verifier is 6,500 times their gate count, so roughly 10^20
  times larger under cubic scaling. It's out of reach.

## 5. Garuda and Pari — ePrint 2024/1245

Dellepere (Provable), Mishra and Shirzad (UPenn). 52 pp.

- **EPC.** Equifficient polynomial commitments enforce that several committed
  polynomials have equal coefficient vectors in bases the setup specifies. The
  commitment then handles the linear checks and the PIOP only the non-linear
  ones (Sec. 2.2–2.3).
- **Pari.** For square R1CS. The proof is **2 G1 + 2 F**, which is 1,280 bits
  (160 B) on BLS12-381. Groth16 is 1,536 bits and Polymath 1,408 (Table 1).
  - The verifier does 3 pairings plus O(|x|) field operations.
  - The prover does O(n log n) field operations and 4 MSMs of size about m.
  - It is proven in the algebraic group model plus the random oracle model
    (interactive version).
  - The setup is circuit-specific. It isn't zero-knowledge as written.
  - Pari is not implemented. The unrolled SNARK is Fig. 6: proof
    `(T, U, v_a, v_b)`, verifier `e(T, δ2H) = e(U, δ1τH − rδ1H)·e(v_aαG + v_bβG + v_qG, H)`.
- **Garuda.** For GR1CS (custom gates) with free linear gates and a linear-time
  prover. Proof and verifier are O(log m). The setup is circuit-specific.
  - It is implemented on arkworks. On Rescue-Prime it proves about 5× faster
    than Groth16 and 2.67× faster than HyperPlonk.
  - Proofs are 29–43× Groth16's size, and the verification key is up to
    14.78 kB (Sec. 2.7).
- **[ours] Connections.**
  - bitvm-gc's DV-SNARK (`circuits/sect233k1`, "ported from
    alpenlabs/dv-pari-circuit", and `dv_bn254`) is **designated-verifier Pari**.
    `ProofRef{commit_p, kzg_k, a0, b0}` corresponds to Pari's `(T, U, v_a, v_b)`,
    and `TrapdoorRef{tau, delta, epsilon}` is the setup trapdoor. The verifier
    replaces the pairings with a G1 relation, checked as the hinted double
    scalar multiplication `x1·G + x2·Q − z·P = 0`.
  - AADP's "Garuda-inspired" SNARK is structurally Pari.

## 6. A Note on the Security of the BitVM3 Garbling Scheme — ePrint 2025/1291

Futoransky and Barbara (Fairgate Labs), Larotonda (UBA/CONICET). 7 pp., with a
proof of concept (BitVM3-garbling-toy).

- They break the **authenticity** of RSA-based garbling:
  1. **BitVM3 [Lin25].** The rules have the form `x0 = a0^e · b0^{e1}`, with
     small public exponents. Fan-out needs adaptors. With exponents e and e2
     coprime, extended Euclid gives `b1 = (b1^e)^{k1} (b1^{e2})^{k2}`. That
     forges an input label from a 2-gate, 3-input circuit, and then the output
     label `x1` (Lemma 2, Cor. 3). "Most non-trivial circuits will suffer from
     many similar exponent collisions", and changing the circuit's topology
     doesn't help (Remark 4).
  2. **Label forward propagation [FDZ25], GOAT's scheme.** Forged through the
     output adaptors (Cor. 5).
  3. **Linear adaptors** (Linus's suggestion). The Franklin–Reiter
     related-message attack recovers `b1` (Thm. 6).
- **[ours]** It applies only to algebraic (RSA-homomorphic) labels. Hash-PRF
  garbling (free-XOR plus one ciphertext per AND, Blake3), which bitvm-gc and
  whir-gc use now, has no such label relations. This is a motivation for staying
  with hash-based garbling.

---

## 7. Our own measurements (whir-gc), for the Evaluation section

Everything was run under a cgroup cap of 32 GB and 8 cores unless noted. Raw
records are in `data/`.

- **2^18-row full STARK verifier** (Keccak-f, 1,625 columns, 22 packed
  variables; rate 1/32, folding 4, terminal security 110; composed 104.3 bits),
  from `data/run-2_18-full-verifier.txt`:
  - 94,069,548 non-free gates (94,041,082 AND and 28,466 OR), 563,964,415 XOR,
    659,074,989 wires, 1,041,024 input bits.
  - Garbled: 1,505 MB in 56.9 s on one core. At most 2,256,536 labels live at
    once. Plan pass: 21.3 s.
  - Proof: 140.0 KiB, of which 52,000 B are opened values, 72,235 B the WHIR
    opening, and 19,176 B the ring switch and zerocheck. Proving takes 5,202.5 s
    on 8 cores (586% CPU). Peak RSS is 6.1 GB, from the prover.
  - Gate profile: ring switch closing 33.6%, Merkle paths 15.5%, column
    combination 12.3%, AIR constraints 11.4%, STARK transcript 11.2%, the rest
    below 4% each.
- **Scaling table** (whir-gc README): 2^5, 2^8, 2^12, 2^16 and 2^18 rows give
  44.6M, 66.5M, 77.7M, 88.7M and 94.1M non-free gates.
- **Gadgets:**
  - `GF(2^128)` tower multiplication: 2,187 AND (3^7).
  - Blake3 compression: 10,281 AND, down from bitvm-gc's 20,657 (measured on
    bc3df6d) by using a one-AND adder. 256 B costs 41,511 and 1,072 B costs
    186,125.
- **Comparison circuits, streamed through the same garbler** (bitvm-gc
  10083d4):
  - bitvm-gc DV-SNARK (designated-verifier Pari, BN254): 481,628,790 non-free
    gates, 1.92B wires, 15.6M live at peak, 2.2 GB, 5m42s. It accepts the valid
    proof and rejects it with one bit flipped. The stored build needs more than
    64 GB.
  - Hinted double scalar multiplication (3 points): 457,933,037 non-free gates.
  - bitvm-gc `GF(2^233)` multiplication (evaluate-multiply-interpolate over
    GF(2^9)): 2,097 AND and 1,524,691 XOR.
- **Before trimming,** the README (`data/whir-gc-README-before-trim.md`) also
  recorded:
  - WHIR-only circuits: 8, 12 and 18 variables, and the effect of a Merkle cap
    (18 variables at a cap of 32 gives 21.2M).
  - Rate/folding sweep.
  - The KoalaBear/Poseidon2 comparison: one Poseidon2 permutation is
    1,240,747 AND, equal to 120 Blake3 compressions.
- **Upstream bugs found along the way,** fixed on bitvm-gc `whir-gc-upstream`:
  - `Cimp` garbling put `b1` in the ciphertext; it should be `b0`.
  - `test_fq_is_qnr_montgomery` misread its output wire.

## 7b. Added after the pre-submission review (abstracts checked on ePrint)

- **Garbling Groth16 with Native Group Operations (2026/2100).** Khambhati,
  Feickert, Lewe, Tiwari. The garbled program is 2.4 MiB including
  projectivization, against 48 GB for Boolean garbling of Groth16. This
  replaces "Boolean-garbled Groth16" as the size baseline for Groth16.
- **BitVM3: Efficient Bitcoin Bridges via Garbled Circuits (2026/933).** Linus
  Woll, Alexopoulos, Aumayr, Avarikioti, Maffei, Tse. Formalises BitVM3-CORE;
  on-chain cost is about $9, with $0.20 for the challenge.
- **Mosaic (2026/812).** Khambhati, Tiwari et al. (Alpen Labs). Maliciously
  secure cut-and-choose using polynomial label correlation; the on-chain
  footprint doesn't depend on the number of copies.
- **Antichain Winternitz (2026/1568).** Tiwari, Feickert. Reveals labels at up to
  52.9% less on-chain cost than Lamport, with 43.8 kB off-chain per bit.
- **Glock (2025/1485), primary source.** Garbled locks, using a
  designated-verifier variant of a modified Pari. The abstract gives no size; the
  "12 MB" figure is BABE's.
- **Argo MAC** is ePrint 2026/049.
- **ZKM blog, "Hash-based is not the same as post-quantum" (2026-09-03).** A
  post-quantum claim needs a stated assumption and a written reduction.

## 7c. Quantum analysis: verified inputs and measurements (2026-09-24)

- **CMS19 (ePrint 2019/834), checked in the text.** BCS applied to public-coin
  IOPs with round-by-round soundness error ε has soundness
  O(t²ε + t³/2^λ) against t-query quantum attackers.
- **WHIR (ePrint 2024/1586, EUROCRYPT 2025), checked.** §5.1 proves round-by-round
  soundness, "which ensures Fiat–Shamir and BCS security". For the sumcheck
  layers, round-by-round soundness is an *assumption* stated in the paper; still
  to be backed by a citation (e.g. CCHLRR18 for sumcheck).
- **WHIR schedule at 2^18** (term_bits 110,
  `whir_schedule_of_the_measured_configurations`):

  | round | queries | pow bits | folding pow bits |
  | --- | ---: | ---: | ---: |
  | 0 | 33 | 30 | 28 |
  | 1 | 20 | 32 | 30 |
  | 2 | 15 | 29 | 32 |
  | terminal | 12 | 27 | — |

  Starting folding pow is 26 bits.
- **Configuration ceiling** (`WHIR_GC_TERM_BITS` env override in
  `keccak_stark.rs`):
  - The profile accepts at most 134 bits per term. Queries stay the same and
    grinding rises to 51–56, its ceiling. At 200 bits it refuses:
    "Grinding { required: 103, ceiling: 56 }".
  - Plonky3's report fully assesses at most 117 bits per term: 108.6 composed,
    bound by constraint batching at 109.0, with WHIR at 111.3.
  - So about 54 quantum bits is the ceiling of the current proof system.
- **"From Cut-and-Choose to Constant-Size Proofs of Garbling Correctness":** not
  found on ePrint or in the zkMesh July recap. It is mentioned only in a search
  snippet, so it is NOT cited.

## 7d. On-chain protocol: sources and measurements (2026-09-24)

The user chose "enforceable protocol + shrink study": the operator garbles, challengers evaluate, the proof is published on-chain, and the reject label unlocks Disprove.

**Primary-source facts (PDFs in `refs/`):**
- **BitVM3 (2026/933).**
  - The operator garbles and the challenger evaluates (§1, §4.1).
  - Inputs are Schnorr adaptor signatures over 8-bit digits (§8.1): "9707 WU, or approximately 2.4 kvB" for a 128-digit (1,024-bit) proof. That is 9.48 WU/bit.
  - Disprove is "370 WU, or approximately 93 vB".
  - §8.1 puts Lamport at 74 B of script plus a 20 B preimage per bit, and says Lamport must be chunked because of the 1,000-item stack limit.
  - Soldering across the 7 kept instances is by VSSS (§8.2, citing Glock); it is asserted, not constructed.
  - Table 1 gives the on-chain cost as O(P).
  - Fig. 1: "Operator in 1 week".
- **Mosaic (2026/812).**
  - P garbles and V evaluates (p.8).
  - Kept copies are tied to one revelation by polynomial label correlation, with an adaptor signature revealing the missing share (abstract).
  - "The on-chain footprint is independent of ℓ and |T|" (p.23).
  - Wires are 8 bits wide. Each 8-bit wire costs 65 B of witness plus 3 B of script (Table 1).
- **Antichain Winternitz (2026/1568).**
  - §2.6: plain Winternitz lets the observer "hash forward to a smaller coordinate and recover the labels associated with another digit value".
  - §2.7: with adaptor signatures, the evaluator holding the key can spend without revealing a label.
  - Table 1:

    | (k, L) | vB/bit | table per bit |
    |---|---|---|
    | (2, 16) | 11.31 | 0.256 kB |
    | (4, 16) | 8.36 | 43.776 kB |

  - Their Lamport baseline is 17.75 vB/bit with 20-byte preimages.
- **Glock (2025/1485).** VSS plus adaptor signatures put a single signature on-chain (§3.4.2). Glock is permissioned.
- **BABE.**
  - Lamport soldering is L = KDF(s) for one instance. zk soldering reduces M sets to one (Tabs. 4–6).
  - Fees are at 2.2 sat/vB and $95,500; BitVM2's unhappy path is $14,211.

**Our measurements:**
- **Lamport script** (`data/lamport_cost.rs`, `data/run-lamport-cost.txt`). 49 B of script plus 17 B of witness per bit, with a 16-byte preimage. 998 bits fit per input (the stack limit), and wrong preimages are rejected. With about 203 WU of per-input overhead that is 66.2 WU = 16.55 vB per bit.
- **Input bits** (`whir-gc/tests/keccak_stark.rs`: `input_bits_of_whir_configurations`; `data/run-input-bits-sweep.txt`).
  - The analytic count equals the measured inputs at 2^5 through 2^18.
  - At 2^18 the split is: opened values 416,000; zerocheck 9,344; ring switch 54,912; WHIR caps 32,768; leaf rows 163,840; Merkle paths 346,624; WHIR other 17,536.
  - The smallest in the sweep is rate 1/256, folding 4, pow budget 48: queries 16/12/9/8, 845,952 bits, 103.89 bits composed, nothing unassessed.
- **Costs at 2^18** (2.2 sat/vB, $95,500):

  | scheme | Assert size | transactions | fee | fee, tuned |
  |---|---|---|---|---|
  | adaptor | 2.47 MvB | 25 | 0.054 BTC, $5,183 | $4,212 |
  | ACW (2,16) | 11.77 MvB | 118 | $24,737 | $20,102 |
  | Lamport | 17.23 MvB | 173 | 0.379 BTC, $36,200 | $29,417 |

- **Translation ciphertexts.** 32 B per input bit per instance, 33 MB per instance at 2^18. Derived, not measured.
- **Open item.** Hash-based soldering to M kept instances at a million input bits is not built.

## 7e. Garbling efficiency (2026-09-25)

The user asked for garbling efficiency η = |GC| / (rows × committed columns), in bytes per committed cell. |GC| is 16 B per non-free gate, and there are 1,625 columns of one bit each.

| rows | η (bytes per cell) |
|---|---|
| 2^5 | 13,715 |
| 2^8 | 2,556 |
| 2^12 | 186.9 |
| 2^16 | 13.32 |
| 2^18 | 3.53 |
| 2^20 | 0.94 |

At 2^20 that is 7.5 garbled bits per trace bit, or 38 kB per Keccak-f. Smaller is better. It falls roughly as 1/R, because |GC| grows only with log R.

## 8. To fix or check before release

1. bitvm-gc `docs/partial_binding_we.tex` credits BABE to "Goat Research Team".
   The authors are Garg, Kolonelos, Sergeevitch, Sridhar and Tse.
2. BABE's garbled-circuit size: the note says ~4.7·10^8 gates, BABE says a
   22 MiB artifact. Reconcile (see Sec. 2).
3. Garbled-circuit sizes compare differently depending on the unit: non-free
   gates, total gates or bytes. BABE converts 2.7B non-free gates at 16 B each.
   We use non-free gates at 16 B per privacy-free half-gate AND. State the unit
   everywhere.
4. The whir-gc proving time at 2^16 (44 min) was single-threaded, and at 2^18
   (87 min) on 8 cores. Keep the labels.
5. Entries in `refs.bib` marked "not read" are cited second-hand. Read them
   before relying on specific claims (especially Glock's 12 MB, [FBFL25] and
   Argo MAC).
6. **Open after the review, needs the authors.** The title's "Post-Quantum"
   (either retitle or add a quantum analysis); repositioning against 2026/2100 and
   BABE; the on-chain input story (1,041,024 bits); a second AIR; authors and CPU
   model.
7. **After review round 2, needs the authors.**
   - A second AIR: SHA-256 and Blake3 binary AIRs read no next-row columns,
     which needs verifier work.
   - Measuring a quantum-secure configuration: this needs a Plonky3 change,
     either a 256-bit challenge field or repetition, plus a query-heavy profile.
   - A citation for round-by-round soundness of sumcheck.
   - Authors and CPU model.
8. **Review round 3 (2026-09-24).**
   - **Fixed:**
     - Streaming memory: two passes; 1 byte per wire for the plan, 0.61 GiB at
       2^18; 18 bytes per live wire, 41 MB at the 2.26M peak.
     - Theorem 1 now uses *adaptive* authenticity, stated as an assumption for
       Blake3-based free-XOR, with a pointer to BHR12 adaptive.
     - "hardest" became "hash-heavy"; captions tightened.
     - Bibliography pages checked by web search (DBLP API unreachable from the
       server): FNO15 191–219, CKKZ12 39–53, BHT98 LNCS 1380 163–169,
       Grover 212–219, Shor 124–134.
   - **Open, needs the authors:** the title's "Post-Quantum" against the
     measured ~52 quantum bits; authors; CPU model. Adaptive authenticity of
     free-XOR in the ROM is an assumption, not a cited theorem: find a reference
     or prove it.
9. **On-chain part and 2^20 (2026-09-25).**
   - **Resolved:** the on-chain input story (§7d: operator-garbles protocol, three
     input schemes priced, input-size sweep); CPU models (Xeon Platinum 8375C;
     EPYC 9355 for 2^20); the 2^20 row; garbling efficiency (§7e).
   - **Open, needs the authors:** the author list; hash-based soldering to M kept
     instances at a million input bits; a narrower AIR or recursion for a smaller
     input; the adaptive-authenticity reference.
10. **Review round 4 (2026-09-25).**
    - **Fixed:**
      - Garbling before the proof is now measured by
        `garbled_before_the_proof_evaluates_real_proofs`
        (`data/run-garble-then-evaluate.txt`). Evaluation takes 11.5 s at 2^5
        and 17.0 s at 2^8, against 20.6 s and 34.0 s for garbling.
      - The quantum level of the Lamport keys is ≈64 bits with 16-byte
        preimages.
      - Citations added: Binius, ring switching, Wiedemann, LFKN, HyperPlonk,
        STIR, Cantor, LCH14, Blake3 and FIPS 202. Their metadata is from memory
        and still needs checking.
      - Related work now covers BitVM3's Table 9 estimate for a garbled STARK
        and TRAPGC-DV.
      - The cut-and-choose setup cost is derived.
      - Tables no longer use resizebox. Fonts are vector (lmodern + T1); the
        PDF had two Type 3 bitmap fonts before.
      - The paper is renamed to `garbled-stark-verifier.tex`.
    - **Open, needs the authors:** the title's "Post-Quantum".

