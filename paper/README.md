# Paper: Garbling a Post-Quantum STARK Verifier for Bitcoin

This is a draft, not yet released.

| file | what |
| --- | --- |
| `garbled-stark-verifier.tex` | the paper (built: `garbled-stark-verifier.pdf`) |
| `refs.bib` | bibliography. The `annote` fields (not printed) record whether we read each source |
| `notes.md` | per-paper notes with section, table and figure references, plus our measurements and a list of things to fix before release |
| `data/` | raw measurement records: the 2^18 run, the streamed bitvm-gc runs, the input-bits sweep, the Lamport script cost, garbling before the proof and evaluating afterwards, and the whir-gc README before trimming (WHIR-only, cap, sweep and KoalaBear data) |
| `refs/` | PDFs of the papers read (git-ignored) |

Build:

```
pdflatex garbled-stark-verifier && bibtex garbled-stark-verifier && pdflatex garbled-stark-verifier && pdflatex garbled-stark-verifier
```

Still to do before release: the author list
and the open points in `notes.md` §8.
