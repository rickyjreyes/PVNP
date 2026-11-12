# PVNP: consolidated publication and preserved manuscript archive

**Primary current publication:** [Wave-Constrained Computation: Formal Equivalence, Physical Resource Bounds, and the P versus NP Problem](preprints/consolidated-wave-computation/README.md), compiled as **one PDF** from the preserved Part I-III sources and independent fixed-mass nodal supplement.

The [one-volume LaTeX master](papers/consolidated-wave-computation/main.tex) introduces publication provenance, verified results, restricted statements and open mathematical claims. It binds the three historically released manuscripts without asserting new original-publication dates. The independent supplement is an appendix rather than a fourth original proof-program paper.

[**Source-to-Lean publication reconciliation**](proofs/pdf-lean-reconciliation-20261107.md) documents every material manuscript correction, preserved refutation, original-machine uniformity gap and current build limitation.

### Historical sources and identifiers

| Original study | Historical release | Maintained LaTeX |
|---|---|---|
| Part I | [Zenodo 17743607](https://doi.org/10.5281/zenodo.17743607), May 7, 2025 | [Source](papers/part-i-curvature-bounded-wave-computation/main.tex) |
| Part II | [Zenodo 17732642](https://doi.org/10.5281/zenodo.17732642), November 26, 2025 | [Source](papers/part-ii-discrete-wcc-turing-equivalence/main.tex) |
| Part III | [Zenodo 17783074](https://doi.org/10.5281/zenodo.17783074), December 1, 2025 | [Source](papers/part-iii-physical-complexity-reassessment/main.tex) |
| Independent supplement | October 2026 technical note | [Source](papers/supplement-fixed-mass-nodal-coercivity/main.tex) |

**One-PDF policy:** `bash scripts/build_pdfs.sh` compiles the original PDFs only temporarily, then produces `preprints/consolidated-wave-computation/paper.pdf`. On successful main CI, the legacy tracked PDF copies are retired. Earlier source versions are still recoverable from Git history and the original Zenodo records.

### Lean Formalization Dashboard
[Interactive dashboard](dashboard/index.html) · [How it is built](dashboard/README.md) · [Authoritative claim inventory](proofs/manuscript-lean-inventory.md). Every total on the dashboard is recomputed from the 91 claim rows of the inventory; the original-statement view is read from the inventory's git history. Open `dashboard/index.html` directly in a browser (no server or network needed). Regenerate with `node pvnp/dashboard/build.js` and verify with `node pvnp/dashboard/check.js`.

### Lean
[Auxiliary formally checked claims](../lean/README.md) across all three parts.

## Current formalization milestones (November 2026)

- [Phase VI, global H² torus flow and F-1 continuum flux](proofs/phase-vi-torus-flux-status.md): merged in [PR #40](https://github.com/rickyjreyes/PVNP/pull/40), all exact-head checks passed.
- [Phase VIII, complete alternating-crossing splicing and near-quadratic single-tape SAT bound](proofs/phase-viii-separation-status.md): merged in [PR #38](https://github.com/rickyjreyes/PVNP/pull/38).
- [Phase IX, exact target statement and tests of candidate invariants](proofs/phase-ix-universal-lower-bound-status.md): the target is proved equivalent to `SATLowerBound`; Tseitin/expander and crossing-information invariants are refuted as separation routes; `SATLowerBound` is not proved.
- [Open proof obligations](proofs/remaining-obstructions.md) and [authoritative Lean status](../lean/formalization.yaml).

**Classical P versus NP is still open.** The manuscript ledger is 79 Exact, 1 Restricted, 4 Refuted, 7 Open (II-10 became Exact on 12 November 2026). These counts describe the amended manuscript, not a percentage of a P versus NP proof. Earlier 70/91 and 73/91 snapshots, plus all five superseded counterexamples (II-7, II-8, II-17, I-10, I-13), remain preserved. I-10's revised count only certifies conditional mixing, not physical curvature collapse. I-12 is conditional on hypothetical P=NP within a restricted charged-encoder model; I-20 proves a description-length obstruction, not a physical NP/P separation.
