# PVNP — Research manuscript collection

This directory follows the pattern used by [rickyjreyes/math](https://github.com/rickyjreyes/math):

- `papers/<slug>/main.tex` — editable LaTeX source, treated as authoritative.
- `preprints/<slug>/paper.pdf` — reproducibly compiled PDF.
- `preprints/<slug>/README.md` — manuscript scope, limitations, and links.

### Part I
[Manuscript & scope](preprints/part-i-curvature-bounded-wave-computation/README.md) · [PDF](preprints/part-i-curvature-bounded-wave-computation/paper.pdf) · [LaTeX](papers/part-i-curvature-bounded-wave-computation/main.tex)

### Part II
[Manuscript & scope](preprints/part-ii-discrete-wcc-turing-equivalence/README.md) · [PDF](preprints/part-ii-discrete-wcc-turing-equivalence/paper.pdf) · [LaTeX](papers/part-ii-discrete-wcc-turing-equivalence/main.tex)

### Part III
[Manuscript & scope](preprints/part-iii-physical-complexity-reassessment/README.md) · [PDF](preprints/part-iii-physical-complexity-reassessment/paper.pdf) · [LaTeX](papers/part-iii-physical-complexity-reassessment/main.tex)

### Lean
[Auxiliary formally checked claims](../lean/README.md) across all three parts.

## Current formalization milestones (November 2026)

- [Phase VI, global H² torus flow and F-1 continuum flux](proofs/phase-vi-torus-flux-status.md): merged in [PR #40](https://github.com/rickyjreyes/PVNP/pull/40), all exact-head checks passed.
- [Phase VIII, complete alternating-crossing splicing and near-quadratic single-tape SAT bound](proofs/phase-viii-separation-status.md): merged in [PR #38](https://github.com/rickyjreyes/PVNP/pull/38).
- [Phase IX, exact target statement and tests of candidate invariants](proofs/phase-ix-universal-lower-bound-status.md): the target is proved equivalent to `SATLowerBound`; Tseitin/expander and crossing-information invariants are refuted as separation routes; `SATLowerBound` is not proved.
- [Open proof obligations](proofs/remaining-obstructions.md) and [authoritative Lean status](../lean/formalization.yaml).

**Classical P versus NP is still open.** The manuscript ledger remains 70 Exact, 2 Restricted, 11 Refuted, 8 Open. These counts describe manuscript formalization, not a percentage of a P versus NP proof.
