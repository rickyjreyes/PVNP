# Publication reconciliation: PVNP manuscripts versus Lean

**Date:** 7 November 2026  
**Scope:** The three revised historical manuscripts, the independent fixed-mass nodal note, the consolidated PVNP release source, and the 91-claim Lean ledger.  
**Source baseline:** Main commit 4b1b29242baec200fcafa02ec3cae2f29820b15b.  
**Publication PR:** #61. **Phase XIV proof PR #60:** merged into `main` at `0dc9e5b` on 8 November 2026, with exact-head Lean kernel verification still pending.

> **Historical 7 November snapshot.** The statements below retain their original context. The amended II-10 status is now **Exact**; see the dated 12 November addendum below and the [authoritative current inventory](manuscript-lean-inventory.md).

## What was changed in the revised manuscripts

| Original claim or result | Historical issue | Updated source and mathematical status |
|---|---|---|
| I-25 | State verifiability plus nonreachability treated as decision-class separation | Historical inference explicitly withdrawn; counterexample PartISeparation.state_separation_not_language_separation |
| I-26 | Target wavefields treated as NP/P language class witnesses | Historical inference withdrawn; the same state-to-language counterexample applies |
| I-27 | WCT target-state reconstruction complexity transferred to NP minus P | Historical inference withdrawn; PartISeparation.accepted_language_not_in_NP_diff_P refutes the inference |
| I-28 | For-each-constructor missed target treated as universal decision lower bound | Withdrawn; PartISeparation.universal_scope_counterexample refutes the quantifier transfer |
| I-40 | Explicit CNF verification combined with uniformly generated formula families | Explicit pair case matched to SATV.V_SAT_mem_P_TM; separately state mathematical generator-composition assumption |
| II-10 | Original two-phase W_M stated as complete uniformly polynomial-time machine | Rewritten as exact intrinsic two-phase runtime and decision correspondence, plus an explicitly conditional uniformity result requiring the original window and input FP writers |
| II-11 through II-15 | Generic uniform discrete class equivalences | Preserved. Their verified generic construction must not be confused with original W_M uniformity |
| III-1 through III-21 | Finite, conditional physical and symbolic statements | Preserve the scope of the established results; distinguished discrete Lean theorems from analytic continuum assumptions |
| III-22 | Arrow of time | Open interpretive remark, not a proved P versus NP claim |

## Official manuscript classification

The unchanged authoritative 91-claim inventory remains:

| Part | Exact | Restricted | Refuted | Open | Total |
|---|---:|---:|---:|---:|---:|
| I | 30 | 1 | 4 | 6 | 41 |
| II | 27 | 1 | 0 | 0 | 28 |
| III | 21 | 0 | 0 | 1 | 22 |
| **Total** | **78** | **2** | **4** | **7** | **91** |

The four refuted source claims remain in the **historical audit**, although the revised PDF no longer presents them as valid propositions. Exact includes proved conditional implications and must never be interpreted as proof of an unproved antecedent, a physical realization, or classical P != NP.

### Restricted

- **I-11:** Uniform discrete equivalence is exact, but a charged continuum physical-to-classical simulation with preparation, measurement and numerical-error cost is not proved.
- **II-10:** The original two-phase decoder and update correspondence are established; complete original input-configuration and lattice writer transducers with polynomial single-tape runtime remain missing. The generic one-cell embedding does not complete W_M.

### Open

- **I-2:** Nonconstructible verifiable WCT field family.
- **I-3:** Formula-dependent physical phase dynamics and robust readout, beyond the logical-energy threshold.
- **I-16:** An unconditional superpolynomial lower bound against every correct dense-SAT decider.
- **I-31:** Input-size-uniform physical separator price.
- **I-32:** Encoding-independent all-decider expander interface growth.
- **I-37:** Arbitrary-formula sound and complete physical toroidal locking.
- **III-22:** Historical interpretive arrow-of-time remark.

## Supporting results must be distinguished from complete original claims

- Classical Cook--Levin, nonuniform circuits and exact SAT target equivalences are not an unconditional SAT lower bound.
- The quadratic and near-quadratic single-tape SAT obstructions do not separate classical P from NP.
- A formula-dependent logical-energy certificate below 1/8 proves a SAT witness criterion, not fast physical phase preparation or WCT PDE convergence.
- Fixed-mass nodal coercivity is proved analytically on a fixed torus with explicit restrictions. Its exact finite two-node analogue is in Lean; the full continuum compactness and detector proof are not in Lean.
- Phase XII and XIII additions were merged into main despite GitHub Actions jobs failing **before checkout and all job steps**. They require fresh full Lean compilation and standard-axiom auditing before being called independently kernel verified.
- Phase XIV PR #60 was squash-merged into `main` at `0dc9e5b`. It establishes an explicit **constant-radius** original lattice MTM writer and complete output-word identity at source level, but has not passed the Lean kernel and axiom audit because GitHub Actions jobs still fail before execution. The general polynomial-radius `FP (originalWindowCode p)` and original input-code `FP` remain unproved; II-10 stays Restricted.

## PDF chronology and release

The previously tracked Part I and Part II PDF binaries predate later LaTeX revisions on 6 November 2026. The stand-alone PDFs therefore cannot be used as evidence of the latest source or current Lean reconciliation.

The consolidated manuscript source is at pvnp/papers/consolidated-wave-computation/main.tex. The one-volume build compiles Part I, II, III and the independent supplement as **temporary archival PDFs** and binds them behind a provenance and correction overview. It must produce one primary release binary at pvnp/preprints/consolidated-wave-computation/paper.pdf.

The three 2025 historical publication identifiers remain:
- Part I: https://doi.org/10.5281/zenodo.17743607
- Part II: https://doi.org/10.5281/zenodo.17732642
- Part III: https://doi.org/10.5281/zenodo.17783074

They are **not** three new November 2026 papers. The independent supplement is an appendix and does not enlarge the original 91-claim inventory.


## One-command independent verification

Run `bash scripts/run_release_verification.sh --all` in a full-history checkout with pinned Lean/Mathlib, LaTeX, Python and Node installed. The script saves complete PDF, Lean, axiom-audit and dashboard logs under ignored `.release-verification/` and fails on any required error. `--pdf-only`, `--lean-only` and `--dashboard-only` isolate blockers. It will **not** mark unexecuted gates successful. The PDF build generates temporary individually rebuilt Part I and II PDFs for review, while only the combined PDF is the publication artifact. These are not newly published independent papers.

## Verification checklist

1. Compile every historical revised LaTeX manuscript using the pinned PDF workflow and verify no LaTeX errors.
2. Generate the consolidated release PDF; inspect PDF page count, text extraction, provenance, and the inclusion of all four archival parts.
3. Execute the full pinned Lean build: cd lean; lake build PVNP.
4. Execute the exact standard-axiom audit from lean/audit/AxiomAudit.lean and the repository audit checker.
5. Check the dashboard: node pvnp/dashboard/build.js --check and node pvnp/dashboard/check.js.
6. Require **actual completed** exact-head CI checks, not runner-level jobs with zero executed steps, before merging and public release.
7. Preserve the original revised LaTeX sources and Zenodo DOIs. Do not rewrite the history or change repo visibility as a side effect of manuscript synchronization.

**Status at creation:** Revised LaTeX and publication workflow have been committed to PR #61; no full updated consolidated PDF has been compiled, and the latest exact-head CI jobs continue to fail before execution. This is a source-level reconciliation, not a verified public release.

## 12 November 2026 addendum: II-10 original scope closed

This is a dated update to the 7 November baseline above, not a retroactive
claim that the original proof was complete at that earlier date. PR #73 adds
concrete, actual single-tape polynomial-radius lattice and configuration
writers, proves exact first-halt output words and polynomial transition counts,
and supplies the two previously missing `FP` witnesses. Its
`TwoPhasePolynomialWriter.originalWM_first_answer` theorem identifies the
original finite-WCC machine's first answer at exactly `2*T_M(x)`, with no
premature output and with the corrected radius/empty-input boundary.

The author reports a successful 7,386-job full Lean build, standard-axiom
audit, and verification gate at source commit
`df8824ca659b2e931eb4302251569d6c6c6140b3`; GitHub-hosted runners did
not execute an equivalent workflow. The amended inventory now has **79 Exact,
1 Restricted, 4 Refuted, 7 Open**, with **Part II 28/28 Exact**. The
remaining Restricted claim is I-11. This result does not establish the
unrestricted continuum WCT↔TM bridge or classical P ≠ NP. For the
mathematical proof chain and verification provenance, see
`pvnp/proofs/II10_VERIFICATION_LEDGER.md`.
