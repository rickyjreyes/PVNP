# Consolidated PVNP technical volume

**Wave-Constrained Computation: Formal Equivalence, Physical Resource Bounds, and the P versus NP Problem**

**Author:** Richard J. Reyes

This is the **primary repository release artifact**, compiled from the three historically released PVNP manuscripts together with the independent fixed-mass nodal-coercivity supplement. It contains a new provenance and formal-verification guide, followed by complete reproductions of the revised source manuscripts.

- [Single consolidated PDF](paper.pdf), produced by `bash scripts/build_pdfs.sh`
- [Consolidated LaTeX source](../../papers/consolidated-wave-computation/main.tex)
- [Historical manuscript and supplement sources](../../papers/)
- [Claim-by-claim Lean formalization inventory](../../proofs/manuscript-lean-inventory.md)
- [Original Zenodo publication identifiers](../../../CONTENTS.md#publication-identifiers)

[**Manuscript-to-Lean source reconciliation**](../../proofs/pdf-lean-reconciliation-20261107.md) details the withdrawn Part I state-to-language theorems, restricted original two-phase construction, and current verification blockers.

## Publication scope

This **bound technical volume is not a proof of classical P != NP**. The existing formalized results include uniform discrete WCC complexity-class equivalences, restricted lower bounds for particular machine models, and conditional physical-resource estimates. The original uniform two-phase lattice/encoder cost proof, continuum physical equivalence, and universal SAT lower bound remain unresolved.

The original 2025 release identifiers retain their historical dates. Inclusion in the current 2026 bound volume does not represent three new papers or erase the source history. The independent supplement is included as an appendix, not counted as an original Part I-III claim.


**Independent release gate:** from the repository root run `bash scripts/run_release_verification.sh --all`. It retains locally rebuilt Part I and II review PDFs, exact source hashes and full logs without committing redundant PDF publications.

**Atomic publication safeguard:** The release verification command first writes a staged candidate under `.release-verification/staged-release/paper.pdf`. `--pdf-only` validates the compiled PDF and leaves it staged without changing the tracked publication file. `--all` promotes that exact candidate to `paper.pdf` only after the compiled-PDF checks, full Lean build, axiom audit, and dashboard verification have all succeeded. If any gate fails, the existing tracked PDF is preserved. `scripts/test_release_staging.py` exercises this behavior with hermetic failure injections. A direct `bash scripts/build_pdfs.sh` remains a developer rebuild and is **not** an independent release certification.

## One-PDF release policy

The three legacy PDFs and supplement PDF are historical compilation artifacts, **not four current primary releases**. The new workflow builds them only temporarily, compiles the single consolidated PDF, and (after a successful main build) removes the redundant PDF binaries from the current branch. Their LaTeX sources remain maintained and the old compiled versions remain accessible through Git history and historical Zenodo records.

A consolidated PDF binary is present on the publication branch, but its correspondence to the most recently revised source manuscripts has **not been independently validated**. The release gate requires a fresh build and per-page comparison, plus a separate full Lean kernel build and axiom audit. GitHub Actions [runner issue #59](https://github.com/rickyjreyes/PVNP/issues/59) currently prevents execution of those checks; do not call the release verified or final until they pass.
