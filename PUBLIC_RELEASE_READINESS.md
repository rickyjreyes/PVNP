# PVNP public-release readiness

**As of 12 November 2026. Status: NO-GO for changing GitHub visibility.**
This is a release-control document, not a new mathematical result or a grant of permission to publish.

## What is integrated

PRs [#68](https://github.com/rickyjreyes/PVNP/pull/68), [#69](https://github.com/rickyjreyes/PVNP/pull/69), and [#73](https://github.com/rickyjreyes/PVNP/pull/73) were merged into `main`. Phase XVIII closes the original discrete II-10 two-phase writer obligation at its corrected scope. The amended 91-claim inventory was **79 Exact, 1 Restricted, 4 Refuted, 7 Open** after #73; PR [#78](https://github.com/rickyjreyes/PVNP/pull/78) refutes I-31 for the frozen trajectory class, which gives **79 Exact, 1 Restricted, 5 Refuted, 6 Open** once accepted. Some Exact entries prove conditional implications only. No classical P versus NP separation, continuum WCT ↔ Turing equivalence, or physical toroidal-locking theorem follows.

At exact Phase XIX commit [`c92158f`](https://github.com/rickyjreyes/PVNP/commit/c92158f99ed6667cce4761de4d4631d2e4086d34), a user-supplied Windows Git Bash log records a successful 7,260-job targeted II-10 build, a 7,386-job complete Lean build, an allowed-axiom audit of 627 declarations (only `propext`, `Classical.choice`, and `Quot.sound`), and 24/24 II-10 regressions. The release preflight also passed four security-audit unit tests and Gitleaks 8.30.1 on all locally available refs, with zero heuristic matches in 287 tracked text files. At later Phase XIX commit [`75a2cd6`](https://github.com/rickyjreyes/PVNP/commit/75a2cd6f5fb526f527f5494c2264ce793eb9ff35), the dashboard generator and all 13 dashboard test groups passed on Windows after a CRLF compatibility fix. These are **user-reported local runs**, not successful GitHub-hosted jobs. CI issue [#59](https://github.com/rickyjreyes/PVNP/issues/59) remains relevant.

## Required gates before public visibility

| Gate | Current evidence | Release decision |
| --- | --- | --- |
| Original II-10 code and manuscript classification | Integrated in #73; local kernel/audit evidence reported | Mathematically accepted in current inventory; retain provenance |
| PR #74 reconciliation | PR #74 closed as superseded; unique unmerged content retained on its branch | Review any unique deltas separately; do not merge conflicting history wholesale |
| Full pinned Lean + axiom audit on final public-release tree | **PASS at `c92158f`: 7,386 jobs, 627 audited declarations**. Later documentation/dashboard commits need their own final reproducibility record | **PROVISIONALLY VERIFIED**, not a completed final all-in-one release gate |
| Python regressions, dashboard generation/check, and manuscript alignment | **PASS:** 24/24 II-10 regressions, 4/4 audit tests and status/source alignment at `c92158f`; 13/13 dashboard groups at `75a2cd6` | Component checks passed locally; combined gate still blocked by PDF tooling |
| Consolidated PDF regeneration and inspection | Existing verification scripts; revised source may postdate artifact | **BLOCKED** |
| Full-history secret/privacy scan | **PASS:** Gitleaks 8.30.1 on all locally available refs; 287 tracked text files yielded zero heuristic matches | Scanner passed; manual review of binaries, PDFs, metadata, historical refs and other branches **PENDING** |
| Third-party content and dataset rights audit | Not completed | **BLOCKED** |
| Software/manuscript licensing decision | No root LICENSE; see [licensing options](docs/PUBLIC_LICENSE_DECISION.md) | **BLOCKED** on author approval |
| Patent and publication disclosure review | Not completed; repository history will become visible | **BLOCKED** on author/patent-counsel review |
| Explicit approval to change private → public | Not given | **BLOCKED** |

**These component passes do not satisfy the final publication gate.** In particular, the PDF build and rendered inspection, manual history/privacy/rights review, explicit licensing and patent disclosure decisions, and author authorization remain outstanding.

## Final verification in a full-history clone

Run in the repository root with pinned Lean/Mathlib, Python 3, Node, PDF tools and a current Gitleaks installation. The strict combined technical gate is `bash scripts/verify_public_release.sh`. To isolate failures, use:

```bash
git status --short
git rev-parse HEAD
git rev-parse --is-shallow-repository
python3 scripts/audit_public_release.py --history
bash scripts/verify_ii10_original_wm.sh
bash scripts/run_release_verification.sh --all
node pvnp/dashboard/build.js --check
node pvnp/dashboard/check.js
python3 scripts/check_manuscript_alignment.py
```

Keep all logs and scan findings in the ignored `.release-verification/` directory; **do not commit secret-scanner findings**. Review any results manually, including false positives, and rotate real exposed credentials before publishing. Check tags, historical commits, other branches, PDF metadata and large/binary assets separately. An automated scan does not certify confidentiality or patent freedom.

For PDF publication, rebuild the one-volume artifact and inspect that it corresponds to current LaTeX; historical Zenodo DOIs are not new publication dates.

## Independent research tracks

- **I-31 (Refuted in PR #78, for the author to accept):** `PVNP.SeparatorFrozen` answers each check listed here before: *quantifiers* — for every κ₀ > 0 there is L₀ with a violation at every L ≥ L₀ and every time; *admissible fields* — exact solutions of the frozen PDE with a one-mode (or three-mode) encoding, polynomial mass |A|²L²; *detector and contrast* — the readout Re ψ (and, separately, |ψ|) keeps the fixed margin |A| for every L; *Φ* — the manuscript's ∫(|∇ψ|² + |Θψ|²) for every Θ with |Θψ| ≤ c|Δψ|, including Δ and Part III's Θ_ε; *readout geometry* — the Euclidean 𝓗¹ of the frontier of the decision region in the fundamental domain; *normalization* — amplitude fixed, mass charged but not fixed, as in the frozen model. A width-dependent price (`layer_price`) is proved as the corrected statement. See `pvnp/proofs/phase-xviii-i31-separator-counterexample.md`.
- **I-32, I-3, I-37, I-2, I-16:** Remain Open.
- **I-11:** Restricted, including the unresolved resource-preserving physical continuum bridge.
- **III-22:** Open in current authoritative inventory. A separate interpretive reclassification proposal (#71) is not incorporated into the 79/1/4/7 count.

These tracks are not prerequisites to making a clearly scoped research repository public; publication gates concern claim accuracy, technical reproducibility, intellectual property and privacy.

## Merge/release policy

Implement safe documentation and checker improvements on `research/pvnp-public-release-readiness`. Keep patent/legal approvals and repository visibility separate. Do not rewrite history, erase negative results, invent hosted CI success, merge superseded proof candidates (#70), or duplicate recovered II-10 work (#72). PR #74 is closed as superseded; preserve its unique unmerged work for targeted file-by-file review.

**Only the author may authorize the final license and private-to-public transition after the blockers are reviewed.**
