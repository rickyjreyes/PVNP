# PVNP public-release readiness

**As of 12 November 2026. Status: NO-GO for changing GitHub visibility.**
This is a release-control document, not a new mathematical result or a grant of permission to publish.

## What is integrated

PRs [#68](https://github.com/rickyjreyes/PVNP/pull/68), [#69](https://github.com/rickyjreyes/PVNP/pull/69), and [#73](https://github.com/rickyjreyes/PVNP/pull/73) were merged into `main`. Phase XVIII closes the original discrete II-10 two-phase writer obligation at its corrected scope. The amended 91-claim inventory is **79 Exact, 1 Restricted, 4 Refuted, 7 Open**. Some Exact entries prove conditional implications only. No classical P versus NP separation, continuum WCT ↔ Turing equivalence, or physical toroidal-locking theorem follows.

The original writer proof was reported to pass pinned Lean 4.23.0, a 7,386-job full build, an allowed-axiom audit, and the repository verification gate at proof head `df8824c` and promotion head `417c2d4`. These are locally reported runs, not successful GitHub-hosted jobs. CI issue [#59](https://github.com/rickyjreyes/PVNP/issues/59) remains relevant: failed jobs with **zero executed steps** provide no compiler verdict.

## Required gates before public visibility

| Gate | Current evidence | Release decision |
| --- | --- | --- |
| Original II-10 code and manuscript classification | Integrated in #73; local kernel/audit evidence reported | Mathematically accepted in current inventory; retain provenance |
| PR #74 reconciliation | Divergent documentation/dashboard promotion overlaps #73 | Open: review unique changes, do not merge conflicting history blindly |
| Full pinned Lean + axiom audit on final public-release tree | Prior local proof-head runs, not a final release-tree run | **BLOCKED** |
| Full Python suite, dashboard generation/check, and manuscript alignment | Partial prior tests and author reports | **BLOCKED** until exact release-head run |
| Consolidated PDF regeneration and inspection | Existing verification scripts; revised source may postdate artifact | **BLOCKED** |
| Full-history secret/privacy scan | No complete-history scanner result recorded | **BLOCKED** |
| Third-party content and dataset rights audit | Not completed | **BLOCKED** |
| Software/manuscript licensing decision | No root LICENSE; see [licensing options](docs/PUBLIC_LICENSE_DECISION.md) | **BLOCKED** on author approval |
| Patent and publication disclosure review | Not completed; repository history will become visible | **BLOCKED** on author/patent-counsel review |
| Explicit approval to change private → public | Not given | **BLOCKED** |

**A green source lint or locally reported proof-head build does not satisfy these final-release gates.**

## Final verification in a full-history clone

Run in the repository root with pinned Lean/Mathlib, Python 3, Node, PDF tools and a current Gitleaks installation:

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

- **I-31 (Open):** Author-reported work on frozen-torus plane-wave and three-mode separator counterexamples is still subject to checking the *exact* original quantifiers, admissible fields, detector/contrast definition, prescribed energy `Φ`, readout geometry, and normalization. Do not upgrade to Refuted on the strength of a candidate or a compiled supporting lemma.
- **I-32, I-3, I-37, I-2, I-16:** Remain Open.
- **I-11:** Restricted, including the unresolved resource-preserving physical continuum bridge.
- **III-22:** Open in current authoritative inventory. A separate interpretive reclassification proposal (#71) is not incorporated into the 79/1/4/7 count.

These tracks are not prerequisites to making a clearly scoped research repository public; publication gates concern claim accuracy, technical reproducibility, intellectual property and privacy.

## Merge/release policy

Implement safe documentation and checker improvements on `research/pvnp-public-release-readiness`. Keep patent/legal approvals and repository visibility separate. Do not rewrite public history, erase negative results, invent CI success, merge superseded proof candidates (#70), or duplicate recovered II-10 work (#72). Resolve #74 file by file.

**Only the author may authorize the final license and private-to-public transition after the blockers are reviewed.**
