# PVNP public-release readiness

**As of 12 November 2026. Status: NO-GO for changing GitHub visibility.**
This is a release-control document, not a new mathematical result or a grant of permission to publish.

## What is integrated

PRs [#68](https://github.com/rickyjreyes/PVNP/pull/68), [#69](https://github.com/rickyjreyes/PVNP/pull/69), [#73](https://github.com/rickyjreyes/PVNP/pull/73), [#78](https://github.com/rickyjreyes/PVNP/pull/78), and [#79](https://github.com/rickyjreyes/PVNP/pull/79) were merged into `main`. Phase XVIII closes the original discrete II-10 two-phase writer obligation at its corrected scope, refutes I-31 **only for the frozen trajectory class with growing domains**, and adds scoped obstruction theorems without upgrading the other claims. The current 91-claim inventory is **79 Exact, 1 Restricted, 5 Refuted, 6 Open**. Some Exact entries prove conditional implications only. No classical P versus NP separation, continuum WCT ↔ Turing equivalence, or physical toroidal-locking theorem follows.

At exact Phase XIX commit [`c92158f`](https://github.com/rickyjreyes/PVNP/commit/c92158f99ed6667cce4761de4d4631d2e4086d34), a user-supplied Windows Git Bash log records a successful 7,260-job targeted II-10 build, a 7,386-job complete Lean build, an allowed-axiom audit of 627 declarations (only `propext`, `Classical.choice`, and `Quot.sound`), and 24/24 II-10 regressions. The release preflight also passed four security-audit unit tests and Gitleaks 8.30.1 on all locally available refs, with zero heuristic matches in 287 tracked text files. At later Phase XIX commit [`75a2cd6`](https://github.com/rickyjreyes/PVNP/commit/75a2cd6f5fb526f527f5494c2264ce793eb9ff35), the dashboard generator and all 13 dashboard test groups passed on Windows after a CRLF compatibility fix. These are **user-reported local runs**, not successful GitHub-hosted jobs. CI issue [#59](https://github.com/rickyjreyes/PVNP/issues/59) remains relevant.

## Required gates before public visibility

| Gate | Current evidence | Release decision |
| --- | --- | --- |
| Original II-10 code and manuscript classification | Integrated in #73; local kernel/audit evidence reported | Mathematically accepted in current inventory; retain provenance |
| PR #74 reconciliation | PR #74 closed as superseded; unique unmerged content retained on its branch | Review any unique deltas separately; do not merge conflicting history wholesale |
| Full pinned Lean + axiom audit on final public-release tree | **PASS at `c92158f`: 7,386 jobs, 627 audited declarations**. Later documentation/dashboard commits need their own final reproducibility record | **PROVISIONALLY VERIFIED**, not a completed final all-in-one release gate |
| Python regressions, dashboard generation/check, and manuscript alignment | **PASS:** 24/24 II-10 regressions, 4/4 audit tests and status/source alignment at `c92158f`; 13/13 dashboard groups at `75a2cd6` | Component checks passed locally; combined gate still blocked by PDF tooling |
| Consolidated PDF regeneration and inspection | Corrected II-10 scope in consolidated LaTeX; free offline page/visual verification script prepared | **PENDING LOCAL REBUILD AND HUMAN INSPECTION** |
| Full-history secret/privacy scan | Prior local Gitleaks scan passed; additional offline history and PDF-metadata inventory tool prepared | Manual review of binaries, PDFs, metadata, historical refs and branches **PENDING** |
| Third-party content and dataset rights audit | [Asset inventory and review plan](docs/RELEASE_RIGHTS_AND_HISTORY.md) prepared | **MANUAL SIGN-OFF PENDING** |
| Software/manuscript licensing decision | Inactive [BSD-3-Clause and CC BY 4.0 proposals](docs/PUBLIC_LICENSE_DECISION.md) ready for selection; no active LICENSE | **AUTHOR APPROVAL PENDING** |
| Patent and publication disclosure review | [Public-safe disclosure checklist](docs/PATENT_PUBLIC_DISCLOSURE_REVIEW.md) prepared | **AUTHOR/PATENT REVIEW PENDING** |
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

- **I-31 (Refuted for the frozen trajectory class, merged PR #78):** `PVNP.SeparatorFrozen` answers each check listed here before: *quantifiers* — for every κ₀ > 0 there is L₀ with a violation at every L ≥ L₀ and every time; *admissible fields* — exact solutions of the frozen PDE with a one-mode (or three-mode) encoding, polynomial mass |A|²L²; *detector and contrast* — the readout Re ψ (and, separately, |ψ|) keeps the fixed margin |A| for every L; *Φ* — the manuscript's ∫(|∇ψ|² + |Θψ|²) for every Θ with |Θψ| ≤ c|Δψ|, including Δ and Part III's Θ_ε; *readout geometry* — the Euclidean 𝓗¹ of the frontier of the decision region in the fundamental domain; *normalization* — amplitude fixed, mass charged but not fixed, as in the frozen model. A width-dependent price (`layer_price`) is proved as the corrected statement. See `pvnp/proofs/phase-xviii-i31-separator-counterexample.md`.
- **I-32, I-3, I-37, I-2, I-16:** Remain Open.
- **I-11:** Restricted, including the unresolved resource-preserving physical continuum bridge.
- **III-22:** Open in current authoritative inventory. A separate interpretive reclassification proposal (#71) is not incorporated into the 79/1/4/7 count.

These tracks are not prerequisites to making a clearly scoped research repository public; publication gates concern claim accuracy, technical reproducibility, intellectual property and privacy.

## Merge/release policy

Implement safe documentation and checker improvements on `research/pvnp-public-release-readiness`. Keep patent/legal approvals and repository visibility separate. Do not rewrite history, erase negative results, invent hosted CI success, merge superseded proof candidates (#70), or duplicate recovered II-10 work (#72). PR #74 is closed as superseded; preserve its unique unmerged work for targeted file-by-file review.

**Only the author may authorize the final license and private-to-public transition after the blockers are reviewed.**

## Free offline release workflow (no GitHub Actions billing)

**Single command:** `bash scripts/review_public_release_offline.sh --all`
For the PDF alone use `--pdf-only`; for rights/history checks use
`--audit-only`; use `--approval-status` to display remaining approvals.
This wrapper supports Python on Windows Git Bash without `python3` on PATH.


Hosted CI is **not a required publication mechanism**. CI issue #59 can be
left unresolved until runner allocation becomes available; this is not a
reason to incur additional GitHub Actions costs. Use a full-history local
clone instead:

```bash
python3 -m unittest pvnp.tests.test_offline_publication_gates
python3 scripts/check_manuscript_alignment.py
bash scripts/verify_public_pdf_offline.sh
python3 scripts/audit_release_assets.py --history
python3 scripts/audit_public_release.py --history
python3 scripts/check_publication_approval.py
```

The PDF command rebuilds the four source manuscripts and bound technical
volume, checks every embedded page against the freshly compiled standalone
PDFs, and exports representative page PNGs to
`.release-verification/pdf-offline/visual/`. **A human must inspect them.**
The history/audit reports and private approval JSON also stay in the
gitignored directory.

For full technical revalidation, the existing locally runnable
`bash scripts/verify_public_release.sh` remains available and invokes
Lean/axiom and other gates. It is separate from hosted Actions.

**Implementation does not equal clearance:** the active code/manuscript
licenses are still unselected; third-party content, historic disclosures,
privacy and patent effects still need a person to review and explicitly
approve. The optional checker
`python3 scripts/check_publication_approval.py --require-approved`
fails until a complete final-commit approval record and the actual
approved licenses exist. Do not change repository visibility automatically.
