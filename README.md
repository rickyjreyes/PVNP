# P vs NP — Wave Curvature Computation

**Richard J. Reyes · Independent Researcher**

Research manuscripts on discrete Wave Curvature Computation (WCC), classical complexity, and physical curvature-resource constraints. Organized after the [math manuscript repository](https://github.com/rickyjreyes/math): a navigable collection with **PDFs, LaTeX sources, scope notes, and a reproducible build workflow**, grouped under `pvnp/`.

**[PVNP public-release readiness](PUBLIC_RELEASE_READINESS.md):** the repository remains private. Exact-head local Lean/axiom/regression checks and the Gitleaks scan have passed, and the dashboard check has passed on the Phase XIX branch. Consolidated PDF verification, manual disclosure/rights review, licensing and patent decisions, and explicit author approval are still pending. Classical P versus NP is unsolved.

**[PDF-to-Lean historical reconciliation](pvnp/proofs/pdf-lean-reconciliation-20261107.md):** documents the original nine-target audit and dated corrections, including II-10's 12 November 2026 closure. Current authoritative statuses are in the [91-claim inventory](pvnp/proofs/manuscript-lean-inventory.md).

## Planned primary publication: one consolidated technical volume

**[Wave-Constrained Computation: Formal Equivalence, Physical Resource Bounds, and the P versus NP Problem](pvnp/preprints/consolidated-wave-computation/README.md)**

The planned primary publication is **one consolidated PDF**. It binds the revised Part I, Part II and Part III manuscripts, plus a separately identified fixed-mass nodal-coercivity appendix, under one editorial overview and historical publication record. The [consolidated LaTeX source](pvnp/papers/consolidated-wave-computation/main.tex) and [one-PDF build workflow](.github/workflows/pdfs.yml) are authoritative for this edition.

The previous studies remain cited by their original Zenodo identifiers and retain their [archival LaTeX sources](pvnp/papers/). Consolidation does **not** represent new publication dates for the original manuscripts. The new primary PDF is available only once the build has actually succeeded; [CI runner issue #59](https://github.com/rickyjreyes/PVNP/issues/59) currently blocks some workflows. Classical P versus NP remains unsolved.

## Verified developments (November 2026)

| Program | Kernel-checked result | Limit |
|---|---|---|
| **Phase XVIII, PR [#73](https://github.com/rickyjreyes/PVNP/pull/73)** | The original II-10 two-phase machine's canonical window and input encodings have explicit polynomial-time transducer constructions in Lean, including `TwoPhasePolynomialWriter.originalWM_decides` and the original finite-control writer proofs. II-10 is now **Exact** for the formalized original discrete model. | Does **not** prove a physical WCT realization, a universal SAT lower bound, or classical `P ≠ NP`. |
| **Phase IX** | `SATTarget.satLowerBound_iff_superpolynomial` proves that the per-input target (every correct `SAT_dense` decider exceeds every `C·\|x\|^k` on arbitrarily long inputs) is equivalent to `SATLowerBound` and to `conj:wcc_depth` for `SAT_dense`. No-go theorems: `TseitinSAT.tseitin_mem_SAT_dense_iff_comp` (expander/Tseitin instances of `SAT_dense` are decided by component parity) and `VerifierCrossing.crossingInfo_not_superpolynomial` (the polynomial-time language `V_SAT` carries quadratic crossing information). | Fixes the target and rules out two candidate invariants. `SATLowerBound` is **not** proved. |
| **Phase VIII, PR [#38](https://github.com/rickyjreyes/PVNP/pull/38)** | `CrossingHennie.hennie` proves alternating crossing-sequence splicing for the ordinary single-tape TM. `CrossingSAT` and `CrossingSATSets` derive mixed-SAT acceptance and a near-quadratic time lower bound. | A **single-tape** lower bound of `Ω(N² / (log N · log \|Λ\|))`, not superpolynomial SAT hardness. |
| **Phase VI, PR [#40](https://github.com/rickyjreyes/PVNP/pull/40)** | `PVNP.Torus.global_wellposed` and `PVNP.Torus.flux_inequality` / `curvature_time_bound` formalize global H² torus evolution and PDE-derived localized-mass flux. | Requires `L > 0`, `γ > 0`, specified solutions and detector regularity/bounds; not a computational resource separation. |
| **Uniform discrete WCC** | Verified polynomial-time class equivalences `P_disc = P_TM` and `NP_disc = NP_TM`, plus finite-model variations. | Does not identify discrete computation with physically charged curvature computation. |

**[Lean Formalization Dashboard](pvnp/dashboard/index.html)**: all 91 manuscript claims in current (amended) and original (October 27) views, conditional Exact claims marked, 14 audited supporting results, finite toroidal results now integrated into `main`, open obligations and recorded verification provenance. Open `pvnp/dashboard/index.html` in a browser from a clone; no server or network access is needed. Its data are generated from the inventory, its git history and the Lean sources (`node pvnp/dashboard/build.js`), and CI rejects stale data (`node pvnp/dashboard/check.js`). See [the dashboard README](pvnp/dashboard/README.md).

**Proof status:** No proof of classical `P ≠ NP` or its opposite. The decisive statement `CrossingSAT.SATLowerBound` (`SAT_dense ∉ P_TM`) is unproved. The manuscript claim inventory is **79 Exact, 1 Restricted, 4 Refuted, 7 Open** (II-10, the uniformity of the original two-phase machine, became Exact on 12 November 2026); “Exact” may describe a conditional implication whose premise is still open. Part II's three corrected claims match existing Lean proofs. Part I's I-13 now matches the proved quiescent support bound; I-10 is re-scoped to a **conditional** common-successor mixing theorem with a new Lean declaration. Neither establishes physical mixing or a SAT lower bound. I-12 now records the conditional P=NP compatibility counterargument for charged encoders; I-20 separates explicit-state description complexity from succinct certificate verification. All original counterexamples and open lower-bound premises are retained.

**Latest local technical verification (12 November 2026):** At exact commit [`c92158f`](https://github.com/rickyjreyes/PVNP/commit/c92158f99ed6667cce4761de4d4631d2e4086d34), a Windows Git Bash run reported a **7,260-job II-10 targeted build**, **7,386-job complete Lean build**, **627-declaration allowed-axiom audit** (only `propext`, `Classical.choice`, `Quot.sound`), **24/24 original II-10 Python regressions**, and **4/4 release-audit tests**. Gitleaks 8.30.1 passed across all locally available refs; a heuristic inspection of 287 tracked text files returned zero matches. These are **user-supplied local logs, not successful hosted CI runs**. At Phase XIX commit [`75a2cd6`](https://github.com/rickyjreyes/PVNP/commit/75a2cd6f5fb526f527f5494c2264ce793eb9ff35), the dashboard generator and all **13 test groups** passed after a Windows CRLF compatibility fix. The dashboard reports **91 claims, 79 Exact (86.8%), 83 resolved (91.2%)**. The 627-declaration build was observed at the earlier commit; it should not be represented as a fresh build of every later documentation-only commit. For repeatable commands, see [Lean verification](lean/README.md) and [release readiness](PUBLIC_RELEASE_READINESS.md). [Phase IX target and invariant tests](pvnp/proofs/phase-ix-universal-lower-bound-status.md) · [Phase VIII proof scope](pvnp/proofs/phase-viii-separation-status.md) · [Phase VI PDE scope](pvnp/proofs/phase-vi-torus-flux-status.md) · [Remaining obligations](pvnp/proofs/remaining-obstructions.md).

## Manuscript publication and archives

| Release | Primary link | Source and provenance |
|---|---|---|
| **Consolidated PVNP technical volume** | [One PDF and publication notes](pvnp/preprints/consolidated-wave-computation/README.md) | [LaTeX master](pvnp/papers/consolidated-wave-computation/main.tex) |
| **Part I** (original 2025 release) | [Zenodo DOI](https://doi.org/10.5281/zenodo.17743607) | [Archival LaTeX](pvnp/papers/part-i-curvature-bounded-wave-computation/main.tex) |
| **Part II** (original 2025 release) | [Zenodo DOI](https://doi.org/10.5281/zenodo.17732642) | [Archival LaTeX](pvnp/papers/part-ii-discrete-wcc-turing-equivalence/main.tex) |
| **Part III** (original 2025 release) | [Zenodo DOI](https://doi.org/10.5281/zenodo.17783074) | [Archival LaTeX](pvnp/papers/part-iii-physical-complexity-reassessment/main.tex) |
| Independent supplement | [Archive source](pvnp/papers/supplement-fixed-mass-nodal-coercivity/main.tex) | Included as an appendix, not counted as a separate new primary paper |

[Detailed historical manuscript map](CONTENTS.md) · [Complete formalization ledger](pvnp/proofs/manuscript-lean-inventory.md)

## Full research goal

**This repository is intended to attempt the complete PVNP program**, from the original WCC proposal and uniform discrete semantics through rigorous nonlinear PDE resource estimates, adversarial hard-instance lower bounds, and the possible classical P-versus-NP bridge. Progress on a restricted model does not close the final conjecture. [Full proof-completion charter, dependencies, and acceptance gates](pvnp/PROOF_COMPLETION_CHARTER.md).

The original manuscripts, independent supplements, negative results, and Lean checks are all retained. Where the strongest claim cannot be proved, the repo records the exact obstruction instead of silently replacing the original goal.

## Mathematical scope

- **Part I** presents a model-relative research program and corrected proof obligations. Its universal physical curvature lower bound and WCC complexity-class separation remain **conditional**. It does **not** prove classical `P != NP`.
- **Part II** gives polynomial-time simulations between **uniform finite-state discrete** WCC and standard Turing computation. Its claims about physical wave realizability and curvature-energy preservation are **separate, not proved by the discrete simulation**.
- The distinction between discrete `P_WCC` and physical curvature-budgeted `P_WCC^phys` must be maintained.
- **Part III** revisits ten issues (`WIN-12`–`WIN-21`) with corrected statements, counterexamples, and explicitly conditional physical conclusions.
- [**Lean formalization**](lean/README.md) provides kernel-checkable supporting results for all three papers; it does not prove the still-open WCC separations.


**Offline PDF and rights release review (no GitHub Actions):** `bash scripts/review_public_release_offline.sh --all` runs the consolidated PDF rebuild, independent PDF content/page checks, asset/history audit and approval-status report. It cannot grant a license or approve publication.

**Reproduce all release checks locally:** `bash scripts/verify_public_release.sh` is the strict release preflight and invokes the combined PDF, Lean, axiom, manuscript and dashboard checks; `bash scripts/run_release_verification.sh --all` runs the underlying release-verification suite. The complete gate has **not** yet passed because the local PDF toolchain (`pdflatex` / `pdfinfo`) was unavailable. Require a successful final gate or an explicitly approved source-only publication scope before release. The individual source PDFs are retained only under ignored `.release-verification/` for review; a single consolidated PDF is the publication output.

## Build the one-PDF release

Run `bash scripts/build_pdfs.sh` with the required LaTeX packages. The build compiles the three source manuscripts and supplement into **temporary archive PDFs** and then generates only `pvnp/preprints/consolidated-wave-computation/paper.pdf` as the primary output. On a successful `main` build, GitHub Actions commits this consolidated PDF and retires four redundant tracked PDF artifacts. The original LaTeX sources and Zenodo publication records are preserved.

**Verification is a separate gate:** the PDF build does not establish Lean proof validity. The complete local Lean/axiom checks passed at `c92158f` notwithstanding [hosted CI runner issue #59](https://github.com/rickyjreyes/PVNP/issues/59); the consolidated PDF generation and rendered-content checks have **not** been completed at the Phase XIX release head. The new free, offline verification is `bash scripts/verify_public_pdf_offline.sh`; successful hosted Actions is not required if the local evidence is complete. GitHub visibility must remain unchanged until manual privacy, third-party content, patent disclosure and license decisions are completed.

## Latest quantitative scaling audit

[Expanding-domain exact nonlinear Hamiltonian plane wave](pvnp/proofs/expanding-domain-hamiltonian-mode.md): on growing periodic devices, fixed positive mass and uniformly bounded Hamiltonian do not give an input-size-independent positive curvature-to-Laplacian coefficient. This does not contradict the existing [fixed-domain nodal coercivity supplement](pvnp/preprints/supplement-fixed-mass-nodal-coercivity/README.md).

## Latest deterministic SAT channel theorem

[Split-input 3-CNF SAT and finite-alphabet lower bound](pvnp/proofs/split-3sat-reliable-channel.md) prove that **every** correct deterministic two-party SAT protocol under standard full-transcript rectangularity has `2^n <= q^m`, where `m` is the number of transcript symbols and `q` their alphabet size. This is a *restricted distributed-communication theorem*, not a universal SAT time lower bound or a proof of classical P ≠ NP. Lean checks the exact 3-CNF semantics and counting argument; the separate amplitude/noise packing bound explicitly requires instrument specifications.

## Bandlimited wave-state reliability bound

For an actual conserved-mass WCT Hamiltonian field read through a complex D-mode projection with adversarial norm-eta noise, the [sphere-packing theorem](pvnp/proofs/bandlimited-noisy-wave-packing.md) shows `N <= (1 + sqrt(M)/eta)^(2D)` for N individually decodable field labels. This standard analytical proof requires receiver spectral-band limits and robust distinct readouts. It **does not** force SAT solvers to distinguish all assignments and is not Lean-certified as a continuum theorem.
