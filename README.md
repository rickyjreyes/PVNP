# P vs NP — Wave Curvature Computation

**Richard J. Reyes · Independent Researcher**

Research manuscripts on discrete Wave Curvature Computation (WCC), classical complexity, and physical curvature-resource constraints. Organized after the [math manuscript repository](https://github.com/rickyjreyes/math): a navigable collection with **PDFs, LaTeX sources, scope notes, and a reproducible build workflow**, grouped under `pvnp/`.

**[PDF-to-Lean reconciliation and release audit](pvnp/proofs/pdf-lean-reconciliation-20261107.md):** identifies the corrected original statements, all nine Restricted/Open obligations, stale legacy PDFs, and the verification gates that remain before public release.

## Primary publication: one consolidated technical volume

**[Wave-Constrained Computation: Formal Equivalence, Physical Resource Bounds, and the P versus NP Problem](pvnp/preprints/consolidated-wave-computation/README.md)**

The primary release is **one consolidated PDF**. It binds the revised Part I, Part II and Part III manuscripts, plus a separately identified fixed-mass nodal-coercivity appendix, under one editorial overview and historical publication record. The [consolidated LaTeX source](pvnp/papers/consolidated-wave-computation/main.tex) and [one-PDF build workflow](.github/workflows/pdfs.yml) are authoritative for this edition.

The previous studies remain cited by their original Zenodo identifiers and retain their [archival LaTeX sources](pvnp/papers/). Consolidation does **not** represent new publication dates for the original manuscripts. The new primary PDF is available only once the build has actually succeeded; [CI runner issue #59](https://github.com/rickyjreyes/PVNP/issues/59) currently blocks some workflows. Classical P versus NP remains unsolved.

## Verified developments (November 2026)

| Program | Kernel-checked result | Limit |
|---|---|---|
| **Phase IX** | `SATTarget.satLowerBound_iff_superpolynomial` proves that the per-input target (every correct `SAT_dense` decider exceeds every `C·\|x\|^k` on arbitrarily long inputs) is equivalent to `SATLowerBound` and to `conj:wcc_depth` for `SAT_dense`. No-go theorems: `TseitinSAT.tseitin_mem_SAT_dense_iff_comp` (expander/Tseitin instances of `SAT_dense` are decided by component parity) and `VerifierCrossing.crossingInfo_not_superpolynomial` (the polynomial-time language `V_SAT` carries quadratic crossing information). | Fixes the target and rules out two candidate invariants. `SATLowerBound` is **not** proved. |
| **Phase VIII, PR [#38](https://github.com/rickyjreyes/PVNP/pull/38)** | `CrossingHennie.hennie` proves alternating crossing-sequence splicing for the ordinary single-tape TM. `CrossingSAT` and `CrossingSATSets` derive mixed-SAT acceptance and a near-quadratic time lower bound. | A **single-tape** lower bound of `Ω(N² / (log N · log \|Λ\|))`, not superpolynomial SAT hardness. |
| **Phase VI, PR [#40](https://github.com/rickyjreyes/PVNP/pull/40)** | `PVNP.Torus.global_wellposed` and `PVNP.Torus.flux_inequality` / `curvature_time_bound` formalize global H² torus evolution and PDE-derived localized-mass flux. | Requires `L > 0`, `γ > 0`, specified solutions and detector regularity/bounds; not a computational resource separation. |
| **Uniform discrete WCC** | Verified polynomial-time class equivalences `P_disc = P_TM` and `NP_disc = NP_TM`, plus finite-model variations. | Does not identify discrete computation with physically charged curvature computation. |

**[Lean Formalization Dashboard](pvnp/dashboard/index.html)**: all 91 manuscript claims in current (amended) and original (October 27) views, conditional Exact claims marked, the 11 Phase X supporting theorems, the PR #49 experiment (verified on its PR head only), open obligations and exact-head CI evidence. Open `pvnp/dashboard/index.html` in a browser from a clone; no server or network access is needed. Its data are generated from the inventory, its git history and the Lean sources (`node pvnp/dashboard/build.js`), and CI rejects stale data (`node pvnp/dashboard/check.js`). See [the dashboard README](pvnp/dashboard/README.md).

**Proof status:** No proof of classical `P ≠ NP` or its opposite. The decisive statement `CrossingSAT.SATLowerBound` (`SAT_dense ∉ P_TM`) is unproved. The manuscript claim inventory remains **78 Exact, 2 Restricted, 4 Refuted, 7 Open**; “Exact” may describe a conditional implication whose premise is still open. Part II's three corrected claims match existing Lean proofs. Part I's I-13 now matches the proved quiescent support bound; I-10 is re-scoped to a **conditional** common-successor mixing theorem with a new Lean declaration. Neither establishes physical mixing or a SAT lower bound. I-12 now records the conditional P=NP compatibility counterargument for charged encoders; I-20 separates explicit-state description complexity from succinct certificate verification. All original counterexamples and open lower-bound premises are retained.

**Reproducibility:** The integration PR #40 passed its exact-head `lean`, `phase-iii-targeted` and PDF `build` checks. To reproduce the Lean build and axiom audit, see [Lean verification](lean/README.md). [Phase IX target and invariant tests](pvnp/proofs/phase-ix-universal-lower-bound-status.md) · [Phase VIII proof scope](pvnp/proofs/phase-viii-separation-status.md) · [Phase VI PDE scope](pvnp/proofs/phase-vi-torus-flux-status.md) · [Remaining obligations](pvnp/proofs/remaining-obstructions.md).

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

## Build the one-PDF release

Run `bash scripts/build_pdfs.sh` with the required LaTeX packages. The build compiles the three source manuscripts and supplement into **temporary archive PDFs** and then generates only `pvnp/preprints/consolidated-wave-computation/paper.pdf` as the primary output. On a successful `main` build, GitHub Actions commits this consolidated PDF and retires four redundant tracked PDF artifacts. The original LaTeX sources and Zenodo publication records are preserved.

**Verification is a separate gate:** the PDF build does not establish the validity of new Lean declarations. Recent Phase XII and XIII changes await a successful full Lean kernel check due to the runner issue.

## Latest quantitative scaling audit

[Expanding-domain exact nonlinear Hamiltonian plane wave](pvnp/proofs/expanding-domain-hamiltonian-mode.md): on growing periodic devices, fixed positive mass and uniformly bounded Hamiltonian do not give an input-size-independent positive curvature-to-Laplacian coefficient. This does not contradict the existing [fixed-domain nodal coercivity supplement](pvnp/preprints/supplement-fixed-mass-nodal-coercivity/README.md).

## Latest deterministic SAT channel theorem

[Split-input 3-CNF SAT and finite-alphabet lower bound](pvnp/proofs/split-3sat-reliable-channel.md) prove that **every** correct deterministic two-party SAT protocol under standard full-transcript rectangularity has `2^n <= q^m`, where `m` is the number of transcript symbols and `q` their alphabet size. This is a *restricted distributed-communication theorem*, not a universal SAT time lower bound or a proof of classical P ≠ NP. Lean checks the exact 3-CNF semantics and counting argument; the separate amplitude/noise packing bound explicitly requires instrument specifications.

## Bandlimited wave-state reliability bound

For an actual conserved-mass WCT Hamiltonian field read through a complex D-mode projection with adversarial norm-eta noise, the [sphere-packing theorem](pvnp/proofs/bandlimited-noisy-wave-packing.md) shows `N <= (1 + sqrt(M)/eta)^(2D)` for N individually decodable field labels. This standard analytical proof requires receiver spectral-band limits and robust distinct readouts. It **does not** force SAT solvers to distinguish all assignments and is not Lean-certified as a continuum theorem.
