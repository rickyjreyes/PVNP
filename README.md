# P vs NP — Wave Curvature Computation

**Richard J. Reyes · Independent Researcher**

Research manuscripts on discrete Wave Curvature Computation (WCC), classical complexity, and physical curvature-resource constraints. Organized after the [math manuscript repository](https://github.com/rickyjreyes/math): a navigable collection with **PDFs, LaTeX sources, scope notes, and a reproducible build workflow**, grouped under `pvnp/`.

## Verified developments (November 2026)

| Program | Kernel-checked result | Limit |
|---|---|---|
| **Phase IX** | `SATTarget.satLowerBound_iff_superpolynomial` proves that the per-input target (every correct `SAT_dense` decider exceeds every `C·\|x\|^k` on arbitrarily long inputs) is equivalent to `SATLowerBound` and to `conj:wcc_depth` for `SAT_dense`. No-go theorems: `TseitinSAT.tseitin_mem_SAT_dense_iff_comp` (expander/Tseitin instances of `SAT_dense` are decided by component parity) and `VerifierCrossing.crossingInfo_not_superpolynomial` (the polynomial-time language `V_SAT` carries quadratic crossing information). | Fixes the target and rules out two candidate invariants. `SATLowerBound` is **not** proved. |
| **Phase VIII, PR [#38](https://github.com/rickyjreyes/PVNP/pull/38)** | `CrossingHennie.hennie` proves alternating crossing-sequence splicing for the ordinary single-tape TM. `CrossingSAT` and `CrossingSATSets` derive mixed-SAT acceptance and a near-quadratic time lower bound. | A **single-tape** lower bound of `Ω(N² / (log N · log \|Λ\|))`, not superpolynomial SAT hardness. |
| **Phase VI, PR [#40](https://github.com/rickyjreyes/PVNP/pull/40)** | `PVNP.Torus.global_wellposed` and `PVNP.Torus.flux_inequality` / `curvature_time_bound` formalize global H² torus evolution and PDE-derived localized-mass flux. | Requires `L > 0`, `γ > 0`, specified solutions and detector regularity/bounds; not a computational resource separation. |
| **Uniform discrete WCC** | Verified polynomial-time class equivalences `P_disc = P_TM` and `NP_disc = NP_TM`, plus finite-model variations. | Does not identify discrete computation with physically charged curvature computation. |

**Proof status:** No proof of classical `P ≠ NP` or its opposite. The decisive statement `CrossingSAT.SATLowerBound` (`SAT_dense ∉ P_TM`) is unproved. The manuscript claim inventory remains **75 Exact, 2 Restricted, 6 Refuted, 8 Open**; “Exact” may describe a conditional implication whose premise is still open. Part II's three corrected claims match existing Lean proofs. Part I's I-13 now matches the proved quiescent support bound; I-10 is re-scoped to a **conditional** common-successor mixing theorem with a new Lean declaration. Neither establishes physical mixing or a SAT lower bound. All original counterexamples are retained.

**Reproducibility:** The integration PR #40 passed its exact-head `lean`, `phase-iii-targeted` and PDF `build` checks. To reproduce the Lean build and axiom audit, see [Lean verification](lean/README.md). [Phase IX target and invariant tests](pvnp/proofs/phase-ix-universal-lower-bound-status.md) · [Phase VIII proof scope](pvnp/proofs/phase-viii-separation-status.md) · [Phase VI PDE scope](pvnp/proofs/phase-vi-torus-flux-status.md) · [Remaining obligations](pvnp/proofs/remaining-obstructions.md).

## Read the manuscripts

| Manuscript | Compiled PDF | LaTeX source | Release |
|---|---|---|---|
| **Part I — P vs NP in Curvature-Bounded Wave Computation** | [PDF](pvnp/preprints/part-i-curvature-bounded-wave-computation/paper.pdf) | [LaTeX](pvnp/papers/part-i-curvature-bounded-wave-computation/main.tex) | May 7, 2025 (original); revised October 27, 2026 |
| **Part II — Discrete Wave-Constrained Computation and Classical Complexity** | [PDF](pvnp/preprints/part-ii-discrete-wcc-turing-equivalence/paper.pdf) | [LaTeX](pvnp/papers/part-ii-discrete-wcc-turing-equivalence/main.tex) | November 26, 2025 (original); revised October 27, 2026 |
| **Part III — Physical Complexity: A Critical Reassessment** | [PDF](pvnp/preprints/part-iii-physical-complexity-reassessment/paper.pdf) | [LaTeX](pvnp/papers/part-iii-physical-complexity-reassessment/main.tex) | December 1, 2025 (original); revised October 27, 2026 |

[**Detailed manuscript map**](CONTENTS.md) · [**PVNP collection**](pvnp/README.md) · [**PDF build workflow**](.github/workflows/pdfs.yml)

## Full research goal

**This repository is intended to attempt the complete PVNP program**, from the original WCC proposal and uniform discrete semantics through rigorous nonlinear PDE resource estimates, adversarial hard-instance lower bounds, and the possible classical P-versus-NP bridge. Progress on a restricted model does not close the final conjecture. [Full proof-completion charter, dependencies, and acceptance gates](pvnp/PROOF_COMPLETION_CHARTER.md).

The original manuscripts, independent supplements, negative results, and Lean checks are all retained. Where the strongest claim cannot be proved, the repo records the exact obstruction instead of silently replacing the original goal.

## Mathematical scope

- **Part I** presents a model-relative research program and corrected proof obligations. Its universal physical curvature lower bound and WCC complexity-class separation remain **conditional**. It does **not** prove classical `P != NP`.
- **Part II** gives polynomial-time simulations between **uniform finite-state discrete** WCC and standard Turing computation. Its claims about physical wave realizability and curvature-energy preservation are **separate, not proved by the discrete simulation**.
- The distinction between discrete `P_WCC` and physical curvature-budgeted `P_WCC^phys` must be maintained.
- **Part III** revisits ten issues (`WIN-12`–`WIN-21`) with corrected statements, counterexamples, and explicitly conditional physical conclusions.
- [**Lean formalization**](lean/README.md) provides kernel-checkable supporting results for all three papers; it does not prove the still-open WCC separations.

## Build PDFs

Run `bash scripts/build_pdfs.sh` in a LaTeX environment with the required packages (including `physics`, `tcolorbox`, `tikz`, and `authblk`). The [GitHub Actions workflow](.github/workflows/pdfs.yml) builds all three PDFs and publishes `pvnp/preprints/*/paper.pdf` to the default branch when repository Actions and write permissions permit.

**Research status:** Not independently peer-reviewed. Git commit dates are revision records and should not be represented as historical first-publication dates.

## Latest quantitative scaling audit

[Expanding-domain exact nonlinear Hamiltonian plane wave](pvnp/proofs/expanding-domain-hamiltonian-mode.md): on growing periodic devices, fixed positive mass and uniformly bounded Hamiltonian do not give an input-size-independent positive curvature-to-Laplacian coefficient. This does not contradict the existing [fixed-domain nodal coercivity supplement](pvnp/preprints/supplement-fixed-mass-nodal-coercivity/README.md).

## Latest deterministic SAT channel theorem

[Split-input 3-CNF SAT and finite-alphabet lower bound](pvnp/proofs/split-3sat-reliable-channel.md) prove that **every** correct deterministic two-party SAT protocol under standard full-transcript rectangularity has `2^n <= q^m`, where `m` is the number of transcript symbols and `q` their alphabet size. This is a *restricted distributed-communication theorem*, not a universal SAT time lower bound or a proof of classical P ≠ NP. Lean checks the exact 3-CNF semantics and counting argument; the separate amplitude/noise packing bound explicitly requires instrument specifications.

## Bandlimited wave-state reliability bound

For an actual conserved-mass WCT Hamiltonian field read through a complex D-mode projection with adversarial norm-eta noise, the [sphere-packing theorem](pvnp/proofs/bandlimited-noisy-wave-packing.md) shows `N <= (1 + sqrt(M)/eta)^(2D)` for N individually decodable field labels. This standard analytical proof requires receiver spectral-band limits and robust distinct readouts. It **does not** force SAT solvers to distinguish all assignments and is not Lean-certified as a continuum theorem.
