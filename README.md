# P vs NP — Wave Curvature Computation

**Richard J. Reyes · Independent Researcher**

Research manuscripts on discrete Wave Curvature Computation (WCC), classical complexity, and physical curvature-resource constraints. Organized after the [math manuscript repository](https://github.com/rickyjreyes/math): a navigable collection with **PDFs, LaTeX sources, scope notes, and a reproducible build workflow**, grouped under `pvnp/`.

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
