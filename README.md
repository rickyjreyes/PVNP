# P vs NP — Wave Curvature Computation

**Richard J. Reyes · Independent Researcher**

Research manuscripts on discrete Wave Curvature Computation (WCC), classical complexity, and physical curvature-resource constraints. Organized after the [math manuscript repository](https://github.com/rickyjreyes/math): a navigable collection with **PDFs, LaTeX sources, scope notes, and a reproducible build workflow**, grouped under `pvnp/`.

## Read the manuscripts

| Manuscript | Compiled PDF | LaTeX source | Release |
|---|---|---|---|
| **Part I — P vs NP in Curvature-Bounded Wave Computation** | [PDF](pvnp/preprints/part-i-curvature-bounded-wave-computation/paper.pdf) | [LaTeX](pvnp/papers/part-i-curvature-bounded-wave-computation/main.tex) | May 7, 2025 (original); revised October 27, 2026 |
| **Part II — Discrete Wave-Constrained Computation and Classical Complexity** | [PDF](pvnp/preprints/part-ii-discrete-wcc-turing-equivalence/paper.pdf) | [LaTeX](pvnp/papers/part-ii-discrete-wcc-turing-equivalence/main.tex) | November 26, 2025 (original); revised October 27, 2026 |

[**Detailed manuscript map**](CONTENTS.md) · [**PVNP collection**](pvnp/README.md) · [**PDF build workflow**](.github/workflows/pdfs.yml)

## Mathematical scope

- **Part I** presents a model-relative research program and corrected proof obligations. Its universal physical curvature lower bound and WCC complexity-class separation remain **conditional**. It does **not** prove classical `P != NP`.
- **Part II** gives polynomial-time simulations between **uniform finite-state discrete** WCC and standard Turing computation. Its claims about physical wave realizability and curvature-energy preservation are **separate, not proved by the discrete simulation**.
- The distinction between discrete `P_WCC` and physical curvature-budgeted `P_WCC^phys` must be maintained.

## Build PDFs

Run `bash scripts/build_pdfs.sh` in a LaTeX environment with the required packages (including `physics`, `tcolorbox`, `tikz`, and `authblk`). The [GitHub Actions workflow](.github/workflows/pdfs.yml) builds both PDFs and publishes `pvnp/preprints/*/paper.pdf` to the default branch when repository Actions and write permissions permit.

**Research status:** Not independently peer-reviewed. Git commit dates are revision records and should not be represented as historical first-publication dates.
