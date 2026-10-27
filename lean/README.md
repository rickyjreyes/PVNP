# PVNP Lean formalization — three-paper scope

**Toolchain:** Lean 4.23.0 and Mathlib v4.23.0. Build with:
\`cd lean && lake update && lake exe cache get && lake build\`.

This is a set of **auxiliary formally stated theorems and explicit counterexamples**, not a kernel proof of the entire PVNP trilogy.

| Manuscript | Source | Intended kernel-checkable facts |
|---|---|---|
| Part I | [PVNP/PartI.lean](PVNP/PartI.lean) | Signed Boolean literals; OR clause penalty; conditional set separation |
| Part II | [PVNP/PartII.lean](PVNP/PartII.lean) | Replay of deterministic transitions; faithful simulation under semiconjugacy; a representative-rule counterexample |
| Part III | [PVNP/PartIII.lean](PVNP/PartIII.lean) | Distinct states with zero symbolic Laplacian; shifted denominator counterexample; positive regularizer; witness-ignoring verifier; total normalized influence ≤ n |

**Outside this formalization:** uniform polynomial-time Turing/WCC equivalence at the level of full machine semantics; physical curvature-cost preservation; H² regularity of PDE evolution; expander domain-wall lower bounds; physical or classical P≠NP. None of these have been added as Lean axioms. Discrete analogues must not be mistaken for continuum theorems.

See [formalization.yaml](formalization.yaml) for precise WIN tags and outstanding work.
