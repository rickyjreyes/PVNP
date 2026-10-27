# PVNP Lean verification — extended formalization

**Scope:** Exact finite Boolean semantics, deterministic local WCC dynamics, and finite Boolean-hypercube inequalities. This is a mechanized **consistent mathematical core**, not proof of the complete manuscripts or of P ≠ NP.

Run `cd lean && lake update && lake exe cache get && lake build`. CI rejects `sorry`, `admit`, and custom `axiom` declarations in the PVNP modules.

| Part | Files | Formally targeted |
|---|---|---|
| I | [Core](PVNP/PartI.lean), [Extended](PVNP/PartIExtended.lean) | Signed Boolean literals, arbitrary finite CNF satisfaction, equivalent zero-penalty encoding, unsatisfiable opposite unit clauses, conditional class separation |
| II | [Core](PVNP/PartII.lean), [Extended](PVNP/PartIIExtended.lean) | Finite deterministic replay, radius-one local WCC machine with fixed rule and boundary state, locality, quantization step/trajectory compatibility under commuting semantics |
| III | [Core](PVNP/PartIII.lean), [Extended](PVNP/PartIIIExtended.lean) | Zero symbolic Laplacian of distinct states, denominator counterexample, positive squared regularizer, witnesses, finite hypercube directional boundary counts and normalized influence ≤ n |

**Open/unformalized obligations:** Uniform polynomial-time Turing equivalence with encoded runtime and machines; quantum field PDE existence, Sobolev estimates and stability; exact physical curvature-energy bounds; exponential locked-expander lower bounds against *all* algorithms; physically admissible NP witness existence; classical and physical P vs NP. These cannot be marked verified without valid theorems and missing hypotheses. No custom axioms stand in for those statements.

[Detailed proof status](formalization.yaml).
