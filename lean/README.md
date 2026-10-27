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

### New curvature-barrier test
[CurvatureBarrier.lean](PVNP/CurvatureBarrier.lean) establishes explicit polynomial *state-encoding* upper bounds on bounded-degree graph Laplacians. These bounds do not prove a solver for SAT. See [analytic note](../pvnp/proofs/curvature-barrier-audit.md).

## Four lower-bound attempts
[Communication](PVNP/Communication.lean) · [Tseitin parity](PVNP/Tseitin.lean) · [Layout and escape time](PVNP/PhysicalBounds.lean) · [Mathematical interpretation](../pvnp/proofs/four-lower-bound-tests.md). These prove restricted inequalities, not unrestricted physical P versus NP.

## Physical communication bridge test
[CurvatureCommunication.lean](PVNP/CurvatureCommunication.lean) formalizes both an affine zero-curvature counterexample and a direct linear bound for a concrete fixed-boundary, paid-slot physical implementation of an exact deterministic DISJ protocol. See the [analytical note](../pvnp/proofs/curvature-communication-bridge.md) for a causal slow-wave counterexample and the sharp 1D Dirichlet inequality. These do not establish a universal WCT curvature cost per bit.

## Actual-PDE readout cost attempt
[HamiltonianTransport.lean](PVNP/HamiltonianTransport.lean) checks cubic–quintic coercivity and algebraic finite-time curvature-tradeoff implications. The [analytical note](../pvnp/proofs/wct-pde-transport-bound.md) derives the conditional localized-mass current bound from the maintained projection-free Hamiltonian PDE and separately treats the real Swift–Hohenberg gradient flow. Continuum PDE conservation, flux integration and Sobolev embedding remain outside this Lean module.
