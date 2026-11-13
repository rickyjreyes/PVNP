# Part III: conserved-data frozen-WCT Laplacian ceiling

**Date:** 13 November 2026
**Lean:** `lean/PVNP/WCTRegularizedCeiling.lean`
**Status:** Pending exact-head full Lean build and axiom audit.

This module extracts a time-uniform estimate from the actual frozen 2D
cubic–quintic Hamiltonian torus PDE and the repository's established
`conservation`, `kin_le_ham`, `norm_Dc_le` theorems.

For every global `IsSolution L κ β γ u`, with `L>0`, `γ>0`, define

```text
M₀ = mass L (u 0)
H₀ = ham L κ β γ (u 0)
B  = sqrt(H₀ + 3β² M₀/(16γ)) + |κ| sqrt(M₀).
```

The kernel-checked target is, for **every** real time `t`,

```text
‖Dc L (u t)‖ ≤ B
‖Dc L (u t)‖² ≤ B²
‖Dc L (u t)‖²/(4ε²) ≤ B²/(4ε²)    (ε>0).
```

Part III's complex-safe regularized curvature functional already has
the separate theorem `PartIIIAnalytic.curvature_cost_le`, bounding
its actual spatial integral by one quarter of the Laplacian energy
times `1/ε²`. The existing
`TorusFlux.normD_eq_integral` identifies the Fourier Laplacian norm
with the classical spatial integral under additional `L1q` regularity.
This new module exposes the **conserved-data ceiling** required for
the combination, not a new proof that the physical-to-Turing simulation
is efficient.

No universal polynomial-in-input resource rail is asserted without
uniform polynomial bounds on the initial mass, Hamiltonian, model
parameters, and inverse regulator. No classical complexity separation
follows from a curvature upper bound alone.
