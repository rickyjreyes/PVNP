# Phase VI verification: periodic-torus H² flow and continuum flux

**Status:** Integrated on `main` through [PR #40](https://github.com/rickyjreyes/PVNP/pull/40), merge `888296eaeaa1095f21613ca3e14486e4c8044c00` (November 5, 2026 PT / November 6 UTC). The PR-head GitHub checks `lean`, `phase-iii-targeted`, and `build` all passed. The root [`lean/PVNP.lean`](../../lean/PVNP.lean) imports the relevant modules; [`lean/audit/AxiomAudit.lean`](../../lean/audit/AxiomAudit.lean) audits named theorems with only standard Lean axioms.

## M3-T: global well-posedness on the periodic square

The frozen cubic–quintic equation is

```math
i\partial_t\psi=(\Delta+\kappa)^2\psi-\beta|\psi|^2\psi+\gamma|\psi|^4\psi
```

on the 2-D torus of period `L > 0`, for `γ > 0`, with data in `H²(T²_L)`. The solution is stated using weighted Fourier-coefficient `ℓ²` states and the coefficientwise PDE formulation.

- [`TorusSeries.lean`](../../lean/PVNP/TorusSeries.lean), [`TorusH2.lean`](../../lean/PVNP/TorusH2.lean) and [`TorusNonlin.lean`](../../lean/PVNP/TorusNonlin.lean): Fourier analysis, H² embedding/algebra estimates and the nonlinear map.
- [`TorusFlow.lean`](../../lean/PVNP/TorusFlow.lean), [`TorusGlobal.lean`](../../lean/PVNP/TorusGlobal.lean): interaction-picture evolution, mass/Hamiltonian conservation, global existence and a priori bounds.
- [`TorusWellPosed.lean`](../../lean/PVNP/TorusWellPosed.lean): `PVNP.Torus.global_wellposed`, `conservation`, `apriori`, `continuous_dependence`. Uniqueness, global existence and continuous dependence hold for the specified torus equation. The mass/Hamiltonian a priori H² bound has constants uniform in `L`, but this is **not** a claim of uniform spectral-gap or detector efficiency as the physical domain grows.

## F-1: continuum flux inequality derived from the PDE

[`TorusMult.lean`](../../lean/PVNP/TorusMult.lean) formalizes multiplication by a detector weight. [`TorusFlux.lean`](../../lean/PVNP/TorusFlux.lean) contains:

- `PVNP.Torus.flux_identity`: differentiation of the localized mass readout along an `IsSolution` solution.
- `PVNP.Torus.flux_static`, `flux_inequality`, `flux_inequality_explicit`: an explicit derivative bound with `Γ` derived from the model and detector estimates. The typed conclusion of `flux_inequality` is `|Jdot| ≤ Gam … * sqrt (‖Dc L (u t)‖)`.
- `PVNP.Torus.curvature_time_bound`: if the detector readout changes by at least `δ` over a time `T > 0` with `Γ > 0`, then `δ⁴/(Γ⁴ T³) ≤ ∫₀ᵀ ‖Dc L (u t)‖² dt`.

**Hypotheses matter.** The detector weight has weighted absolutely summable Fourier coefficients (`L1q`), is real in the relevant Fourier sense (`rev (co L χv) = co L χv`), and its gradient/Laplacian obey explicit bounds. These are theorems about this frozen PDE and a specified localized-mass detector, not a universal bound on every physical readout, computational encoding or SAT decider. The earlier abstract `TransportCalculus` result still takes a flux inequality as a premise; `TorusFlux` discharges it for this torus model under its own hypotheses.

## Still open

- M3-C: certified lattice-to-continuum convergence and numerical error budgets.
- M1: resource-faithful physical simulation and computational realization.
- M2: a lower bound against **all** deterministic SAT deciders, not just particular physical devices.
- The classical separation `SAT_dense ∉ P_TM` and `P ≠ NP`.

See [the current obstruction ledger](remaining-obstructions.md), [Phase VIII SAT analysis](phase-viii-separation-status.md), and [the formalization status](../../lean/formalization.yaml). The manuscript claim inventory is unchanged: **70 Exact, 2 Restricted, 11 Refuted, 8 Open**.
