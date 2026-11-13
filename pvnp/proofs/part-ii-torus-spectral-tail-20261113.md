# Part II: torus spectral tails without a sharp evolution cutoff

**Date:** 13 November 2026
**Code:** `lean/PVNP/TorusSpectralTail.lean`
**Verification:** Pending exact-head CI.

The maintained nonlinear WCT equation is not finite-mode invariant.
`PVNP.FourierReceiver.cubic_quintic_generates_new_modes` already
establishes this fact for explicit two-mode data.

The new lemmas work with the *actual* `Torus.co L v` Fourier
coefficients and `Torus.qf L k = |ξ_k|²`:

For a finite index set `S`, a positive cutoff `K`, and
`qf L k ≥ K²` on `S`,

```text
K⁴ Σ_{k∈S} ‖co L v k‖²
  ≤ Σ_{k∈S} (qf L k)² ‖co L v k‖².
```

A bound `D²` on the finite weighted sum immediately implies

```text
Σ_{k∈S} ‖co L v k‖² ≤ D²/K⁴.
```

These are exact spectral arithmetic results on arbitrary finite sets
of WCT Fourier modes. In combination with the existing
`TorusFlux.normD_eq_integral`, the same weight is the classical
spatial Laplacian norm for sufficiently regular fields.

**Infinite-tail completion:** The further declarations
`infinite_high_frequency_mass_bound` and
`infinite_tail_mass_from_curvature_budget` bound the total infinite
spectral tail using `Torus.summable_co_sq`, `summable_sq (Dc L v)`,
`Torus.Dc_apply` and `Torus.norm_sq_eq`. They prove
`K⁴ ∑'_{qf≥K²} |co|² ≤ ‖Dc L v‖²` and therefore
`∑'_{qf≥K²} |co|² ≤ D²/K⁴` whenever
`‖Dc L v‖² ≤ D²`. These are genuine infinite Fourier sums,
not a sharp cutoff on the nonlinear state.

**Remaining limits:** They do not prove polynomial-time numerical
simulation of the nonlinear PDE, or that an approximately bandlimited
state is an exactly bandlimited solution.

The larger physical-to-Turing simulation in Part II remains a
separate mathematical obligation. No theorem in this PR presupposes
that simulation, and no manuscript claim is automatically reclassified.
