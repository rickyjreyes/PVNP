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

**Important limits:** these two statements do not yet justify
passing to the *entire infinite high-frequency tail*; that requires
summability and an appropriate monotone-limit argument. Nor do they
show that the PDE evolution can be numerically computed in polynomial
time, or that an approximately bandlimited state is an exactly
bandlimited solution.

The larger physical-to-Turing simulation in Part II remains a
separate mathematical obligation. No theorem in this PR presupposes
that simulation, and no manuscript claim is automatically reclassified.
