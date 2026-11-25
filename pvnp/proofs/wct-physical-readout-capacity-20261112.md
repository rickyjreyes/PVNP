# WCT physical two-outcome readout capacity: Lean proof candidate

**Research branch:** `research/wct-physical-readout-capacity-20261112`
**New module:** `lean/PVNP/PhysicalReadoutCapacity.lean`
**Base:** main at `025af546f30eaf11bfbeca65285d0ee70930b076`
**Status:** Submitted proof candidate, not yet compilation/axiom-audit verified on this branch.
**Classical P versus NP:** Unsolved.
**Physical WCT P versus NP:** Unsolved.

## Mathematical target

For the exact frozen cubic–quintic WCT torus PDE, let
`Jdet L χv (u t)` be the localized-mass detector and
`Γ_u = Torus.Gam L κ β γ a b (u 0)` be the PDE-derived flux constant,
where `a = aW L (co L χv)` and `b = bW L (co L χv)`.

The previously derived, formally stated PDE flux theorem establishes

```
δ^4 / (Γ_u^4 T^3) ≤ ∫₀ᵀ ‖Δu(t)‖₂² dt
```

under the existing torus assumptions (including L > 0, γ > 0,
regular real detector, solution, T > 0, Γ_u > 0 and detector change >= δ).

This module derives its budget form

```
δ^4 ≤ Γ_u^4 T^3 B_u
```

whenever the integral is at most `B_u`.

For TWO trajectories `u,v` with equal detector values at time zero,
and final detector readings at least `δ` apart, one of the two must
change its own detector reading by at least `δ/2`. Hence

```
(δ/2)^4 ≤ Γ_u^4 T^3 B_u
    OR
(δ/2)^4 ≤ Γ_v^4 T^3 B_v
```

Both budgets and both flux constants are explicitly charged.
This is a disjunction: the proof does not identify which branch must pay,
and does not assume both do.

## New declarations

* `detector_contrast_budget`: one-trajectory resource product from
  `Torus.curvature_time_bound`.
* `two_outcomes_require_change`: pairwise detector contrast gives
  nonzero motion in at least one branch from a common initial reading.
* `binary_readout_resource_disjunction`: two-PDE-trajectory resource
  floor with individual Gamma constants and curvature budgets.
* `no_binary_readout_below_both_budgets`: contradiction if both branches
  are claimed to spend less than the necessary lower bound.

## Scope and adversarial tests

* No claim that SAT necessarily creates two trajectories satisfying
  common initial detector reading and positive final separation.
* No claim that arbitrary physical encoders are admissible, uniform,
  bounded-cost, or local. Encoding and decoding complexity remain to
  be charged before any language-level conclusion.
* No claim that these PDE dynamics attract to stable phase locks.
  `PVNP.TorusNoLocking` still applies.
* No claim that lower bounds for local mass transfer establish
  lower bounds on all algorithms or computation time alone.
* The `Γ_u` and `Γ_v` constants depend on the solutions and detector;
  for a uniform family, independently bound them as input length grows.
* Fixed / equal initial readout is not the same as equal initial state.
* Does not introduce a new spectral support axiom.
* Avoid marking I-16, I-3, I-11 or I-37 closed.

## Verification gate

After checking out this branch in a working tree with Lean 4.23.0
and pinned Mathlib:

```bash
cd lean
lake exe cache get
lake build PVNP.PhysicalReadoutCapacity
lake build PVNP
lake env lean audit/AxiomAudit.lean > audit-output.txt
python3 audit/check_axioms.py audit/AxiomAudit.lean audit-output.txt
```

GitHub Actions issue #59 previously prevented hosted runner execution.
Do not label these four declarations kernel-verified until the exact-head
build and axiom audit have actually passed.

## Next mathematical obligation

To connect the new detector inequality to SAT, define one fixed physical
computation family with an explicit uniform encoder, decoder, bounded
input noise, detector regularity and allowable initial-state preparation.
Then show an unavoidable detector separation requirement for a specified
pair of inputs, including encoder cost. Such a result will be a
**model-relative transport lower bound**, not automatically a classical
superpolynomial SAT lower bound.

Only after establishing an algorithm-independent language-level lower
bound for every permitted physical SAT decider can the physical WCT
P/NP separation be stated as unconditional. The classical transfer is
an additional independent theorem.
