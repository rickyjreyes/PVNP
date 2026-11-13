import PVNP.TorusFlux

/-!
# WCT physical readout: a two-outcome curvature/time resource obligation

This module uses the *actual* frozen cubic-quintic torus PDE and the
localized-mass detector `PVNP.Torus.Jdet`. The existing PDE-derived theorem
`Torus.curvature_time_bound` proves that changing detector mass by `δ`
within time `T` costs at least `δ^4 / (Γ^4 T^3)` of integrated squared
Laplacian norm.

New here:
* `detector_contrast_budget`: the equivalent positive resource-product
  inequality with a charged integrated-curvature budget.
* `two_outcomes_require_change`: elementary but exact two-trajectory
  distinguishability, assuming a common initial detector reading.
* `binary_readout_resource_disjunction`: for any two PDE solutions that start
  with the same detector value and end separated by `δ`, AT LEAST ONE
  trajectory must pay the stated curvature/time budget. Both branches
  are charged and have their own PDE-derived constants.
* `no_binary_readout_below_both_budgets`: an explicit no-go statement if
  both branches are claimed to operate below that cost.

This establishes a physical readout resource inequality, NOT an arbitrary
SAT decision lower bound or a WCT P/NP separation. The detector regularity,
positive Gamma conditions, and common initial *detector reading* are explicit.
It does not assume that the initial physical states are the same, that the
trajectories attract to locks, or that SAT must produce such a detector pair.
-/

open MeasureTheory

namespace PVNP.PhysicalReadoutCapacity

open PVNP.Torus

variable {L κ β γ : ℝ}

/-- If the detected mass changes by at least `δ` in time `T`, and the
integrated squared Laplacian is at most `B`, the PDE forces
`δ^4 ≤ Γ^4 T^3 B`. This is the charged, denominator-free form of the
existing torus flux theorem, not a new spectral-cutoff assumption. -/
theorem detector_contrast_budget
    (hL : 0 < L) (hγ : 0 < γ)
    {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv)
    {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u)
    {T δ B : ℝ} (hT : 0 < T) (hδ : 0 ≤ δ)
    (hΓ : 0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0))
    (hchange : δ ≤ |Jdet L χv (u T) - Jdet L χv (u 0)|)
    (hbudget : (∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2) ≤ B) :
    δ ^ 4 ≤
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ^ 4 *
        T ^ 3 * B := by
  have hflux := curvature_time_bound (L := L) (κ := κ) (β := β) (γ := γ)
    hL hγ hq hreal (aW_nonneg L (co L χv)) (bW_nonneg L (co L χv))
    (detector_bounds hq).1 (detector_bounds hq).2 hu hT hΓ hδ hchange
  have hden : 0 <
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ^ 4 * T ^ 3 := by
    positivity
  have hbound := le_trans hflux hbudget
  have hprod := (div_le_iff₀ hden).mp hbound
  calc
    δ ^ 4 ≤ B *
        (Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ^ 4 *
          T ^ 3) := hprod
    _ = Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ^ 4 *
        T ^ 3 * B := by ring

/-- Two detector outputs starting with the same value and ending at
separation `δ` require at least one branch to change by `δ/2`.
This statement does not claim either branch has hard computational work. -/
theorem two_outcomes_require_change
    (a₀ b₀ aT bT δ : ℝ)
    (hinit : a₀ = b₀) (hsep : δ ≤ |aT - bT|) :
    δ / 2 ≤ |aT - a₀| ∨ δ / 2 ≤ |bT - b₀| := by
  have hdecomp : aT - bT = (aT - a₀) - (bT - b₀) := by
    rw [hinit]
    ring
  have ha := abs_le.mp (le_refl (|aT - a₀|))
  have hb := abs_le.mp (le_refl (|bT - b₀|))
  have htriangle : |aT - bT| ≤ |aT - a₀| + |bT - b₀| := by
    rw [hdecomp]
    apply abs_le.mpr
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  by_contra h
  push_neg at h
  linarith

/-- Two exact PDE trajectories, one localized-mass detector.
If the initial detector readings agree and the final readings differ by
at least `δ`, then at least one branch must spend the stated curvature
budget. The two Gamma constants and curvature budgets are NOT assumed
identical and are each computed from their own trajectory. -/
theorem binary_readout_resource_disjunction
    (hL : 0 < L) (hγ : 0 < γ)
    {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv)
    (u v : ℝ → ℓ2)
    (hu : IsSolution L κ β γ u) (hv : IsSolution L κ β γ v)
    {T δ Bu Bv : ℝ} (hT : 0 < T) (hδ : 0 ≤ δ)
    (hΓu : 0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0))
    (hΓv : 0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (v 0))
    (hinit : Jdet L χv (u 0) = Jdet L χv (v 0))
    (hsep : δ ≤ |Jdet L χv (u T) - Jdet L χv (v T)|)
    (hBu : (∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2) ≤ Bu)
    (hBv : (∫ t in (0 : ℝ)..T, ‖Dc L (v t)‖ ^ 2) ≤ Bv) :
    (δ / 2) ^ 4 ≤
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ^ 4 *
        T ^ 3 * Bu ∨
    (δ / 2) ^ 4 ≤
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (v 0) ^ 4 *
        T ^ 3 * Bv := by
  rcases two_outcomes_require_change
      (Jdet L χv (u 0)) (Jdet L χv (v 0))
      (Jdet L χv (u T)) (Jdet L χv (v T)) δ hinit hsep with hc | hc
  · exact Or.inl (detector_contrast_budget (L := L) (κ := κ) (β := β) (γ := γ)
      hL hγ hq hreal hu hT (by linarith) hΓu hc hBu)
  · exact Or.inr (detector_contrast_budget (L := L) (κ := κ) (β := β) (γ := γ)
      hL hγ hq hreal hv hT (by linarith) hΓv hc hBv)

/-- A conditional impossibility theorem: a pair of PDE solutions
cannot acquire detector contrast `δ` from equal detector readings if the
claimed resource ceilings for BOTH branches are strictly below the
necessary PDE-derived lower bounds. This is a readout theorem, not SAT. -/
theorem no_binary_readout_below_both_budgets
    (hL : 0 < L) (hγ : 0 < γ)
    {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv)
    (u v : ℝ → ℓ2)
    (hu : IsSolution L κ β γ u) (hv : IsSolution L κ β γ v)
    {T δ Bu Bv : ℝ} (hT : 0 < T) (hδ : 0 ≤ δ)
    (hΓu : 0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0))
    (hΓv : 0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (v 0))
    (hinit : Jdet L χv (u 0) = Jdet L χv (v 0))
    (hsep : δ ≤ |Jdet L χv (u T) - Jdet L χv (v T)|)
    (hBu : (∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2) ≤ Bu)
    (hBv : (∫ t in (0 : ℝ)..T, ‖Dc L (v t)‖ ^ 2) ≤ Bv)
    (hsmallu :
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ^ 4 *
        T ^ 3 * Bu < (δ / 2) ^ 4)
    (hsmallv :
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (v 0) ^ 4 *
        T ^ 3 * Bv < (δ / 2) ^ 4) : False := by
  rcases binary_readout_resource_disjunction (L := L) (κ := κ)
      (β := β) (γ := γ) hL hγ hq hreal u v hu hv hT hδ hΓu hΓv
      hinit hsep hBu hBv with h | h
  · exact (not_lt_of_ge h) hsmallu
  · exact (not_lt_of_ge h) hsmallv

end PVNP.PhysicalReadoutCapacity
