import PVNP.TorusFlux
import PVNP.PartIIIAnalytic

/-!
# Part III: a conserved-data Laplacian ceiling for the frozen WCT PDE

Part III's corrected regularized curvature operator has pointwise
upper bound |Θ_ε| ≤ |Δψ|/(2ε). This module exposes the time-uniform
Laplacian norm ceiling for actual solutions of the frozen two-dimensional
cubic–quintic torus PDE, using the mass and Hamiltonian conservation
and coercivity theorems already proved in PVNP.Torus.

In particular, this is not an assumption of a polynomial curvature
rail. If the conserved mass, Hamiltonian and inverse regulator scale
polynomially in a uniform input family, this derived Laplacian
*majorant* does also. The result does not prove that every physical
device admits polynomial rails, nor a universal SAT lower bound.
-/

namespace PVNP.WCTRegularizedCeiling

open PVNP.Torus

/-- Conserved-data upper bound for ‖Δψ(t)‖₂, evaluated at t=0. -/
noncomputable def lapBudget (L κ β γ : ℝ) (u₀ : ℓ2) : ℝ :=
  Real.sqrt (ham L κ β γ u₀ +
    3 * β ^ 2 / (16 * γ) * mass L u₀) +
    |κ| * Real.sqrt (mass L u₀)

theorem lapBudget_nonneg (L κ β γ : ℝ) (u₀ : ℓ2) :
    0 ≤ lapBudget L κ β γ u₀ := by
  unfold lapBudget
  positivity

/-- The actual frozen torus PDE bounds every time slice's Laplacian norm
by one number depending only on initial mass and Hamiltonian. -/
theorem frozen_torus_laplacian_ceiling
    {L κ β γ : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) (t : ℝ) :
    ‖Dc L (u t)‖ ≤ lapBudget L κ β γ (u 0) := by
  have hcons := conservation hL hu t
  have hP : ‖Lc L (u t)‖ = Real.sqrt (mass L (u 0)) := by
    rw [← hcons.1, mass_eq_norm_Lc, Real.sqrt_sq (norm_nonneg _)]
  have hcap : ‖Ac L κ (u t)‖ ≤
      Real.sqrt (ham L κ β γ (u 0) +
        3 * β ^ 2 / (16 * γ) * mass L (u 0)) := by
    rw [← hcons.1, ← hcons.2]
    exact Real.le_sqrt_of_sq_le (kin_le_ham hL hγ (u t))
  have hnorm := norm_Dc_le L κ (u t)
  rw [hP] at hnorm
  unfold lapBudget
  linarith

/-- The squared Laplacian norm has the corresponding uniform-in-time
bound, without assuming exact finite Fourier support. -/
theorem frozen_torus_laplacian_squared_ceiling
    {L κ β γ : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) (t : ℝ) :
    ‖Dc L (u t)‖ ^ 2 ≤ (lapBudget L κ β γ (u 0)) ^ 2 := by
  have h := frozen_torus_laplacian_ceiling hL hγ hu t
  have hn := norm_nonneg (Dc L (u t))
  have hb := lapBudget_nonneg L κ β γ (u 0)
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hn hb)]

/-- For the regularized-curvature upper-envelope (Laplacian²/4ε²),
the actual frozen PDE provides a time-uniform conserved-data ceiling.
PartIIIAnalytic.curvature_cost_le proves independently that the corrected
complex-safe curvature cost is below this envelope after the
Laplacian's spatial integral is identified with ‖Dc‖². -/
theorem regularized_laplacian_envelope_ceiling
    {L κ β γ ε : ℝ} (hL : 0 < L) (hγ : 0 < γ) (hε : 0 < ε)
    {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) (t : ℝ) :
    ‖Dc L (u t)‖ ^ 2 / (4 * ε ^ 2) ≤
      (lapBudget L κ β γ (u 0)) ^ 2 / (4 * ε ^ 2) := by
  have hsq := frozen_torus_laplacian_squared_ceiling hL hγ hu t
  exact div_le_div_of_nonneg_right hsq (by positivity)

end PVNP.WCTRegularizedCeiling
