import PVNP.RoundedStepBudget

/-!
# Exact finite readout with an arbitrary real H² detector

Only detector coefficients indexed by S-S can affect a trial state
supported in S. No infinite detector convolution or truncation error
is needed for the finite readout itself.
-/
open Complex
open scoped BigOperators
namespace PVNP.TorusGalerkin
open PVNP.Torus PVNP.ContinuumPrecision

theorem finite_detector_sum {L : ℝ} (hL : 0 < L) {χ v : ℓ2}
    (hreal : rev (co L χ) = co L χ) (S : Finset Z2)
    (hv : Supported S v) :
    Jdet L χ v =
      (∑ k ∈ S, (starRingEnd ℂ) (co L v k) *
        ((L : ℂ)⁻¹ * ∑ j ∈ S, co L χ (k-j)*co L v j)).re := by
  rw [Jdet_eq_re hL hreal, inner_Lc, co_mulH hL]
  have hco : ∀ j, j ∉ S → co L v j = 0 := by
    intro j hj
    simp [co, hv j hj]
  have hsum : (∑' k : Z2, (starRingEnd ℂ) (co L v k) *
      pr L (co L χ) (co L v) k) =
      ∑ k ∈ S, (starRingEnd ℂ) (co L v k) *
        ((L : ℂ)⁻¹ * ∑ j ∈ S, co L χ (k-j)*co L v j) := by
    calc
      _ = ∑ k ∈ S, (starRingEnd ℂ) (co L v k) *
          pr L (co L χ) (co L v) k := by
        apply tsum_eq_sum
        intro k hk
        rw [hco k hk, map_zero, zero_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [finite_pr L (co L χ) (co L v) S hco k]
  rw [hsum]

theorem finite_detector_dependence {L : ℝ} (hL : 0 < L)
    {χ χ' v : ℓ2} (hreal : rev (co L χ) = co L χ)
    (hreal' : rev (co L χ') = co L χ') (S : Finset Z2)
    (hv : Supported S v)
    (heq : ∀ k ∈ S, ∀ j ∈ S, co L χ (k-j) = co L χ' (k-j)) :
    Jdet L χ v = Jdet L χ' v := by
  rw [finite_detector_sum hL hreal S hv, finite_detector_sum hL hreal' S hv]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hinner : (∑ j ∈ S, co L χ (k-j)*co L v j) =
      ∑ j ∈ S, co L χ' (k-j)*co L v j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [heq k hk j hj]
  rw [hinner]

theorem finite_detector_free_sum {L : ℝ} (hL : 0 < L) (κ t : ℝ)
    {χ v : ℓ2} (hreal : rev (co L χ) = co L χ) (S : Finset Z2)
    (hv : Supported S v) :
    Jdet L χ (U L κ t v) =
      (∑ k ∈ S, (starRingEnd ℂ) (ph L κ t k * co L v k) *
        ((L : ℂ)⁻¹ * ∑ j ∈ S, co L χ (k-j) *
          (ph L κ t j * co L v j))).re := by
  rw [finite_detector_sum hL hreal S (support_U L κ t hv)]
  simp only [co_U]

end PVNP.TorusGalerkin
