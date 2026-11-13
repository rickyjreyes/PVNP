import PVNP.TorusFlux

/-!
# Part II: exact finite-frequency spectral tail bound on the frozen WCT torus

An H² (Laplacian) bound controls high-frequency mass without assuming
that the nonlinear PDE preserves a sharp spectral cutoff.

This module uses the **actual** torus coefficient map `co L v` and
squared-frequency `qf L k = |ξ_k|²` of the maintained WCT Fourier
formalization. For any finite set S of indices with `qf L k ≥ K²`:

  K⁴ Σ_{k ∈ S} ‖co L v k‖²
    ≤ Σ_{k ∈ S} (qf L k)² ‖co L v k‖².

If the right-hand side is bounded by D², the tail mass is ≤ D²/K⁴.
Both statements are finite-sum consequences of the Fourier spectral
weighting; no imaginary exact cutoff or linearity of the nonlinear
evolution is presumed.

This is NOT a theorem of polynomial-time numerical simulation, and
does not assert that all Fourier tails over an infinite set are small
without the additional summability / limiting argument.
-/

namespace PVNP.TorusSpectralTail

open PVNP.Torus Finset

/-- On a finite set of modes all having squared frequency at least K²,
the squared Laplacian spectral weight pays at least K⁴ times their mass. -/
theorem finite_high_frequency_mass_bound
    (L K : ℝ) (v : ℓ2) (S : Finset Z2) (hK : 0 < K)
    (hS : ∀ k ∈ S, K ^ 2 ≤ qf L k) :
    K ^ 4 * (∑ k ∈ S, ‖co L v k‖ ^ 2) ≤
      ∑ k ∈ S, (qf L k) ^ 2 * ‖co L v k‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hfreq := hS k hk
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hq : 0 ≤ qf L k := le_trans hK2 hfreq
  have hfactor : 0 ≤ (qf L k - K ^ 2) * (qf L k + K ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hfreq) (add_nonneg hq hK2)
  have hq4 : K ^ 4 ≤ (qf L k) ^ 2 := by nlinarith [hfactor]
  exact mul_le_mul_of_nonneg_right hq4 (sq_nonneg _)

/-- For any certified finite spectral curvature budget D², the energy
in every specified finite high-frequency subset is at most D²/K⁴. -/
theorem finite_tail_mass_from_curvature_budget
    (L K D : ℝ) (v : ℓ2) (S : Finset Z2) (hK : 0 < K)
    (hS : ∀ k ∈ S, K ^ 2 ≤ qf L k)
    (hD : (∑ k ∈ S, (qf L k) ^ 2 * ‖co L v k‖ ^ 2) ≤ D ^ 2) :
    (∑ k ∈ S, ‖co L v k‖ ^ 2) ≤ D ^ 2 / K ^ 4 := by
  have htail := finite_high_frequency_mass_bound L K v S hK hS
  apply (le_div_iff₀ (pow_pos hK 4)).2
  nlinarith [htail, hD]

end PVNP.TorusSpectralTail
