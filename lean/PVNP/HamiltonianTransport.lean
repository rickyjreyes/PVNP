import Mathlib

/-!
# Model-relative transport cost for the maintained WCT Hamiltonian rail

Source PDE (wct-pde/src/wct_pde/projection_free.py):
  i ∂ₜψ = (Δ + κ)² ψ - β|ψ|²ψ + γ|ψ|⁴ψ, κ = k_star².

Lean proves the pointwise cubic–quintic coercivity identity and the
NONTRIVIAL ALGEBRAIC COMPOSITION of a detector/Hölder resource bound.

The analytical localized-mass current formula, Fourier integration by
parts, the Sobolev estimate, and global PDE existence are NOT formalized.
No claim about all WCT theories or about classical P ≠ NP is made.
-/

namespace PVNP.HamiltonianTransport

/-- Exact completion of squares for the mass-subcritical lower envelope
of the cubic–quintic potential, for γ > 0 and s = |ψ|² ≥ 0. -/
theorem cubic_quintic_potential_lower
    (β γ s : ℝ) (hγ : 0 < γ) (hs : 0 ≤ s) :
    -(3 * β ^ 2 / (16 * γ)) * s ≤
      -(β / 2) * s ^ 2 + (γ / 3) * s ^ 3 := by
  have hg : γ ≠ 0 := ne_of_gt hγ
  have hsquare :
      -(β / 2) * s ^ 2 + (γ / 3) * s ^ 3 +
        (3 * β ^ 2 / (16 * γ)) * s =
        (γ / 3) * s * (s - 3 * β / (4 * γ)) ^ 2 := by
    field_simp
    <;> ring
  have hnonneg :
      0 ≤ (γ / 3) * s * (s - 3 * β / (4 * γ)) ^ 2 := by
    positivity
  linarith

/-- Hamiltonian lower bounded by squared bandpass norm minus mass potential
necessarily bounds that bandpass norm. The PDE conservation identities
are separate analytical obligations. -/
theorem bandpass_norm_sq_control
    (H B mass c : ℝ)
    (hpotential : B ^ 2 - c * mass ^ 2 ≤ H) :
    B ^ 2 ≤ H + c * mass ^ 2 := by
  linarith

/-- The algebraic bridge required after the PDE flux estimate and the
time Hölder estimate have been proved. The hypotheses are consciously
distinct: observable transport, time-Hölder, and curvature domination.

  δ ≤ Γ τ,
  τ^4 ≤ T^3 D,
  D ≤ W C
imply
  δ^4 ≤ Γ^4 T^3 W C.

Here D represents spacetime ∫||Δψ||₂², while C is a regularized
curvature cost. A Lean proof of these integral PDE hypotheses remains open. -/
theorem finite_time_curvature_transport_tradeoff
    (δ Γ τ T D C W : ℝ)
    (hδ : 0 ≤ δ) (hΓ : 0 ≤ Γ) (hτ : 0 ≤ τ)
    (hT : 0 ≤ T) (hW : 0 ≤ W)
    (hobs : δ ≤ Γ * τ)
    (hholder : τ ^ 4 ≤ T ^ 3 * D)
    (hcurvature : D ≤ W * C) :
    δ ^ 4 ≤ Γ ^ 4 * T ^ 3 * W * C := by
  have hγτ : 0 ≤ Γ * τ := mul_nonneg hΓ hτ
  have hsquare :
      δ ^ 2 ≤ (Γ * τ) ^ 2 := by
    have hnon :
        0 ≤ (Γ * τ - δ) * (Γ * τ + δ) :=
      mul_nonneg (sub_nonneg.mpr hobs) (add_nonneg hγτ hδ)
    nlinarith
  have hfourth :
      δ ^ 4 ≤ (Γ * τ) ^ 4 := by
    have hnon :
        0 ≤ ((Γ * τ) ^ 2 - δ ^ 2) *
          ((Γ * τ) ^ 2 + δ ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hsquare)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    nlinarith
  have hscaled :
      Γ ^ 4 * τ ^ 4 ≤ Γ ^ 4 * (T ^ 3 * D) :=
    mul_le_mul_of_nonneg_left hholder (pow_nonneg hΓ 4)
  have hscaled2 :
      Γ ^ 4 * (T ^ 3 * D) ≤
        Γ ^ 4 * (T ^ 3 * (W * C)) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hΓ 4)
    exact mul_le_mul_of_nonneg_left hcurvature (pow_nonneg hT 3)
  calc
    δ ^ 4 ≤ (Γ * τ) ^ 4 := hfourth
    _ = Γ ^ 4 * τ ^ 4 := by ring
    _ ≤ Γ ^ 4 * (T ^ 3 * D) := hscaled
    _ ≤ Γ ^ 4 * (T ^ 3 * (W * C)) := hscaled2
    _ = Γ ^ 4 * T ^ 3 * W * C := by ring

/-- The corresponding positive energy drop for the maintained
Swift–Hohenberg gradient flow, provided the analytical Cauchy–Schwarz
readout/dissipation estimate has been supplied. Not a curvature bound. -/
theorem gradient_flow_energy_drop_lower
    (δ detectorNorm T drop : ℝ)
    (hNorm : 0 < detectorNorm) (hT : 0 < T)
    (hreadout : δ ^ 2 ≤ detectorNorm ^ 2 * T * drop) :
    δ ^ 2 / (detectorNorm ^ 2 * T) ≤ drop := by
  have hden : 0 < detectorNorm ^ 2 * T :=
    mul_pos (sq_pos_of_pos hNorm) hT
  apply (div_le_iff₀ hden).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hreadout

end PVNP.HamiltonianTransport
