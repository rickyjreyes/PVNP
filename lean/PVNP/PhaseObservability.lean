import Mathlib

/-!
# Phase-sensitive WCT observability: exact algebraic proof contracts

Source PDE (wct-pde/src/wct_pde/projection_free.py):
  i ψ_t = (Δ + κ)²ψ - β|ψ|²ψ + γ|ψ|⁴ψ.

This module checks algebraic consequences of a zero-mean detector's
PDE-derived evolution inequality and the safe regularized curvature
comparison. The integration-by-parts, Fourier spectral gap, Sobolev,
polynomial Lipschitz, and continuum differentiability arguments
are detailed in the accompanying paper note but NOT kernel formalized.

It also tests two obstructions: uniform phase rotation can have zero
spatial curvature; density-weighted curvature loses coercivity at nodes.
-/

namespace PVNP.PhaseObservability

/-- For every complex uniform-amplitude state the discrete second
difference vanishes, irrespective of its (possibly evolving) phase. -/
theorem constant_second_difference_zero (z : ℂ) :
    z - 2 * z + z = 0 := by
  ring

/-- With k_star = 1, beta = 2, gamma = 1, a homogeneous amplitude
A = 2 rotates at frequency omega = 1 - 2*4 + 16 = 9.
The analytic time-dependence e^(-i omega t) is not formalized here. -/
theorem maintained_default_uniform_frequency :
    (1 : ℝ) ^ 2 - 2 * (2 : ℝ) ^ 2 + (2 : ℝ) ^ 4 = 9 := by
  norm_num

/-- The WCT density-weight F(|psi|²) can vanish at a node although
the independent Laplacian factor need not vanish. -/
noncomputable def densityWeight (amplitude epsilon : ℝ) : ℝ :=
  amplitude ^ 2 / (amplitude ^ 2 + epsilon ^ 2) ^ 2

theorem densityWeight_at_node (epsilon : ℝ) :
    densityWeight 0 epsilon = 0 := by
  simp [densityWeight]

theorem node_weighted_cost_zero (laplacian epsilon : ℝ) :
    densityWeight 0 epsilon * laplacian ^ 2 = 0 := by
  simp [densityWeight_at_node]

theorem safe_regularizer_positive (amplitude epsilon : ℝ)
    (heps : 0 < epsilon) :
    0 < amplitude ^ 2 + epsilon ^ 2 := by
  have hsq : 0 < epsilon ^ 2 := sq_pos_of_pos heps
  nlinarith [sq_nonneg amplitude]

/-- A nonzero Fourier-mode coefficient forces Laplacian energy via
the spectral identity; the exact Fourier/Parseval theorem is an
external mathematical premise here, not declared as an axiom. -/
theorem spectral_mode_curvature_transfer
    (eigenvalue coefficient laplacianEnergy
      curvatureCost amplitudeCap epsilon : ℝ)
    (hspectral : eigenvalue ^ 2 * coefficient ^ 2 ≤ laplacianEnergy)
    (hweight : laplacianEnergy ≤
      (amplitudeCap ^ 2 + epsilon ^ 2) * curvatureCost) :
    eigenvalue ^ 2 * coefficient ^ 2 ≤
      (amplitudeCap ^ 2 + epsilon ^ 2) * curvatureCost :=
  hspectral.trans hweight

/-- Composition of the mean-zero observable/Poincare/Hölder estimate
with the globally phase-safe curvature domination. This is the
abstract algebraic kernel certificate, not the continuum PDE theorem. -/
theorem finite_time_phase_readout_bound
    (contrast detectorConstant time lapTimeEnergy
      curvatureCost amplitudeCap epsilon : ℝ)
    (hK : 0 ≤ detectorConstant) (hT : 0 ≤ time)
    (hreadout : contrast ^ 2 ≤
      detectorConstant ^ 2 * time * lapTimeEnergy)
    (hweight : lapTimeEnergy ≤
      (amplitudeCap ^ 2 + epsilon ^ 2) * curvatureCost) :
    contrast ^ 2 ≤
      detectorConstant ^ 2 * time *
        (amplitudeCap ^ 2 + epsilon ^ 2) * curvatureCost := by
  have hnonneg : 0 ≤ detectorConstant ^ 2 * time :=
    mul_nonneg (sq_nonneg _) hT
  have hscaled := mul_le_mul_of_nonneg_left hweight hnonneg
  calc
    contrast ^ 2 ≤ detectorConstant ^ 2 * time * lapTimeEnergy := hreadout
    _ ≤ detectorConstant ^ 2 * time *
        ((amplitudeCap ^ 2 + epsilon ^ 2) * curvatureCost) := hscaled
    _ = detectorConstant ^ 2 * time *
        (amplitudeCap ^ 2 + epsilon ^ 2) * curvatureCost := by ring

/-- Strict detector contrast forces a positive phase-safe curvature cost
for fixed positive time, detector constant, and regularizer. -/
theorem finite_time_phase_readout_lower
    (contrast detectorConstant time lapTimeEnergy
      curvatureCost amplitudeCap epsilon : ℝ)
    (hK : 0 < detectorConstant) (hT : 0 < time)
    (heps : 0 < epsilon)
    (hreadout : contrast ^ 2 ≤
      detectorConstant ^ 2 * time * lapTimeEnergy)
    (hweight : lapTimeEnergy ≤
      (amplitudeCap ^ 2 + epsilon ^ 2) * curvatureCost) :
    contrast ^ 2 /
      (detectorConstant ^ 2 * time *
        (amplitudeCap ^ 2 + epsilon ^ 2)) ≤ curvatureCost := by
  have hd : 0 < detectorConstant ^ 2 * time *
      (amplitudeCap ^ 2 + epsilon ^ 2) :=
    mul_pos (mul_pos (sq_pos_of_pos hK) hT)
      (safe_regularizer_positive amplitudeCap epsilon heps)
  apply (div_le_iff₀ hd).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (finite_time_phase_readout_bound contrast detectorConstant time
      lapTimeEnergy curvatureCost amplitudeCap epsilon
      (le_of_lt hK) (le_of_lt hT) hreadout hweight)

/-- If two real-valued detector outputs differ by δ while their initial
readout agrees, at least δ must be accounted for by the sum of their
two absolute readout changes. (For complex outputs, use norm triangle.) -/
theorem two_readout_paths_contrast
    (initial final0 final1 contrast : ℝ)
    (hcontrast : contrast ≤ |final1 - final0|) :
    contrast ≤ |final1 - initial| + |final0 - initial| := by
  calc
    contrast ≤ |final1 - final0| := hcontrast
    _ = |(final1 - initial) + (initial - final0)| := by ring
    _ ≤ |final1 - initial| + |initial - final0| := abs_add_le _ _
    _ = |final1 - initial| + |final0 - initial| := by
      rw [abs_sub_comm initial final0]

end PVNP.PhaseObservability
