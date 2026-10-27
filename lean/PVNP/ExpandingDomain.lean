import Mathlib

/-!
# Expanding-domain countermodel: exact algebra for the WCT density weight

For a single normalized Fourier mode of fixed mass 1 on a 2D torus of
area V, the pointwise density is s = 1/V and the regularized density
weight at alpha = 0 and epsilon = 1 is

    F(s) = s/(s+1)^2 = V/(V+1)^2.

Consequently F(s) ≤ 1/V, and for every positive c one can choose V
with F(s) < c. A fixed-domain, positive-mass coercivity coefficient
therefore cannot be silently promoted to a domain-uniform one.

The companion analytic note constructs an EXACT solution of the
maintained nonlinear projection-free WCT Hamiltonian and proves
bounded mass/Hamiltonian alongside vanishing curvature cost. Lean
here certifies the scalar weight inequalities, not PDE evolution
or continuum Fourier identities.
-/

namespace PVNP.ExpandingDomain

noncomputable def modeDensityRatio (volume : ℝ) : ℝ :=
  volume / (volume + 1) ^ 2

theorem modeDensityRatio_nonneg (volume : ℝ) (hV : 0 < volume) :
    0 ≤ modeDensityRatio volume := by
  unfold modeDensityRatio
  positivity

theorem modeDensityRatio_le_inverse_volume
    (volume : ℝ) (hV : 0 < volume) :
    modeDensityRatio volume ≤ 1 / volume := by
  unfold modeDensityRatio
  have hden : 0 < (volume + 1) ^ 2 := by positivity
  apply (div_le_div_iff₀ hden hV).2
  nlinarith

/-- There is no uniform positive lower bound on the density-weight
fraction of Laplacian energy as the physical domain grows, even when
the total wave mass is held fixed at one. -/
theorem no_positive_uniform_density_ratio
    (c : ℝ) (hc : 0 < c) :
    ∃ volume : ℝ, 0 < volume ∧ modeDensityRatio volume < c := by
  have hV : 0 < (2 : ℝ) / c := by positivity
  refine ⟨2 / c, hV, ?_⟩
  have h := modeDensityRatio_le_inverse_volume (2 / c) hV
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hrecip : (1 : ℝ) / (2 / c) = c / 2 := by
    field_simp [hc0]
    <;> ring
  rw [hrecip] at h
  linarith

/-- The exact Fourier mode Laplacian squared norm equals q² times
the fixed L² mass. Multiplying it by its uniform density weight is
an algebraically exact factorization. -/
theorem normalized_mode_curvature_identity
    (volume q : ℝ) :
    modeDensityRatio volume * (q ^ 2) =
      volume * q ^ 2 / (volume + 1) ^ 2 := by
  unfold modeDensityRatio
  ring

/-- One representative conserved-energy upper bound:
mass 1, κ=1, β=2, γ=1, 0≤q≤1, V≥1, where q=|k|².
The actual nonlinear wave is analyzed in the analytic note. -/
theorem normalized_mode_hamiltonian_bounded
    (volume q : ℝ) (hV : 1 ≤ volume)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - q) ^ 2 - 1 / volume + 1 / (3 * volume ^ 2)
      ≤ (4 : ℝ) / 3 := by
  have hV0 : 0 < volume := by linarith
  have hV2 : 1 ≤ volume ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hV)
      (by linarith : 0 ≤ volume + 1)]
  have hfrac : 1 / (3 * volume ^ 2) ≤ (1 : ℝ) / 3 := by
    have hden : 0 < 3 * volume ^ 2 := by positivity
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 3)).2
    nlinarith
  have hq : (1 - q) ^ 2 ≤ (1 : ℝ) := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have hminus : -(1 / volume) ≤ 0 := by
    have : 0 ≤ (1 : ℝ) / volume := by positivity
    linarith
  linarith

end PVNP.ExpandingDomain
