import Mathlib

/-!
# Fixed-mass nodal curvature: finite two-site theorem

Auxiliary formalization for the independent PVNP supplement. Not part of the
original WCT/P versus NP proof.

In a connected two-site graph with field values a,b (real), mass
m = a²+b² and epsilon² > 0, the density-weighted second-difference
energy controls the unweighted energy even when one node is zero:

  (m/(2*(m+epsilon²)²))*[2*(a-b)²]
    ≤ (w(a²)+w(b²))*(a-b)²,

where w(s) = s/(s+epsilon²)².

The continuum fixed-mass / Hamiltonian-sublevel compactness theorem is
proved analytically in the accompanying independent LaTeX note; this
module does not purport to kernel-certify Rellich compactness or PDE
conservation.
-/

namespace PVNP.FixedMassNodal

noncomputable def scalarWeight (s e : ℝ) : ℝ :=
  s / (s + e) ^ 2

theorem nodeWeight_zero (e : ℝ) :
    scalarWeight 0 e = 0 := by
  simp [scalarWeight]

/-- Every nonnegative density s below a total mass m has a bounded
denominator, so the weight dominates s/(m+e)². -/
theorem scalarWeight_lower
    (s m e : ℝ)
    (hs : 0 ≤ s) (hsm : s ≤ m) (he : 0 < e) :
    s / (m + e) ^ 2 ≤ scalarWeight s e := by
  have hsmall : 0 < s + e := by linarith
  have hlarge : 0 < m + e := by linarith
  have hminus : 0 ≤ (m + e) - (s + e) := by linarith
  have hplus : 0 ≤ (m + e) + (s + e) := by linarith
  have hsq : (s + e) ^ 2 ≤ (m + e) ^ 2 := by
    nlinarith [mul_nonneg hminus hplus]
  have hmul :
      s * (s + e) ^ 2 ≤ s * (m + e) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hs
  unfold scalarWeight
  exact (div_le_div_iff₀
    (sq_pos_of_pos hlarge) (sq_pos_of_pos hsmall)).2 hmul

/-- Exact node-tolerant coercivity on a two-vertex connected graph.
The graph Laplacian has values (b-a,a-b), hence its squared energy
is 2(a-b)². The right side is density-weighted Laplacian energy.
No assumption that a and b are nonzero is used. -/
theorem two_site_nodal_coercivity (a b e : ℝ) (he : 0 < e) :
    ((a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2 + e) ^ 2) *
      (a - b) ^ 2 ≤
    (scalarWeight (a ^ 2) e + scalarWeight (b ^ 2) e) *
      (a - b) ^ 2 := by
  let m : ℝ := a ^ 2 + b ^ 2
  have ham : a ^ 2 ≤ m := by
    dsimp [m]
    nlinarith [sq_nonneg b]
  have hbm : b ^ 2 ≤ m := by
    dsimp [m]
    nlinarith [sq_nonneg a]
  have ha := scalarWeight_lower (a ^ 2) m e (sq_nonneg a) ham he
  have hb := scalarWeight_lower (b ^ 2) m e (sq_nonneg b) hbm he
  have hsum :
      m / (m + e) ^ 2 ≤
        scalarWeight (a ^ 2) e + scalarWeight (b ^ 2) e := by
    calc
      m / (m + e) ^ 2 =
          a ^ 2 / (m + e) ^ 2 + b ^ 2 / (m + e) ^ 2 := by
            dsimp [m]
            ring
      _ ≤ scalarWeight (a ^ 2) e +
          scalarWeight (b ^ 2) e := add_le_add ha hb
  have hc := mul_le_mul_of_nonneg_right hsum (sq_nonneg (a - b))
  simpa only [m] using hc

/-- Fixed mass m yields a fully explicit positive coefficient when m>0.
This theorem remains valid for node-containing fields, e.g. a=0. -/
theorem two_site_fixed_mass_coercivity
    (a b m e : ℝ)
    (he : 0 < e)
    (hmass : a ^ 2 + b ^ 2 = m) :
    (m / (2 * (m + e) ^ 2)) * (2 * (a - b) ^ 2) ≤
    (scalarWeight (a ^ 2) e + scalarWeight (b ^ 2) e) *
      (a - b) ^ 2 := by
  have h := two_site_nodal_coercivity a b e he
  rw [hmass] at h
  calc
    (m / (2 * (m + e) ^ 2)) * (2 * (a - b) ^ 2) =
        (m / (m + e) ^ 2) * (a - b) ^ 2 := by ring
    _ ≤ (scalarWeight (a ^ 2) e + scalarWeight (b ^ 2) e) *
        (a - b) ^ 2 := h

/-- Strictly positive coefficient at strictly positive mass and
regularization, even if either site has zero amplitude. -/
theorem two_site_coefficient_positive
    (m e : ℝ) (hm : 0 < m) (he : 0 < e) :
    0 < m / (2 * (m + e) ^ 2) := by
  have hden : 0 < 2 * (m + e) ^ 2 := by positivity
  exact div_pos hm hden

/-- Algebraic transport transfer: a dynamical observability inequality
and a fixed-mass nodal coercivity constant jointly imply a
time-integrated density-weighted resource lower bound. This module
does not assert that the analytical PDE estimates were formalized. -/
theorem readout_to_density_weighted_cost
    (contrast detectorConstant time lapEnergy densityCost c : ℝ)
    (hdetector : 0 ≤ detectorConstant)
    (htime : 0 ≤ time)
    (hc : 0 ≤ c)
    (hreadout : contrast ^ 2 ≤
      detectorConstant ^ 2 * time * lapEnergy)
    (hcoercive : c * lapEnergy ≤ densityCost) :
    c * contrast ^ 2 ≤
      detectorConstant ^ 2 * time * densityCost := by
  calc
    c * contrast ^ 2 ≤
        c * (detectorConstant ^ 2 * time * lapEnergy) :=
      mul_le_mul_of_nonneg_left hreadout hc
    _ = (detectorConstant ^ 2 * time) * (c * lapEnergy) := by ring
    _ ≤ (detectorConstant ^ 2 * time) * densityCost :=
      mul_le_mul_of_nonneg_left hcoercive
        (mul_nonneg (sq_nonneg _) htime)
    _ = detectorConstant ^ 2 * time * densityCost := by ring

end PVNP.FixedMassNodal
