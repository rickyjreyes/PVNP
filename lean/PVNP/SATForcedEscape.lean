import PVNP.SATForcedBarrier

/-!
# Controlled escape and the exact peak-energy barrier for the fixed false well

A prescribed common phase rotation reaches a satisfying readout in normalized time one,
with zero graph curvature and energy at most 32/25. A cyclic sum-of-squares decomposition
proves every successful continuous admissible path crosses that same energy.
No general SAT algorithm or realization theorem for the frozen PDE is asserted.
-/
namespace PVNP.SATDynamics
open PVNP.PartIPsiSat PVNP.InterwovenSAT PVNP.SATFalseWell

noncomputable def escapeField (t : ℝ) : ℕ → ℂ :=
  fun _ => Complex.exp (((Real.pi * (1 - t) : ℝ) : ℂ) * Complex.I)

theorem escape_admissible (t : ℝ) : Admissible (escapeField t) := by
  intro i
  exact Complex.norm_exp_ofReal_mul_I _

theorem escape_continuous (i : ℕ) : Continuous fun t => escapeField t i := by
  unfold escapeField
  fun_prop

theorem escape_start : escapeField 0 = fieldOf fun _ => false := by
  funext i
  simp [escapeField, fieldOf, Complex.exp_pi_mul_I]

theorem escape_end : escapeField 1 = fieldOf fun _ => true := by
  funext i
  simp [escapeField, fieldOf]

theorem escape_curvature (F : CNF3) (t : ℝ) : Ecurv F (sq (escapeField t)) = 0 := by
  unfold PVNP.InterwovenSAT.sq escapeField
  exact Ecurv_const F _

theorem escape_energy (lam mu t : ℝ) :
    energySB trapFormula lam mu (escapeField t) =
      (1 - (1 + Real.cos (Real.pi * (1 - t))) / 2) ^ 2 *
        (1 + 5 * ((1 + Real.cos (Real.pi * (1 - t))) / 2)) := by
  have hz : ‖Complex.exp (((Real.pi * (1 - t) : ℝ) : ℂ) * Complex.I) ^ 2‖ = 1 := by
    rw [norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow]
  unfold energySB
  rw [escape_curvature, show Ecoup trapFormula (sq (escapeField t)) = 0 from Ecoup_const _ hz]
  simp only [mul_zero, add_zero, Elog, Elogic_trapFormula]
  have hs : ∀ i, sPos (phases (escapeField t)) i =
      (1 + Real.cos (Real.pi * (1 - t))) / 2 := by
    intro i
    rw [sPos_eq (escape_admissible t) i]
    simp only [escapeField, Complex.exp_ofReal_mul_I_re]
  rw [hs, hs, hs]
  unfold trapEnergy
  ring

theorem escape_energy_bound (lam mu t : ℝ) :
    energySB trapFormula lam mu (escapeField t) ≤ 32 / 25 := by
  rw [escape_energy]
  set s := (1 + Real.cos (Real.pi * (1 - t))) / 2
  have hs : s ≤ 1 := by dsimp [s]; linarith [Real.cos_le_one (Real.pi * (1 - t))]
  have h : 0 ≤ (s - 1 / 5) ^ 2 * (7 - 5 * s) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

theorem escape_readout (lam mu : ℝ) : energySB trapFormula lam mu (escapeField 1) = 0 := by
  rw [escape_energy]
  norm_num

/-- Exact cyclic sum-of-squares decomposition of the false-well polynomial. -/
theorem trapEnergy_decomposition (x y z : ℝ) :
    trapEnergy x y z =
      (1 - (x+y+z)/3)^2 * (1 + 5*((x+y+z)/3)) +
      (1/2 - 23*(x+y+z)/54 + 2*x/3 + 7*z/9)*(x-y)^2 +
      (1/2 - 23*(x+y+z)/54 + 2*y/3 + 7*x/9)*(y-z)^2 +
      (1/2 - 23*(x+y+z)/54 + 2*z/3 + 7*y/9)*(z-x)^2 := by
  unfold trapEnergy
  ring

theorem trapEnergy_mean_lower {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x+y+z ≤ 3/5) :
    (1 - (x+y+z)/3)^2 * (1 + 5*((x+y+z)/3)) ≤ trapEnergy x y z := by
  have ha : 0 ≤ 1/2 - 23*(x+y+z)/54 := by linarith
  have h1 : 0 ≤ (1/2 - 23*(x+y+z)/54 + 2*x/3 + 7*z/9)*(x-y)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 - 23*(x+y+z)/54 + 2*y/3 + 7*x/9)*(y-z)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ (1/2 - 23*(x+y+z)/54 + 2*z/3 + 7*y/9)*(z-x)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  rw [trapEnergy_decomposition]
  linarith

theorem trapEnergy_before_saddle {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x+y+z ≤ 3/5) : 1 ≤ trapEnergy x y z := by
  have h := trapEnergy_mean_lower hx hy hz hs
  have hpos : 0 ≤ (x+y+z)*(1-(x+y+z)+5*(x+y+z)^2/27) :=
    mul_nonneg (by linarith) (by nlinarith [sq_nonneg (x+y+z)])
  nlinarith

theorem trapEnergy_saddle {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x+y+z = 3/5) : 32/25 ≤ trapEnergy x y z := by
  have h := trapEnergy_mean_lower hx hy hz hs.le
  rw [hs] at h
  norm_num at h ⊢
  exact h

/-- Matching lower bound for all continuous admissible successful paths on this instance. -/
theorem readout_requires_sharp_peak {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {Ψ : ℝ → ℕ → ℂ} (hadm : ∀ t, Admissible (Ψ t))
    (hc : ∀ i, Continuous fun t => Ψ t i) {T : ℝ} (hT : 0 ≤ T)
    (h0 : Ψ 0 = fieldOf fun _ => false)
    (hread : energySB trapFormula lam mu (Ψ T) < 1/8) :
    ∃ t ∈ Set.Icc 0 T, 32/25 ≤ energySB trapFormula lam mu (Ψ t) := by
  let s : ℕ → ℝ → ℝ := fun i t => sPos (phases (Ψ t)) i
  have hsc : ∀ i, Continuous (s i) := by
    intro i
    have he : s i = fun t => (1 + (Ψ t i).re) / 2 := by
      funext t
      exact sPos_eq (hadm t) i
    rw [he]
    exact (continuous_const.add (Complex.continuous_re.comp (hc i))).div_const 2
  have hnn : ∀ i t, 0 ≤ s i t := fun i t => sPos_nonneg _ i
  have hE : ∀ t, trapEnergy (s 0 t) (s 1 t) (s 2 t) ≤ energySB trapFormula lam mu (Ψ t) := by
    intro t
    have h := energySB_ge_Elog trapFormula hlam hmu (hadm t)
    simpa only [Elog, Elogic_trapFormula, s] using h
  let q : ℝ → ℝ := fun t => s 0 t + s 1 t + s 2 t
  have hqc : Continuous q := ((hsc 0).add (hsc 1)).add (hsc 2)
  have hq0 : q 0 = 0 := by
    have he : ∀ i, s i 0 = 0 := by
      intro i
      dsimp [s]
      rw [h0, sPos_eq (fieldOf_admissible _) i]
      simp [fieldOf]
    simp [q, he]
  have hqT : 3/5 < q T := by
    by_contra hn
    have h := trapEnergy_before_saddle (hnn 0 T) (hnn 1 T) (hnn 2 T) (le_of_not_gt hn)
    have := hE T
    linarith
  obtain ⟨t, ht, hqt⟩ := intermediate_value_Icc hT hqc.continuousOn
    (show (3/5 : ℝ) ∈ Set.Icc (q 0) (q T) from ⟨by rw [hq0]; norm_num, hqT.le⟩)
  exact ⟨t, ht, (trapEnergy_saddle (hnn 0 t) (hnn 1 t) (hnn 2 t) hqt).trans (hE t)⟩

end PVNP.SATDynamics
