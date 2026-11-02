import PVNP.PartIIIAnalytic

/-!
# Part III Proposition `prop:highfreq` on the periodic cube `(0, 2π)³`

The manuscript states the high-frequency counterexample on the 3-D periodic
cube.  This module lifts the one-dimensional theorems of
`PVNP.PartIIIAnalytic` to that exact setting:

* the field `Ψ_N(x) = 1 + sin(N x₁)/N` on `ℝ³ = ℝ × ℝ × ℝ`;
* classical partial derivatives along the coordinate lines, the 3-D
  Laplacian `∂₁∂₁ + ∂₂∂₂ + ∂₃∂₃` and gradient energy density
  `(∂₁Ψ)² + (∂₂Ψ)² + (∂₃Ψ)²`;
* `lap3_psi`: `ΔΨ_N(x) = −N sin(N x₁)` everywhere;
* `cube_gradient_energy`: `∫_{[0,2π]³} |∇Ψ_N|² = 4π³` for every `N ≥ 1`;
* `cube_curvature_lower`: `∫_{[0,2π]³} |Θ₁[Ψ_N]|² ≥ (16/25) π³ N²` for
  `N ≥ 2` — exactly the manuscript's constants.

Integrals over the cube are genuine Lebesgue integrals for the product
measure, factorized by Fubini (`setIntegral_prod_mul`).
-/

open MeasureTheory Real PVNP.PartIIIAnalytic

namespace PVNP.PartIIIHighFreq3D

/-- Partial derivatives along coordinate lines in `ℝ × ℝ × ℝ`. -/
noncomputable def p1 (f : ℝ × ℝ × ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ := deriv (fun s => f (s, x.2)) x.1
noncomputable def p2 (f : ℝ × ℝ × ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  deriv (fun s => f (x.1, s, x.2.2)) x.2.1
noncomputable def p3 (f : ℝ × ℝ × ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  deriv (fun s => f (x.1, x.2.1, s)) x.2.2

/-- The 3-D Laplacian. -/
noncomputable def lap3 (f : ℝ × ℝ × ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  p1 (p1 f) x + p2 (p2 f) x + p3 (p3 f) x

/-- Gradient energy density. -/
noncomputable def gradSq (f : ℝ × ℝ × ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  p1 f x ^ 2 + p2 f x ^ 2 + p3 f x ^ 2

/-- Regularized curvature density `Θ₁` in 3-D. -/
noncomputable def theta3 (f : ℝ × ℝ × ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  -(lap3 f x * f x) / (f x ^ 2 + 1)

/-- The 3-D field `Ψ_N(x) = ψ_N(x₁)`. -/
noncomputable def Psi (N : ℕ) (x : ℝ × ℝ × ℝ) : ℝ := psiN N x.1

theorem p1_Psi {N : ℕ} (hN : 0 < N) : p1 (Psi N) = fun x => Real.cos (N * x.1) := by
  funext x; simp only [p1, Psi]; rw [deriv_psiN hN]

theorem p2_const (g : ℝ → ℝ) : p2 (fun x : ℝ × ℝ × ℝ => g x.1) = fun _ => 0 := by
  funext x; simp [p2]

theorem p3_const (g : ℝ → ℝ) : p3 (fun x : ℝ × ℝ × ℝ => g x.1) = fun _ => 0 := by
  funext x; simp [p3]

theorem p1_cos (N : ℕ) : p1 (fun x : ℝ × ℝ × ℝ => Real.cos (N * x.1)) =
    fun x => -(N * Real.sin (N * x.1)) := by
  funext x
  simp only [p1]
  have h := (Real.hasDerivAt_cos (N * x.1)).comp x.1 ((hasDerivAt_id x.1).const_mul (N : ℝ))
  rw [show (fun s : ℝ => Real.cos (N * s)) = Real.cos ∘ HMul.hMul (N : ℝ) from rfl, h.deriv]
  ring

theorem lap3_psi {N : ℕ} (hN : 0 < N) (x : ℝ × ℝ × ℝ) : lap3 (Psi N) x = -(N * Real.sin (N * x.1)) := by
  simp only [lap3]
  rw [p1_Psi hN, p1_cos, show Psi N = fun x : ℝ × ℝ × ℝ => psiN N x.1 from rfl, p2_const, p3_const]
  simp [p2, p3]

theorem gradSq_psi {N : ℕ} (hN : 0 < N) (x : ℝ × ℝ × ℝ) : gradSq (Psi N) x = Real.cos (N * x.1) ^ 2 := by
  simp only [gradSq]
  rw [p1_Psi hN, show Psi N = fun x : ℝ × ℝ × ℝ => psiN N x.1 from rfl, p2_const, p3_const]
  simp

theorem theta3_psi {N : ℕ} (hN : 0 < N) (x : ℝ × ℝ × ℝ) : theta3 (Psi N) x = theta1 (psiN N) x.1 := by
  simp only [theta3, theta1, lap3_psi hN, deriv2_psiN hN, Psi]

/-- The cube `[0,2π]³`. -/
def cube : Set (ℝ × ℝ × ℝ) := Set.Icc 0 (2 * π) ×ˢ (Set.Icc 0 (2 * π) ×ˢ Set.Icc 0 (2 * π))

/-- Fubini on the cube for functions of the first coordinate. -/
theorem cube_integral_fst (F : ℝ → ℝ) :
    ∫ x in cube, F x.1 = (∫ t in (0 : ℝ)..2 * π, F t) * (2 * π) ^ 2 := by
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
    F (fun _ => (1 : ℝ)) (Set.Icc 0 (2 * π)) (Set.Icc 0 (2 * π) ×ˢ Set.Icc 0 (2 * π))
  simp only [mul_one] at h
  rw [cube, Measure.volume_eq_prod, h, setIntegral_const, smul_eq_mul, mul_one,
    intervalIntegral.integral_of_le (by positivity), integral_Icc_eq_integral_Ioc]
  congr 1
  rw [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by have := Real.pi_pos; linarith)]
  ring

/-- **Gradient energy on the cube is `4π³` for every `N ≥ 1`.** -/
theorem cube_gradient_energy {N : ℕ} (hN : 0 < N) : ∫ x in cube, gradSq (Psi N) x = 4 * π ^ 3 := by
  have : (fun x => gradSq (Psi N) x) = fun x : ℝ × ℝ × ℝ => Real.cos (N * x.1) ^ 2 :=
    funext (gradSq_psi hN)
  rw [this, cube_integral_fst (fun t => Real.cos (N * t) ^ 2), integral_cos_sq_mul hN]
  ring

/-- **Curvature cost on the cube is at least `(16/25) π³ N²` for `N ≥ 2`**
(Part III Proposition `prop:highfreq`, exact constants). -/
theorem cube_curvature_lower {N : ℕ} (hN : 2 ≤ N) :
    16 / 25 * π ^ 3 * (N : ℝ) ^ 2 ≤ ∫ x in cube, (theta3 (Psi N) x) ^ 2 := by
  have hN0 : 0 < N := by omega
  have : (fun x => (theta3 (Psi N) x) ^ 2) = fun x : ℝ × ℝ × ℝ => (theta1 (psiN N) x.1) ^ 2 :=
    funext fun x => by rw [theta3_psi hN0]
  rw [this, cube_integral_fst (fun t => (theta1 (psiN N) t) ^ 2)]
  have h1 := highfreq_curvature_lower hN
  have h2 : (0 : ℝ) ≤ (2 * π) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

/-- Amplitude bounds `1/2 ≤ Ψ_N ≤ 3/2` hold on all of `ℝ³` for `N ≥ 2`. -/
theorem Psi_bounds {N : ℕ} (hN : 2 ≤ N) (x : ℝ × ℝ × ℝ) : 1 / 2 ≤ Psi N x ∧ Psi N x ≤ 3 / 2 :=
  psiN_bounds hN x.1

end PVNP.PartIIIHighFreq3D
