import Mathlib

/-!
# Part III, function-space statements (issue #12)

Genuine analytic versions of Part III statements that were previously only
symbolic in `PVNP.PartIII`.

* `theta_pointwise_le`, `curvature_cost_le` (Part III Lemma `lem:h2bound`):
  for **every** measure space, every field `ψ` and every function `lap`
  (the strong or weak Laplacian of `ψ`), and every `ε > 0`,
  `∫ |Θ_ε|² ≤ (1/(4ε²)) ∫ |Δψ|²`, where
  `Θ_ε = -Δψ · conj ψ / (|ψ|² + ε²)`.  Lebesgue integrals in `ℝ≥0∞`; no
  integrability hypotheses are needed.
* `capacity_law` (Part III Theorem `thm:capacity`): the corrected,
  explicitly conditional, uniform version.
* `laplacian_const`, `zero_cost_counterexample` (Part III Proposition
  `prop:zero_cost`): the constant fields `0` and `1` on `ℝ^d` are distinct
  everywhere but their difference has identically zero (Mathlib) Laplacian
  and therefore zero regularized curvature cost on every domain.
* `highfreq_gradient_energy`, `highfreq_curvature_lower` (Part III
  Proposition `prop:highfreq`, one-dimensional periodic version):
  `ψ_N(x) = 1 + sin(Nx)/N` on `[0, 2π]` has gradient energy exactly `π` for
  every `N ≥ 1`, while its regularized curvature cost is at least
  `(4/25) π N²`.  Finite first-derivative energy does not bound the curvature
  functional.
-/

namespace PVNP.PartIIIAnalytic

open MeasureTheory Real

/-! ### The regularized curvature functional -/

/-- Complex-safe regularized curvature density. -/
noncomputable def theta {X : Type*} (ε : ℝ) (ψ lap : X → ℂ) (x : X) : ℂ :=
  -(lap x * (starRingEnd ℂ) (ψ x)) / ((‖ψ x‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)

/-- Regularized curvature cost `C_{Θ,ε}` as a Lebesgue integral. -/
noncomputable def curvatureCost {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ε : ℝ) (ψ lap : X → ℂ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (‖theta ε ψ lap x‖ ^ 2) ∂μ

theorem ratio_le (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε) : r / (r ^ 2 + ε ^ 2) ≤ 1 / (2 * ε) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (r - ε)]

theorem theta_pointwise_le {X : Type*} {ε : ℝ} (hε : 0 < ε) (ψ lap : X → ℂ) (x : X) :
    ‖theta ε ψ lap x‖ ≤ ‖lap x‖ / (2 * ε) := by
  have hden : (0 : ℝ) < ‖ψ x‖ ^ 2 + ε ^ 2 := by positivity
  rw [theta, norm_div, norm_neg, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hden]
  calc ‖lap x‖ * ‖ψ x‖ / (‖ψ x‖ ^ 2 + ε ^ 2)
      = ‖lap x‖ * (‖ψ x‖ / (‖ψ x‖ ^ 2 + ε ^ 2)) := by ring
    _ ≤ ‖lap x‖ * (1 / (2 * ε)) :=
        mul_le_mul_of_nonneg_left (ratio_le _ _ (norm_nonneg _) hε) (norm_nonneg _)
    _ = ‖lap x‖ / (2 * ε) := by ring

/-- **Part III Lemma `lem:h2bound`.** -/
theorem curvature_cost_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {ε : ℝ} (hε : 0 < ε) (ψ lap : X → ℂ) :
    curvatureCost μ ε ψ lap ≤
      ENNReal.ofReal (1 / (4 * ε ^ 2)) * ∫⁻ x, ENNReal.ofReal (‖lap x‖ ^ 2) ∂μ := by
  rw [curvatureCost, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h := theta_pointwise_le hε ψ lap x
  have h0 := norm_nonneg (theta ε ψ lap x)
  calc ‖theta ε ψ lap x‖ ^ 2 ≤ (‖lap x‖ / (2 * ε)) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 1 / (4 * ε ^ 2) * ‖lap x‖ ^ 2 := by field_simp; ring

/-- **Part III Theorem `thm:capacity` (corrected conditional capacity law).**
If a uniform family of fields obeys `∫|Δψ|² ≤ q²` then every member has
curvature cost at most `q² / (4ε²)`.  The second-derivative hypothesis is an
explicit premise, not derived from energy or locality. -/
theorem capacity_law {ι X : Type*} [MeasurableSpace X] (μ : Measure X)
    {ε : ℝ} (hε : 0 < ε) (ψ lap : ι → X → ℂ) (q : ℝ)
    (hq : ∀ i, ∫⁻ x, ENNReal.ofReal (‖lap i x‖ ^ 2) ∂μ ≤ ENNReal.ofReal (q ^ 2)) :
    ∀ i, curvatureCost μ ε (ψ i) (lap i) ≤ ENNReal.ofReal (q ^ 2 / (4 * ε ^ 2)) := by
  intro i
  calc curvatureCost μ ε (ψ i) (lap i)
      ≤ ENNReal.ofReal (1 / (4 * ε ^ 2)) * ∫⁻ x, ENNReal.ofReal (‖lap i x‖ ^ 2) ∂μ :=
        curvature_cost_le μ hε _ _
    _ ≤ ENNReal.ofReal (1 / (4 * ε ^ 2)) * ENNReal.ofReal (q ^ 2) := by gcongr; exact hq i
    _ = ENNReal.ofReal (q ^ 2 / (4 * ε ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-! ### Zero-cost counterexample with the genuine Laplacian -/

section ZeroCost

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open InnerProductSpace in
theorem laplacian_const (c : ℂ) : laplacian (fun _ : E => c) = 0 := by
  funext x
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_const_of_ne (by norm_num : (2 : ℕ) ≠ 0)]

open InnerProductSpace in
/-- **Part III Proposition `prop:zero_cost`.** The fields `ψ₀ ≡ 0` and
`ψ₁ ≡ 1` differ at every point, yet `Δ(ψ₁ - ψ₀) ≡ 0`, so the regularized
curvature separation cost vanishes for every measure and every `ε`. -/
theorem zero_cost_counterexample [MeasurableSpace E] (μ : Measure E) (ε : ℝ) :
    (∀ x : E, (fun _ : E => (1 : ℂ)) x - (fun _ : E => (0 : ℂ)) x ≠ 0) ∧
    laplacian (fun _ : E => (1 : ℂ) - 0) = 0 ∧
    curvatureCost μ ε (fun _ : E => (1 : ℂ) - 0) (laplacian (fun _ : E => (1 : ℂ) - 0)) = 0 := by
  refine ⟨fun _ => by norm_num, laplacian_const _, ?_⟩
  rw [laplacian_const]
  simp [curvatureCost, theta]

end ZeroCost

/-! ### High-frequency counterexample -/

/-- `ψ_N(x) = 1 + sin(Nx)/N`. -/
noncomputable def psiN (N : ℕ) (x : ℝ) : ℝ := 1 + Real.sin (N * x) / N

theorem psiN_hasDerivAt {N : ℕ} (hN : 0 < N) (x : ℝ) :
    HasDerivAt (psiN N) (Real.cos (N * x)) x := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := ((Real.hasDerivAt_sin (N * x)).comp x ((hasDerivAt_id x).const_mul (N : ℝ))).div_const N
  have h2 := h.const_add 1
  convert h2 using 1
  field_simp

theorem deriv_psiN {N : ℕ} (hN : 0 < N) : deriv (psiN N) = fun x => Real.cos (N * x) :=
  funext fun x => (psiN_hasDerivAt hN x).deriv

theorem deriv2_psiN {N : ℕ} (hN : 0 < N) :
    deriv (deriv (psiN N)) = fun x => -(N * Real.sin (N * x)) := by
  rw [deriv_psiN hN]
  funext x
  have h := (Real.hasDerivAt_cos (N * x)).comp x ((hasDerivAt_id x).const_mul (N : ℝ))
  rw [show (fun x => Real.cos (N * x)) = Real.cos ∘ HMul.hMul (N : ℝ) from rfl, h.deriv]
  ring

/-- Real regularized curvature density with `ε = 1`. -/
noncomputable def theta1 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(deriv (deriv f) x * f x) / (f x ^ 2 + 1)

theorem integral_sin_sq_mul {N : ℕ} (hN : 0 < N) :
    ∫ x in (0 : ℝ)..2 * π, Real.sin (N * x) ^ 2 = π := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hN', integral_sin_sq]
  have : Real.sin (N * (2 * π)) = 0 := by
    rw [show (N : ℝ) * (2 * π) = ((2 * N : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  simp only [mul_zero, Real.sin_zero, this, zero_mul, smul_eq_mul]
  field_simp
  ring

theorem integral_cos_sq_mul {N : ℕ} (hN : 0 < N) :
    ∫ x in (0 : ℝ)..2 * π, Real.cos (N * x) ^ 2 = π := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hN', integral_cos_sq]
  have : Real.sin (N * (2 * π)) = 0 := by
    rw [show (N : ℝ) * (2 * π) = ((2 * N : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  simp only [mul_zero, Real.sin_zero, this, mul_zero, smul_eq_mul]
  field_simp
  ring

/-- Gradient energy of `ψ_N` on one period is exactly `π`, for every `N ≥ 1`. -/
theorem highfreq_gradient_energy {N : ℕ} (hN : 0 < N) :
    ∫ x in (0 : ℝ)..2 * π, (deriv (psiN N) x) ^ 2 = π := by
  rw [deriv_psiN hN]; exact integral_cos_sq_mul hN

theorem psiN_bounds {N : ℕ} (hN : 2 ≤ N) (x : ℝ) : 1 / 2 ≤ psiN N x ∧ psiN N x ≤ 3 / 2 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := Real.abs_sin_le_one (N * x)
  have h : |Real.sin (N * x) / N| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N), div_le_iff₀ (by positivity)]
    nlinarith
  unfold psiN
  constructor <;> linarith [abs_le.1 h]

theorem ratio_ge {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 3 / 2) : 2 / 5 ≤ r / (r ^ 2 + 1) := by
  rw [le_div_iff₀ (by positivity)]; nlinarith

theorem theta1_psiN {N : ℕ} (hN : 0 < N) (x : ℝ) :
    theta1 (psiN N) x = N * Real.sin (N * x) * (psiN N x / (psiN N x ^ 2 + 1)) := by
  simp only [theta1, deriv2_psiN hN]; ring

theorem continuous_psiN (N : ℕ) : Continuous (psiN N) := by
  unfold psiN; fun_prop

/-- **Part III Proposition `prop:highfreq` (1D periodic form).** For `N ≥ 2`
the curvature cost of `ψ_N` is at least `(4/25) π N²`, while its gradient
energy is `π` (`highfreq_gradient_energy`) and `1/2 ≤ ψ_N ≤ 3/2`. -/
theorem highfreq_curvature_lower {N : ℕ} (hN : 2 ≤ N) :
    4 / 25 * π * (N : ℝ) ^ 2 ≤ ∫ x in (0 : ℝ)..2 * π, (theta1 (psiN N) x) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hcont : Continuous fun x => (theta1 (psiN N) x) ^ 2 := by
    have : (fun x => (theta1 (psiN N) x) ^ 2) = fun x =>
        (N * Real.sin (N * x) * (psiN N x / (psiN N x ^ 2 + 1))) ^ 2 :=
      funext fun x => by rw [theta1_psiN hN0]
    rw [this]
    have hp := continuous_psiN N
    refine Continuous.pow (Continuous.mul (by fun_prop) (Continuous.div hp (by fun_prop)
      (fun x => by positivity))) 2
  have hlow : ∀ x ∈ Set.Icc (0 : ℝ) (2 * π),
      4 / 25 * (N : ℝ) ^ 2 * Real.sin (N * x) ^ 2 ≤ (theta1 (psiN N) x) ^ 2 := by
    intro x _
    rw [theta1_psiN hN0]
    obtain ⟨b1, b2⟩ := psiN_bounds hN x
    have hr := ratio_ge b1 b2
    have hr0 : (0 : ℝ) ≤ 2 / 5 := by norm_num
    have hsq : (2 / 5 : ℝ) ^ 2 ≤ (psiN N x / (psiN N x ^ 2 + 1)) ^ 2 :=
      pow_le_pow_left₀ hr0 hr 2
    have hs : 0 ≤ ((N : ℝ) * Real.sin (N * x)) ^ 2 := sq_nonneg _
    calc 4 / 25 * (N : ℝ) ^ 2 * Real.sin (N * x) ^ 2
        = ((N : ℝ) * Real.sin (N * x)) ^ 2 * (2 / 5) ^ 2 := by ring
      _ ≤ ((N : ℝ) * Real.sin (N * x)) ^ 2 * (psiN N x / (psiN N x ^ 2 + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hs
      _ = (N * Real.sin (N * x) * (psiN N x / (psiN N x ^ 2 + 1))) ^ 2 := by ring
  have hval : ∫ x in (0 : ℝ)..2 * π, 4 / 25 * (N : ℝ) ^ 2 * Real.sin (N * x) ^ 2 =
      4 / 25 * (N : ℝ) ^ 2 * π := by
    rw [intervalIntegral.integral_const_mul, integral_sin_sq_mul hN0]
  have hc2 : Continuous fun x : ℝ => 4 / 25 * (N : ℝ) ^ 2 * Real.sin (N * x) ^ 2 := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by positivity)
    (hc2.intervalIntegrable _ _) (hcont.intervalIntegrable _ _) hlow
  rw [hval] at hmono
  linarith [show 4 / 25 * π * (N : ℝ) ^ 2 = 4 / 25 * (N : ℝ) ^ 2 * π by ring]

/-- The curvature functional is unbounded along a family of fixed gradient
energy: no bound `C ≤ F(gradient energy)` holds. -/
theorem no_gradient_energy_control :
    ¬ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N → ∫ x in (0 : ℝ)..2 * π, (theta1 (psiN N) x) ^ 2 ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max B 3)
  have hN3 : (3 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) < N := by linarith
    exact_mod_cast this.le
  have h1 := highfreq_curvature_lower hN2
  have h2 := hB N hN2
  have hNB : B < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hA : 12 / 25 * (N : ℝ) ^ 2 ≤ 4 / 25 * π * (N : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hC : (N : ℝ) ≤ 12 / 25 * (N : ℝ) ^ 2 := by nlinarith
  linarith

end PVNP.PartIIIAnalytic
