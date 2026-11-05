import Mathlib

/-!
# Part I, Proposition WIN-04 (`lem:dim-lock`): a finite-energy smooth field on `ℝ⁴`

**Manuscript statement.** For `d = 4` there exist nonzero smooth localized fields with finite
`‖∇ψ‖²_{L²}` and finite corrected regularized curvature energy `‖Θ_ε[ψ]‖²_{L²}`, where
`Θ_ε[ψ] = −Δψ ψ̄ / (|ψ|² + ε e^{−α|ψ|²})`, `ε > 0`, `α ≥ 0`. Consequently the failure of
`H¹ ↪ L^∞` for `d > 3` does not prove that every higher-dimensional configuration has infinite
WCT curvature energy.

**Formalization.** `ψ(x) = e^{−‖x‖²}` on `EuclideanSpace ℝ (Fin 4)`, with Mathlib's genuine
Laplacian `InnerProductSpace.laplacian`.
* `laplacian_ψ`: `Δψ = (4‖x‖² − 8) e^{−‖x‖²}`, as in the manuscript's proof.
* `win04_gaussian`: `ψ` is smooth, nonzero and integrable (localized), and both `‖∇ψ‖²` and
  `Θ_ε[ψ]²` are integrable.
-/

namespace PVNP.PartIDimLock

open MeasureTheory InnerProductSpace

/-- `ℝ⁴`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The field `ψ(x) = e^{−‖x‖²}`. -/
noncomputable def ψ (x : E4) : ℝ := Real.exp (-‖x‖ ^ 2)

/-- The corrected regularized curvature `Θ_ε[f] = −Δf f̄ / (|f|² + ε e^{−α|f|²})` (real field). -/
noncomputable def Θε (ε α : ℝ) (f : E4 → ℝ) (x : E4) : ℝ :=
  -(laplacian f x * f x) / (f x ^ 2 + ε * Real.exp (-α * f x ^ 2))

theorem contDiff_ψ : ContDiff ℝ ⊤ ψ :=
  ((contDiff_norm_sq ℝ).neg).exp

theorem hasFDerivAt_ψ (x : E4) :
    HasFDerivAt ψ ((-2 * Real.exp (-‖x‖ ^ 2)) • innerSL ℝ x) x := by
  have h1 : HasFDerivAt (fun y : E4 => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using (hasFDerivAt_id x).norm_sq
  have h2 := h1.neg.exp
  convert h2 using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply, ContinuousLinearMap.neg_apply,
    smul_eq_mul, nsmul_eq_mul, Pi.neg_apply]
  ring

theorem fderiv_ψ_apply (y v : E4) :
    fderiv ℝ ψ y v = -2 * Real.exp (-‖y‖ ^ 2) * inner ℝ y v := by
  rw [(hasFDerivAt_ψ y).fderiv]
  simp [mul_assoc]

/-- The second directional derivative `∂_v ∂_w ψ(x)`. -/
theorem fderiv_fderiv_ψ (x v w : E4) :
    fderiv ℝ (fderiv ℝ ψ) x v w =
      4 * Real.exp (-‖x‖ ^ 2) * inner ℝ x v * inner ℝ x w - 2 * Real.exp (-‖x‖ ^ 2) * inner ℝ v w := by
  have hdiff : Differentiable ℝ (fderiv ℝ ψ) :=
    (contDiff_ψ.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hcurve : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hA : HasDerivAt (fun s : ℝ => fderiv ℝ ψ (x + s • v) w) (fderiv ℝ (fderiv ℝ ψ) x v w) 0 := by
    have h1 := (hdiff x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp)
    exact h1.clm_apply (hasDerivAt_const 0 w) |>.congr_deriv (by simp)
  -- explicit derivative of `s ↦ −2 e^{−‖x+sv‖²} ⟪x+sv, w⟫`
  have hn : HasDerivAt (fun s : ℝ => ‖x + s • v‖ ^ 2) (2 * inner ℝ x v) 0 := by
    simpa using hcurve.norm_sq
  have he : HasDerivAt (fun s : ℝ => Real.exp (-‖x + s • v‖ ^ 2))
      (Real.exp (-‖x‖ ^ 2) * -(2 * inner ℝ x v)) 0 := by
    simpa using hn.neg.exp
  have hi : HasDerivAt (fun s : ℝ => inner ℝ (x + s • v) w) (inner ℝ v w) 0 := by
    have : (fun s : ℝ => inner ℝ (x + s • v) w) = fun s => inner ℝ x w + s * inner ℝ v w := by
      funext s; rw [inner_add_left, real_inner_smul_left]
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ v w)).const_add (inner ℝ x w)
  have hB : HasDerivAt (fun s : ℝ => fderiv ℝ ψ (x + s • v) w)
      (-2 * (Real.exp (-‖x‖ ^ 2) * -(2 * inner ℝ x v) * inner ℝ x w +
        Real.exp (-‖x‖ ^ 2) * inner ℝ v w)) 0 := by
    have hfun : (fun s : ℝ => fderiv ℝ ψ (x + s • v) w) =
        fun s => -2 * (Real.exp (-‖x + s • v‖ ^ 2) * inner ℝ (x + s • v) w) := by
      funext s; rw [fderiv_ψ_apply]; ring
    rw [hfun]
    have := (he.mul hi).const_mul (-2 : ℝ)
    simpa using this
  rw [hA.unique hB]
  ring

theorem laplacian_ψ (x : E4) : laplacian ψ x = (4 * ‖x‖ ^ 2 - 8) * Real.exp (-‖x‖ ^ 2) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_fderiv_ψ]
  set b := stdOrthonormalBasis ℝ E4
  have hsum : ∑ i, inner ℝ x (b i) * inner ℝ x (b i) = ‖x‖ ^ 2 := by
    have := b.sum_inner_mul_inner x x
    rw [real_inner_self_eq_norm_sq] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (b i) x]
  have hone : ∀ i, inner ℝ (b i) (b i) = (1 : ℝ) := by
    intro i
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow]
  have hcard : (Finset.univ : Finset (Fin (Module.finrank ℝ E4))).card = 4 := by
    simp
  simp only [hone, mul_one, Finset.sum_sub_distrib]
  rw [show ∑ i, 4 * Real.exp (-‖x‖ ^ 2) * inner ℝ x (b i) * inner ℝ x (b i) =
      4 * Real.exp (-‖x‖ ^ 2) * ∑ i, inner ℝ x (b i) * inner ℝ x (b i) by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring, hsum,
    Finset.sum_const, hcard]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-! ### Integrability -/

theorem integrable_ψ : Integrable ψ := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace (ι := Fin 4) (b := 1)
    (by simp) 0 0
  have h' := h.norm
  refine h'.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [Complex.norm_exp, ψ]
  congr 1
  simp only [zero_mul, add_zero, neg_mul, one_mul, Complex.neg_re]
  norm_cast

theorem exp_neg_mul_le (s : ℝ) (hs : 0 ≤ s) : s * Real.exp (-s) ≤ 1 := by
  have h1 : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
  have h2 : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-s)]

theorem sq_exp_neg_le (s : ℝ) (hs : 0 ≤ s) : s ^ 2 * Real.exp (-s) ≤ 2 := by
  have h1 : 1 + s + s ^ 2 / 2 ≤ Real.exp s := Real.quadratic_le_exp_of_nonneg hs
  have h2 : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-s), sq_nonneg s]

theorem norm_fderiv_ψ (x : E4) : ‖fderiv ℝ ψ x‖ = 2 * Real.exp (-‖x‖ ^ 2) * ‖x‖ := by
  rw [(hasFDerivAt_ψ x).fderiv, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  rw [abs_of_nonpos (by nlinarith [Real.exp_pos (-‖x‖ ^ 2)])]
  ring

theorem ψ_pos (x : E4) : 0 < ψ x := Real.exp_pos _

theorem ψ_le_one (x : E4) : ψ x ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg x])

/-- **Part I, Proposition WIN-04 (`lem:dim-lock`).**  The Gaussian on `ℝ⁴` is a smooth,
nonzero, localized (integrable) field with finite `‖∇ψ‖²_{L²}` and finite corrected regularized
curvature energy `‖Θ_ε[ψ]‖²_{L²}`, for every `ε > 0`, `α ≥ 0`. -/
theorem win04_gaussian (ε α : ℝ) (hε : 0 < ε) (hα : 0 ≤ α) :
    ContDiff ℝ ⊤ ψ ∧ ψ 0 ≠ 0 ∧ Integrable ψ ∧
      (∀ x, laplacian ψ x = (4 * ‖x‖ ^ 2 - 8) * Real.exp (-‖x‖ ^ 2)) ∧
      Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2) ∧
      Integrable (fun x => Θε ε α ψ x ^ 2) := by
  refine ⟨contDiff_ψ, (ψ_pos 0).ne', integrable_ψ, laplacian_ψ, ?_, ?_⟩
  · -- `‖∇ψ‖² = 4‖x‖² e^{−2‖x‖²} ≤ 4 e^{−‖x‖²}`
    refine (integrable_ψ.const_mul 4).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((contDiff_ψ.continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable
    · rw [norm_fderiv_ψ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := exp_neg_mul_le (‖x‖ ^ 2) (by positivity)
      have h2 : 0 < Real.exp (-‖x‖ ^ 2) := Real.exp_pos _
      unfold ψ
      nlinarith
  · -- `Θ_ε² ≤ (96 e^{2α}/ε²) e^{−‖x‖²}`
    have hcont : Continuous fun x => Θε ε α ψ x ^ 2 := by
      have hlap : laplacian ψ = fun x => (4 * ‖x‖ ^ 2 - 8) * Real.exp (-‖x‖ ^ 2) :=
        funext laplacian_ψ
      unfold Θε
      rw [hlap]
      have hψc : Continuous ψ := contDiff_ψ.continuous
      refine (Continuous.div ?_ ?_ fun x => ?_).pow 2
      · exact (((continuous_const.mul (continuous_norm.pow 2)).sub continuous_const).mul
          ((continuous_norm.pow 2).neg.rexp)).mul hψc |>.neg
      · exact (hψc.pow 2).add (continuous_const.mul ((continuous_const.mul (hψc.pow 2)).rexp))
      · have := ψ_pos x
        positivity
    refine (integrable_ψ.const_mul (96 * Real.exp (2 * α) / ε ^ 2)).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    set s := ‖x‖ ^ 2 with hs
    have hs0 : 0 ≤ s := by positivity
    have hψ : ψ x = Real.exp (-s) := rfl
    have hp := ψ_pos x
    have hle := ψ_le_one x
    have hψ2 : ψ x ^ 2 ≤ 1 := by nlinarith
    have hden : ε * Real.exp (-α) ≤ ψ x ^ 2 + ε * Real.exp (-α * ψ x ^ 2) := by
      have : Real.exp (-α) ≤ Real.exp (-α * ψ x ^ 2) :=
        Real.exp_le_exp.2 (by nlinarith [mul_nonneg hα (sub_nonneg.2 hψ2)])
      nlinarith [sq_nonneg (ψ x), mul_le_mul_of_nonneg_left this hε.le]
    have hdenpos : 0 < ε * Real.exp (-α) := by positivity
    have hdpos : 0 < ψ x ^ 2 + ε * Real.exp (-α * ψ x ^ 2) := lt_of_lt_of_le hdenpos hden
    have hΘ : |Θε ε α ψ x| ≤ |laplacian ψ x| / (ε * Real.exp (-α)) := by
      unfold Θε
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hp, abs_of_pos hdpos]
      calc |laplacian ψ x| * ψ x / (ψ x ^ 2 + ε * Real.exp (-α * ψ x ^ 2))
          ≤ |laplacian ψ x| * 1 / (ε * Real.exp (-α)) := by
            apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hle (abs_nonneg _))
              hdenpos hden
        _ = |laplacian ψ x| / (ε * Real.exp (-α)) := by ring
    have hlap2 : laplacian ψ x ^ 2 ≤ 96 * Real.exp (-s) := by
      rw [laplacian_ψ, ← hs, mul_pow]
      have e2 : Real.exp (-s) ^ 2 = Real.exp (-s) * Real.exp (-s) := by ring
      have h1 := sq_exp_neg_le s hs0
      have h2 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have h3 : 0 < Real.exp (-s) := Real.exp_pos _
      have h4 : (4 * s - 8) ^ 2 ≤ 16 * s ^ 2 + 64 := by nlinarith
      rw [e2]
      nlinarith
    have hsqΘ : Θε ε α ψ x ^ 2 ≤ laplacian ψ x ^ 2 / (ε * Real.exp (-α)) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hΘ 2
      rwa [sq_abs, div_pow, sq_abs] at this
    calc Θε ε α ψ x ^ 2 ≤ laplacian ψ x ^ 2 / (ε * Real.exp (-α)) ^ 2 := hsqΘ
      _ ≤ 96 * Real.exp (-s) / (ε * Real.exp (-α)) ^ 2 :=
          div_le_div_of_nonneg_right hlap2 (by positivity)
      _ = 96 * Real.exp (2 * α) / ε ^ 2 * ψ x := by
          have h7 : Real.exp (2 * α) * Real.exp (-α) ^ 2 = 1 := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
          have h8 : Real.exp (2 * α) = 1 / Real.exp (-α) ^ 2 := by
            rw [eq_div_iff (by positivity), h7]
          rw [hψ, h8, mul_pow]
          ring

end PVNP.PartIDimLock
