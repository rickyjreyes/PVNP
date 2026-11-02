import Mathlib

/-!
# Spectral gap on a circle of length `L`: sharp Wirtinger inequality and its collapse (issue #10)

A genuine function-space inequality (no algebraic stand-in) on the circle
`AddCircle L` with Mathlib's normalized Haar probability measure
(`∫ · ∂haarAddCircle = (1/L) ∫₀ᴸ · dx`).

* `fourierCoeff_of_deriv`: for a continuous periodic field `f` with
  continuous derivative `g` along the circle, `f̂(n) = L/(2πin) · ĝ(n)`
  for `n ≠ 0`.
* `hasSum_sq_fourierCoeff_cont`: Parseval as a `HasSum` for continuous fields.
* `wirtinger`: `(2π/L)² (∫‖f‖² − ‖f̂(0)‖²) ≤ ∫‖g‖²`, i.e. the mean-square
  gradient energy controls the variance about the mean `f̂(0)` with the
  spectral-gap constant `(2π/L)²`.
* `wirtinger_sharp`: equality for `f = e^{2πix/L}`, so `(2π/L)²` is optimal.
* `no_uniform_poincare`: for every `c > 0` there is a circle length `L` and a
  smooth field violating `∫‖g‖² ≥ c (∫‖f‖² − ‖f̂(0)‖²)`.

Interpretation for the resource program (O5/O6): on input-size-dependent
domains `L_n → ∞`, no `n`-uniform positive constant converts distinguishable
contrast (variance) into a gradient/curvature-energy cost.  This is the
analytic mechanism behind the expanding-domain countermodel
(`PVNP.ExpandingDomain.no_positive_uniform_density_ratio`), now proved for
genuine functions rather than for a scalar model.
-/

open MeasureTheory AddCircle Complex Real

namespace PVNP.SpectralGap

variable {L : ℝ} [hL : Fact (0 < L)]

/-- The lift of the pull-back of a circle function is the function itself. -/
theorem liftIoc_pullback (f : AddCircle L → ℂ) :
    AddCircle.liftIoc L 0 (fun x : ℝ => f x) = f := by
  funext t
  simp only [AddCircle.liftIoc, Function.comp_apply, Set.restrict_apply]
  conv_rhs => rw [← (AddCircle.equivIoc L 0).symm_apply_apply t]
  rfl

/-- **Fourier coefficients of a derivative on the circle.** -/
theorem fourierCoeff_of_deriv (f g : C(AddCircle L, ℂ))
    (hfg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f y) (g x) x) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeff (⇑f) n = (L / (2 * π * I * n)) * fourierCoeff (⇑g) n := by
  have hab : (0 : ℝ) < 0 + L := by simpa using hL.out
  have h1 : fourierCoeff (⇑f) n = fourierCoeffOn hab (fun x : ℝ => f x) n := by
    have := fourierCoeff_liftIoc_eq (T := L) (a := 0) (fun x : ℝ => f x) n
    rw [liftIoc_pullback] at this; exact this
  have h2 : fourierCoeff (⇑g) n = fourierCoeffOn hab (fun x : ℝ => g x) n := by
    have := fourierCoeff_liftIoc_eq (T := L) (a := 0) (fun x : ℝ => g x) n
    rw [liftIoc_pullback] at this; exact this
  have hcont : Continuous fun x : ℝ => g x := g.continuous.comp continuous_quotient_mk'
  rw [h1, h2, fourierCoeffOn_of_hasDerivAt hab hn (fun x _ => hfg x)
    (hcont.intervalIntegrable _ _)]
  have hper : f ((0 + L : ℝ) : AddCircle L) = f ((0 : ℝ) : AddCircle L) := by
    rw [zero_add, AddCircle.coe_period, QuotientAddGroup.mk_zero]
  rw [hper, sub_self, mul_zero, zero_sub]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- Coefficientwise gap: `(2π/L)² ‖f̂(n)‖² ≤ ‖ĝ(n)‖²` for `n ≠ 0`. -/
theorem coeff_gap (f g : C(AddCircle L, ℂ))
    (hfg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f y) (g x) x) {n : ℤ} (hn : n ≠ 0) :
    (2 * π / L) ^ 2 * ‖fourierCoeff (⇑f) n‖ ^ 2 ≤ ‖fourierCoeff (⇑g) n‖ ^ 2 := by
  have hL0 := hL.out
  have hrel := fourierCoeff_of_deriv f g hfg hn
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have hnorm : ‖fourierCoeff (⇑f) n‖ * (2 * π * |(n : ℝ)|) = L * ‖fourierCoeff (⇑g) n‖ := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have key : (2 * π * I * n) * fourierCoeff (⇑f) n = L * fourierCoeff (⇑g) n := by
      rw [hrel]; field_simp
    have := congrArg norm key
    rw [norm_mul (2 * (π : ℂ) * I * n) (fourierCoeff (⇑f) n),
      norm_mul (L : ℂ) (fourierCoeff (⇑g) n)] at this
    have h2 : ‖(2 * π * I * n : ℂ)‖ = 2 * π * |(n : ℝ)| := by
      simp [norm_mul, Complex.norm_I, abs_of_pos Real.pi_pos]
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0] at this
    linarith
  have hfn := norm_nonneg (fourierCoeff (⇑f) n)
  have hle : (2 * π / L) * ‖fourierCoeff (⇑f) n‖ ≤ ‖fourierCoeff (⇑g) n‖ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL0]
    have : 2 * π * ‖fourierCoeff (⇑f) n‖ ≤ ‖fourierCoeff (⇑f) n‖ * (2 * π * |(n : ℝ)|) := by
      have := mul_le_mul_of_nonneg_left hn1 (by positivity : 0 ≤ 2 * π * ‖fourierCoeff (⇑f) n‖)
      nlinarith
    linarith
  have h0 : 0 ≤ (2 * π / L) * ‖fourierCoeff (⇑f) n‖ := by positivity
  calc (2 * π / L) ^ 2 * ‖fourierCoeff (⇑f) n‖ ^ 2
      = ((2 * π / L) * ‖fourierCoeff (⇑f) n‖) ^ 2 := by ring
    _ ≤ ‖fourierCoeff (⇑g) n‖ ^ 2 := pow_le_pow_left₀ h0 hle 2

/-- **Parseval for continuous fields**, as a `HasSum`. -/
theorem hasSum_sq_fourierCoeff_cont (f : C(AddCircle L, ℂ)) :
    HasSum (fun n => ‖fourierCoeff (⇑f) n‖ ^ 2) (∫ t, ‖f t‖ ^ 2 ∂haarAddCircle) := by
  set F := ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ f
  have hcoeff : ∀ n, fourierCoeff (⇑F) n = fourierCoeff (⇑f) n := fourierCoeff_toLp f
  have hs : Summable (fun n => ‖fourierCoeff (⇑f) n‖ ^ 2) := by
    have hm := lp.memℓp (fourierBasis.repr F)
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)] at hm
    refine hm.congr fun n => ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [fourierBasis_repr, hcoeff]
  have ht := tsum_sq_fourierCoeff F
  simp only [hcoeff] at ht
  have hint : ∫ t, ‖F t‖ ^ 2 ∂haarAddCircle = ∫ t, ‖f t‖ ^ 2 ∂haarAddCircle :=
    integral_congr_ae ((ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) haarAddCircle f).mono
      fun t ht => by simp only [F]; rw [ht])
  rw [← hint, ← ht]
  exact hs.hasSum

/-- **Sharp Wirtinger / spectral-gap inequality on the circle of length `L`.** -/
theorem wirtinger (f g : C(AddCircle L, ℂ))
    (hfg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f y) (g x) x) :
    (2 * π / L) ^ 2 * (∫ t, ‖f t‖ ^ 2 ∂haarAddCircle - ‖fourierCoeff (⇑f) 0‖ ^ 2) ≤
      ∫ t, ‖g t‖ ^ 2 ∂haarAddCircle := by
  have hf := hasSum_sq_fourierCoeff_cont f
  have hg := hasSum_sq_fourierCoeff_cont g
  set F : ℤ → ℝ := fun n => ‖fourierCoeff (⇑f) n‖ ^ 2
  have hb := (hf.update 0 0).mul_left ((2 * π / L) ^ 2)
  have hle : ∀ n, (2 * π / L) ^ 2 * Function.update F 0 0 n ≤ ‖fourierCoeff (⇑g) n‖ ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · rw [Function.update_of_ne hn]; exact coeff_gap f g hfg hn
  have := hasSum_le hle hb hg
  linarith

/-- The fundamental mode `e^{2πix/L}` attains equality. -/
theorem wirtinger_sharp :
    (∀ x : ℝ, HasDerivAt (fun y : ℝ => (fourier 1 : C(AddCircle L, ℂ)) y)
        (((2 * π * I * ((1 : ℤ) : ℂ) / L) • (fourier 1 : C(AddCircle L, ℂ))) x) x) ∧
    ∫ t, ‖(fourier 1 : C(AddCircle L, ℂ)) t‖ ^ 2 ∂haarAddCircle = 1 ∧
    fourierCoeff (⇑(fourier 1 : C(AddCircle L, ℂ))) 0 = 0 ∧
    ∫ t, ‖((2 * π * I * ((1 : ℤ) : ℂ) / L) • (fourier 1 : C(AddCircle L, ℂ))) t‖ ^ 2
        ∂haarAddCircle = (2 * π / L) ^ 2 := by
  have hL0 := hL.out
  have hnorm1 : ∀ t : AddCircle L, ‖(fourier 1 : C(AddCircle L, ℂ)) t‖ = 1 := by
    intro t
    have h : (fourier (-1) t * fourier 1 t : ℂ) = 1 := by
      rw [← fourier_add]; simp [fourier_zero]
    rw [fourier_neg, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    have h' : ‖(fourier 1 : C(AddCircle L, ℂ)) t‖ ^ 2 = 1 := by exact_mod_cast h
    have hn := norm_nonneg ((fourier 1 : C(AddCircle L, ℂ)) t)
    nlinarith [sq_nonneg (‖(fourier 1 : C(AddCircle L, ℂ)) t‖ - 1)]
  have hint1 : ∫ t, ‖(fourier 1 : C(AddCircle L, ℂ)) t‖ ^ 2 ∂haarAddCircle = 1 := by
    simp only [hnorm1, one_pow, integral_const, smul_eq_mul, mul_one]
    exact measureReal_univ_eq_one
  refine ⟨fun x => ?_, hint1, ?_, ?_⟩
  · have := hasDerivAt_fourier L 1 x
    simpa [ContinuousMap.smul_apply, smul_eq_mul] using this
  · rw [fourierCoeff]
    simp only [neg_zero, fourier_zero, one_smul]
    exact integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
      (fourier_add_half_inv_index one_ne_zero hL0)
  · have hc : ‖(2 * π * I * ((1 : ℤ) : ℂ) / L : ℂ)‖ = 2 * π / L := by
      simp [norm_mul, Complex.norm_I, abs_of_pos Real.pi_pos, abs_of_pos hL0]
    simp only [ContinuousMap.smul_apply, smul_eq_mul, norm_mul, hc, hnorm1, mul_one]
    simp only [integral_const, smul_eq_mul]
    rw [measureReal_univ_eq_one, one_mul]

/-- **No domain-uniform Poincaré constant.** For every `c > 0` there is a
circle length `L` and a smooth field whose gradient energy is below
`c × variance`. -/
theorem no_uniform_poincare (c : ℝ) (hc : 0 < c) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      letI : Fact (0 < L) := ⟨hL⟩
      ∃ f g : C(AddCircle L, ℂ), (∀ x : ℝ, HasDerivAt (fun y : ℝ => f y) (g x) x) ∧
        ∫ t, ‖g t‖ ^ 2 ∂haarAddCircle <
          c * (∫ t, ‖f t‖ ^ 2 ∂haarAddCircle - ‖fourierCoeff (⇑f) 0‖ ^ 2) := by
  obtain ⟨L, hL1, hLc⟩ : ∃ L : ℝ, 1 ≤ L ∧ (2 * π / L) ^ 2 < c := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((2 * π) ^ 2 / c)
    refine ⟨N + 1, by linarith [N.cast_nonneg (α := ℝ)], ?_⟩
    have hN1 : (0 : ℝ) < N + 1 := by positivity
    rw [div_pow, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at hN
    have : (N : ℝ) ≤ (N + 1) ^ 2 := by nlinarith
    nlinarith
  have hL0 : 0 < L := by linarith
  letI : Fact (0 < L) := ⟨hL0⟩
  obtain ⟨hd, h1, h0, hg⟩ := wirtinger_sharp (L := L)
  refine ⟨L, hL0, _, _, hd, ?_⟩
  rw [hg, h1, h0, norm_zero]
  simpa using hLc

end PVNP.SpectralGap
