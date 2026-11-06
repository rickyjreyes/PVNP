import PVNP.TorusWellPosed

/-!
# Multiplication by a detector weight on `L²(T_L²)` coefficients (F-1 groundwork)

For an absolutely summable coefficient sequence `c` (a continuous weight `χ = field L c`),
`Mc L c y` is the coefficient sequence of `χ·Y`, where `Y` has `L²` coefficients `y ∈ ℓ²`
(Young's inequality, `norm_Mc_le`).

* `norm_Mc2_le_sup`: if `|χ₁(x)|² + |χ₂(x)|² ≤ a²` everywhere, then
  `‖χ₁Y₁ + χ₂Y₂‖_{L²} ≤ a (‖Y₁‖²_{L²} + ‖Y₂‖²_{L²})^{1/2}` for all `Y₁, Y₂ ∈ L²`.  This is
  the *sup-norm* bound (not the cruder Wiener-norm bound): it is proved for finitely supported
  coefficients from the pointwise inequality and extended by density (`trunc`).
* `im_inner_Mc_self`: `⟨χY, Y⟩_{L²}` is real when `χ` is real-valued (`rev c = c`).
-/

open Complex Set Filter Topology InnerProductSpace MeasureTheory
open scoped Real ENNReal NNReal

namespace PVNP.Torus

variable {L : ℝ}

/-! ### The convolution operator -/

theorem summable_conv_l2 {c : Z2 → ℂ} (hc : L1 c) (y : ℓ2) (k : Z2) :
    Summable fun j => c j * y (k - j) :=
  Summable.of_norm ((hc.mul_right ‖y‖).of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) y _) (norm_nonneg _)))

theorem Mc_summable {c : Z2 → ℂ} (hc : L1 c) (y : ℓ2) :
    Summable fun k => ‖(L : ℂ)⁻¹ * ∑' j, c j * y (k - j)‖ ^ 2 := by
  have h := (young y hc).1
  have e : ∀ k, ‖(L : ℂ)⁻¹ * ∑' j, c j * y (k - j)‖ ^ 2 =
      |L|⁻¹ ^ 2 * ‖∑' j, c j * y (k - j)‖ ^ 2 := fun k => by
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [e]
  exact h.mul_left _

open Classical in
/-- The coefficients of `χ·Y` for `χ = field L c`, `c ∈ ℓ¹`, and `Y` with coefficients `y ∈ ℓ²`. -/
noncomputable def Mc (L : ℝ) (c : Z2 → ℂ) (y : ℓ2) : ℓ2 :=
  if hc : L1 c then mk (fun k => (L : ℂ)⁻¹ * ∑' j, c j * y (k - j)) (Mc_summable hc y) else 0

theorem Mc_apply {c : Z2 → ℂ} (hc : L1 c) (y : ℓ2) (k : Z2) :
    Mc L c y k = (L : ℂ)⁻¹ * ∑' j, c j * y (k - j) := by
  rw [Mc, dif_pos hc]; rfl

/-- On absolutely summable coefficients, `Mc` is the product coefficient sequence `pr`. -/
theorem Mc_apply_pr {c : Z2 → ℂ} (hc : L1 c) (y : ℓ2) (k : Z2) :
    Mc L c y k = pr L c y k := by
  rw [Mc_apply hc, pr]
  congr 1
  rw [← (Equiv.subLeft k).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

theorem norm_Mc_le {c : Z2 → ℂ} (hc : L1 c) (y : ℓ2) :
    ‖Mc L c y‖ ≤ |L|⁻¹ * (∑' j, ‖c j‖) * ‖y‖ := by
  refine norm_le_of_tsum_sq_le _ (by positivity) ?_
  have h := (young y hc).2
  calc ∑' k, ‖Mc L c y k‖ ^ 2 = |L|⁻¹ ^ 2 * ∑' k, ‖∑' j, c j * y (k - j)‖ ^ 2 := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        rw [Mc_apply hc, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |L|⁻¹ ^ 2 * (‖y‖ * ∑' j, ‖c j‖) ^ 2 := mul_le_mul_of_nonneg_left h (by positivity)
    _ = (|L|⁻¹ * (∑' j, ‖c j‖) * ‖y‖) ^ 2 := by ring

theorem Mc_add {c : Z2 → ℂ} (hc : L1 c) (y y' : ℓ2) : Mc L c (y + y') = Mc L c y + Mc L c y' := by
  ext k
  rw [lp.coeFn_add, Pi.add_apply, Mc_apply hc, Mc_apply hc, Mc_apply hc, ← mul_add,
    ← (summable_conv_l2 hc y k).tsum_add (summable_conv_l2 hc y' k)]
  congr 1
  refine tsum_congr fun j => ?_
  rw [lp.coeFn_add, Pi.add_apply, mul_add]

theorem Mc_smul {c : Z2 → ℂ} (hc : L1 c) (a : ℂ) (y : ℓ2) : Mc L c (a • y) = a • Mc L c y := by
  ext k
  rw [lp.coeFn_smul, Pi.smul_apply, Mc_apply hc, Mc_apply hc, smul_eq_mul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [show (fun j => c j * (a * y (k - j))) = fun j => a * (c j * y (k - j)) by
    funext j; ring, tsum_mul_left]
  ring

/-- `Mc` as a continuous linear map. -/
noncomputable def McL (L : ℝ) {c : Z2 → ℂ} (hc : L1 c) : ℓ2 →L[ℂ] ℓ2 :=
  LinearMap.mkContinuous
    { toFun := Mc L c
      map_add' := Mc_add hc
      map_smul' := fun a y => Mc_smul hc a y }
    (|L|⁻¹ * ∑' j, ‖c j‖) (fun y => norm_Mc_le hc y)

theorem McL_apply {c : Z2 → ℂ} (hc : L1 c) (y : ℓ2) : McL L hc y = Mc L c y := rfl

/-! ### Truncations: finitely supported coefficients are dense -/

/-- The truncation `Σ_{i ∈ F} y_i δ_i`. -/
noncomputable def trunc (F : Finset Z2) (y : ℓ2) : ℓ2 := ∑ i ∈ F, lp.single 2 i (y i)

theorem trunc_apply (F : Finset Z2) (y : ℓ2) (k : Z2) :
    trunc F y k = if k ∈ F then y k else 0 := by
  rw [trunc, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single]
  split_ifs with hk
  · rw [Finset.sum_eq_single k (fun i _ hik => Pi.single_eq_of_ne' hik _) (fun h => (h hk).elim)]
    exact Pi.single_eq_same _ _
  · exact Finset.sum_eq_zero fun i hi => Pi.single_eq_of_ne (by rintro rfl; exact hk hi) _

theorem L1_trunc (F : Finset Z2) (y : ℓ2) : L1 (trunc F y) := by
  refine summable_of_ne_finset_zero (s := F) fun k hk => ?_
  rw [trunc_apply, if_neg hk, norm_zero]

theorem tendsto_trunc (y : ℓ2) : Tendsto (fun F => trunc F y) atTop (𝓝 y) :=
  (lp.hasSum_single (p := 2) (by norm_num) y)

/-! ### Sup-norm bounds -/

theorem integrable_sq_field {a : Z2 → ℂ} (ha : L1 a) :
    Integrable (fun x => ‖field L a x‖ ^ 2) (box L) := by
  refine integrable_of_cont_bdd (by have := continuous_field (L := L) ha; fun_prop)
    (C := (|L|⁻¹ * ∑' k, ‖a k‖) ^ 2) (fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_field_le ha x) 2

theorem field_Mc {c : Z2 → ℂ} (hc : L1 c) (y : ℓ2) (hy : L1 y) (x : ℝ × ℝ) :
    field L (Mc L c y) x = field L c x * field L y x := by
  rw [field_mul hc hy]
  congr 1
  funext k
  exact Mc_apply_pr hc y k

theorem L1_Mc {c : Z2 → ℂ} (hc : L1 c) (y : ℓ2) (hy : L1 y) : L1 (Mc L c y) := by
  have h := L1_pr (L := L) hc hy
  unfold L1 at h ⊢
  simpa only [Mc_apply_pr hc] using h

/-- The two-component sup-norm bound on finitely supported (absolutely summable)
coefficients. -/
theorem norm_Mc2_le_sup_l1 (hL : 0 < L) {c₁ c₂ : Z2 → ℂ} (hc₁ : L1 c₁) (hc₂ : L1 c₂) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : ∀ x, ‖field L c₁ x‖ ^ 2 + ‖field L c₂ x‖ ^ 2 ≤ a ^ 2) {y₁ y₂ : ℓ2}
    (hy₁ : L1 y₁) (hy₂ : L1 y₂) :
    ‖Mc L c₁ y₁ + Mc L c₂ y₂‖ ≤ a * Real.sqrt (‖y₁‖ ^ 2 + ‖y₂‖ ^ 2) := by
  have hm₁ := L1_Mc (L := L) hc₁ y₁ hy₁
  have hm₂ := L1_Mc (L := L) hc₂ y₂ hy₂
  have hsum : L1 (Mc L c₁ y₁ + Mc L c₂ y₂) := by
    have := L1_add hm₁ hm₂
    simpa only [lp.coeFn_add] using this
  have h1 : ‖Mc L c₁ y₁ + Mc L c₂ y₂‖ ^ 2 =
      ∫ x, ‖field L c₁ x * field L y₁ x + field L c₂ x * field L y₂ x‖ ^ 2 ∂box L := by
    have e : ∑' k, ‖(Mc L c₁ y₁ + Mc L c₂ y₂) k‖ ^ 2 =
        ∑' k, ‖(⇑(Mc L c₁ y₁) + ⇑(Mc L c₂ y₂)) k‖ ^ 2 := by simp only [lp.coeFn_add]
    rw [norm_sq_eq, e, ← integral_norm_sq hL hsum]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [field_add hm₁ hm₂, field_Mc hc₁ y₁ hy₁, field_Mc hc₂ y₂ hy₂]
  have h2 : ‖y₁‖ ^ 2 + ‖y₂‖ ^ 2 =
      ∫ x, (‖field L y₁ x‖ ^ 2 + ‖field L y₂ x‖ ^ 2) ∂box L := by
    rw [integral_add (integrable_sq_field hy₁) (integrable_sq_field hy₂),
      integral_norm_sq hL hy₁, integral_norm_sq hL hy₂, norm_sq_eq, norm_sq_eq]
  have hpt : ∀ x, ‖field L c₁ x * field L y₁ x + field L c₂ x * field L y₂ x‖ ^ 2 ≤
      a ^ 2 * (‖field L y₁ x‖ ^ 2 + ‖field L y₂ x‖ ^ 2) := by
    intro x
    set p := ‖field L c₁ x‖
    set q := ‖field L c₂ x‖
    set r := ‖field L y₁ x‖
    set s := ‖field L y₂ x‖
    have hn : ‖field L c₁ x * field L y₁ x + field L c₂ x * field L y₂ x‖ ≤ p * r + q * s :=
      (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
    have hcs : (p * r + q * s) ^ 2 ≤ (p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2) := by
      nlinarith [sq_nonneg (p * s - q * r)]
    calc ‖field L c₁ x * field L y₁ x + field L c₂ x * field L y₂ x‖ ^ 2 ≤ (p * r + q * s) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2) := hcs
      _ ≤ a ^ 2 * (r ^ 2 + s ^ 2) := mul_le_mul_of_nonneg_right (ha x) (by positivity)
  have hint : Integrable (fun x => ‖field L c₁ x * field L y₁ x +
      field L c₂ x * field L y₂ x‖ ^ 2) (box L) := by
    have h := integrable_sq_field (L := L) hsum
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [field_add hm₁ hm₂, field_Mc hc₁ y₁ hy₁, field_Mc hc₂ y₂ hy₂]
  have h3 : ‖Mc L c₁ y₁ + Mc L c₂ y₂‖ ^ 2 ≤ a ^ 2 * (‖y₁‖ ^ 2 + ‖y₂‖ ^ 2) := by
    rw [h1, h2, ← integral_const_mul]
    exact integral_mono hint (((integrable_sq_field hy₁).add (integrable_sq_field hy₂)).const_mul _)
      hpt
  calc ‖Mc L c₁ y₁ + Mc L c₂ y₂‖ = Real.sqrt (‖Mc L c₁ y₁ + Mc L c₂ y₂‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (a ^ 2 * (‖y₁‖ ^ 2 + ‖y₂‖ ^ 2)) := Real.sqrt_le_sqrt h3
    _ = a * Real.sqrt (‖y₁‖ ^ 2 + ‖y₂‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0]

/-- **The sup-norm bound**: if `|χ₁|² + |χ₂|² ≤ a²` pointwise, then
`‖χ₁Y₁ + χ₂Y₂‖_{L²} ≤ a (‖Y₁‖² + ‖Y₂‖²)^{1/2}` for all `Y₁, Y₂ ∈ L²(T_L²)`. -/
theorem norm_Mc2_le_sup (hL : 0 < L) {c₁ c₂ : Z2 → ℂ} (hc₁ : L1 c₁) (hc₂ : L1 c₂) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : ∀ x, ‖field L c₁ x‖ ^ 2 + ‖field L c₂ x‖ ^ 2 ≤ a ^ 2) (y₁ y₂ : ℓ2) :
    ‖Mc L c₁ y₁ + Mc L c₂ y₂‖ ≤ a * Real.sqrt (‖y₁‖ ^ 2 + ‖y₂‖ ^ 2) := by
  have hcont : Continuous fun p : ℓ2 × ℓ2 =>
      a * Real.sqrt (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) - ‖Mc L c₁ p.1 + Mc L c₂ p.2‖ := by
    have h1 := (McL L (c := c₁) hc₁).continuous
    have h2 := (McL L (c := c₂) hc₂).continuous
    have : Continuous fun p : ℓ2 × ℓ2 => ‖McL L hc₁ p.1 + McL L hc₂ p.2‖ := by fun_prop
    simp only [McL_apply] at this
    fun_prop
  have hlim : Tendsto (fun F => (trunc F y₁, trunc F y₂)) atTop (𝓝 (y₁, y₂)) :=
    (tendsto_trunc y₁).prodMk_nhds (tendsto_trunc y₂)
  set Φ : ℓ2 × ℓ2 → ℝ := fun p =>
    a * Real.sqrt (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) - ‖Mc L c₁ p.1 + Mc L c₂ p.2‖ with hΦ
  have hge : 0 ≤ Φ (y₁, y₂) := ge_of_tendsto ((hcont.tendsto (y₁, y₂)).comp hlim)
    (Eventually.of_forall fun F => by
      show 0 ≤ a * Real.sqrt (‖trunc F y₁‖ ^ 2 + ‖trunc F y₂‖ ^ 2) -
        ‖Mc L c₁ (trunc F y₁) + Mc L c₂ (trunc F y₂)‖
      exact sub_nonneg.2 (norm_Mc2_le_sup_l1 hL hc₁ hc₂ ha0 ha (L1_trunc F y₁) (L1_trunc F y₂)))
  rw [hΦ] at hge
  simp only at hge
  linarith

/-- One-component version: `|χ| ≤ b` gives `‖χY‖_{L²} ≤ b‖Y‖_{L²}`. -/
theorem norm_Mc_le_sup (hL : 0 < L) {c : Z2 → ℂ} (hc : L1 c) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ x, ‖field L c x‖ ≤ b) (y : ℓ2) : ‖Mc L c y‖ ≤ b * ‖y‖ := by
  have h0 : L1 (0 : Z2 → ℂ) := by unfold L1; simpa using summable_zero
  have h := norm_Mc2_le_sup hL hc h0 hb0 (fun x => by
    have : field L (0 : Z2 → ℂ) x = 0 := by simp [field]
    rw [this, norm_zero]
    nlinarith [hb x, norm_nonneg (field L c x)]) y 0
  have hz : Mc L (0 : Z2 → ℂ) (0 : ℓ2) = 0 := by
    ext k; rw [Mc_apply h0]; simp
  rw [hz, add_zero, norm_zero] at h
  have e : Real.sqrt (‖y‖ ^ 2 + 0 ^ 2) = ‖y‖ := by
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (norm_nonneg _)]
  rwa [e] at h

/-! ### Real weights -/

theorem field_real_of_rev {c : Z2 → ℂ} (hreal : rev c = c) (x : ℝ × ℝ) :
    (starRingEnd ℂ) (field L c x) = field L c x := by
  rw [← field_rev, hreal]

theorem im_inner_Mc_self_l1 (hL : 0 < L) {c : Z2 → ℂ} (hc : L1 c) (hreal : rev c = c) {y : ℓ2}
    (hy : L1 y) : (inner ℂ (Mc L c y) y).im = 0 := by
  have hm := L1_Mc (L := L) hc y hy
  rw [lp.inner_eq_tsum]
  have e : (∑' k, inner ℂ (Mc L c y k) (y k)) = ∑' k, (starRingEnd ℂ) (Mc L c y k) * y k := by
    refine tsum_congr fun k => ?_
    rw [RCLike.inner_apply, mul_comm]
  rw [e, ← integral_conj_mul hL hm hy]
  have e2 : (fun x => (starRingEnd ℂ) (field L (Mc L c y) x) * field L y x) =
      fun x => ((((field L c x).re * ‖field L y x‖ ^ 2) : ℝ) : ℂ) := by
    funext x
    rw [field_Mc hc y hy, map_mul, field_real_of_rev hreal, mul_assoc, mul_comm _ (field L y x),
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hre : field L c x = ((field L c x).re : ℂ) := by
      apply Complex.ext
      · simp
      · have h := field_real_of_rev (L := L) hreal x
        have : (field L c x).im = -(field L c x).im := by
          conv_lhs => rw [← h]
          simp
        simp; linarith
    rw [hre, Complex.ofReal_re]
    push_cast
    ring
  rw [e2, integral_complex_ofReal, Complex.ofReal_im]

/-- **`⟨χY, Y⟩_{L²}` is real for a real weight `χ`.** -/
theorem im_inner_Mc_self (hL : 0 < L) {c : Z2 → ℂ} (hc : L1 c) (hreal : rev c = c) (y : ℓ2) :
    (inner ℂ (Mc L c y) y).im = 0 := by
  have hcont : Continuous fun z : ℓ2 => (inner ℂ (McL L hc z) z).im :=
    Complex.continuous_im.comp (((McL L hc).continuous).inner continuous_id)
  have h := (hcont.tendsto y).comp (tendsto_trunc y)
  have h0 : ∀ F, (fun z : ℓ2 => (inner ℂ (McL L hc z) z).im) (trunc F y) = 0 := fun F =>
    im_inner_Mc_self_l1 hL hc hreal (L1_trunc F y)
  have := tendsto_nhds_unique (h.congr (fun F => h0 F)) tendsto_const_nhds
  simpa [McL_apply] using this

end PVNP.Torus
