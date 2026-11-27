import PVNP.GalerkinTaylorSeries

/-!
# Cutoff-independent analytic norms for the frozen torus flow

In the repository's `H²` coordinates `v_k = (1 + q_L(k)) ψ̂_k`, the exponentially weighted norm is
`A_σ(v)² = Σ_k e^{2σ|k|} |v_k|²`, with `|k| = |k₁| + |k₂|`. It is the `H²` norm of
`e^{σ|D|}ψ`, the analytic norm of the user's specification with the `L`-scaled frequency
weight.

* `asum_mulH`: **analytic Banach algebra.** `A_σ(mulH v w) ≤ C_A A_σ(v) A_σ(w)`, with the same
  constant `C_A` as the `H²` algebra estimate. The proof lifts `v` to the nonnegative sequence
  `e^{σ|k|}|v_k|` (`lift`). Subadditivity `|k| ≤ |k − j| + |j|` turns the weighted convolution
  into an unweighted convolution of lifts (`aw_mulH_le`).
* `asq_conjH`, `asq_trunc_le`, `asq_U`: conjugation is an isometry, Fourier truncation is a
  contraction, and the free dispersion `U(t)` is an isometry. The skew-adjoint dispersion
  therefore does not change `A_σ`.
* `anorm_Fnl_le`: `A_σ(Fnl u) ≤ |β| C_A² A_σ(u)³ + |γ| C_A⁴ A_σ(u)⁵`.
* `asq_interp`: interpolation between the `H²` norm and a larger radius,
  `A_{σ'}(v)² ≤ e^{2σ'N}‖v‖² + e^{−2(σ−σ')N} A_σ(v)²` for `σ' ≤ σ` and every `N`.
* `tail_le`: `Σ_{|k|>N} |v_k|² ≤ e^{−2σN} A_σ(v)²`.

None of the constants depends on a Fourier cutoff.
-/

namespace PVNP.Analytic

open Finset PVNP.Torus PVNP.TorusGalerkin Complex

variable {L : ℝ}

/-! ### Mode size and weights -/

/-- The size of a mode, `|k₁| + |k₂|`. -/
def size (k : Z2) : ℝ := |(k.1 : ℝ)| + |(k.2 : ℝ)|

theorem size_nonneg (k : Z2) : 0 ≤ size k := by unfold size; positivity

theorem size_add_le (a b : Z2) : size (a + b) ≤ size a + size b := by
  unfold size
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  have h1 := abs_add_le (a.1 : ℝ) (b.1 : ℝ)
  have h2 := abs_add_le (a.2 : ℝ) (b.2 : ℝ)
  linarith

theorem size_neg (k : Z2) : size (-k) = size k := by
  unfold size
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg, abs_neg]

theorem size_le_sub_add (k j : Z2) : size k ≤ size (k - j) + size j := by
  have h := size_add_le (k - j) j
  rwa [sub_add_cancel] at h

/-- The analytic weight `e^{σ|k|}`. -/
noncomputable def aw (σ : ℝ) (k : Z2) : ℝ := Real.exp (σ * size k)

theorem aw_pos (σ : ℝ) (k : Z2) : 0 < aw σ k := Real.exp_pos _

theorem aw_le_mul {σ : ℝ} (hσ : 0 ≤ σ) (k j : Z2) : aw σ k ≤ aw σ (k - j) * aw σ j := by
  unfold aw
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have := size_le_sub_add k j
  nlinarith

theorem aw_neg (σ : ℝ) (k : Z2) : aw σ (-k) = aw σ k := by
  unfold aw; rw [size_neg]

theorem aw_zero (k : Z2) : aw 0 k = 1 := by unfold aw; simp

/-! ### The analytic norm -/

/-- Analytic summability: `Σ_k e^{2σ|k|} |v_k|² < ∞`. -/
def ASum (σ : ℝ) (v : ℓ2) : Prop := Summable fun k => (aw σ k * ‖v k‖) ^ 2

/-- `A_σ(v)² = Σ_k e^{2σ|k|} |v_k|²` in `H²` coordinates. -/
noncomputable def asq (σ : ℝ) (v : ℓ2) : ℝ := ∑' k, (aw σ k * ‖v k‖) ^ 2

/-- The analytic norm `A_σ(v)`. -/
noncomputable def anorm (σ : ℝ) (v : ℓ2) : ℝ := Real.sqrt (asq σ v)

theorem asq_nonneg (σ : ℝ) (v : ℓ2) : 0 ≤ asq σ v := tsum_nonneg fun _ => sq_nonneg _

theorem anorm_nonneg (σ : ℝ) (v : ℓ2) : 0 ≤ anorm σ v := Real.sqrt_nonneg _

theorem anorm_sq (σ : ℝ) (v : ℓ2) : anorm σ v ^ 2 = asq σ v :=
  Real.sq_sqrt (asq_nonneg σ v)

theorem asq_zero_radius (v : ℓ2) : asq 0 v = ‖v‖ ^ 2 := by
  unfold asq
  rw [norm_sq_eq]
  exact tsum_congr fun k => by rw [aw_zero, one_mul]

theorem asum_zero_radius (v : ℓ2) : ASum 0 v := by
  unfold ASum
  simpa only [aw_zero, one_mul] using summable_sq v

/-- Finitely supported states are analytic of every radius. -/
theorem asum_of_supported {S : Finset Z2} {v : ℓ2} (hv : Supported S v) (σ : ℝ) :
    ASum σ v := by
  unfold ASum
  apply summable_of_ne_finset_zero (s := S)
  intro k hk
  rw [hv k hk, norm_zero, mul_zero]; norm_num

/-- The lift `ṽ_k = e^{σ|k|}|v_k|`, with `‖ṽ‖² = A_σ(v)²`. -/
noncomputable def lift (σ : ℝ) (v : ℓ2) (h : ASum σ v) : ℓ2 :=
  mk (fun k => ((aw σ k * ‖v k‖ : ℝ) : ℂ))
    (h.congr fun k => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])

theorem lift_apply (σ : ℝ) (v : ℓ2) (h : ASum σ v) (k : Z2) :
    lift σ v h k = ((aw σ k * ‖v k‖ : ℝ) : ℂ) := rfl

theorem norm_lift_sq (σ : ℝ) (v : ℓ2) (h : ASum σ v) : ‖lift σ v h‖ ^ 2 = asq σ v := by
  rw [norm_sq_eq]
  refine tsum_congr fun k => ?_
  rw [lift_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_lift (σ : ℝ) (v : ℓ2) (h : ASum σ v) : ‖lift σ v h‖ = anorm σ v := by
  rw [anorm, ← norm_lift_sq σ v h, Real.sqrt_sq (norm_nonneg _)]

theorem co_lift (σ : ℝ) (v : ℓ2) (h : ASum σ v) (k : Z2) :
    co L (lift σ v h) k = ((aw σ k * ‖co L v k‖ : ℝ) : ℂ) := by
  rw [co, lift_apply, norm_co, ← Complex.ofReal_div]
  congr 1
  ring

theorem norm_co_lift (σ : ℝ) (v : ℓ2) (h : ASum σ v) (k : Z2) :
    ‖co L (lift σ v h) k‖ = aw σ k * ‖co L v k‖ := by
  rw [co_lift, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (aw_pos σ k).le (norm_nonneg _))]

/-! ### The analytic Banach algebra -/

/-- **Pointwise domination** of the weighted product by the product of lifts. -/
theorem aw_mulH_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {v w : ℓ2} (hv : ASum σ v)
    (hw : ASum σ w) (k : Z2) :
    aw σ k * ‖mulH L v w k‖ ≤ ‖mulH L (lift σ v hv) (lift σ w hw) k‖ := by
  have ha : L1 (co L v) := L1_co' hL v
  have hb : L1 (co L w) := L1_co' hL w
  have hA : L1 (co L (lift σ v hv)) := L1_co' hL _
  have hB : L1 (co L (lift σ w hw)) := L1_co' hL _
  have hab : Summable fun j => ‖co L v (k - j)‖ * ‖co L w j‖ :=
    (summable_conv_norm ha hb).prod_factor k
  have hAB : Summable fun j => ‖co L (lift σ v hv) (k - j)‖ * ‖co L (lift σ w hw) j‖ :=
    (summable_conv_norm hA hB).prod_factor k
  have hwk := (wt_pos L k).le
  have hreal : ∀ j, co L (lift σ v hv) (k - j) * co L (lift σ w hw) j =
      ((aw σ (k - j) * ‖co L v (k - j)‖ * (aw σ j * ‖co L w j‖) : ℝ) : ℂ) := by
    intro j
    rw [co_lift, co_lift, ← Complex.ofReal_mul]
  have hAB' : Summable fun j => aw σ (k - j) * ‖co L v (k - j)‖ * (aw σ j * ‖co L w j‖) :=
    hAB.congr fun j => by rw [norm_co_lift, norm_co_lift]
  have hnn : 0 ≤ ∑' j, aw σ (k - j) * ‖co L v (k - j)‖ * (aw σ j * ‖co L w j‖) :=
    tsum_nonneg fun j => by have := aw_pos σ (k - j); have := aw_pos σ j; positivity
  have hnorm : ‖mulH L (lift σ v hv) (lift σ w hw) k‖ =
      wt L k * (L⁻¹ * ∑' j, aw σ (k - j) * ‖co L v (k - j)‖ * (aw σ j * ‖co L w j‖)) := by
    rw [mulH_apply hL, pr, tsum_congr hreal, ← Complex.ofReal_tsum, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL, abs_of_nonneg hwk, abs_of_nonneg hnn]
  rw [hnorm, mulH_apply hL, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwk]
  have h1 := norm_pr_le (L := L) ha hb k
  rw [abs_of_pos hL] at h1
  have h2 : aw σ k * ∑' j, ‖co L v (k - j)‖ * ‖co L w j‖ ≤
      ∑' j, aw σ (k - j) * ‖co L v (k - j)‖ * (aw σ j * ‖co L w j‖) := by
    rw [← tsum_mul_left]
    refine (hab.mul_left _).tsum_le_tsum (fun j => ?_) hAB'
    have hm := aw_le_mul hσ k j
    have h0 : 0 ≤ ‖co L v (k - j)‖ * ‖co L w j‖ := by positivity
    calc aw σ k * (‖co L v (k - j)‖ * ‖co L w j‖)
        ≤ aw σ (k - j) * aw σ j * (‖co L v (k - j)‖ * ‖co L w j‖) :=
          mul_le_mul_of_nonneg_right hm h0
      _ = aw σ (k - j) * ‖co L v (k - j)‖ * (aw σ j * ‖co L w j‖) := by ring
  have hLi : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  have hak := (aw_pos σ k).le
  calc aw σ k * (wt L k * ‖pr L (co L v) (co L w) k‖)
      ≤ aw σ k * (wt L k * (L⁻¹ * ∑' j, ‖co L v (k - j)‖ * ‖co L w j‖)) := by gcongr
    _ = wt L k * (L⁻¹ * (aw σ k * ∑' j, ‖co L v (k - j)‖ * ‖co L w j‖)) := by ring
    _ ≤ wt L k * (L⁻¹ * ∑' j, aw σ (k - j) * ‖co L v (k - j)‖ * (aw σ j * ‖co L w j‖)) := by
        gcongr

/-- **The analytic Banach algebra estimate**, with the `H²` constant `C_A`. -/
theorem asum_mulH (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {v w : ℓ2} (hv : ASum σ v)
    (hw : ASum σ w) :
    ASum σ (mulH L v w) ∧ asq σ (mulH L v w) ≤ (CA L) ^ 2 * asq σ v * asq σ w := by
  set P := mulH L (lift σ v hv) (lift σ w hw)
  have hpt : ∀ k, (aw σ k * ‖mulH L v w k‖) ^ 2 ≤ ‖P k‖ ^ 2 := fun k =>
    pow_le_pow_left₀ (mul_nonneg (aw_pos σ k).le (norm_nonneg _)) (aw_mulH_le hL hσ hv hw k) 2
  have hs : ASum σ (mulH L v w) :=
    (summable_sq P).of_nonneg_of_le (fun _ => sq_nonneg _) hpt
  refine ⟨hs, ?_⟩
  have h1 : asq σ (mulH L v w) ≤ ‖P‖ ^ 2 := by
    rw [norm_sq_eq]
    exact hs.tsum_le_tsum hpt (summable_sq P)
  have h2 : ‖P‖ ≤ CA L * ‖lift σ v hv‖ * ‖lift σ w hw‖ := norm_mulH_le hL _ _
  have h3 : ‖P‖ ^ 2 ≤ (CA L * ‖lift σ v hv‖ * ‖lift σ w hw‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  calc asq σ (mulH L v w) ≤ ‖P‖ ^ 2 := h1
    _ ≤ (CA L * ‖lift σ v hv‖ * ‖lift σ w hw‖) ^ 2 := h3
    _ = (CA L) ^ 2 * asq σ v * asq σ w := by
        rw [mul_pow, mul_pow, norm_lift_sq, norm_lift_sq]

theorem anorm_mulH_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {v w : ℓ2} (hv : ASum σ v)
    (hw : ASum σ w) : anorm σ (mulH L v w) ≤ CA L * anorm σ v * anorm σ w := by
  have h := (asum_mulH hL hσ hv hw).2
  have hC := CA_nonneg hL
  rw [anorm, anorm, anorm, ← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg _),
    ← Real.sqrt_mul (mul_nonneg (sq_nonneg _) (asq_nonneg _ _))]
  exact Real.sqrt_le_sqrt h

/-! ### Conjugation, truncation, scalars, sums and dispersion -/

theorem asum_conjH {σ : ℝ} {v : ℓ2} (hv : ASum σ v) : ASum σ (conjH v) := by
  unfold ASum at hv ⊢
  have h := (Equiv.neg Z2).summable_iff.mpr hv
  refine h.congr fun k => ?_
  simp only [Function.comp, Equiv.neg_apply, conjH_apply, Complex.norm_conj, aw_neg]

theorem asq_conjH (σ : ℝ) (v : ℓ2) : asq σ (conjH v) = asq σ v := by
  unfold asq
  rw [← (Equiv.neg Z2).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply, conjH_apply, Complex.norm_conj, aw_neg, neg_neg]

theorem anorm_conjH (σ : ℝ) (v : ℓ2) : anorm σ (conjH v) = anorm σ v := by
  rw [anorm, anorm, asq_conjH]

theorem asum_trunc {σ : ℝ} (S : Finset Z2) (v : ℓ2) : ASum σ (trunc S v) :=
  asum_of_supported (trunc_supported S v) σ

theorem asq_trunc_le {σ : ℝ} (S : Finset Z2) {v : ℓ2} (hv : ASum σ v) :
    asq σ (trunc S v) ≤ asq σ v := by
  refine (asum_trunc S v).tsum_le_tsum (fun k => ?_) hv
  rw [trunc_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, mul_zero, zero_pow two_ne_zero]; positivity

theorem asum_smul {σ : ℝ} (c : ℂ) {v : ℓ2} (hv : ASum σ v) : ASum σ (c • v) := by
  unfold ASum at hv ⊢
  refine (hv.mul_left (‖c‖ ^ 2)).congr fun k => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, norm_smul]
  ring

theorem asq_smul (σ : ℝ) (c : ℂ) (v : ℓ2) : asq σ (c • v) = ‖c‖ ^ 2 * asq σ v := by
  unfold asq
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, norm_smul]
  ring

theorem anorm_smul (σ : ℝ) (c : ℂ) (v : ℓ2) : anorm σ (c • v) = ‖c‖ * anorm σ v := by
  rw [anorm, anorm, asq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Triangle inequality for the analytic norm. -/
theorem anorm_add_le {σ : ℝ} {v w : ℓ2} (hv : ASum σ v) (hw : ASum σ w) :
    ASum σ (v + w) ∧ anorm σ (v + w) ≤ anorm σ v + anorm σ w := by
  set X := lift σ v hv + lift σ w hw
  have hpt : ∀ k, (aw σ k * ‖(v + w) k‖) ^ 2 ≤ ‖X k‖ ^ 2 := by
    intro k
    have hX : X k = ((aw σ k * ‖v k‖ + aw σ k * ‖w k‖ : ℝ) : ℂ) := by
      simp only [X, lp.coeFn_add, Pi.add_apply, lift_apply, Complex.ofReal_add]
    have hn : ‖X k‖ = aw σ k * ‖v k‖ + aw σ k * ‖w k‖ := by
      rw [hX, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
        have := aw_pos σ k; positivity)]
    rw [hn]
    have h1 : ‖(v + w) k‖ ≤ ‖v k‖ + ‖w k‖ := by
      rw [lp.coeFn_add, Pi.add_apply]; exact norm_add_le _ _
    have h0 : 0 ≤ aw σ k * ‖(v + w) k‖ := mul_nonneg (aw_pos σ k).le (norm_nonneg _)
    have h2 : aw σ k * ‖(v + w) k‖ ≤ aw σ k * ‖v k‖ + aw σ k * ‖w k‖ := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left h1 (aw_pos σ k).le
    exact pow_le_pow_left₀ h0 h2 2
  have hs : ASum σ (v + w) := (summable_sq X).of_nonneg_of_le (fun _ => sq_nonneg _) hpt
  refine ⟨hs, ?_⟩
  have h1 : asq σ (v + w) ≤ ‖X‖ ^ 2 := by
    rw [norm_sq_eq]; exact hs.tsum_le_tsum hpt (summable_sq X)
  have h2 : ‖X‖ ≤ anorm σ v + anorm σ w := by
    rw [← norm_lift σ v hv, ← norm_lift σ w hw]; exact norm_add_le _ _
  rw [anorm]
  calc Real.sqrt (asq σ (v + w)) ≤ Real.sqrt (‖X‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖X‖ := Real.sqrt_sq (norm_nonneg _)
    _ ≤ _ := h2

theorem asq_U (σ : ℝ) (κ t : ℝ) (v : ℓ2) : asq σ (U L κ t v) = asq σ v := by
  unfold asq
  refine tsum_congr fun k => ?_
  rw [U_apply, norm_mul, norm_ph, one_mul]

theorem asum_U {σ : ℝ} (κ t : ℝ) {v : ℓ2} (hv : ASum σ v) : ASum σ (U L κ t v) := by
  unfold ASum at hv ⊢
  refine hv.congr fun k => ?_
  rw [U_apply, norm_mul, norm_ph, one_mul]

/-! ### The nonlinearity -/

/-- **Analytic bound for the actual nonlinearity.** -/
theorem anorm_Fnl_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) (β γ : ℝ) {u : ℓ2} (hu : ASum σ u) :
    ASum σ (Fnl L β γ u) ∧
      anorm σ (Fnl L β γ u) ≤
        |β| * CA L ^ 2 * anorm σ u ^ 3 + |γ| * CA L ^ 4 * anorm σ u ^ 5 := by
  have hC := CA_nonneg hL
  set a := anorm σ u
  have ha : 0 ≤ a := anorm_nonneg σ u
  have hj := asum_conjH hu
  have hja : anorm σ (conjH u) = a := anorm_conjH σ u
  have m2 := asum_mulH hL hσ hu hu
  have b2 : anorm σ (mulH L u u) ≤ CA L * a * a := anorm_mulH_le hL hσ hu hu
  have m3 := asum_mulH hL hσ m2.1 hj
  have b3 : anorm σ (mulH L (mulH L u u) (conjH u)) ≤ CA L ^ 2 * a ^ 3 := by
    calc _ ≤ CA L * anorm σ (mulH L u u) * anorm σ (conjH u) := anorm_mulH_le hL hσ m2.1 hj
      _ ≤ CA L * (CA L * a * a) * a := by rw [hja]; gcongr
      _ = CA L ^ 2 * a ^ 3 := by ring
  have m3' := asum_mulH hL hσ m2.1 hu
  have b3' : anorm σ (mulH L (mulH L u u) u) ≤ CA L ^ 2 * a ^ 3 := by
    calc _ ≤ CA L * anorm σ (mulH L u u) * anorm σ u := anorm_mulH_le hL hσ m2.1 hu
      _ ≤ CA L * (CA L * a * a) * a := by gcongr
      _ = CA L ^ 2 * a ^ 3 := by ring
  have m4 := asum_mulH hL hσ m3'.1 hj
  have b4 : anorm σ (mulH L (mulH L (mulH L u u) u) (conjH u)) ≤ CA L ^ 3 * a ^ 4 := by
    calc _ ≤ CA L * anorm σ (mulH L (mulH L u u) u) * anorm σ (conjH u) :=
          anorm_mulH_le hL hσ m3'.1 hj
      _ ≤ CA L * (CA L ^ 2 * a ^ 3) * a := by rw [hja]; gcongr
      _ = CA L ^ 3 * a ^ 4 := by ring
  have m5 := asum_mulH hL hσ m4.1 hj
  have b5 : anorm σ (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u)) ≤
      CA L ^ 4 * a ^ 5 := by
    calc _ ≤ CA L * anorm σ (mulH L (mulH L (mulH L u u) u) (conjH u)) * anorm σ (conjH u) :=
          anorm_mulH_le hL hσ m4.1 hj
      _ ≤ CA L * (CA L ^ 3 * a ^ 4) * a := by rw [hja]; gcongr
      _ = CA L ^ 4 * a ^ 5 := by ring
  have s3 := asum_smul (-(β : ℂ)) m3.1
  have s5 := asum_smul (γ : ℂ) m5.1
  obtain ⟨hsum, hle⟩ := anorm_add_le s3 s5
  refine ⟨by rw [Fnl]; exact hsum, ?_⟩
  rw [Fnl]
  refine hle.trans ?_
  rw [anorm_smul, anorm_smul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have hb0 := abs_nonneg β
  have hg0 := abs_nonneg γ
  calc |β| * anorm σ (mulH L (mulH L u u) (conjH u)) +
        |γ| * anorm σ (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u))
      ≤ |β| * (CA L ^ 2 * a ^ 3) + |γ| * (CA L ^ 4 * a ^ 5) := by gcongr
    _ = _ := by ring

/-! ### Interpolation and tails -/

/-- **Interpolation** between the `H²` norm and a larger analytic radius. -/
theorem asq_interp {σ σ' N : ℝ} (hσ' : 0 ≤ σ') (hσσ' : σ' ≤ σ) {v : ℓ2} (hv : ASum σ v) :
    asq σ' v ≤ Real.exp (2 * σ' * N) * ‖v‖ ^ 2 + Real.exp (-(2 * (σ - σ') * N)) * asq σ v := by
  have hpt : ∀ k, (aw σ' k * ‖v k‖) ^ 2 ≤
      Real.exp (2 * σ' * N) * ‖v k‖ ^ 2 +
        Real.exp (-(2 * (σ - σ') * N)) * (aw σ k * ‖v k‖) ^ 2 := by
    intro k
    have e1 : (aw σ' k * ‖v k‖) ^ 2 = Real.exp (2 * σ' * size k) * ‖v k‖ ^ 2 := by
      rw [aw, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    have e2 : (aw σ k * ‖v k‖) ^ 2 = Real.exp (2 * σ * size k) * ‖v k‖ ^ 2 := by
      rw [aw, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e1, e2]
    have hv0 := sq_nonneg ‖v k‖
    rcases le_or_gt (size k) N with hk | hk
    · have h1 : Real.exp (2 * σ' * size k) ≤ Real.exp (2 * σ' * N) :=
        Real.exp_le_exp.2 (by nlinarith)
      have h2 : 0 ≤ Real.exp (-(2 * (σ - σ') * N)) * (Real.exp (2 * σ * size k) * ‖v k‖ ^ 2) := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_right h1 hv0]
    · have h1 : Real.exp (2 * σ' * size k) ≤
          Real.exp (-(2 * (σ - σ') * N)) * Real.exp (2 * σ * size k) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
      have h2 : 0 ≤ Real.exp (2 * σ' * N) * ‖v k‖ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h1 hv0]
  have hs1 : Summable fun k => Real.exp (2 * σ' * N) * ‖v k‖ ^ 2 := (summable_sq v).mul_left _
  have hs2 : Summable fun k => Real.exp (-(2 * (σ - σ') * N)) * (aw σ k * ‖v k‖) ^ 2 :=
    hv.mul_left _
  have hs : ASum σ' v := (hs1.add hs2).of_nonneg_of_le (fun _ => sq_nonneg _) hpt
  calc asq σ' v ≤ ∑' k, (Real.exp (2 * σ' * N) * ‖v k‖ ^ 2 +
        Real.exp (-(2 * (σ - σ') * N)) * (aw σ k * ‖v k‖) ^ 2) :=
        hs.tsum_le_tsum hpt (hs1.add hs2)
    _ = Real.exp (2 * σ' * N) * ‖v‖ ^ 2 + Real.exp (-(2 * (σ - σ') * N)) * asq σ v := by
        rw [hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, ← norm_sq_eq]; rfl

/-- Smaller radii are dominated by larger ones. -/
theorem asq_mono {σ σ' : ℝ} (hσσ' : σ' ≤ σ) {v : ℓ2} (hv : ASum σ v) :
    ASum σ' v ∧ asq σ' v ≤ asq σ v := by
  have hpt : ∀ k, (aw σ' k * ‖v k‖) ^ 2 ≤ (aw σ k * ‖v k‖) ^ 2 := by
    intro k
    have h : aw σ' k ≤ aw σ k := Real.exp_le_exp.2 (by nlinarith [size_nonneg k])
    exact pow_le_pow_left₀ (mul_nonneg (aw_pos σ' k).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_right h (norm_nonneg _)) 2
  have hs : ASum σ' v := hv.of_nonneg_of_le (fun _ => sq_nonneg _) hpt
  exact ⟨hs, hs.tsum_le_tsum hpt hv⟩

/-- **Fourier tail beyond size `N`.** -/
theorem tail_le {σ N : ℝ} (hσ : 0 ≤ σ) {v : ℓ2} (hv : ASum σ v) (S : Finset Z2)
    (hS : ∀ k ∉ S, N ≤ size k) :
    ‖trunc S v - v‖ ^ 2 ≤ Real.exp (-(2 * σ * N)) * asq σ v := by
  rw [norm_sq_eq]
  have hpt : ∀ k, ‖(trunc S v - v) k‖ ^ 2 ≤
      Real.exp (-(2 * σ * N)) * (aw σ k * ‖v k‖) ^ 2 := by
    intro k
    rw [lp.coeFn_sub, Pi.sub_apply, trunc_apply]
    split_ifs with hk
    · rw [sub_self, norm_zero, zero_pow two_ne_zero]; positivity
    · rw [zero_sub, norm_neg]
      have e : (aw σ k * ‖v k‖) ^ 2 = Real.exp (2 * σ * size k) * ‖v k‖ ^ 2 := by
        rw [aw, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
      rw [e, ← mul_assoc, ← Real.exp_add]
      have h1 : 1 ≤ Real.exp (-(2 * σ * N) + 2 * σ * size k) :=
        Real.one_le_exp (by nlinarith [hS k hk])
      nlinarith [sq_nonneg ‖v k‖]
  calc ∑' k, ‖(trunc S v - v) k‖ ^ 2 ≤ ∑' k, Real.exp (-(2 * σ * N)) * (aw σ k * ‖v k‖) ^ 2 :=
        (summable_sq _).tsum_le_tsum hpt (hv.mul_left _)
    _ = Real.exp (-(2 * σ * N)) * asq σ v := by rw [tsum_mul_left]; rfl

end PVNP.Analytic
