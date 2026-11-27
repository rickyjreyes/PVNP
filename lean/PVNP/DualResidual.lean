import PVNP.DetectorQuadratic

/-!
# Dual-weighted residuals: the analytic core of the dynamic detector bound

The dual weight is `e^{−σ|k|} = 1 / e^{σ|k|}` (`dw`), and the dual square norm is
`|v|_{−σ}² = Σ_k e^{−2σ|k|} |v_k|²` (`dsq`). The detector pairs the Galerkin error only with
analytic functions, so the error may be measured in this weak norm. In it, the discarded Fourier
tail enters with the doubled exponent.

* `dw_le_mul`: `e^{−σ|k|} ≤ e^{σ|k−j|} e^{−σ|j|}`, since `|j| ≤ |k| + |k − j|`.
* `dsq_mulH_le`, the **dual module estimate**: `|v·w|_{−σ}² ≤ C_A² A_σ(v)² |w|_{−σ}²`. An
  analytic factor acts boundedly on the dual space, with the same constant `C_A` as the algebra
  estimate `Analytic.asum_mulH`.
* `dsq_tail_le`, the **dual tail**: if every discarded mode has size `≥ N`, then
  `|v − P_S v|_{−σ}² ≤ e^{−4σN} A_σ(v)²`. In the `H²` norm the exponent is `2σN` (`tail_le`).
* `dsq_mulH_tail_le`, the **quadratic residual**: the product of an analytic factor with a
  discarded tail is `≤ C_A² A_σ(v)² e^{−4σN} A_σ(w)²` in the dual norm.

These are steps (b) and (c) of the dynamic derivation in
`pvnp/proofs/phase-xxxi-detector-division.md` (registry obligations C2.1 and C2.2). The energy
inequality along the Galerkin error and the Gronwall step (C2.3, C2.4) are not formalized here.
-/

namespace PVNP.DualResidual

open Complex PVNP.Torus PVNP.Analytic

variable {L : ℝ}

/-- The dual weight `e^{−σ|k|}`. -/
noncomputable def dw (σ : ℝ) (k : Z2) : ℝ := Real.exp (-(σ * size k))

theorem dw_pos (σ : ℝ) (k : Z2) : 0 < dw σ k := Real.exp_pos _

theorem dw_le_one {σ : ℝ} (hσ : 0 ≤ σ) (k : Z2) : dw σ k ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hσ (size_nonneg k)))

theorem dw_mul_aw (σ : ℝ) (k : Z2) : dw σ k * aw σ k = 1 := by
  unfold dw aw; rw [← Real.exp_add]; simp

theorem dw_le_mul {σ : ℝ} (hσ : 0 ≤ σ) (k j : Z2) : dw σ k ≤ aw σ (k - j) * dw σ j := by
  unfold dw aw
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h := size_add_le k (j - k)
  have e : k + (j - k) = j := by abel
  rw [e, DetectorQuadratic.size_sub_comm] at h
  have h2 := mul_le_mul_of_nonneg_left h hσ
  rw [mul_add] at h2
  linarith

/-- The dual square norm `Σ_k e^{−2σ|k|} |v_k|²`. -/
noncomputable def dsq (σ : ℝ) (v : ℓ2) : ℝ := ∑' k, (dw σ k * ‖v k‖) ^ 2

theorem dsq_nonneg (σ : ℝ) (v : ℓ2) : 0 ≤ dsq σ v := tsum_nonneg fun _ => sq_nonneg _

theorem dsum {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : Summable fun k => (dw σ k * ‖v k‖) ^ 2 :=
  (summable_sq v).of_nonneg_of_le (fun _ => sq_nonneg _) fun k => by
    have h1 := dw_le_one hσ k
    have h0 := (dw_pos σ k).le
    have h : dw σ k * ‖v k‖ ≤ ‖v k‖ := by nlinarith [norm_nonneg (v k)]
    exact pow_le_pow_left₀ (mul_nonneg h0 (norm_nonneg _)) h 2

/-- The dual lift `k ↦ e^{−σ|k|} |v_k|`. -/
noncomputable def dlift {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : ℓ2 :=
  mk (fun k => ((dw σ k * ‖v k‖ : ℝ) : ℂ))
    ((dsum hσ v).congr fun k => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])

theorem dlift_apply {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) (k : Z2) :
    dlift hσ v k = ((dw σ k * ‖v k‖ : ℝ) : ℂ) := rfl

theorem norm_dlift_sq {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : ‖dlift hσ v‖ ^ 2 = dsq σ v := by
  rw [norm_sq_eq]
  refine tsum_congr fun k => ?_
  rw [dlift_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem co_dlift {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) (k : Z2) :
    co L (dlift hσ v) k = ((dw σ k * ‖co L v k‖ : ℝ) : ℂ) := by
  rw [co, dlift_apply, norm_co, ← Complex.ofReal_div]
  congr 1
  ring

theorem norm_co_dlift {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) (k : Z2) :
    ‖co L (dlift hσ v) k‖ = dw σ k * ‖co L v k‖ := by
  rw [co_dlift, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (dw_pos σ k).le (norm_nonneg _))]

/-- **Pointwise domination** of the dual-weighted product by the product of an analytic lift and a
dual lift. -/
theorem dw_mulH_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {v : ℓ2} (hv : ASum σ v) (w : ℓ2)
    (k : Z2) : dw σ k * ‖mulH L v w k‖ ≤ ‖mulH L (lift σ v hv) (dlift hσ w) k‖ := by
  have ha : L1 (co L v) := L1_co' hL v
  have hb : L1 (co L w) := L1_co' hL w
  have hA : L1 (co L (lift σ v hv)) := L1_co' hL _
  have hB : L1 (co L (dlift hσ w)) := L1_co' hL _
  have hab : Summable fun j => ‖co L v (k - j)‖ * ‖co L w j‖ :=
    (summable_conv_norm ha hb).prod_factor k
  have hAB : Summable fun j => ‖co L (lift σ v hv) (k - j)‖ * ‖co L (dlift hσ w) j‖ :=
    (summable_conv_norm hA hB).prod_factor k
  have hwk := (wt_pos L k).le
  have hreal : ∀ j, co L (lift σ v hv) (k - j) * co L (dlift hσ w) j =
      ((aw σ (k - j) * ‖co L v (k - j)‖ * (dw σ j * ‖co L w j‖) : ℝ) : ℂ) := by
    intro j
    rw [co_lift, co_dlift, ← Complex.ofReal_mul]
  have hAB' : Summable fun j => aw σ (k - j) * ‖co L v (k - j)‖ * (dw σ j * ‖co L w j‖) :=
    hAB.congr fun j => by rw [norm_co_lift, norm_co_dlift]
  have hnn : 0 ≤ ∑' j, aw σ (k - j) * ‖co L v (k - j)‖ * (dw σ j * ‖co L w j‖) :=
    tsum_nonneg fun j => by have := aw_pos σ (k - j); have := dw_pos σ j; positivity
  have hnorm : ‖mulH L (lift σ v hv) (dlift hσ w) k‖ =
      wt L k * (L⁻¹ * ∑' j, aw σ (k - j) * ‖co L v (k - j)‖ * (dw σ j * ‖co L w j‖)) := by
    rw [mulH_apply hL, pr, tsum_congr hreal, ← Complex.ofReal_tsum, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL, abs_of_nonneg hwk, abs_of_nonneg hnn]
  rw [hnorm, mulH_apply hL, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwk]
  have h1 := norm_pr_le (L := L) ha hb k
  rw [abs_of_pos hL] at h1
  have h2 : dw σ k * ∑' j, ‖co L v (k - j)‖ * ‖co L w j‖ ≤
      ∑' j, aw σ (k - j) * ‖co L v (k - j)‖ * (dw σ j * ‖co L w j‖) := by
    rw [← tsum_mul_left]
    refine (hab.mul_left _).tsum_le_tsum (fun j => ?_) hAB'
    have hm := dw_le_mul hσ k j
    have h0 : 0 ≤ ‖co L v (k - j)‖ * ‖co L w j‖ := by positivity
    calc dw σ k * (‖co L v (k - j)‖ * ‖co L w j‖)
        ≤ aw σ (k - j) * dw σ j * (‖co L v (k - j)‖ * ‖co L w j‖) :=
          mul_le_mul_of_nonneg_right hm h0
      _ = aw σ (k - j) * ‖co L v (k - j)‖ * (dw σ j * ‖co L w j‖) := by ring
  have hLi : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  have hak := (dw_pos σ k).le
  calc dw σ k * (wt L k * ‖pr L (co L v) (co L w) k‖)
      ≤ dw σ k * (wt L k * (L⁻¹ * ∑' j, ‖co L v (k - j)‖ * ‖co L w j‖)) := by gcongr
    _ = wt L k * (L⁻¹ * (dw σ k * ∑' j, ‖co L v (k - j)‖ * ‖co L w j‖)) := by ring
    _ ≤ wt L k * (L⁻¹ * ∑' j, aw σ (k - j) * ‖co L v (k - j)‖ * (dw σ j * ‖co L w j‖)) := by
        gcongr

/-- **The dual module estimate**: `|v·w|_{−σ}² ≤ C_A² A_σ(v)² |w|_{−σ}²`. -/
theorem dsq_mulH_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {v : ℓ2} (hv : ASum σ v) (w : ℓ2) :
    dsq σ (mulH L v w) ≤ (CA L) ^ 2 * asq σ v * dsq σ w := by
  set P := mulH L (lift σ v hv) (dlift hσ w)
  have hpt : ∀ k, (dw σ k * ‖mulH L v w k‖) ^ 2 ≤ ‖P k‖ ^ 2 := fun k =>
    pow_le_pow_left₀ (mul_nonneg (dw_pos σ k).le (norm_nonneg _)) (dw_mulH_le hL hσ hv w k) 2
  have h1 : dsq σ (mulH L v w) ≤ ‖P‖ ^ 2 := by
    rw [norm_sq_eq]
    exact (dsum hσ _).tsum_le_tsum hpt (summable_sq P)
  have h2 : ‖P‖ ≤ CA L * ‖lift σ v hv‖ * ‖dlift hσ w‖ := norm_mulH_le hL _ _
  have h3 : ‖P‖ ^ 2 ≤ (CA L * ‖lift σ v hv‖ * ‖dlift hσ w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  calc dsq σ (mulH L v w) ≤ ‖P‖ ^ 2 := h1
    _ ≤ (CA L * ‖lift σ v hv‖ * ‖dlift hσ w‖) ^ 2 := h3
    _ = (CA L) ^ 2 * asq σ v * dsq σ w := by
        rw [mul_pow, mul_pow, norm_lift_sq, norm_dlift_sq]

/-- **The dual tail**: `|v − P_S v|_{−σ}² ≤ e^{−4σN} A_σ(v)²` when every mode outside `S` has
size `≥ N`. -/
theorem dsq_tail_le {σ N : ℝ} (hσ : 0 ≤ σ) {v : ℓ2} (hv : ASum σ v) (S : Finset Z2)
    (hS : ∀ k ∉ S, N ≤ size k) :
    dsq σ (v - trunc S v) ≤ Real.exp (-(4 * σ * N)) * asq σ v := by
  have hpt : ∀ k, (dw σ k * ‖(v - trunc S v) k‖) ^ 2 ≤
      Real.exp (-(4 * σ * N)) * (aw σ k * ‖v k‖) ^ 2 := by
    intro k
    rw [lp.coeFn_sub, Pi.sub_apply, trunc_apply]
    split_ifs with hk
    · rw [sub_self, norm_zero, mul_zero, zero_pow two_ne_zero]; positivity
    · rw [sub_zero]
      have e1 : (dw σ k * ‖v k‖) ^ 2 = Real.exp (-(2 * σ * size k)) * ‖v k‖ ^ 2 := by
        rw [dw, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
      have e2 : (aw σ k * ‖v k‖) ^ 2 = Real.exp (2 * σ * size k) * ‖v k‖ ^ 2 := by
        rw [aw, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
      rw [e1, e2, ← mul_assoc, ← Real.exp_add]
      have h1 : Real.exp (-(2 * σ * size k)) ≤ Real.exp (-(4 * σ * N) + 2 * σ * size k) :=
        Real.exp_le_exp.2 (by nlinarith [mul_nonneg hσ (sub_nonneg.2 (hS k hk))])
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  calc dsq σ (v - trunc S v) ≤ ∑' k, Real.exp (-(4 * σ * N)) * (aw σ k * ‖v k‖) ^ 2 :=
        (dsum hσ _).tsum_le_tsum hpt (hv.mul_left _)
    _ = Real.exp (-(4 * σ * N)) * asq σ v := by rw [tsum_mul_left]; rfl

/-- **The quadratic residual**: an analytic factor times a discarded tail is small in the dual
norm with the doubled exponent. -/
theorem dsq_mulH_tail_le (hL : 0 < L) {σ N : ℝ} (hσ : 0 ≤ σ) {v w : ℓ2} (hv : ASum σ v)
    (hw : ASum σ w) (S : Finset Z2) (hS : ∀ k ∉ S, N ≤ size k) :
    dsq σ (mulH L v (w - trunc S w)) ≤
      (CA L) ^ 2 * asq σ v * (Real.exp (-(4 * σ * N)) * asq σ w) := by
  have h1 := dsq_mulH_le hL hσ hv (w - trunc S w)
  have h2 := dsq_tail_le hσ hw S hS
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg _) (asq_nonneg _ _)))

end PVNP.DualResidual
