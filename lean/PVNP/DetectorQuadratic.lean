import PVNP.AnalyticNorm
import PVNP.WeakNormApproximation
import PVNP.WCTSATDevice

/-!
# The detector sees the Fourier tail only quadratically

`Jdet L χ v = ∫ χ |ψ|²` is the repository's physical readout. Truncating the state to a finite
mode set `S` changes it by the general Lipschitz bound (`weak_detector_lipschitz`), which is
**linear** in the discarded tail `t = v − P_S v`. For a detector of bandwidth `r` (the
coefficients of `χ` vanish outside `size ≤ r`), the change is **quadratic** in tail quantities.

* `detector_split`, exact: `J(v) − J(P_S v) = Re(⟨t, χt⟩ + ⟨t, χb⟩ + ⟨b, χt⟩)`. Here
  `b = P_B v` is the part of `v` on the boundary layer `B ⊆ S`, the modes of `S` that the
  multiplier couples to modes outside `S` (`IsLayer`).
* `detector_layer_bound`: `|J(v) − J(P_S v)| ≤ C_det ‖t‖ (‖t‖ + 2‖b‖)`.
* `detector_static_quadratic`: if every mode outside `S` has size `≥ N` and every layer mode has
  size `≥ N − r`, then
  `|J(v) − J(P_S v)| ≤ C_det e^{−σN} (e^{−σN} + 2e^{−σ(N−r)}) A_σ(v)²`.
* `detector_band_quadratic`: for a detector of bandwidth `r ≥ 0`, with the layer built from `S`,
  `|J(v) − J(P_S v)| ≤ 3 C_det e^{σr} e^{−2σN} A_σ(v)²`.
* `device_detector_quadratic`: the SAT device's actual detector `χ = L⁻¹(1 + cos(2πx₁/L))`
  (`WCTSATDevice.detector`) has bandwidth `1`, so
  `|J(v) − J(P_S v)| ≤ 3 C_det e^{σ} e^{−2σN} A_σ(v)²`.

The full state truncation error is `‖t‖ ≤ e^{−σN} A_σ(v)` (`tail_le`). The detector needs only
half as many modes: the exponent is `2σN`, not `σN`.

This is the **static** statement, for a fixed state. The dynamic statement for the Galerkin
flow is derived, but not kernel-checked, in `pvnp/proofs/phase-xxxi-detector-division.md`.
-/

namespace PVNP.DetectorQuadratic

open Complex PVNP.Torus PVNP.ContinuumPrecision PVNP.Analytic

variable {L : ℝ}

theorem co_trunc (S : Finset Z2) (v : ℓ2) (k : Z2) :
    co L (trunc S v) k = if k ∈ S then co L v k else 0 := by
  unfold co; rw [trunc_apply]; split_ifs <;> simp

theorem co_mulH_eq_zero (hL : 0 < L) (χv δ : ℓ2) (k : Z2)
    (h : ∀ j, co L χv (k - j) * co L δ j = 0) : co L (mulH L χv δ) k = 0 := by
  rw [co_mulH hL, pr]
  simp only [h, tsum_zero, mul_zero]

theorem co_mulH_congr (hL : 0 < L) (χv δ δ' : ℓ2) (k : Z2)
    (h : ∀ j, co L χv (k - j) * co L δ j = co L χv (k - j) * co L δ' j) :
    co L (mulH L χv δ) k = co L (mulH L χv δ') k := by
  rw [co_mulH hL, co_mulH hL, pr, pr]
  congr 2
  funext j
  exact h j

/-- `B ⊆ S` is a boundary layer of `S` for the multiplier `χ`: on `S \ B` the multiplier couples
only to modes of `S`. -/
def IsLayer (L : ℝ) (χv : ℓ2) (S B : Finset Z2) : Prop :=
  B ⊆ S ∧ ∀ k j, k ∈ S → k ∉ B → j ∉ S → co L χv (k - j) = 0 ∧ co L χv (j - k) = 0

theorem inner_layer_left (hL : 0 < L) {χv : ℓ2} {S B : Finset Z2} (hl : IsLayer L χv S B)
    (v : ℓ2) :
    inner ℂ (Lc L (trunc S v)) (Lc L (mulH L χv (v - trunc S v))) =
      inner ℂ (Lc L (trunc B v)) (Lc L (mulH L χv (v - trunc S v))) := by
  rw [inner_Lc, inner_Lc]
  refine tsum_congr fun k => ?_
  rw [co_trunc, co_trunc]
  by_cases hkB : k ∈ B
  · rw [if_pos (hl.1 hkB), if_pos hkB]
  · rw [if_neg hkB]
    by_cases hkS : k ∈ S
    · rw [if_pos hkS]
      have h0 : co L (mulH L χv (v - trunc S v)) k = 0 := by
        apply co_mulH_eq_zero hL
        intro j
        rw [co_sub, Pi.sub_apply, co_trunc]
        by_cases hjS : j ∈ S
        · rw [if_pos hjS, sub_self, mul_zero]
        · rw [(hl.2 k j hkS hkB hjS).1, zero_mul]
      rw [h0, mul_zero, mul_zero]
    · rw [if_neg hkS]

theorem inner_layer_right (hL : 0 < L) {χv : ℓ2} {S B : Finset Z2} (hl : IsLayer L χv S B)
    (v : ℓ2) :
    inner ℂ (Lc L (v - trunc S v)) (Lc L (mulH L χv (trunc S v))) =
      inner ℂ (Lc L (v - trunc S v)) (Lc L (mulH L χv (trunc B v))) := by
  rw [inner_Lc, inner_Lc]
  refine tsum_congr fun k => ?_
  by_cases hkS : k ∈ S
  · have h0 : co L (v - trunc S v) k = 0 := by
      rw [co_sub, Pi.sub_apply, co_trunc, if_pos hkS, sub_self]
    rw [h0, map_zero, zero_mul, zero_mul]
  · congr 1
    apply co_mulH_congr hL
    intro j
    rw [co_trunc, co_trunc]
    by_cases hjB : j ∈ B
    · rw [if_pos (hl.1 hjB), if_pos hjB]
    · rw [if_neg hjB]
      by_cases hjS : j ∈ S
      · rw [if_pos hjS, (hl.2 j k hjS hjB hkS).2, zero_mul, zero_mul]
      · rw [if_neg hjS]

/-- **Exact splitting of the detector change under truncation.** -/
theorem detector_split (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv)
    {S B : Finset Z2} (hl : IsLayer L χv S B) (v : ℓ2) :
    Jdet L χv v - Jdet L χv (trunc S v) =
      (inner ℂ (Lc L (v - trunc S v)) (Lc L (mulH L χv (v - trunc S v))) +
        inner ℂ (Lc L (v - trunc S v)) (Lc L (mulH L χv (trunc B v))) +
        inner ℂ (Lc L (trunc B v)) (Lc L (mulH L χv (v - trunc S v)))).re := by
  rw [Jdet_eq_re hL hreal, Jdet_eq_re hL hreal, ← Complex.sub_re]
  congr 1
  rw [← inner_layer_left hL hl v, ← inner_layer_right hL hl v]
  obtain ⟨w, hw⟩ : ∃ w, w = trunc S v := ⟨_, rfl⟩
  rw [← hw]
  obtain ⟨t, ht⟩ : ∃ t, t = v - w := ⟨_, rfl⟩
  rw [← ht]
  have hv : v = t + w := by rw [ht]; abel
  rw [hv, map_add, mulH_add_right hL, map_add, inner_add_left, inner_add_right, inner_add_right]
  ring

/-- **Quadratic layer bound**: `|J(v) − J(P_S v)| ≤ C_det ‖t‖ (‖t‖ + 2‖b‖)`. -/
theorem detector_layer_bound (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv)
    {S B : Finset Z2} (hl : IsLayer L χv S B) (v : ℓ2) :
    |Jdet L χv v - Jdet L χv (trunc S v)| ≤
      Cdet L χv * ‖v - trunc S v‖ * (‖v - trunc S v‖ + 2 * ‖trunc B v‖) := by
  rw [detector_split hL hreal hl v]
  have hC := Cdet_nonneg hL χv
  have hm : ∀ δ, ‖Lc L (mulH L χv δ)‖ ≤ Cdet L χv * ‖δ‖ := fun δ =>
    (norm_Lc_mulH_le hL χv δ).trans (mul_le_mul_of_nonneg_left (norm_Lc_le L δ) hC)
  have ht := norm_Lc_le L (v - trunc S v)
  have hb := norm_Lc_le L (trunc B v)
  have e1 : ‖inner ℂ (Lc L (v - trunc S v)) (Lc L (mulH L χv (v - trunc S v)))‖ ≤
      ‖v - trunc S v‖ * (Cdet L χv * ‖v - trunc S v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul ht (hm _) (norm_nonneg _) (norm_nonneg _))
  have e2 : ‖inner ℂ (Lc L (v - trunc S v)) (Lc L (mulH L χv (trunc B v)))‖ ≤
      ‖v - trunc S v‖ * (Cdet L χv * ‖trunc B v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul ht (hm _) (norm_nonneg _) (norm_nonneg _))
  have e3 : ‖inner ℂ (Lc L (trunc B v)) (Lc L (mulH L χv (v - trunc S v)))‖ ≤
      ‖trunc B v‖ * (Cdet L χv * ‖v - trunc S v‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hb (hm _) (norm_nonneg _) (norm_nonneg _))
  refine (Complex.abs_re_le_norm _).trans ?_
  refine ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans ?_
  calc _ ≤ ‖v - trunc S v‖ * (Cdet L χv * ‖v - trunc S v‖) +
        ‖v - trunc S v‖ * (Cdet L χv * ‖trunc B v‖) +
        ‖trunc B v‖ * (Cdet L χv * ‖v - trunc S v‖) := add_le_add (add_le_add e1 e2) e3
    _ = _ := by ring

/-- A truncation to large modes is small in the analytic norm. -/
theorem layer_le {σ M : ℝ} (hσ : 0 ≤ σ) {v : ℓ2} (hv : ASum σ v) (B : Finset Z2)
    (hB : ∀ k ∈ B, M ≤ size k) :
    ‖trunc B v‖ ^ 2 ≤ Real.exp (-(2 * σ * M)) * asq σ v := by
  rw [norm_sq_eq]
  have hpt : ∀ k, ‖trunc B v k‖ ^ 2 ≤ Real.exp (-(2 * σ * M)) * (aw σ k * ‖v k‖) ^ 2 := by
    intro k
    rw [trunc_apply]
    split_ifs with hk
    · have e : (aw σ k * ‖v k‖) ^ 2 = Real.exp (2 * σ * size k) * ‖v k‖ ^ 2 := by
        rw [aw, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
      rw [e, ← mul_assoc, ← Real.exp_add]
      have h1 : 1 ≤ Real.exp (-(2 * σ * M) + 2 * σ * size k) :=
        Real.one_le_exp (by nlinarith [hB k hk])
      nlinarith [sq_nonneg ‖v k‖]
    · rw [norm_zero, zero_pow two_ne_zero]; positivity
  calc ∑' k, ‖trunc B v k‖ ^ 2 ≤ ∑' k, Real.exp (-(2 * σ * M)) * (aw σ k * ‖v k‖) ^ 2 :=
        (summable_sq _).tsum_le_tsum hpt (hv.mul_left _)
    _ = Real.exp (-(2 * σ * M)) * asq σ v := by rw [tsum_mul_left]; rfl

/-- **Static detector-specific bound.** If every mode outside `S` has size `≥ N` and every layer
mode has size `≥ N − r`, the detector error of truncation is
`≤ C_det e^{−σN} (e^{−σN} + 2e^{−σ(N−r)}) A_σ(v)²`. -/
theorem detector_static_quadratic (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv)
    {S B : Finset Z2} (hl : IsLayer L χv S B) {σ N r : ℝ} (hσ : 0 ≤ σ)
    (hS : ∀ k ∉ S, N ≤ size k) (hB : ∀ k ∈ B, N - r ≤ size k) {v : ℓ2} (hv : ASum σ v) :
    |Jdet L χv v - Jdet L χv (trunc S v)| ≤
      Cdet L χv * Real.exp (-(σ * N)) * (Real.exp (-(σ * N)) + 2 * Real.exp (-(σ * (N - r)))) *
        asq σ v := by
  have h := detector_layer_bound hL hreal hl v
  have hA := anorm_nonneg σ v
  have ht : ‖v - trunc S v‖ ≤ Real.exp (-(σ * N)) * anorm σ v := by
    have h2 := tail_le hσ hv S hS
    rw [norm_sub_rev] at h2
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hA), mul_pow, anorm_sq,
      ← Real.exp_nat_mul]
    convert h2 using 3
    push_cast; ring
  have hb : ‖trunc B v‖ ≤ Real.exp (-(σ * (N - r))) * anorm σ v := by
    have h2 := layer_le hσ hv B hB
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hA), mul_pow, anorm_sq,
      ← Real.exp_nat_mul]
    convert h2 using 3
    push_cast; ring
  have hC := Cdet_nonneg hL χv
  calc |Jdet L χv v - Jdet L χv (trunc S v)|
      ≤ Cdet L χv * ‖v - trunc S v‖ * (‖v - trunc S v‖ + 2 * ‖trunc B v‖) := h
    _ ≤ Cdet L χv * (Real.exp (-(σ * N)) * anorm σ v) *
        (Real.exp (-(σ * N)) * anorm σ v + 2 * (Real.exp (-(σ * (N - r))) * anorm σ v)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ht hC) (by linarith) (by positivity)
          (mul_nonneg hC (mul_nonneg (Real.exp_pos _).le hA))
    _ = _ := by rw [← anorm_sq]; ring

section Layer

open scoped Classical

/-- The boundary layer of `S` at bandwidth `r`: modes of `S` within size `r` of a mode
outside `S`. -/
noncomputable def layer (S : Finset Z2) (r : ℝ) : Finset Z2 :=
  S.filter fun k => ∃ j, j ∉ S ∧ size (k - j) ≤ r

theorem size_sub_comm (k j : Z2) : size (j - k) = size (k - j) := by
  rw [← size_neg, neg_sub]

theorem isLayer_of_band {χv : ℓ2} {r : ℝ} (hband : ∀ m, co L χv m ≠ 0 → size m ≤ r)
    (S : Finset Z2) : IsLayer L χv S (layer S r) := by
  refine ⟨Finset.filter_subset _ _, fun k j hk hkB hj => ?_⟩
  have hfar : r < size (k - j) := by
    by_contra h
    push_neg at h
    exact hkB (Finset.mem_filter.2 ⟨hk, j, hj, h⟩)
  constructor
  · by_contra h
    exact absurd (hband _ h) (not_le.2 hfar)
  · by_contra h
    exact absurd (hband _ h) (by rw [size_sub_comm]; exact not_le.2 hfar)

theorem layer_size {S : Finset Z2} {N r : ℝ} (hS : ∀ k ∉ S, N ≤ size k) :
    ∀ k ∈ layer S r, N - r ≤ size k := by
  intro k hk
  obtain ⟨_, j, hj, hjr⟩ := Finset.mem_filter.1 hk
  have h1 := hS j hj
  have h2 := size_add_le k (j - k)
  have e : k + (j - k) = j := by abel
  rw [e, size_sub_comm] at h2
  linarith

end Layer

/-- **Detector-specific truncation bound at bandwidth `r`.** For a real detector whose
coefficients vanish outside `size ≤ r`, and a truncation set `S` whose complement has
`size ≥ N`, `|J(v) − J(P_S v)| ≤ 3 C_det e^{σr} e^{−2σN} A_σ(v)²`. -/
theorem detector_band_quadratic (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv)
    {r : ℝ} (hr : 0 ≤ r) (hband : ∀ m, co L χv m ≠ 0 → size m ≤ r) {σ N : ℝ} (hσ : 0 ≤ σ)
    (S : Finset Z2) (hS : ∀ k ∉ S, N ≤ size k) {v : ℓ2} (hv : ASum σ v) :
    |Jdet L χv v - Jdet L χv (trunc S v)| ≤
      3 * Cdet L χv * Real.exp (σ * r) * Real.exp (-(2 * σ * N)) * asq σ v := by
  have h := detector_static_quadratic hL hreal (isLayer_of_band hband S) hσ hS
    (layer_size hS) hv
  have e1 : Real.exp (-(σ * N)) ≤ Real.exp (-(σ * (N - r))) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg hσ hr])
  have e2 : Real.exp (-(σ * N)) * Real.exp (-(σ * (N - r))) =
      Real.exp (σ * r) * Real.exp (-(2 * σ * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hC := Cdet_nonneg hL χv
  have hA := asq_nonneg σ v
  calc _ ≤ _ := h
    _ ≤ Cdet L χv * Real.exp (-(σ * N)) * (3 * Real.exp (-(σ * (N - r)))) * asq σ v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC (Real.exp_pos _).le)) hA
    _ = 3 * Cdet L χv * (Real.exp (-(σ * N)) * Real.exp (-(σ * (N - r)))) * asq σ v := by ring
    _ = _ := by rw [e2]; ring

/-- The SAT device's detector has bandwidth `1`. -/
theorem device_band (L : ℝ) : ∀ m, co L (WCTSATDevice.detector L) m ≠ 0 → size m ≤ 1 := by
  intro m hm
  rw [WCTSATDevice.co_detector] at hm
  by_cases h0 : m = 0
  · subst h0; simp [size]
  by_cases h1 : m = WCTSATDevice.e1v
  · subst h1; simp [size, WCTSATDevice.e1v]
  by_cases h2 : m = -WCTSATDevice.e1v
  · subst h2; simp [size, WCTSATDevice.e1v]
  exact absurd (WCTSATDevice.dco_eq_zero h0 h1 h2) hm

theorem device_real (L : ℝ) :
    rev (co L (WCTSATDevice.detector L)) = co L (WCTSATDevice.detector L) := by
  rw [WCTSATDevice.co_detector]; exact WCTSATDevice.rev_dco

/-- **The SAT device's detector sees the tail quadratically.** -/
theorem device_detector_quadratic (hL : 0 < L) {σ N : ℝ} (hσ : 0 ≤ σ) (S : Finset Z2)
    (hS : ∀ k ∉ S, N ≤ size k) {v : ℓ2} (hv : ASum σ v) :
    |Jdet L (WCTSATDevice.detector L) v - Jdet L (WCTSATDevice.detector L) (trunc S v)| ≤
      3 * Cdet L (WCTSATDevice.detector L) * Real.exp σ * Real.exp (-(2 * σ * N)) * asq σ v := by
  have h := detector_band_quadratic hL (device_real L) zero_le_one (device_band L) hσ S hS hv
  rwa [mul_one] at h

end PVNP.DetectorQuadratic
