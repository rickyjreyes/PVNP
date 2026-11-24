import PVNP.CertifiedIntegrator

/-!
# Effective weak-norm approximation for the actual detector

The H² ball has no uniform H² Fourier cutoff. In the physical L² norm
represented by Lc, the same ball has an explicit cutoff rate, and the
actual quadratic detector and polynomial nonlinearity are Lipschitz
on that ball in L². This avoids a stronger regularity hypothesis for
the spatial tail, but does not remove radius or stability costs.
-/

open Complex
namespace PVNP.TorusGalerkin
open PVNP.Torus PVNP.ContinuumPrecision

theorem weak_projection_tail (L : ℝ) (S : Finset Z2) (v : ℓ2) {K : ℝ}
    (hK : 0 < K) (hcut : ∀ k ∉ S, K ≤ wt L k) :
    ‖Lc L (trunc S v - v)‖ ≤ ‖v‖ / K := by
  have hp : ∀ k : Z2, ‖Lc L (trunc S v - v) k‖ ^ 2 ≤
      (K⁻¹)^2 * ‖v k‖ ^ 2 := by
    intro k
    rw [Lc_apply, norm_co, lp.coeFn_sub, Pi.sub_apply, trunc_apply]
    by_cases hk : k ∈ S
    · simp [hk]
      positivity
    · rw [if_neg hk, zero_sub, norm_neg]
      have hi : (wt L k)⁻¹ ≤ K⁻¹ :=
        inv_le_inv_of_le hK (hcut k hk)
      have hd : ‖v k‖ / wt L k ≤ K⁻¹ * ‖v k‖ := by
        rw [div_eq_mul_inv, mul_comm (‖v k‖)]
        exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
      exact (pow_le_pow_left₀ (by positivity) hd 2).trans_eq (by ring)
  have h := tsum_le_tsum hp (summable_sq _) ((summable_sq v).mul_left ((K⁻¹)^2))
  rw [tsum_mul_left, ← norm_sq_eq v] at h
  apply norm_le_of_tsum_sq_le _ (by positivity)
  simpa only [div_eq_mul_inv, mul_pow, mul_comm] using h

/-- The existing physical detector needs only L² closeness, with no
H² closeness required. -/
theorem weak_detector_lipschitz (hL : 0 < L) {χ : ℓ2}
    (hreal : rev (co L χ) = co L χ) (v w : ℓ2) :
    |Jdet L χ v - Jdet L χ w| ≤
      Cdet L χ * (‖Lc L v‖ + ‖Lc L w‖) * ‖Lc L (v-w)‖ := by
  rw [Jdet_eq_re hL hreal, Jdet_eq_re hL hreal, ← Complex.sub_re]
  have e : inner ℂ (Lc L v) (Lc L (mulH L χ v)) - inner ℂ (Lc L w) (Lc L (mulH L χ w)) =
      inner ℂ (Lc L (v - w)) (Lc L (mulH L χ v)) +
        inner ℂ (Lc L w) (Lc L (mulH L χ (v - w))) := by
    rw [mulH_sub_right hL, map_sub, map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [e]
  have h1 : ‖Lc L (mulH L χ v)‖ ≤ Cdet L χ * ‖Lc L v‖ :=
    norm_Lc_mulH_le hL χ v
  have h2 : ‖Lc L (mulH L χ (v-w))‖ ≤ Cdet L χ * ‖Lc L (v-w)‖ :=
    norm_Lc_mulH_le hL χ (v-w)
  calc
    _ ≤ ‖inner ℂ (Lc L (v - w)) (Lc L (mulH L χ v)) +
          inner ℂ (Lc L w) (Lc L (mulH L χ (v - w)))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (Lc L (v - w)) (Lc L (mulH L χ v))‖ +
          ‖inner ℂ (Lc L w) (Lc L (mulH L χ (v - w)))‖ := norm_add_le _ _
    _ ≤ ‖Lc L (v - w)‖ * ‖Lc L (mulH L χ v)‖ +
          ‖Lc L w‖ * ‖Lc L (mulH L χ (v - w))‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖Lc L (v-w)‖ * (Cdet L χ * ‖Lc L v‖) +
          ‖Lc L w‖ * (Cdet L χ * ‖Lc L (v-w)‖) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    _ = _ := by ring

theorem weak_detector_cutoff (hL : 0 < L) {χ : ℓ2}
    (hreal : rev (co L χ) = co L χ) (S : Finset Z2) (v : ℓ2)
    {K : ℝ} (hK : 0 < K) (hcut : ∀ k ∉ S, K ≤ wt L k) :
    |Jdet L χ (trunc S v) - Jdet L χ v| ≤
      Cdet L χ * (2 * ‖v‖) * (‖v‖ / K) := by
  have h := weak_detector_lipschitz hL hreal (trunc S v) v
  have h1 := (norm_Lc_le L (trunc S v)).trans (trunc_norm_le S v)
  have h2 := norm_Lc_le L v
  have h3 := weak_projection_tail L S v hK hcut
  have hC := Cdet_nonneg hL χ
  have hsum : ‖Lc L (trunc S v)‖ + ‖Lc L v‖ ≤ 2 * ‖v‖ := by linarith
  exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left hsum hC) h3
    (norm_nonneg _) (by positivity))

theorem weak_mulH_comm (hL : 0 < L) (v w : ℓ2) : mulH L v w = mulH L w v := by
  have hc : co L (mulH L v w) = co L (mulH L w v) := by
    apply coeff_unique hL (L1_co' hL _) (L1_co' hL _)
    funext x
    rw [field_mulH hL, field_mulH hL, mul_comm]
  ext k
  rw [← wt_mul_co L (mulH L v w) k, ← wt_mul_co L (mulH L w v) k, hc]

theorem weak_mul_bound (hL : 0 < L) (v w : ℓ2) :
    ‖Lc L (mulH L v w)‖ ≤ CA L * ‖v‖ * ‖Lc L w‖ := by
  have h := norm_Lc_mulH_le hL v w
  have hs := tsum_norm_co_le hL v
  have hC : L⁻¹ * (∑' j, ‖co L v j‖) ≤ CA L * ‖v‖ := by
    calc
      _ ≤ L⁻¹ * (Real.sqrt (SL L) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hL.le)
      _ = (CA L / 4) * ‖v‖ := by unfold CA; ring
      _ ≤ CA L * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith [CA_nonneg hL]) (norm_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

theorem weak_conj_norm (L : ℝ) (v : ℓ2) : ‖Lc L (conjH v)‖ = ‖Lc L v‖ := by
  have h : ∑' k, ‖co L (conjH v) k‖ ^ 2 = ∑' k, ‖co L v k‖ ^ 2 := by
    simp only [co_conjH, rev, Complex.norm_conj]
    exact (Equiv.neg Z2).tsum_eq (fun k => ‖co L v k‖ ^ 2)
  have hs : ‖Lc L (conjH v)‖ ^ 2 = ‖Lc L v‖ ^ 2 := by
    rw [norm_sq_Lc, norm_sq_Lc, h]
  nlinarith [norm_nonneg (Lc L (conjH v)), norm_nonneg (Lc L v)]

theorem weak_lip_mul {L : ℝ} (hL : 0 < L) {X Y X' Y' : ℓ2}
    {d a A b B : ℝ} (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : ‖Lc L (X-X')‖ ≤ a*d) (hY' : ‖Y'‖ ≤ B)
    (hY : ‖Lc L (Y-Y')‖ ≤ b*d) (hX' : ‖X‖ ≤ A) :
    ‖Lc L (mulH L X Y - mulH L X' Y')‖ ≤ CA L * (a*B + A*b)*d := by
  have e : mulH L X Y - mulH L X' Y' =
      mulH L (X-X') Y' + mulH L X (Y-Y') := by
    rw [mulH_sub_left hL, mulH_sub_right hL]; abel
  rw [e, map_add]
  have h1 := weak_mul_bound hL Y' (X-X')
  rw [weak_mulH_comm hL Y' (X-X')] at h1
  have h2 := weak_mul_bound hL X (Y-Y')
  have hc := CA_nonneg hL
  calc
    _ ≤ ‖Lc L (mulH L (X-X') Y')‖ + ‖Lc L (mulH L X (Y-Y'))‖ := norm_add_le _ _
    _ ≤ CA L * ‖Y'‖ * ‖Lc L (X-X')‖ + CA L * ‖X‖ * ‖Lc L (Y-Y')‖ :=
      add_le_add h1 h2
    _ ≤ CA L * B * (a*d) + CA L * A * (b*d) := by gcongr
    _ = _ := by ring

theorem weak_Fnl_sub_le (hL : 0 < L) (β γ : ℝ) {u v : ℓ2} {R : ℝ} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖Lc L (Fnl L β γ u - Fnl L β γ v)‖ ≤ LF L β γ R * ‖Lc L (u - v)‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hu
  have hc := CA_nonneg hL
  set d := ‖Lc L (u - v)‖
  set C := CA L
  have hcu : ‖conjH u‖ ≤ R := by rw [norm_conjH]; exact hu
  have hcv : ‖conjH v‖ ≤ R := by rw [norm_conjH]; exact hv
  have hcd : ‖Lc L (conjH u - conjH v)‖ ≤ 1 * d := by rw [← conjH_sub, weak_conj_norm, one_mul]
  have hd : ‖Lc L (u - v)‖ ≤ 1 * d := by rw [one_mul]
  -- P2 = u u
  have p2 : ‖Lc L (mulH L u u - mulH L v v)‖ ≤ C * (1 * R + R * 1) * d := weak_lip_mul hL (norm_nonneg _) zero_le_one hR hd hv hd hu
  have b2u : ‖mulH L u u‖ ≤ C * R * R := norm_mulH_le' hL hu hu
  have b2v : ‖mulH L v v‖ ≤ C * R * R := norm_mulH_le' hL hv hv
  -- cubic
  have p3 : ‖Lc L (mulH L (mulH L u u) (conjH u) - mulH L (mulH L v v) (conjH v))‖ ≤
      C * (C * (1 * R + R * 1) * R + C * R * R * 1) * d :=
    weak_lip_mul hL (norm_nonneg _) (by positivity) (by positivity) p2 b2v hcd hcu
  -- quintic chain
  have q3 : ‖Lc L (mulH L (mulH L u u) u - mulH L (mulH L v v) v)‖ ≤
      C * (C * (1 * R + R * 1) * R + C * R * R * 1) * d :=
    weak_lip_mul hL (norm_nonneg _) (by positivity) (by positivity) p2 b2v hd hu
  have b3u : ‖mulH L (mulH L u u) u‖ ≤ C * (C * R * R) * R := norm_mulH_le' hL b2u hu
  have b3v : ‖mulH L (mulH L v v) v‖ ≤ C * (C * R * R) * R := norm_mulH_le' hL b2v hv
  have q4 : ‖Lc L (mulH L (mulH L (mulH L u u) u) (conjH u) -
      mulH L (mulH L (mulH L v v) v) (conjH v))‖ ≤
      C * (C * (C * (1 * R + R * 1) * R + C * R * R * 1) * R + C * (C * R * R) * R * 1) * d :=
    weak_lip_mul hL (norm_nonneg _) (by positivity) (by positivity) q3 b3v hcd hcu
  have b4v : ‖mulH L (mulH L (mulH L v v) v) (conjH v)‖ ≤ C * (C * (C * R * R) * R) * R :=
    norm_mulH_le' hL b3v hcv
  have b4u : ‖mulH L (mulH L (mulH L u u) u) (conjH u)‖ ≤ C * (C * (C * R * R) * R) * R :=
    norm_mulH_le' hL b3u hcu
  have q5 : ‖Lc L (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u) -
      mulH L (mulH L (mulH L (mulH L v v) v) (conjH v)) (conjH v))‖ ≤
      C * (C * (C * (C * (1 * R + R * 1) * R + C * R * R * 1) * R + C * (C * R * R) * R * 1) * R +
        C * (C * (C * R * R) * R) * R * 1) * d :=
    weak_lip_mul hL (norm_nonneg _) (by positivity) (by positivity) q4 b4v hcd hcu
  have e : Fnl L β γ u - Fnl L β γ v =
      (-(β : ℂ)) • (mulH L (mulH L u u) (conjH u) - mulH L (mulH L v v) (conjH v)) +
      (γ : ℂ) • (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u) -
        mulH L (mulH L (mulH L (mulH L v v) v) (conjH v)) (conjH v)) := by
    unfold Fnl; rw [smul_sub, smul_sub]; abel
  rw [e, map_add, map_smul, map_smul]
  have hd0 : 0 ≤ d := norm_nonneg _
  calc _ ≤ ‖(-(β : ℂ)) • Lc L (mulH L (mulH L u u) (conjH u) - mulH L (mulH L v v) (conjH v))‖ +
        ‖(γ : ℂ) • Lc L (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u) -
          mulH L (mulH L (mulH L (mulH L v v) v) (conjH v)) (conjH v))‖ := norm_add_le _ _
    _ = |β| * ‖Lc L (mulH L (mulH L u u) (conjH u) - mulH L (mulH L v v) (conjH v))‖ +
        |γ| * ‖Lc L (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u) -
          mulH L (mulH L (mulH L (mulH L v v) v) (conjH v)) (conjH v))‖ := by
        rw [norm_smul, norm_smul, norm_neg, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |β| * (C * (C * (1 * R + R * 1) * R + C * R * R * 1) * d) +
        |γ| * (C * (C * (C * (C * (1 * R + R * 1) * R + C * R * R * 1) * R +
          C * (C * R * R) * R * 1) * R + C * (C * (C * R * R) * R) * R * 1) * d) := by
        gcongr
    _ = LF L β γ R * d := by unfold LF; ring


theorem weak_Gf_sub_le {L κ β γ R : ℝ} (hL : 0 < L) (t : ℝ)
    {a b : ℓ2} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Lc L (Gf L κ β γ t a - Gf L κ β γ t b)‖ ≤
      LF L β γ R * ‖Lc L (a-b)‖ := by
  have h := weak_Fnl_sub_le hL β γ
    (u := U L κ t a) (v := U L κ t b) (R := R)
    (by rwa [norm_U]) (by rwa [norm_U])
  rw [← map_sub, Lc_U, norm_U] at h
  rw [Gf, Gf, ← smul_sub, ← map_sub, map_smul, norm_smul, norm_neg,
    Complex.norm_I, one_mul, Lc_U, norm_U]
  exact h

end PVNP.TorusGalerkin
