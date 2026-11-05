import PVNP.TorusNonlin

/-!
# The cubic–quintic flow on `H²(T_L²)`: conservation laws and global existence

The Cauchy problem `i∂ₜψ = (Δ+κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ` on the torus `T_L²` is solved in the
interaction picture `w(t) = U(−t) ψ(t)`, `w' = G(t, w) = −i U(−t) F(U(t) w)` (`Gf`).  The
architecture (radial retraction, Picard–Lindelöf on every `[−T, T]`, conservation, clopen
argument) is adapted from `rickyjreyes/math@30a5ddc`, `MathProofs/CubicQuinticFlow.lean`
(whole-plane `H²(ℝ²)`), with the Fourier transform replaced by Fourier series on the torus; no
external theorem is imported.

* `hasDerivAt_mass`: `d/dt ‖ψ(t)‖²_{L²} = 0`;
* `hasDerivAt_ham`: `d/dt H(ψ(t)) = 0` for `H = ‖(Δ+κ)ψ‖² + ∫(−β/2|ψ|⁴ + γ/3|ψ|⁶)`;
  the potential is differentiated along `U(s) w(s)` with the weak generator
  (`hasDerivAt_pot_U`, `tendsto_Qh`, `tendsto_norm_sq_div`);
* `norm_le_apriori`: the **a priori bound** `‖ψ‖_{H²} ≤ (1 + |κ|)√M + √(H + 3β²M/(16γ))`,
  uniform in `L`;
* `exists_global`: global existence for every `w₀ ∈ ℓ²` (`γ > 0`); `ode_unique`: uniqueness;
  `ode_dist_le`: the Gronwall estimate behind continuous dependence.
-/

open Complex Set Filter Topology InnerProductSpace
open scoped Real ENNReal NNReal

namespace PVNP.Torus

variable {L κ β γ : ℝ}

attribute [local irreducible] U Fnl

/-! ### Inner products -/

theorem inner_U (L κ t : ℝ) (x y : ℓ2) : inner ℂ (U L κ t x) (U L κ t y) = inner ℂ x y := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [U_apply, RCLike.inner_apply, map_mul]
  have h : (starRingEnd ℂ) (ph L κ t k) * ph L κ t k = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ph]; simp
  linear_combination (y k * (starRingEnd ℂ) (x k)) * h

theorem inner_U_neg (L κ t : ℝ) (x y : ℓ2) :
    inner ℂ x (U L κ (-t) y) = inner ℂ (U L κ t x) y := by
  rw [← inner_U L κ t x (U L κ (-t) y), U_U_neg]

theorem inner_Lc (L : ℝ) (f g : ℓ2) :
    inner ℂ (Lc L f) (Lc L g) = ∑' k, (starRingEnd ℂ) (co L f k) * co L g k := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  rw [Lc_apply, Lc_apply, RCLike.inner_apply, mul_comm]

theorem inner_Ac (L κ : ℝ) (f g : ℓ2) :
    inner ℂ (Ac L κ f) (Ac L κ g) =
      ∑' k, (om L κ k : ℂ) * ((starRingEnd ℂ) (co L f k) * co L g k) := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  rw [Ac_apply, Ac_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal, om]
  push_cast
  ring

theorem re_neg_I_mul (z : ℂ) : (-I * z).re = z.im := by simp [Complex.mul_re]

theorem real_inner_eq (x y : ℓ2) : (inner ℝ x y : ℝ) = (inner ℂ x y).re := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner x y)]
  refine tsum_congr fun k => ?_
  exact real_inner_eq_re_inner ℂ (x k) (y k)

/-! ### The interaction-picture vector field -/

/-- The interaction-picture vector field `G(t, w) = −i U(−t) F(U(t) w)`. -/
noncomputable def Gf (L κ β γ : ℝ) (t : ℝ) (w : ℓ2) : ℓ2 :=
  (-I) • U L κ (-t) (Fnl L β γ (U L κ t w))

theorem U_Gf (t : ℝ) (w : ℓ2) : U L κ t (Gf L κ β γ t w) = (-I) • Fnl L β γ (U L κ t w) := by
  rw [Gf, map_smul, U_U_neg]

theorem Gf_zero (hL : 0 < L) (t : ℝ) : Gf L κ β γ t 0 = 0 := by
  rw [Gf, map_zero, Fnl_zero hL, map_zero, smul_zero]

theorem norm_Gf_sub_le (hL : 0 < L) {R : ℝ} (t : ℝ) {a b : ℓ2} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Gf L κ β γ t a - Gf L κ β γ t b‖ ≤ LF L β γ R * ‖a - b‖ := by
  have h := norm_Fnl_sub_le hL β γ (u := U L κ t a) (v := U L κ t b) (R := R)
    (by rwa [norm_U]) (by rwa [norm_U])
  rw [← map_sub, norm_U] at h
  rw [Gf, Gf, ← smul_sub, ← map_sub, norm_smul, norm_neg, Complex.norm_I, one_mul, norm_U]
  exact h

theorem norm_Gf_le (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) {a : ℓ2} (ha : ‖a‖ ≤ R) :
    ‖Gf L κ β γ t a‖ ≤ LF L β γ R * R := by
  have h0 : ‖(0 : ℓ2)‖ ≤ R := by rw [norm_zero]; exact hR
  have h := norm_Gf_sub_le (κ := κ) (β := β) (γ := γ) hL t ha h0
  rw [Gf_zero hL, sub_zero, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left ha (LF_nonneg L β γ R))

theorem continuous_Gf (hL : 0 < L) : Continuous fun p : ℝ × ℓ2 => Gf L κ β γ p.1 p.2 := by
  have h1 : Continuous fun p : ℝ × ℓ2 => Fnl L β γ (U L κ p.1 p.2) :=
    (continuous_Fnl hL β γ).comp (continuous_U_uncurry L κ)
  have h3 : Continuous fun p : ℝ × ℓ2 => ((-p.1, Fnl L β γ (U L κ p.1 p.2)) : ℝ × ℓ2) :=
    continuous_fst.neg.prodMk h1
  have h2 : Continuous fun p : ℝ × ℓ2 => U L κ (-p.1) (Fnl L β γ (U L κ p.1 p.2)) :=
    (continuous_U_uncurry L κ).comp h3
  exact h2.const_smul (-I)

theorem lipschitzOnWith_Gf (hL : 0 < L) {R : ℝ} (t : ℝ) :
    LipschitzOnWith ⟨LF L β γ R, LF_nonneg L β γ R⟩ (Gf L κ β γ t) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at ha hb
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_Gf_sub_le hL t ha hb

/-! ### Radial retraction and the truncated equation -/

/-- The radial retraction onto the closed ball of radius `R`. -/
noncomputable def retr (R : ℝ) (x : ℓ2) : ℓ2 :=
  if ‖x‖ ≤ R then x else ((R / ‖x‖ : ℝ) : ℂ) • x

theorem retr_of_le {R : ℝ} {x : ℓ2} (h : ‖x‖ ≤ R) : retr R x = x := if_pos h

theorem retr_of_lt {R : ℝ} {x : ℓ2} (h : R < ‖x‖) : retr R x = ((R / ‖x‖ : ℝ) : ℂ) • x :=
  if_neg (not_le.2 h)

theorem norm_ofReal_smul {c : ℝ} (hc : 0 ≤ c) (x : ℓ2) : ‖((c : ℝ) : ℂ) • x‖ = c * ‖x‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

theorem norm_retr_le {R : ℝ} (hR : 0 ≤ R) (x : ℓ2) : ‖retr R x‖ ≤ R := by
  rcases le_or_gt ‖x‖ R with h | h
  · rw [retr_of_le h]; exact h
  · have hx : 0 < ‖x‖ := lt_of_le_of_lt hR h
    rw [retr_of_lt h, norm_ofReal_smul (div_nonneg hR hx.le), div_mul_cancel₀ _ hx.ne']

theorem norm_retr_sub_aux {R : ℝ} (hR : 0 ≤ R) {x y : ℓ2} (hx : ‖x‖ ≤ R) (hy : R < ‖y‖) :
    ‖x - ((R / ‖y‖ : ℝ) : ℂ) • y‖ ≤ 2 * ‖x - y‖ := by
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt hR hy
  have hc : R / ‖y‖ ≤ 1 := (div_le_one hy0).2 hy.le
  have e : y - ((R / ‖y‖ : ℝ) : ℂ) • y = ((1 - R / ‖y‖ : ℝ) : ℂ) • y := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have h1 : ‖y - ((R / ‖y‖ : ℝ) : ℂ) • y‖ = ‖y‖ - R := by
    rw [e, norm_ofReal_smul (by linarith), sub_mul, one_mul, div_mul_cancel₀ _ hy0.ne']
  have h2 : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le y x
  calc ‖x - ((R / ‖y‖ : ℝ) : ℂ) • y‖ ≤ ‖x - y‖ + ‖y - ((R / ‖y‖ : ℝ) : ℂ) • y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖x - y‖ := by rw [h1]; linarith

theorem retr_arith {R a b d : ℝ} (hR : 0 ≤ R) (ha : R < a) (hb : R < b) (hd : |a - b| ≤ d) :
    R / a * d + |R / a - R / b| * b ≤ 2 * d := by
  have ha0 : 0 < a := lt_of_le_of_lt hR ha
  have hb0 : 0 < b := lt_of_le_of_lt hR hb
  have hc : 0 ≤ R / a := div_nonneg hR ha0.le
  have hc1 : R / a ≤ 1 := (div_le_one ha0).2 ha.le
  have e1 : |R / a - R / b| * b = |(R / a - R / b) * b| := by rw [abs_mul, abs_of_pos hb0]
  have e2 : (R / a - R / b) * b = R / a * (b - a) := by field_simp
  have h1 : |R / a - R / b| * b = R / a * |a - b| := by
    rw [e1, e2, abs_mul, abs_of_nonneg hc, abs_sub_comm]
  rw [h1]
  calc R / a * d + R / a * |a - b| ≤ R / a * d + R / a * d := by gcongr
    _ = R / a * (2 * d) := by ring
    _ ≤ 1 * (2 * d) := by gcongr; linarith [abs_nonneg (a - b)]
    _ = 2 * d := one_mul _

/-- The retraction is `2`-Lipschitz. -/
theorem norm_retr_sub_le {R : ℝ} (hR : 0 ≤ R) (x y : ℓ2) :
    ‖retr R x - retr R y‖ ≤ 2 * ‖x - y‖ := by
  rcases le_or_gt ‖x‖ R with hx | hx <;> rcases le_or_gt ‖y‖ R with hy | hy
  · rw [retr_of_le hx, retr_of_le hy]; linarith [norm_nonneg (x - y)]
  · rw [retr_of_le hx, retr_of_lt hy]; exact norm_retr_sub_aux hR hx hy
  · rw [retr_of_lt hx, retr_of_le hy, norm_sub_rev, norm_sub_rev x y]
    exact norm_retr_sub_aux hR hy hx
  · rw [retr_of_lt hx, retr_of_lt hy]
    have hx0 : 0 < ‖x‖ := lt_of_le_of_lt hR hx
    have e : ((R / ‖x‖ : ℝ) : ℂ) • x - ((R / ‖y‖ : ℝ) : ℂ) • y =
        ((R / ‖x‖ : ℝ) : ℂ) • (x - y) + ((R / ‖x‖ - R / ‖y‖ : ℝ) : ℂ) • y := by
      rw [smul_sub, Complex.ofReal_sub, sub_smul]; abel
    rw [e]
    calc _ ≤ ‖((R / ‖x‖ : ℝ) : ℂ) • (x - y)‖ + ‖((R / ‖x‖ - R / ‖y‖ : ℝ) : ℂ) • y‖ :=
          norm_add_le _ _
      _ = R / ‖x‖ * ‖x - y‖ + |R / ‖x‖ - R / ‖y‖| * ‖y‖ := by
          rw [norm_ofReal_smul (div_nonneg hR hx0.le), norm_smul, Complex.norm_real,
            Real.norm_eq_abs]
      _ ≤ 2 * ‖x - y‖ := retr_arith hR hx hy (abs_norm_sub_norm_le x y)

/-- The truncated field `G(t, π_R w)`. -/
noncomputable def Gtr (L κ β γ R : ℝ) (t : ℝ) (a : ℓ2) : ℓ2 := Gf L κ β γ t (retr R a)

theorem Gtr_of_le {R : ℝ} (t : ℝ) {a : ℓ2} (ha : ‖a‖ ≤ R) :
    Gtr L κ β γ R t a = Gf L κ β γ t a := by rw [Gtr, retr_of_le ha]

theorem lipschitzWith_Gtr (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    LipschitzWith ⟨2 * LF L β γ R, mul_nonneg zero_le_two (LF_nonneg L β γ R)⟩
      (Gtr L κ β γ R t) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm, dist_eq_norm, Gtr, Gtr, NNReal.coe_mk]
  calc _ ≤ LF L β γ R * ‖retr R a - retr R b‖ :=
        norm_Gf_sub_le hL t (norm_retr_le hR a) (norm_retr_le hR b)
    _ ≤ LF L β γ R * (2 * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left (norm_retr_sub_le hR a b) (LF_nonneg L β γ R)
    _ = 2 * LF L β γ R * ‖a - b‖ := by ring

theorem norm_Gtr_le (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) (a : ℓ2) :
    ‖Gtr L κ β γ R t a‖ ≤ LF L β γ R * R :=
  norm_Gf_le hL hR t (norm_retr_le hR a)

theorem continuous_Gtr_time (hL : 0 < L) (R : ℝ) (a : ℓ2) :
    Continuous fun t => Gtr L κ β γ R t a := by
  have h1 : Continuous fun t : ℝ => ((t, retr R a) : ℝ × ℓ2) :=
    continuous_id.prodMk continuous_const
  have h2 : Continuous fun t : ℝ => Gf L κ β γ t (retr R a) :=
    (continuous_Gf (κ := κ) (β := β) (γ := γ) hL).comp h1
  exact h2

/-- Local existence on `[−T, T]` for the truncated equation (Picard–Lindelöf). -/
theorem exists_local_tr (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R) (u₀ : ℓ2) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → ℓ2, α 0 = u₀ ∧ ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt α (Gtr L κ β γ R t (α t)) (Icc (-T) T) t := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  obtain ⟨B, hB⟩ : ∃ B, B = LF L β γ R * R := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact mul_nonneg (LF_nonneg L β γ R) hR
  have hPL : IsPicardLindelof (Gtr L κ β γ R) (tmin := -T) (tmax := T) ⟨0, h0⟩ u₀
      ⟨B * T, mul_nonneg hB0 hT⟩ 0 ⟨B, hB0⟩
      ⟨2 * LF L β γ R, mul_nonneg zero_le_two (LF_nonneg L β γ R)⟩ := by
    refine ⟨fun t _ => (lipschitzWith_Gtr hL hR t).lipschitzOnWith, fun x _ => ?_,
      fun t _ x _ => ?_, ?_⟩
    · exact (continuous_Gtr_time hL R x).continuousOn
    · rw [NNReal.coe_mk, hB]; exact norm_Gtr_le hL hR t x
    · simp only [NNReal.coe_mk, NNReal.coe_zero, sub_zero, zero_sub, neg_neg, max_self]
      exact le_refl _
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hα⟩

/-- Global existence for the truncated equation. -/
theorem exists_global_tr (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R) (u₀ : ℓ2) :
    ∃ W : ℝ → ℓ2, W 0 = u₀ ∧ ∀ t, HasDerivAt W (Gtr L κ β γ R t (W t)) t := by
  have hloc : ∀ n : ℕ, ∃ α : ℝ → ℓ2, α 0 = u₀ ∧ ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivWithinAt α (Gtr L κ β γ R t (α t)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t :=
    fun n => exists_local_tr hL hR u₀ (by positivity)
  choose α hα0 hα using hloc
  have hder : ∀ (n : ℕ) (t : ℝ), |t| < (n : ℝ) + 1 →
      HasDerivAt (α n) (Gtr L κ β γ R t (α n t)) t := by
    intro n t ht
    have h1 := neg_abs_le t
    have h2 := le_abs_self t
    exact (hα n t ⟨by linarith, by linarith⟩).hasDerivAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcons : ∀ (m n : ℕ) (t : ℝ), |t| < (m : ℝ) + 1 → |t| < (n : ℝ) + 1 → α m t = α n t := by
    intro m n t hm hn
    obtain ⟨T, hT⟩ : ∃ T, T = min ((m : ℝ) + 1) ((n : ℝ) + 1) := ⟨_, rfl⟩
    have hTm : T ≤ (m : ℝ) + 1 := hT ▸ min_le_left _ _
    have hTn : T ≤ (n : ℝ) + 1 := hT ▸ min_le_right _ _
    have htT : |t| < T := hT ▸ lt_min hm hn
    have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg t) htT
    have key := ODE_solution_unique_of_mem_Ioo (v := Gtr L κ β γ R) (s := fun _ => univ)
      (fun s _ => (lipschitzWith_Gtr hL hR s).lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, hT0⟩)
      (fun s hs => ⟨hder m s (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩), trivial⟩)
      (fun s hs => ⟨hder n s (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩), trivial⟩)
      ((hα0 m).trans (hα0 n).symm)
    exact key ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨fun t => α ⌈|t|⌉₊ t, hα0 _, fun t => ?_⟩
  have hn : |t| < (⌈|t|⌉₊ : ℝ) + 1 := lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  refine (hder _ t hn).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_abs.tendsto t).eventually (gt_mem_nhds hn)] with s hs
  exact hcons _ _ s (lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)) hs

/-! ### Conservation of mass -/

theorem hasDerivAt_Lc {w : ℝ → ℓ2} {w' : ℓ2} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => Lc L (w s)) (Lc L w') t :=
  ((Lc L).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw

theorem hasDerivAt_Ac {w : ℝ → ℓ2} {w' : ℓ2} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => Ac L κ (w s)) (Ac L κ w') t :=
  ((Ac L κ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw

theorem Lc_Gf (t : ℝ) (w : ℓ2) :
    Lc L (Gf L κ β γ t w) = (-I) • U L κ (-t) (Lc L (Fnl L β γ (U L κ t w))) := by
  rw [Gf, map_smul, Lc_U]

theorem Ac_Gf (t : ℝ) (w : ℓ2) :
    Ac L κ (Gf L κ β γ t w) = (-I) • U L κ (-t) (Ac L κ (Fnl L β γ (U L κ t w))) := by
  rw [Gf, map_smul, Ac_U]

/-- **Conservation of mass** (infinitesimal form). -/
theorem hasDerivAt_mass (hL : 0 < L) {w : ℝ → ℓ2} {t : ℝ}
    (hw : HasDerivAt w (Gf L κ β γ t (w t)) t) :
    HasDerivAt (fun s => mass L (w s)) 0 t := by
  have h := (hasDerivAt_Lc (L := L) hw).norm_sq
  simp_rw [mass_eq_norm_Lc]
  convert h using 1
  rw [real_inner_eq, Lc_Gf, inner_smul_right, inner_U_neg, ← Lc_U, re_neg_I_mul, inner_Lc,
    inner_Fnl_im hL, mul_zero]

/-- `‖ψ(t)‖²` along the free flow. -/
theorem mass_U (L κ t : ℝ) (v : ℓ2) : mass L (U L κ t v) = mass L v := by
  rw [mass_eq_norm_Lc, mass_eq_norm_Lc, Lc_U, norm_U]

theorem norm_Ac_U (L κ t : ℝ) (v : ℓ2) : ‖Ac L κ (U L κ t v)‖ = ‖Ac L κ v‖ := by
  rw [Ac_U, norm_U]

/-! ### The weak generator -/

/-- The weak generator `⟨f, −i(Δ+κ)²u⟩ = −i ⟨(Δ+κ)f, (Δ+κ)u⟩`. -/
noncomputable def Lw (L κ : ℝ) (f u : ℓ2) : ℂ := -I * inner ℂ (Ac L κ f) (Ac L κ u)

/-- The difference quotient `h⁻¹ ⟨f, U(h)u − u⟩`. -/
noncomputable def Qh (L κ h : ℝ) (f u : ℓ2) : ℂ :=
  ((h⁻¹ : ℝ) : ℂ) * inner ℂ (Lc L f) (Lc L (U L κ h u) - Lc L u)

theorem norm_ph_sub_one_le (L κ h : ℝ) (k : Z2) : ‖ph L κ h k - 1‖ ≤ om L κ k * |h| := by
  have hom : 0 ≤ om L κ k := by unfold om; positivity
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => ph L κ s k)
    (f' := fun s => -I * (om L κ k : ℂ) * ph L κ s k) (s := univ) (x := 0) (y := h) (C := om L κ k)
    (fun s _ => (hasDerivAt_ph L κ s k).hasDerivWithinAt)
    (fun s _ => by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_ph, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hom])
    convex_univ trivial trivial
  simpa [ph_zero, Real.norm_eq_abs] using hmv

theorem Qh_eq (L κ h : ℝ) (f u : ℓ2) :
    Qh L κ h f u = ∑' k, (starRingEnd ℂ) (co L f k) *
      (((h⁻¹ : ℝ) : ℂ) * (ph L κ h k - 1)) * co L u k := by
  rw [Qh, ← map_sub, inner_Lc, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [co_sub, Pi.sub_apply, co_U]
  ring

theorem Lw_eq (L κ : ℝ) (f u : ℓ2) :
    Lw L κ f u = ∑' k, (starRingEnd ℂ) (co L f k) * (-I * (om L κ k : ℂ)) * co L u k := by
  rw [Lw, inner_Ac, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  ring

theorem summable_om_bound (L κ : ℝ) (f u : ℓ2) :
    Summable fun k => ‖co L f k‖ * om L κ k * ‖co L u k‖ := by
  have hs : Summable fun k => (‖Ac L κ f k‖ ^ 2 + ‖Ac L κ u k‖ ^ 2) / 2 :=
    ((summable_sq _).add (summable_sq _)).div_const 2
  refine hs.of_nonneg_of_le (fun k => by unfold om; positivity) (fun k => ?_)
  have e : ‖co L f k‖ * om L κ k * ‖co L u k‖ = ‖Ac L κ f k‖ * ‖Ac L κ u k‖ := by
    rw [Ac_apply, Ac_apply, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, om, ← sq_abs]
    ring
  rw [e]
  nlinarith [sq_nonneg (‖Ac L κ f k‖ - ‖Ac L κ u k‖)]

/-- **The difference quotients converge to the weak generator.** -/
theorem tendsto_Qh (L κ : ℝ) (f u : ℓ2) :
    Tendsto (fun h => Qh L κ h f u) (𝓝[≠] 0) (𝓝 (Lw L κ f u)) := by
  simp_rw [Qh_eq, Lw_eq]
  refine tendsto_tsum_of_dominated_convergence (summable_om_bound L κ f u) (fun k => ?_)
    (Eventually.of_forall fun h k => ?_)
  · have hd := hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_ph L κ 0 k)
    simp only [zero_add, ph_zero, mul_one] at hd
    have hd' : Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : ℂ) * (ph L κ h k - 1)) (𝓝[≠] 0)
        (𝓝 (-I * (om L κ k : ℂ))) := by
      refine hd.congr fun h => ?_
      rw [Complex.real_smul]
    exact (hd'.const_mul _).mul_const _
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, norm_inv,
      Real.norm_eq_abs]
    have hb := norm_ph_sub_one_le L κ h k
    have hom : 0 ≤ om L κ k := by unfold om; positivity
    rcases eq_or_ne h 0 with rfl | hh
    · simp; positivity
    · have hh' : 0 < |h| := abs_pos.2 hh
      have : |h|⁻¹ * ‖ph L κ h k - 1‖ ≤ om L κ k := by
        rw [inv_mul_le_iff₀ hh']; linarith [mul_comm (om L κ k) |h|]
      calc ‖co L f k‖ * (|h|⁻¹ * ‖ph L κ h k - 1‖) * ‖co L u k‖ ≤
          ‖co L f k‖ * om L κ k * ‖co L u k‖ := by gcongr

/-- `‖U(h)u − u‖²_{L²} = o(|h|)`. -/
theorem tendsto_norm_U_sub_sq_div (L κ : ℝ) (u : ℓ2) :
    Tendsto (fun h => ‖Lc L (U L κ h u) - Lc L u‖ ^ 2 / |h|) (𝓝[≠] 0) (𝓝 0) := by
  have e : ∀ h, ‖Lc L (U L κ h u) - Lc L u‖ ^ 2 / |h| =
      ∑' k, ‖ph L κ h k - 1‖ ^ 2 / |h| * ‖co L u k‖ ^ 2 := by
    intro h
    rw [← map_sub, norm_sq_eq, ← tsum_div_const]
    refine tsum_congr fun k => ?_
    rw [Lc_apply, co_sub, Pi.sub_apply, co_U, show ph L κ h k * co L u k - co L u k =
      (ph L κ h k - 1) * co L u k by ring, norm_mul, mul_pow]
    ring
  simp_rw [e]
  have hs : Summable fun k => 2 * (om L κ k * ‖co L u k‖ ^ 2) := by
    refine ((summable_sq (Ac L κ u)).mul_left 2).congr fun k => ?_
    rw [Ac_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, om]
  have key := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[≠] (0 : ℝ))
    (f := fun h k => ‖ph L κ h k - 1‖ ^ 2 / |h| * ‖co L u k‖ ^ 2) (g := fun _ => (0 : ℝ)) hs
    ?_ ?_
  · simpa using key
  · intro k -- pointwise: `‖ph − 1‖²/|h| ≤ om² |h| → 0`
    have hom : 0 ≤ om L κ k := by unfold om; positivity
    have hlim : Tendsto (fun h : ℝ => om L κ k ^ 2 * |h| * ‖co L u k‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
        have h := continuous_abs.tendsto (0 : ℝ)
        rw [abs_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      simpa using (this.const_mul (om L κ k ^ 2)).mul_const (‖co L u k‖ ^ 2)
    refine squeeze_zero (fun h => by positivity) (fun h => ?_) hlim
    rcases eq_or_ne h 0 with rfl | hh
    · simp
    · have hh' : 0 < |h| := abs_pos.2 hh
      have hb := norm_ph_sub_one_le L κ h k
      have : ‖ph L κ h k - 1‖ ^ 2 / |h| ≤ om L κ k ^ 2 * |h| := by
        rw [div_le_iff₀ hh']
        calc ‖ph L κ h k - 1‖ ^ 2 ≤ (om L κ k * |h|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ = om L κ k ^ 2 * |h| * |h| := by ring
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  · refine Eventually.of_forall fun h k => ?_
    have hom : 0 ≤ om L κ k := by unfold om; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases eq_or_ne h 0 with rfl | hh
    · simp; positivity
    · have hh' : 0 < |h| := abs_pos.2 hh
      have hb := norm_ph_sub_one_le L κ h k
      have h2 : ‖ph L κ h k - 1‖ ≤ 2 := by
        calc ‖ph L κ h k - 1‖ ≤ ‖ph L κ h k‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_ph, norm_one]; norm_num
      have : ‖ph L κ h k - 1‖ ^ 2 / |h| ≤ 2 * om L κ k := by
        rw [div_le_iff₀ hh']
        calc ‖ph L κ h k - 1‖ ^ 2 = ‖ph L κ h k - 1‖ * ‖ph L κ h k - 1‖ := sq _
          _ ≤ 2 * (om L κ k * |h|) := mul_le_mul h2 hb (norm_nonneg _) (by norm_num)
          _ = 2 * om L κ k * |h| := by ring
      calc ‖ph L κ h k - 1‖ ^ 2 / |h| * ‖co L u k‖ ^ 2 ≤ 2 * om L κ k * ‖co L u k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right this (sq_nonneg _)
        _ = 2 * (om L κ k * ‖co L u k‖ ^ 2) := by ring

end PVNP.Torus
