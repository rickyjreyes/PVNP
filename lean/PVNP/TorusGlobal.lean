import PVNP.TorusFlow

/-!
# Conservation of the Hamiltonian, the a priori bound and global existence on `T_L²`

* `hasDerivAt_inner_U`: product rule for `s ↦ ⟨f, U(s) w(s)⟩_{L²}` (weak generator);
* `hasDerivAt_pot_U`: derivative of the potential along `U(s) w(s)`;
* `hasDerivAt_ham`: **conservation of the Hamiltonian** `H = ‖(Δ+κ)ψ‖² + ∫(−β/2|ψ|⁴ + γ/3|ψ|⁶)`;
* `norm_le_apriori`: `‖ψ‖_{H²} ≤ (1 + |κ|)√M + √(H + 3β²M/(16γ))`, **uniform in `L`**;
* `exists_global`: global existence of the interaction-picture solution (`γ > 0`);
* `ode_unique`: uniqueness.
-/

open Complex Set Filter Topology InnerProductSpace
open scoped Real ENNReal NNReal

namespace PVNP.Torus

variable {L κ β γ : ℝ}

attribute [local irreducible] U Fnl

/-! ### Auxiliary limits -/

theorem tendsto_add_nhdsNE (t : ℝ) : Tendsto (fun h : ℝ => t + h) (𝓝[≠] 0) (𝓝 t) := by
  have h : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) := tendsto_const_nhds.add tendsto_id
  rw [add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_abs_nhdsNE : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
  have h := continuous_abs.tendsto (0 : ℝ)
  rw [abs_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem real_smul_eq (r : ℝ) (y : ℓ2) : r • y = (r : ℂ) • y := by
  ext k
  simp only [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

theorem norm_Lc_le (L : ℝ) (v : ℓ2) : ‖Lc L v‖ ≤ ‖v‖ := by
  have h := tsum_co_sq_le L v
  rw [← norm_sq_Lc] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-! ### Product rule against the weak generator -/

/-- **Product rule** for `s ↦ ⟨f, U(s) w(s)⟩_{L²}`. -/
theorem hasDerivAt_inner_U (f : ℓ2) {w : ℝ → ℓ2} {w' : ℓ2} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => inner ℂ (Lc L f) (Lc L (U L κ s (w s))))
      (inner ℂ (Lc L f) (Lc L (U L κ t w')) + Lw L κ f (U L κ t (w t))) t := by
  -- free part
  have hχ : HasDerivAt (fun s => inner ℂ (Lc L f) (Lc L (U L κ s (w t))))
      (Lw L κ f (U L κ t (w t))) t := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    refine (tendsto_Qh L κ f (U L κ t (w t))).congr fun h => ?_
    rw [Qh, ← inner_sub_right, add_comm t h, U_add, Complex.real_smul, ← map_sub]
  -- moving part
  have hρ : HasDerivAt (fun s => inner ℂ (Lc L f) (Lc L (U L κ s (w s - w t))))
      (inner ℂ (Lc L f) (Lc L (U L κ t w'))) t := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h1 := hasDerivAt_iff_tendsto_slope_zero.1 hw
    have h2 := (tendsto_add_nhdsNE t).prodMk_nhds h1
    have h3 := ((continuous_U_uncurry L κ).tendsto (t, w')).comp h2
    have h4 := (((Lc L).continuous.tendsto _).comp h3)
    have h5 := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := Lc L f)) h4
    refine h5.congr fun h => ?_
    simp only [Function.comp, sub_self, map_zero, inner_zero_right, sub_zero]
    rw [real_smul_eq, map_smul, map_smul, inner_smul_right, Complex.real_smul]
  have e : (fun s => inner ℂ (Lc L f) (Lc L (U L κ s (w s)))) = fun s =>
      inner ℂ (Lc L f) (Lc L (U L κ s (w s - w t))) +
        inner ℂ (Lc L f) (Lc L (U L κ s (w t))) := by
    funext s
    rw [← inner_add_right, ← map_add, ← map_add, sub_add_cancel]
  rw [e]
  exact hρ.add hχ

/-- `‖ψ(t+h) − ψ(t)‖²_{L²} = o(|h|)` along `ψ(s) = U(s) w(s)`. -/
theorem tendsto_norm_sq_div {w : ℝ → ℓ2} {w' : ℓ2} {t : ℝ} (hw : HasDerivAt w w' t) :
    Tendsto (fun h => ‖Lc L (U L κ (t + h) (w (t + h))) - Lc L (U L κ t (w t))‖ ^ 2 / |h|)
      (𝓝[≠] 0) (𝓝 0) := by
  have h1 := hasDerivAt_iff_tendsto_slope_zero.1 hw
  have h2 : Tendsto (fun h : ℝ => |h| * ‖h⁻¹ • (w (t + h) - w t)‖ ^ 2) (𝓝[≠] 0)
      (𝓝 (0 * ‖w'‖ ^ 2)) := tendsto_abs_nhdsNE.mul (h1.norm.pow 2)
  rw [zero_mul] at h2
  have h3 := tendsto_norm_U_sub_sq_div L κ (U L κ t (w t))
  have h4 := (h2.const_mul 2).add (h3.const_mul 2)
  rw [mul_zero, add_zero] at h4
  refine squeeze_zero' (Eventually.of_forall fun h => by positivity) ?_ h4
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < |h| := abs_pos.2 hh
  have hsplit : Lc L (U L κ (t + h) (w (t + h))) - Lc L (U L κ t (w t)) =
      Lc L (U L κ (t + h) (w (t + h) - w t)) +
        (Lc L (U L κ h (U L κ t (w t))) - Lc L (U L κ t (w t))) := by
    rw [← U_add, add_comm h t, map_sub, map_sub]; abel
  have ha : ‖Lc L (U L κ (t + h) (w (t + h) - w t))‖ ≤ ‖w (t + h) - w t‖ :=
    (norm_Lc_le L _).trans_eq (norm_U _ _ _ _)
  have hn : ‖h⁻¹ • (w (t + h) - w t)‖ = ‖w (t + h) - w t‖ / |h| := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_eq_div]
  rw [hsplit, hn]
  set a := ‖Lc L (U L κ (t + h) (w (t + h) - w t))‖
  set b := ‖Lc L (U L κ h (U L κ t (w t))) - Lc L (U L κ t (w t))‖
  set c := ‖w (t + h) - w t‖
  have hx : ‖Lc L (U L κ (t + h) (w (t + h) - w t)) +
      (Lc L (U L κ h (U L κ t (w t))) - Lc L (U L κ t (w t)))‖ ≤ a + b := norm_add_le _ _
  have hsq : ‖Lc L (U L κ (t + h) (w (t + h) - w t)) +
      (Lc L (U L κ h (U L κ t (w t))) - Lc L (U L κ t (w t)))‖ ^ 2 ≤ 2 * c ^ 2 + 2 * b ^ 2 := by
    have e1 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have e2 : a ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    nlinarith [sq_nonneg (a - b)]
  calc _ ≤ (2 * c ^ 2 + 2 * b ^ 2) / |h| := div_le_div_of_nonneg_right hsq hh'.le
    _ = 2 * (|h| * (c / |h|) ^ 2) + 2 * (b ^ 2 / |h|) := by field_simp

/-- The derivative of the potential along `U(s) w(s)`. -/
theorem hasDerivAt_pot_U (hL : 0 < L) {w : ℝ → ℓ2} {w' : ℓ2} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => pot L β γ (U L κ s (w s)))
      (2 * (inner ℂ (Lc L (Fnl L β γ (U L κ t (w t)))) (Lc L (U L κ t w')) +
        Lw L κ (Fnl L β γ (U L κ t (w t))) (U L κ t (w t))).re) t := by
  obtain ⟨u, hu⟩ : ∃ u, u = U L κ t (w t) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = Fnl L β γ u := ⟨_, rfl⟩
  rw [← hu, ← hf]
  have hlin := hasDerivAt_inner_U (L := L) (κ := κ) f hw
  rw [← hu] at hlin
  have hlin' : HasDerivAt (fun s => 2 * (inner ℂ (Lc L f) (Lc L (U L κ s (w s)))).re)
      (2 * (inner ℂ (Lc L f) (Lc L (U L κ t w')) + Lw L κ f u).re) t :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hlin).const_mul 2
  obtain ⟨R, hR⟩ : ∃ R, R = ‖w t‖ + 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = 3 * |β| * (L⁻¹ * Real.sqrt (SL L) * R) ^ 2 +
      5 * |γ| * (L⁻¹ * Real.sqrt (SL L) * R) ^ 4 := ⟨_, rfl⟩
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖w (t + h)‖ < R := by
    rw [hR]
    exact (hw.continuousAt.tendsto.comp (tendsto_add_nhdsNE t)).norm.eventually
      (gt_mem_nhds (lt_add_one _))
  have hrem : HasDerivAt (fun s => pot L β γ (U L κ s (w s)) -
      2 * (inner ℂ (Lc L f) (Lc L (U L κ s (w s)))).re) 0 t := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hlim := (tendsto_norm_sq_div (L := L) (κ := κ) hw).const_mul C
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev, self_mem_nhdsWithin] with h hh hh0
    have hh' : 0 < |h| := abs_pos.2 hh0
    have hu0 : ‖u‖ ≤ R := by rw [hu, norm_U, hR]; linarith
    have hu1 : ‖U L κ (t + h) (w (t + h))‖ ≤ R := by rw [norm_U]; exact hh.le
    have hT := pot_taylor hL β γ hu0 hu1
    rw [← hf, ← hC] at hT
    have e1 : (∑' k, (starRingEnd ℂ) (co L f k) *
        (co L (U L κ (t + h) (w (t + h))) k - co L u k)) =
        inner ℂ (Lc L f) (Lc L (U L κ (t + h) (w (t + h))) - Lc L u) := by
      rw [← map_sub, inner_Lc, co_sub]; rfl
    have e2 : ∑' k, ‖co L (U L κ (t + h) (w (t + h))) k - co L u k‖ ^ 2 =
        ‖Lc L (U L κ (t + h) (w (t + h))) - Lc L u‖ ^ 2 := by
      rw [← map_sub, norm_sq_Lc, co_sub]; rfl
    rw [e1, e2] at hT
    have heq : pot L β γ (U L κ (t + h) (w (t + h))) -
          2 * (inner ℂ (Lc L f) (Lc L (U L κ (t + h) (w (t + h))))).re -
          (pot L β γ (U L κ t (w t)) - 2 * (inner ℂ (Lc L f) (Lc L (U L κ t (w t)))).re) =
        pot L β γ (U L κ (t + h) (w (t + h))) - pot L β γ u -
          2 * (inner ℂ (Lc L f) (Lc L (U L κ (t + h) (w (t + h))) - Lc L u)).re := by
      rw [inner_sub_right, Complex.sub_re, hu]
      ring
    rw [heq, norm_smul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, inv_mul_eq_div,
      mul_div_assoc', ← hu]
    exact div_le_div_of_nonneg_right hT hh'.le
  have h := hrem.add hlin'
  rw [zero_add] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  exact (sub_add_cancel _ _).symm

/-! ### The Hamiltonian -/

/-- The Hamiltonian `H(ψ) = ‖(Δ+κ)ψ‖²_{L²} + ∫_{[0,L]²} (−β/2|ψ|⁴ + γ/3|ψ|⁶)`. -/
noncomputable def ham (L κ β γ : ℝ) (v : ℓ2) : ℝ := ‖Ac L κ v‖ ^ 2 + pot L β γ v

theorem ham_U (t : ℝ) (v : ℓ2) :
    ham L κ β γ (U L κ t v) = ‖Ac L κ v‖ ^ 2 + pot L β γ (U L κ t v) := by
  rw [ham, norm_Ac_U]

theorem re_neg_I_mul_inner_self (x : ℓ2) : (-I * inner ℂ x x).re = 0 := by
  rw [re_neg_I_mul, ← RCLike.im_to_complex, inner_self_im]

/-- **Conservation of the Hamiltonian** (infinitesimal form). -/
theorem hasDerivAt_ham (hL : 0 < L) {w : ℝ → ℓ2} {t : ℝ}
    (hw : HasDerivAt w (Gf L κ β γ t (w t)) t) :
    HasDerivAt (fun s => ham L κ β γ (U L κ s (w s))) 0 t := by
  have hk := (hasDerivAt_Ac (L := L) (κ := κ) hw).norm_sq
  have hp := hasDerivAt_pot_U (β := β) (γ := γ) (κ := κ) hL hw
  have h := hk.add hp
  have e : (fun s => ham L κ β γ (U L κ s (w s))) =
      fun s => ‖Ac L κ (w s)‖ ^ 2 + pot L β γ (U L κ s (w s)) := by
    funext s; rw [ham_U]
  rw [e]
  convert h using 1
  set u := U L κ t (w t)
  have hc := inner_conj_symm (𝕜 := ℂ) (Ac L κ (Fnl L β γ u)) (Ac L κ u)
  rw [real_inner_eq, Ac_Gf, inner_smul_right, inner_U_neg, ← Ac_U, U_Gf, map_smul,
    inner_smul_right, Lw, Complex.add_re, re_neg_I_mul_inner_self, zero_add]
  rw [re_neg_I_mul, re_neg_I_mul, ← hc, Complex.conj_im]
  ring

/-! ### Continuity of the energies -/

theorem continuous_pot (hL : 0 < L) (β γ : ℝ) : Continuous (pot L β γ) := by
  rw [continuous_iff_continuousAt]
  intro e
  obtain ⟨R, hR⟩ : ∃ R, R = ‖e‖ + 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = 3 * |β| * (L⁻¹ * Real.sqrt (SL L) * R) ^ 2 +
      5 * |γ| * (L⁻¹ * Real.sqrt (SL L) * R) ^ 4 := ⟨_, rfl⟩
  have hev : ∀ᶠ f in 𝓝 e, ‖f‖ < R := by
    rw [hR]; exact (continuous_norm.tendsto e).eventually (gt_mem_nhds (lt_add_one _))
  have hv : Tendsto (fun f => ‖f - e‖) (𝓝 e) (𝓝 0) := by
    have := ((continuous_id.sub (continuous_const : Continuous fun _ : ℓ2 => e)).norm.tendsto e)
    simpa using this
  have hlim : Tendsto (fun f => C * ‖f - e‖ ^ 2 + 2 * ‖Lc L (Fnl L β γ e)‖ * ‖f - e‖)
      (𝓝 e) (𝓝 0) := by
    have h := ((hv.pow 2).const_mul C).add (hv.const_mul (2 * ‖Lc L (Fnl L β γ e)‖))
    simpa using h
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun f => norm_nonneg _) ?_ hlim
  filter_upwards [hev] with f hf
  have he : ‖e‖ ≤ R := by rw [hR]; linarith
  have hT := pot_taylor hL β γ he hf.le
  rw [← hC] at hT
  have e1 : (∑' k, (starRingEnd ℂ) (co L (Fnl L β γ e) k) * (co L f k - co L e k)) =
      inner ℂ (Lc L (Fnl L β γ e)) (Lc L f - Lc L e) := by
    rw [← map_sub, inner_Lc, co_sub]; rfl
  have e2 : ∑' k, ‖co L f k - co L e k‖ ^ 2 = ‖Lc L f - Lc L e‖ ^ 2 := by
    rw [← map_sub, norm_sq_Lc, co_sub]; rfl
  rw [e1, e2] at hT
  have hd : ‖Lc L f - Lc L e‖ ≤ ‖f - e‖ := by rw [← map_sub]; exact norm_Lc_le L _
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hin : |2 * (inner ℂ (Lc L (Fnl L β γ e)) (Lc L f - Lc L e)).re| ≤
      2 * ‖Lc L (Fnl L β γ e)‖ * ‖f - e‖ := by
    rw [abs_mul, abs_two, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hd (norm_nonneg _)))
  have h1 := abs_le.1 hT
  have h2 := abs_le.1 hin
  have h3 : C * ‖Lc L f - Lc L e‖ ^ 2 ≤ C * ‖f - e‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) hC0
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem continuous_ham (hL : 0 < L) (κ β γ : ℝ) : Continuous (ham L κ β γ) :=
  ((continuous_norm.comp (Ac L κ).continuous).pow 2).add (continuous_pot hL β γ)

theorem continuous_mass (L : ℝ) : Continuous (mass L) := by
  have : mass L = fun v => ‖Lc L v‖ ^ 2 := funext fun v => mass_eq_norm_Lc L v
  rw [this]
  exact (continuous_norm.comp (Lc L).continuous).pow 2

/-! ### The a priori bound -/

theorem normG_sq (L : ℝ) (v : ℓ2) :
    ‖G1c L v‖ ^ 2 + ‖G2c L v‖ ^ 2 = ∑' k, qf L k * ‖co L v k‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq, ← (summable_sq (G1c L v)).tsum_add (summable_sq (G2c L v))]
  refine tsum_congr fun k => ?_
  rw [G1c_apply, G2c_apply, norm_mul (I * _) (co L v k), norm_mul (I * _) (co L v k),
    norm_I_xi1, norm_I_xi2, mul_pow, mul_pow, sq_abs, sq_abs, qf]
  ring

theorem normD_sq (L : ℝ) (v : ℓ2) : ‖Dc L v‖ ^ 2 = ∑' k, (qf L k * ‖co L v k‖) ^ 2 := by
  rw [norm_sq_eq]
  refine tsum_congr fun k => ?_
  rw [Dc_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (qf_nonneg L k)]

/-- **Interpolation** `‖∇ψ‖² ≤ ‖ψ‖ ‖Δψ‖`. -/
theorem normG_sq_le (L : ℝ) (v : ℓ2) :
    ‖G1c L v‖ ^ 2 + ‖G2c L v‖ ^ 2 ≤ ‖Lc L v‖ * ‖Dc L v‖ := by
  rw [normG_sq]
  have h := tsum_mul_le_sqrt (x := fun k => ‖co L v k‖) (y := fun k => qf L k * ‖co L v k‖)
    (fun _ => norm_nonneg _) (fun k => mul_nonneg (qf_nonneg L k) (norm_nonneg _))
    (summable_co_sq L v) (by
      have := summable_sq (Dc L v)
      refine this.congr fun k => ?_
      rw [Dc_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (qf_nonneg L k)])
  have e : ∀ k, qf L k * ‖co L v k‖ ^ 2 = ‖co L v k‖ * (qf L k * ‖co L v k‖) := fun k => by ring
  simp_rw [e]
  calc _ ≤ Real.sqrt (∑' k, ‖co L v k‖ ^ 2) * Real.sqrt (∑' k, (qf L k * ‖co L v k‖) ^ 2) := h.2
    _ = ‖Lc L v‖ * ‖Dc L v‖ := by
        rw [← norm_sq_Lc, ← normD_sq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem Dc_eq (L κ : ℝ) (v : ℓ2) : Dc L v = Ac L κ v - (κ : ℂ) • Lc L v := by
  ext k
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, Dc_apply, Ac_apply, Lc_apply,
    smul_eq_mul]
  push_cast
  ring

/-- `‖Δψ‖ ≤ ‖(Δ+κ)ψ‖ + |κ| ‖ψ‖`. -/
theorem norm_Dc_le (L κ : ℝ) (v : ℓ2) : ‖Dc L v‖ ≤ ‖Ac L κ v‖ + |κ| * ‖Lc L v‖ := by
  rw [Dc_eq L κ]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- **Bandpass coercivity** `‖(Δ+κ)ψ‖² ≤ H + (3β²/16γ) M`, uniform in `L`. -/
theorem kin_le_ham (hL : 0 < L) (hγ : 0 < γ) (v : ℓ2) :
    ‖Ac L κ v‖ ^ 2 ≤ ham L κ β γ v + 3 * β ^ 2 / (16 * γ) * mass L v := by
  have h := pot_add_mass_nonneg hL β γ hγ v
  rw [ham]; linarith

/-- **The a priori bound** `‖ψ‖_{H²} ≤ (1 + |κ|)√M + √(H + 3β²M/(16γ))`, uniform in `L`. -/
theorem norm_le_apriori (hL : 0 < L) (hγ : 0 < γ) (v : ℓ2) :
    ‖v‖ ≤ (1 + |κ|) * Real.sqrt (mass L v) +
      Real.sqrt (ham L κ β γ v + 3 * β ^ 2 / (16 * γ) * mass L v) := by
  have hM : Real.sqrt (mass L v) = ‖Lc L v‖ := by
    rw [mass_eq_norm_Lc, Real.sqrt_sq (norm_nonneg _)]
  have hK : ‖Ac L κ v‖ ≤ Real.sqrt (ham L κ β γ v + 3 * β ^ 2 / (16 * γ) * mass L v) :=
    Real.le_sqrt_of_sq_le (kin_le_ham hL hγ v)
  have hD := norm_Dc_le L κ v
  have hG := normG_sq_le L v
  have hdec := norm_sq_decomp L v
  have h2 : ‖v‖ ^ 2 ≤ (‖Lc L v‖ + ‖Dc L v‖) ^ 2 := by
    nlinarith [norm_nonneg (Lc L v), norm_nonneg (Dc L v)]
  have h3 : ‖v‖ ≤ ‖Lc L v‖ + ‖Dc L v‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  rw [hM]
  nlinarith [abs_nonneg κ, norm_nonneg (Lc L v)]

/-- The a priori radius from mass and Hamiltonian. -/
noncomputable def Rap (κ β γ M H : ℝ) : ℝ :=
  (1 + |κ|) * Real.sqrt M + Real.sqrt (H + 3 * β ^ 2 / (16 * γ) * M)

theorem Rap_nonneg (κ β γ M H : ℝ) : 0 ≤ Rap κ β γ M H := by unfold Rap; positivity

/-! ### Global existence and uniqueness -/

/-- Conservation of mass and Hamiltonian along any solution of `w' = G(t, w)`. -/
theorem conserved (hL : 0 < L) {W : ℝ → ℓ2} (hW : ∀ t, HasDerivAt W (Gf L κ β γ t (W t)) t)
    (t : ℝ) :
    mass L (W t) = mass L (W 0) ∧ ham L κ β γ (U L κ t (W t)) = ham L κ β γ (W 0) := by
  constructor
  · exact is_const_of_deriv_eq_zero (f := fun s => mass L (W s))
      (fun s => (hasDerivAt_mass hL (hW s)).differentiableAt)
      (fun s => (hasDerivAt_mass hL (hW s)).deriv) t 0
  · have h : ham L κ β γ (U L κ t (W t)) = ham L κ β γ (U L κ 0 (W 0)) :=
      is_const_of_deriv_eq_zero (f := fun s => ham L κ β γ (U L κ s (W s)))
        (fun s => (hasDerivAt_ham hL (hW s)).differentiableAt)
        (fun s => (hasDerivAt_ham hL (hW s)).deriv) t 0
    rwa [U_zero] at h

theorem continuous_U_path {W : ℝ → ℓ2} (hW : Continuous W) :
    Continuous fun s => U L κ s (W s) := by
  have h1 : Continuous fun s : ℝ => ((s, W s) : ℝ × ℓ2) := continuous_id.prodMk hW
  exact (continuous_U_uncurry L κ).comp h1

/-- **Global existence** for `w' = G(t, w)` (`γ > 0`): the truncated solution never leaves the
ball on which the truncation is inactive, by conservation of mass and Hamiltonian. -/
theorem exists_global (hL : 0 < L) (hγ : 0 < γ) (u₀ : ℓ2) :
    ∃ W : ℝ → ℓ2, W 0 = u₀ ∧ ∀ t, HasDerivAt W (Gf L κ β γ t (W t)) t := by
  set C₀ := Rap κ β γ (mass L u₀) (ham L κ β γ u₀) with hC₀
  have hbd : ∀ e : ℓ2, mass L e = mass L u₀ → ham L κ β γ e = ham L κ β γ u₀ → ‖e‖ ≤ C₀ := by
    intro e h1 h2
    have h := norm_le_apriori (κ := κ) (β := β) hL hγ e
    rwa [h1, h2] at h
  have hC₀0 : 0 ≤ C₀ := Rap_nonneg _ _ _ _ _
  obtain ⟨R, hR⟩ : ∃ R, R = C₀ + 1 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; linarith
  obtain ⟨W, hW0, hW⟩ := exists_global_tr (κ := κ) (β := β) (γ := γ) hL hR0 u₀
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hinner : ∀ s, ‖W s‖ ≤ R → HasDerivAt W (Gf L κ β γ s (W s)) s := fun s hs => by
    have h := hW s
    rwa [Gtr_of_le s hs] at h
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = {t | mass L (W t) = mass L u₀ ∧
      ham L κ β γ (U L κ t (W t)) = ham L κ β γ u₀} := ⟨_, rfl⟩
  have hSb : ∀ t ∈ S, ‖W t‖ ≤ C₀ := by
    intro t ht
    rw [hS] at ht
    have h := hbd (U L κ t (W t)) (by rw [mass_U]; exact ht.1) ht.2
    rwa [norm_U] at h
  have hm : Continuous fun t => mass L (W t) := (continuous_mass L).comp hWc
  have hE : Continuous fun t => ham L κ β γ (U L κ t (W t)) :=
    (continuous_ham hL κ β γ).comp (continuous_U_path hWc)
  have hclosed : IsClosed S := by
    rw [hS]
    exact (isClosed_eq hm continuous_const).inter (isClosed_eq hE continuous_const)
  have hopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro t ht
    have htR : ‖W t‖ < R := by rw [hR]; linarith [hSb t ht]
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
      ((continuous_norm.comp hWc).continuousAt.preimage_mem_nhds (gt_mem_nhds htR))
    refine ⟨ε, hε, fun s hs => ?_⟩
    have hder : ∀ x ∈ Metric.ball t ε, HasDerivAt W (Gf L κ β γ x (W x)) x :=
      fun x hx => hinner x (hball hx).le
    have hpre : IsPreconnected (Metric.ball t ε) := (convex_ball t ε).isPreconnected
    have h1 : mass L (W s) = mass L (W t) :=
      Metric.isOpen_ball.is_const_of_deriv_eq_zero (f := fun x => mass L (W x)) hpre
        (fun x hx => (hasDerivAt_mass hL (hder x hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => (hasDerivAt_mass hL (hder x hx)).deriv) hs (Metric.mem_ball_self hε)
    have h2 : ham L κ β γ (U L κ s (W s)) = ham L κ β γ (U L κ t (W t)) :=
      Metric.isOpen_ball.is_const_of_deriv_eq_zero
        (f := fun x => ham L κ β γ (U L κ x (W x))) hpre
        (fun x hx => (hasDerivAt_ham hL (hder x hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => (hasDerivAt_ham hL (hder x hx)).deriv) hs (Metric.mem_ball_self hε)
    rw [hS] at ht ⊢
    exact ⟨h1.trans ht.1, h2.trans ht.2⟩
  have h0S : (0 : ℝ) ∈ S := by
    rw [hS]
    exact ⟨by rw [hW0], by rw [U_zero, hW0]⟩
  have hSu : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0S⟩
  refine ⟨W, hW0, fun t => hinner t ?_⟩
  have ht : t ∈ S := by rw [hSu]; exact mem_univ t
  rw [hR]
  linarith [hSb t ht]

/-- **Uniqueness** for `w' = G(t, w)`. -/
theorem ode_unique (hL : 0 < L) {W₁ W₂ : ℝ → ℓ2}
    (h₁ : ∀ t, HasDerivAt W₁ (Gf L κ β γ t (W₁ t)) t)
    (h₂ : ∀ t, HasDerivAt W₂ (Gf L κ β γ t (W₂ t)) t) (h0 : W₁ 0 = W₂ 0) : W₁ = W₂ := by
  funext t
  obtain ⟨T, hT⟩ : ∃ T, T = |t| + 1 := ⟨_, rfl⟩
  have hc₁ : ContinuousOn W₁ (Icc (-T) T) :=
    (continuous_iff_continuousAt.2 fun s => (h₁ s).continuousAt).continuousOn
  have hc₂ : ContinuousOn W₂ (Icc (-T) T) :=
    (continuous_iff_continuousAt.2 fun s => (h₂ s).continuousAt).continuousOn
  obtain ⟨R₁, hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₁
  obtain ⟨R₂, hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₂
  obtain ⟨R, hR⟩ : ∃ R, R = max R₁ R₂ := ⟨_, rfl⟩
  have ht0 := abs_nonneg t
  have key := ODE_solution_unique_of_mem_Ioo (v := Gf L κ β γ)
    (s := fun _ => Metric.closedBall (0 : ℓ2) R) (K := ⟨LF L β γ R, LF_nonneg L β γ R⟩)
    (fun s _ => lipschitzOnWith_Gf hL s)
    (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, by linarith⟩)
    (fun s hs => ⟨h₁ s, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hR₁ s (Ioo_subset_Icc_self hs)).trans (hR ▸ le_max_left _ _)⟩)
    (fun s hs => ⟨h₂ s, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hR₂ s (Ioo_subset_Icc_self hs)).trans (hR ▸ le_max_right _ _)⟩) h0
  exact key ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

end PVNP.Torus
