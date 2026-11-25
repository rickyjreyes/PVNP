import PVNP.WCTSATDevice

/-!
# A blind SAT-correct frozen-torus readout with one fixed budget

`WCTSATDevice.preloaded_device` bypasses the readout transport bound by preparing the answer at
time zero, and `blindness_necessary` shows that the bound needs initial blindness. This module
shows that blindness does not make the bound grow with the input either.

**Two-mode states.** `twoMode L a b` has Fourier coefficient `a` at `0` and `b` at `e₁ = (1, 0)`.
For the detector `χ(x) = L⁻¹(1 + cos(2πx₁/L))` of `WCTSATDevice`:

* `Jdet_twoMode`: `J = (|a|² + |b|² + Re(ā b))/L`;
* `Jdot_twoMode`: `J' = ((κ − q)² − κ²) Im(ā b)/L`, `q = |ξ_{e₁}|² = (2π/L)²`
  (the flux identity; the nonlinearity does not contribute).

So the states `a = 1, b = ±i` have the same reading and opposite fluxes whenever
`(κ − q)² ≠ κ²` (for example whenever `κ ≤ 0`, `flux_condition_of_nonpos`).

**Results.**

* `blind_pair_exists`: for every torus `L > 0` and all `κ, β` and `γ > 0` with `(κ − q)² ≠ κ²`
  there are two exact solutions with **equal** initial readings whose readings at some time
  `T > 0` lie on opposite sides of a threshold with a positive margin.
* `blind_device`: hence there is a SAT-correct frozen-torus device that is blind (every pair of
  formulas has initial skew `0`) and whose curvature budget is bounded by one constant `B` for
  **every** formula.

The encoder of `blind_device` (`F ↦` one of two fixed initial states) is a SAT decider, as in
the preloaded device. The point is quantitative: the readout bound of `device_pair_budget` holds
for this device with `ε = 0`, and it is met by budgets that do not depend on the formula. A
transport argument alone therefore cannot force any growth of the budget with the input, even
under the blindness rail; the cost of deciding SAT sits in the encoder.
-/

open Complex Filter Topology MeasureTheory
open scoped Real

namespace PVNP.WCTSATBlind

open PVNP.Torus PVNP.PartIPsiSat PVNP.WCTSATDevice

variable {L κ β γ : ℝ}

/-! ### Two-mode states -/

/-- The state with coefficient `a` at the zero mode and `b` at `e₁`. -/
noncomputable def twoMode (L : ℝ) (a b : ℂ) : ℓ2 := mode L 0 a + mode L e1v b

/-- Its coefficient sequence. -/
noncomputable def tc (a b : ℂ) : Z2 → ℂ := Pi.single 0 a + Pi.single e1v b

theorem co_twoMode (L : ℝ) (a b : ℂ) : co L (twoMode L a b) = tc a b := by
  simp only [twoMode, co_add, co_mode, tc]

theorem tc_zero (a b : ℂ) : tc a b 0 = a := by
  simp [tc, e1v_ne_zero.symm]

theorem tc_e1v (a b : ℂ) : tc a b e1v = b := by
  simp [tc, e1v_ne_zero]

theorem tc_eq_zero (a b : ℂ) {k : Z2} (h0 : k ≠ 0) (h1 : k ≠ e1v) : tc a b k = 0 := by
  simp [tc, h0, h1]

theorem e1v_sub_self : e1v - e1v = 0 := sub_self _

theorem zero_sub_e1v : (0 : Z2) - e1v = -e1v := zero_sub _

/-- The detector convolution of a two-mode state. -/
theorem pr_dco_tc (L : ℝ) (a b : ℂ) (k : Z2) :
    pr L dco (tc a b) k = (L : ℂ)⁻¹ * (dco k * a + dco (k - e1v) * b) := by
  unfold pr
  congr 1
  rw [tsum_eq_sum (s := {0, e1v})]
  · rw [Finset.sum_pair e1v_ne_zero.symm, tc_zero, tc_e1v, sub_zero]
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    rw [tc_eq_zero a b hj.1 hj.2, mul_zero]

theorem pr_dco_tc_zero (L : ℝ) (a b : ℂ) :
    pr L dco (tc a b) 0 = (L : ℂ)⁻¹ * (a + b / 2) := by
  rw [pr_dco_tc, zero_sub_e1v, dco_zero, dco_neg_e1v]
  ring

theorem pr_dco_tc_e1v (L : ℝ) (a b : ℂ) :
    pr L dco (tc a b) e1v = (L : ℂ)⁻¹ * (a / 2 + b) := by
  rw [pr_dco_tc, e1v_sub_self, dco_zero, dco_e1v]
  ring

/-- The inner product of `ℓ2` in coordinates. -/
theorem inner_eq_tsum (x y : ℓ2) : inner ℂ x y = ∑' k, (starRingEnd ℂ) (x k) * y k := by
  rw [lp.inner_eq_tsum]
  exact tsum_congr fun k => RCLike.inner_apply' _ _

/-! ### Reading and flux of two-mode states -/

/-- **The reading of a two-mode state:** `J = (|a|² + |b|² + Re(ā b))/L`. -/
theorem Jdet_twoMode (hL : 0 < L) (a b : ℂ) :
    Jdet L (detector L) (twoMode L a b) =
      (Complex.normSq a + Complex.normSq b + ((starRingEnd ℂ) a * b).re) / L := by
  have hreal : rev (co L (detector L)) = co L (detector L) := by rw [co_detector]; exact rev_dco
  rw [Jdet_eq_re hL hreal, inner_Lc, co_mulH hL, co_detector, co_twoMode]
  rw [tsum_eq_sum (s := {0, e1v})]
  · rw [Finset.sum_pair e1v_ne_zero.symm, tc_zero, tc_e1v, pr_dco_tc_zero, pr_dco_tc_e1v,
      ← Complex.ofReal_inv]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.add_im, Complex.mul_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.normSq_apply]
    field_simp
    ring
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [tc_eq_zero a b hk.1 hk.2, map_zero, zero_mul]

/-- `|ξ_{e₁}|² = (2π/L)²`. -/
theorem qf_e1v (L : ℝ) : qf L e1v = (2 * π / L) ^ 2 := by
  simp [qf, xi1, xi2, e1v]

/-- **The flux of a two-mode state:** `J' = ((κ − q)² − κ²) Im(ā b)/L`, `q = qf L e₁`. -/
theorem Jdot_twoMode (hL : 0 < L) (a b : ℂ) :
    Jdot L κ (detector L) (twoMode L a b) =
      ((κ - qf L e1v) ^ 2 - κ ^ 2) * ((starRingEnd ℂ) a * b).im / L := by
  unfold Jdot
  rw [inner_eq_tsum]
  have hAc : ∀ v : ℓ2, ∀ k, Ac L κ v k = ((κ - qf L k : ℝ) : ℂ) * co L v k :=
    fun v k => Ac_apply L κ v k
  simp_rw [hAc, co_mulH hL, co_detector, co_twoMode]
  rw [tsum_eq_sum (s := {0, e1v})]
  · rw [Finset.sum_pair e1v_ne_zero.symm, tc_zero, tc_e1v, pr_dco_tc_zero, pr_dco_tc_e1v,
      qf_zero, ← Complex.ofReal_inv]
    simp only [map_mul, map_add, map_div₀, Complex.conj_ofReal, map_ofNat]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.add_im, Complex.mul_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im]
    field_simp
    ring
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [tc_eq_zero a b hk.1 hk.2, mul_zero, mul_zero]

/-- The flux condition holds for every `κ ≤ 0`. -/
theorem flux_condition_of_nonpos (hL : 0 < L) (hκ : κ ≤ 0) : (κ - qf L e1v) ^ 2 ≠ κ ^ 2 := by
  have hq : 0 < qf L e1v := by
    rw [qf_e1v]
    have : 0 < 2 * π / L := by positivity
    positivity
  intro h
  nlinarith [sq_nonneg κ]

/-! ### A function with nonzero derivative leaves zero on the right -/

theorem exists_pos_ne_of_hasDerivAt {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0)
    (h0 : f 0 = 0) (hne : f' ≠ 0) : ∃ T, 0 < T ∧ f T ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hlim := hf.tendsto_slope_zero_right
  have hev : (fun t : ℝ => t⁻¹ • (f (0 + t) - f 0)) =ᶠ[𝓝[>] 0] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [zero_add, hcon t ht, h0, sub_self, smul_zero]
  have h2 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 f') := hlim.congr' hev
  exact hne (tendsto_nhds_unique h2 tendsto_const_nhds)

/-! ### The blind pair and the blind device -/

/-- **A blind pair.** Two exact solutions of the frozen equation with equal initial readings
whose readings at a time `T > 0` lie on opposite sides of a threshold with a positive margin. -/
theorem blind_pair_exists (hL : 0 < L) (hγ : 0 < γ) (hκ : (κ - qf L e1v) ^ 2 ≠ κ ^ 2) :
    ∃ u v : ℝ → ℓ2, ∃ T threshold margin : ℝ, 0 < T ∧ 0 < margin ∧
      IsSolution L κ β γ u ∧ IsSolution L κ β γ v ∧
      Jdet L (detector L) (u 0) = Jdet L (detector L) (v 0) ∧
      threshold + margin ≤ Jdet L (detector L) (u T) ∧
      Jdet L (detector L) (v T) ≤ threshold - margin := by
  have hreal : rev (co L (detector L)) = co L (detector L) := by rw [co_detector]; exact rev_dco
  obtain ⟨u, ⟨hu0, hu⟩, -⟩ := global_wellposed (κ := κ) (β := β) hL hγ (twoMode L 1 I)
  obtain ⟨w, ⟨hw0, hw⟩, -⟩ := global_wellposed (κ := κ) (β := β) hL hγ (twoMode L 1 (-I))
  set f : ℝ → ℝ := fun t => Jdet L (detector L) (u t) - Jdet L (detector L) (w t) with hf
  have hfd : HasDerivAt f (Jdot L κ (detector L) (u 0) - Jdot L κ (detector L) (w 0)) 0 :=
    (flux_identity hL hreal hu 0).sub (flux_identity hL hreal hw 0)
  have hJ : Jdet L (detector L) (twoMode L 1 I) = Jdet L (detector L) (twoMode L 1 (-I)) := by
    rw [Jdet_twoMode hL, Jdet_twoMode hL]
    simp
  have hf0 : f 0 = 0 := by simp only [hf, hu0, hw0, hJ, sub_self]
  have hder : Jdot L κ (detector L) (u 0) - Jdot L κ (detector L) (w 0) =
      2 * (((κ - qf L e1v) ^ 2 - κ ^ 2) / L) := by
    rw [hu0, hw0, Jdot_twoMode hL, Jdot_twoMode hL]
    simp
    ring
  have hne : Jdot L κ (detector L) (u 0) - Jdot L κ (detector L) (w 0) ≠ 0 := by
    rw [hder]
    have : (κ - qf L e1v) ^ 2 - κ ^ 2 ≠ 0 := sub_ne_zero.mpr hκ
    have hL' : L ≠ 0 := hL.ne'
    positivity
  obtain ⟨T, hT, hfT⟩ := exists_pos_ne_of_hasDerivAt hfd hf0 hne
  have hinit : Jdet L (detector L) (u 0) = Jdet L (detector L) (w 0) := by
    rw [hu0, hw0, hJ]
  rcases lt_or_gt_of_ne hfT with hlt | hgt
  · -- the second trajectory reads higher at `T`
    refine ⟨w, u, T, (Jdet L (detector L) (u T) + Jdet L (detector L) (w T)) / 2,
      (Jdet L (detector L) (w T) - Jdet L (detector L) (u T)) / 2, hT, ?_, hw, hu,
      hinit.symm, ?_, ?_⟩
    · simp only [hf] at hlt; linarith
    · linarith
    · linarith
  · refine ⟨u, w, T, (Jdet L (detector L) (u T) + Jdet L (detector L) (w T)) / 2,
      (Jdet L (detector L) (u T) - Jdet L (detector L) (w T)) / 2, hT, ?_, hu, hw,
      hinit, ?_, ?_⟩
    · simp only [hf] at hgt; linarith
    · linarith
    · linarith

open Classical in
/-- **A blind SAT-correct device with one fixed budget.** Under the flux condition there is a
frozen-torus SAT device with one detector, one threshold and one time `T`, whose prepared states
all have the same initial reading (initial skew `0` for every pair of formulas), that reads every
satisfiable formula at least `margin` above the threshold and every unsatisfiable one at least
`margin` below it, and whose curvature budget on `[0, T]` is at most one constant `B` for every
formula. Its encoder is a SAT decider. -/
theorem blind_device (hL : 0 < L) (hγ : 0 < γ) (hκ : (κ - qf L e1v) ^ 2 ≠ κ ^ 2) :
    ∃ run : CNF3 → ℝ → ℓ2, ∃ T threshold margin B : ℝ, 0 < T ∧ 0 < margin ∧
      (∀ F, IsSolution L κ β γ (run F)) ∧
      (∀ F F', Jdet L (detector L) (run F 0) = Jdet L (detector L) (run F' 0)) ∧
      (∀ F, Sat F → threshold + margin ≤ Jdet L (detector L) (run F T)) ∧
      (∀ F, ¬ Sat F → Jdet L (detector L) (run F T) ≤ threshold - margin) ∧
      (∀ F, (∫ t in (0 : ℝ)..T, ‖Dc L (run F t)‖ ^ 2) ≤ B) := by
  obtain ⟨u, v, T, th, m, hT, hm, hu, hv, h0, hyes, hno⟩ :=
    blind_pair_exists (β := β) hL hγ hκ
  set Bu := ∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2
  set Bv := ∫ t in (0 : ℝ)..T, ‖Dc L (v t)‖ ^ 2
  have hBu : 0 ≤ Bu := budget_nonneg hT.le u
  have hBv : 0 ≤ Bv := budget_nonneg hT.le v
  refine ⟨fun F => if Sat F then u else v, T, th, m, Bu + Bv, hT, hm, fun F => ?_,
    fun F F' => ?_, fun F hF => ?_, fun F hF => ?_, fun F => ?_⟩
  · by_cases hF : Sat F <;> simp only [hF, if_true, if_false] <;> assumption
  · by_cases hF : Sat F <;> by_cases hF' : Sat F' <;>
      simp only [hF, hF', if_true, if_false, h0]
  · simp only [hF, if_true]; exact hyes
  · simp only [hF, if_false]; exact hno
  · by_cases hF : Sat F
    · simp only [hF, if_true]; linarith
    · simp only [hF, if_false]; linarith

end PVNP.WCTSATBlind
