import PVNP.TorusGlobal

/-!
# M3-T: global well-posedness of the frozen WCT PDE in `H²(T_L²)`

**The equation.** `i ∂ₜψ = (Δ + κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ` on the torus `T_L² = (ℝ/Lℤ)²`, `L > 0`.

**Solutions** (`IsSolution L κ β γ u`).  A state `u t ∈ ℓ2` represents the `H²(T_L²)` field
`ψ(t) = field L (co L (u t))` (Fourier coefficients `ψ̂_k(t) = co L (u t) k`, orthonormal
normalisation, `‖u t‖ = ‖ψ(t)‖_{H²}`).  A solution is a map `u ∈ C(ℝ; H²)` whose Fourier
coefficients satisfy, for every `k ∈ ℤ²` and every `t`,

  `d/dt ψ̂_k(t) = −i ( (κ − |ξ_k|²)² ψ̂_k(t) + \widehat{N(ψ(t))}_k )`,

where `\widehat{N(ψ(t))}_k = fc L (fun x ↦ fnl β γ (ψ(t,x))) k` is the `k`-th Fourier coefficient
(the integral `L⁻¹ ∫_{[0,L]²} N(ψ(t,x)) conj(e_k(x)) dx`) of the *physical* nonlinearity
`N(z) = −β|z|²z + γ|z|⁴z` evaluated pointwise.  This is the PDE tested against every Fourier
mode, i.e. the standard distributional (weak-in-space, strong-in-time) formulation on the torus.

**Results** (all for arbitrary `L > 0`):

* `isSolution_of_ode`, `ode_of_isSolution`: solutions are exactly the interaction-picture
  trajectories `u(t) = U(t) w(t)`, `w' = G(t, w)`;
* `global_wellposed`: for `γ > 0` and every `u₀ ∈ H²(T_L²)`, a **unique global solution**;
* `conservation`: mass `∫|ψ|²` and Hamiltonian `‖(Δ+κ)ψ‖² + ∫(−β/2|ψ|⁴ + γ/3|ψ|⁶)` are constant;
* `apriori`: `‖ψ(t)‖_{H²} ≤ (1+|κ|)√M + √(H + 3β²M/16γ)` for all `t` (uniform in `L`);
* `lipschitz_dependence`, `continuous_dependence`: Lipschitz/continuous dependence on the data
  in `C([−T, T]; H²)`;
* `kin_eq_integral`: for fields with two classical derivatives the kinetic term is the classical
  `∫_{[0,L]²} |(Δ + κ)ψ|²` with `WCTPlaneWave.shifted`.

**Constants.** The a priori bound is uniform in `L`.  The local Lipschitz constant
`LF L β γ R = |β|·3·CA²R² + |γ|·5·CA⁴R⁴` depends on `L` only through the algebra constant
`CA L = 4√(SL L)/L`, which is bounded by `6` for all `L ≥ 1` (`CA_le`); for `L < 1` it is a
fixed-domain constant (`CA L ≤ 4(1 + L/2)/L`).
-/

open Complex Set Filter Topology InnerProductSpace MeasureTheory
open scoped Real ENNReal NNReal

namespace PVNP.Torus

variable {L κ β γ : ℝ}

attribute [local irreducible] U Fnl

/-- **Solutions of the frozen PDE** `i∂ₜψ = (Δ+κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ` on `T_L²` with values
in `H²(T_L²)` (see the module docstring). -/
def IsSolution (L κ β γ : ℝ) (u : ℝ → ℓ2) : Prop :=
  Continuous u ∧ ∀ t k, HasDerivAt (fun s => co L (u s) k)
    (-I * ((om L κ k : ℂ) * co L (u t) k + fc L (fun x => fnl β γ (field L (co L (u t)) x)) k)) t

/-! ### Coefficientwise derivatives -/

theorem hasDerivAt_apply {W : ℝ → ℓ2} {W' : ℓ2} {t : ℝ} (hW : HasDerivAt W W' t) (k : Z2) :
    HasDerivAt (fun s => W s k) (W' k) t :=
  ((evalL k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hW

/-- If every coefficient of `W` has derivative given by a continuous `ℓ²`-valued `g`, then `W`
is differentiable in `ℓ²` with derivative `g`. -/
theorem hasDerivAt_of_coeff {W g : ℝ → ℓ2} (hg : Continuous g)
    (hW : ∀ t k, HasDerivAt (fun s => W s k) (g t k) t) (t : ℝ) : HasDerivAt W (g t) t := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable a b
  have heq : ∀ s, W s = W 0 + ∫ r in (0 : ℝ)..s, g r := by
    intro s
    ext k
    have h1 : (∫ r in (0 : ℝ)..s, g r) k = ∫ r in (0 : ℝ)..s, g r k := by
      have := ((evalL k).restrictScalars ℝ).intervalIntegral_comp_comm (hint 0 s)
      simpa using this.symm
    have hck : Continuous fun r => g r k := (evalL k).continuous.comp hg
    have h2 : ∫ r in (0 : ℝ)..s, g r k = W s k - W 0 k :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hW r k)
        (hck.intervalIntegrable 0 s)
    rw [lp.coeFn_add, Pi.add_apply, h1, h2]
    ring
  have hd := (intervalIntegral.integral_hasDerivAt_right (hint 0 t)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add (W 0)
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun s => heq s)

theorem ph_mul_ph_neg (L κ t : ℝ) (k : Z2) : ph L κ t k * ph L κ (-t) k = 1 := by
  rw [← ph_add, add_neg_cancel, ph_zero]

theorem hasDerivAt_ph_neg (L κ t : ℝ) (k : Z2) :
    HasDerivAt (fun s => ph L κ (-s) k) (I * (om L κ k : ℂ) * ph L κ (-t) k) t := by
  have h := (hasDerivAt_ph L κ (-t) k).scomp t (hasDerivAt_neg t)
  convert h using 1
  simp only [Complex.real_smul]
  push_cast
  ring

theorem co_Gf (t : ℝ) (w : ℓ2) (k : Z2) :
    co L (Gf L κ β γ t w) k = -I * ph L κ (-t) k * co L (Fnl L β γ (U L κ t w)) k := by
  simp only [co, Gf, lp.coeFn_smul, Pi.smul_apply, U_apply, smul_eq_mul]
  ring

/-! ### Solutions ↔ interaction-picture trajectories -/

/-- Interaction-picture trajectories give solutions of the PDE. -/
theorem isSolution_of_ode (hL : 0 < L) {W : ℝ → ℓ2}
    (hW : ∀ t, HasDerivAt W (Gf L κ β γ t (W t)) t) :
    IsSolution L κ β γ fun t => U L κ t (W t) := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  refine ⟨continuous_U_path hWc, fun t k => ?_⟩
  have hc : HasDerivAt (fun s => co L (W s) k) (co L (Gf L κ β γ t (W t)) k) t := by
    have h := (hasDerivAt_apply (hW t) k).div_const (wt L k : ℂ)
    simpa only [co] using h
  have hprod := (hasDerivAt_ph L κ t k).mul hc
  simp_rw [co_U]
  convert hprod using 1
  rw [fc_fnl hL, co_Gf]
  have h1 := ph_mul_ph_neg L κ t k
  linear_combination (I * co L (Fnl L β γ (U L κ t (W t))) k) * h1

/-- Solutions of the PDE give interaction-picture trajectories. -/
theorem ode_of_isSolution (hL : 0 < L) {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) (t : ℝ) :
    HasDerivAt (fun s => U L κ (-s) (u s)) (Gf L κ β γ t (U L κ (-t) (u t))) t := by
  have hg : Continuous fun s => Gf L κ β γ s (U L κ (-s) (u s)) := by
    have h1 : Continuous fun s => U L κ (-s) (u s) := by
      have : Continuous fun s : ℝ => ((-s, u s) : ℝ × ℓ2) := continuous_neg.prodMk hu.1
      exact (continuous_U_uncurry L κ).comp this
    have h2 : Continuous fun s : ℝ => ((s, U L κ (-s) (u s)) : ℝ × ℓ2) := continuous_id.prodMk h1
    exact (continuous_Gf hL).comp h2
  refine hasDerivAt_of_coeff hg (fun s k => ?_) t
  have hk : HasDerivAt (fun r => u r k) ((wt L k : ℂ) *
      (-I * ((om L κ k : ℂ) * co L (u s) k +
        fc L (fun x => fnl β γ (field L (co L (u s)) x)) k))) s := by
    have h := (hu.2 s k).const_mul (wt L k : ℂ)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    simp only
    rw [wt_mul_co]
  have hprod := (hasDerivAt_ph_neg L κ s k).mul hk
  simp only [U_apply]
  convert hprod using 1
  have e1 : (Gf L κ β γ s (U L κ (-s) (u s))) k =
      (wt L k : ℂ) * (-I * ph L κ (-s) k * co L (Fnl L β γ (u s)) k) := by
    rw [← wt_mul_co L (Gf L κ β γ s (U L κ (-s) (u s))) k, co_Gf, U_U_neg]
  rw [e1, fc_fnl hL, ← wt_mul_co L (u s) k]
  ring

/-! ### Global well-posedness -/

/-- **M3-T: global well-posedness in `H²(T_L²)`.**  For every `L > 0`, `κ, β ∈ ℝ`, `γ > 0` and
every datum `u₀ ∈ H²(T_L²)` there is exactly one global solution `u ∈ C(ℝ; H²)` with
`u(0) = u₀`. -/
theorem global_wellposed (hL : 0 < L) (hγ : 0 < γ) (u₀ : ℓ2) :
    ∃! u : ℝ → ℓ2, u 0 = u₀ ∧ IsSolution L κ β γ u := by
  obtain ⟨W, hW0, hW⟩ := exists_global (κ := κ) (β := β) hL hγ u₀
  refine ⟨fun t => U L κ t (W t), ⟨by simp only [U_zero, hW0], isSolution_of_ode hL hW⟩, ?_⟩
  rintro v ⟨hv0, hv⟩
  have hWv := ode_of_isSolution hL hv
  have h0 : (fun s => U L κ (-s) (v s)) 0 = W 0 := by simp only [neg_zero, U_zero, hv0, hW0]
  have heq := ode_unique hL hWv hW h0
  funext t
  have := congrFun heq t
  simp only at this
  rw [← this, U_U_neg]

/-- **Conservation of mass and Hamiltonian** along every solution. -/
theorem conservation (hL : 0 < L) {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) (t : ℝ) :
    mass L (u t) = mass L (u 0) ∧ ham L κ β γ (u t) = ham L κ β γ (u 0) := by
  have hW := ode_of_isSolution hL hu
  have h := conserved hL hW t
  simp only [neg_zero, U_zero, U_U_neg] at h
  refine ⟨?_, h.2⟩
  rw [← h.1, mass_U]

/-- **A priori bound**, uniform in `L`: `‖ψ(t)‖_{H²} ≤ (1+|κ|)√M₀ + √(H₀ + 3β²M₀/16γ)`. -/
theorem apriori (hL : 0 < L) (hγ : 0 < γ) {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) (t : ℝ) :
    ‖u t‖ ≤ Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) := by
  have h := norm_le_apriori (κ := κ) (β := β) hL hγ (u t)
  rwa [(conservation hL hu t).1, (conservation hL hu t).2] at h

/-! ### Dependence on the data -/

theorem lipschitzOnWith_Gf_rev (hL : 0 < L) {R : ℝ} (s : ℝ) :
    LipschitzOnWith ⟨LF L β γ R, LF_nonneg L β γ R⟩ (fun x => -Gf L κ β γ (-s) x)
      (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  have h := (lipschitzOnWith_Gf (κ := κ) (β := β) (γ := γ) hL (R := R) (-s)).dist_le_mul a ha b hb
  show dist (-Gf L κ β γ (-s) a) (-Gf L κ β γ (-s) b) ≤ _
  rw [dist_neg_neg]
  exact h

theorem hasDerivAt_rev {W : ℝ → ℓ2} (hW : ∀ t, HasDerivAt W (Gf L κ β γ t (W t)) t) (s : ℝ) :
    HasDerivAt (fun r => W (-r)) (-Gf L κ β γ (-s) (W (-s))) s := by
  have h := (hW (-s)).scomp s (hasDerivAt_neg s)
  rw [neg_one_smul] at h
  exact h

/-- **Gronwall estimate** for `w' = G(t, w)` along trajectories in the ball of radius `R`. -/
theorem ode_dist_le (hL : 0 < L) {W₁ W₂ : ℝ → ℓ2}
    (h₁ : ∀ t, HasDerivAt W₁ (Gf L κ β γ t (W₁ t)) t)
    (h₂ : ∀ t, HasDerivAt W₂ (Gf L κ β γ t (W₂ t)) t) {R : ℝ}
    (hR₁ : ∀ t, ‖W₁ t‖ ≤ R) (hR₂ : ∀ t, ‖W₂ t‖ ≤ R) {T t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖W₁ t - W₂ t‖ ≤ ‖W₁ 0 - W₂ 0‖ * Real.exp (LF L β γ R * T) := by
  have hK := LF_nonneg L β γ R
  have hc₁ : Continuous W₁ := continuous_iff_continuousAt.2 fun s => (h₁ s).continuousAt
  have hc₂ : Continuous W₂ := continuous_iff_continuousAt.2 fun s => (h₂ s).continuousAt
  have hm₁ : ∀ s, W₁ s ∈ Metric.closedBall (0 : ℓ2) R := fun s => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hR₁ s
  have hm₂ : ∀ s, W₂ s ∈ Metric.closedBall (0 : ℓ2) R := fun s => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hR₂ s
  rcases le_total 0 t with h0 | h0
  · have key := dist_le_of_trajectories_ODE_of_mem (v := Gf L κ β γ)
      (s := fun _ => Metric.closedBall (0 : ℓ2) R) (K := ⟨LF L β γ R, hK⟩) (a := 0) (b := T)
      (fun s _ => lipschitzOnWith_Gf hL s) hc₁.continuousOn
      (fun s _ => (h₁ s).hasDerivWithinAt) (fun s _ => hm₁ s) hc₂.continuousOn
      (fun s _ => (h₂ s).hasDerivWithinAt) (fun s _ => hm₂ s) (le_refl _) t ⟨h0, ht.2⟩
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk, sub_zero] at key
    exact key.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK)) (norm_nonneg _))
  · have hc₁' : Continuous fun r => W₁ (-r) := hc₁.comp continuous_neg
    have hc₂' : Continuous fun r => W₂ (-r) := hc₂.comp continuous_neg
    have key := dist_le_of_trajectories_ODE_of_mem (v := fun s x => -Gf L κ β γ (-s) x)
      (s := fun _ => Metric.closedBall (0 : ℓ2) R) (K := ⟨LF L β γ R, hK⟩) (a := 0) (b := T)
      (f := fun r => W₁ (-r)) (g := fun r => W₂ (-r))
      (fun s _ => lipschitzOnWith_Gf_rev hL s) hc₁'.continuousOn
      (fun s _ => (hasDerivAt_rev h₁ s).hasDerivWithinAt) (fun s _ => hm₁ (-s)) hc₂'.continuousOn
      (fun s _ => (hasDerivAt_rev h₂ s).hasDerivWithinAt) (fun s _ => hm₂ (-s)) (le_refl _) (-t)
      ⟨by linarith, by linarith [ht.1]⟩
    simp only [neg_neg, neg_zero] at key
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk, sub_zero] at key
    exact key.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.1]) hK)) (norm_nonneg _))

/-- **Lipschitz dependence on the data**: if both solutions have a priori radius at most `R`,
then `‖v(t) − u(t)‖_{H²} ≤ ‖v(0) − u(0)‖_{H²} · exp(LF(R)·T)` on `[−T, T]`. -/
theorem lipschitz_dependence (hL : 0 < L) (hγ : 0 < γ) {u v : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u) (hv : IsSolution L κ β γ v) {R : ℝ}
    (hRu : Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) ≤ R)
    (hRv : Rap κ β γ (mass L (v 0)) (ham L κ β γ (v 0)) ≤ R) {T t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖v t - u t‖ ≤ ‖v 0 - u 0‖ * Real.exp (LF L β γ R * T) := by
  have hWu := ode_of_isSolution hL hu
  have hWv := ode_of_isSolution hL hv
  have hbu : ∀ s, ‖U L κ (-s) (u s)‖ ≤ R := fun s => by
    rw [norm_U]; exact (apriori hL hγ hu s).trans hRu
  have hbv : ∀ s, ‖U L κ (-s) (v s)‖ ≤ R := fun s => by
    rw [norm_U]; exact (apriori hL hγ hv s).trans hRv
  have key := ode_dist_le hL hWv hWu hbv hbu ht
  simp only [neg_zero, U_zero] at key
  rwa [← map_sub, norm_U] at key

theorem continuous_Rap (hL : 0 < L) (κ β γ : ℝ) :
    Continuous fun v : ℓ2 => Rap κ β γ (mass L v) (ham L κ β γ v) := by
  unfold Rap
  have h1 := continuous_mass L
  have h2 := continuous_ham hL κ β γ
  fun_prop

/-- **Continuous dependence on the data** in `C([−T, T]; H²(T_L²))`. -/
theorem continuous_dependence (hL : 0 < L) (hγ : 0 < γ) {u : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : ℝ → ℓ2, IsSolution L κ β γ v → ‖v 0 - u 0‖ < δ →
      ∀ t ∈ Icc (-T) T, ‖v t - u t‖ < ε := by
  set R := Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) + 1 with hR
  have hc := (continuous_Rap hL κ β γ).continuousAt (x := u 0)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
  set e := Real.exp (LF L β γ R * T) with he
  have he0 : 0 < e := Real.exp_pos _
  refine ⟨min δ₁ (ε / (e + 1)), lt_min hδ₁ (by positivity), fun v hv hv0 t ht => ?_⟩
  have hδ : ‖v 0 - u 0‖ < δ₁ := lt_of_lt_of_le hv0 (min_le_left _ _)
  have hδ' : ‖v 0 - u 0‖ < ε / (e + 1) := lt_of_lt_of_le hv0 (min_le_right _ _)
  have hRv : Rap κ β γ (mass L (v 0)) (ham L κ β γ (v 0)) ≤ R := by
    have h := hball (by rw [dist_eq_norm]; exact hδ)
    rw [Real.dist_eq] at h
    linarith [(abs_lt.1 h).2]
  have hRu : Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) ≤ R := by rw [hR]; linarith
  have key := lipschitz_dependence hL hγ hu hv hRu hRv ht
  calc ‖v t - u t‖ ≤ ‖v 0 - u 0‖ * e := key
    _ ≤ ε / (e + 1) * e := mul_le_mul_of_nonneg_right hδ'.le he0.le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-! ### The kinetic energy is the classical one for regular fields -/

/-- For fields with two classical derivatives, `‖(Δ+κ)ψ‖²_{L²}` in Fourier variables is the
classical integral `∫_{[0,L]²} |(Δ+κ)ψ|²`, with `WCTPlaneWave.shifted κ` built from genuine
coordinate derivatives. -/
theorem kin_eq_integral (hL : 0 < L) (κ : ℝ) (v : ℓ2) (hq : L1q L (co L v)) :
    ‖Ac L κ v‖ ^ 2 =
      ∫ x, ‖PVNP.WCTPlaneWave.shifted κ (field L (co L v)) x‖ ^ 2 ∂box L := by
  have hA : L1 fun k => ((κ - qf L k : ℝ) : ℂ) * co L v k :=
    (hq.mul_left (|κ| + 1)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hq0 := qf_nonneg L k
      calc |κ - qf L k| ≤ |κ| + qf L k := by
            have := abs_sub κ (qf L k); rwa [abs_of_nonneg hq0] at this
        _ ≤ (|κ| + 1) * (1 + qf L k) := by nlinarith [abs_nonneg κ])
  have hq1 : L1 fun k => -(qf L k : ℂ) * co L v k :=
    hq.mul_bound _ (fun k => by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (qf_nonneg L k)]
      linarith)
  have hsh : PVNP.WCTPlaneWave.shifted κ (field L (co L v)) =
      field L (fun k => ((κ - qf L k : ℝ) : ℂ) * co L v k) := by
    funext x
    simp only [PVNP.WCTPlaneWave.shifted]
    rw [lap_field hq]
    have e : (fun k => ((κ - qf L k : ℝ) : ℂ) * co L v k) =
        (fun k => -(qf L k : ℂ) * co L v k) + (κ : ℂ) • co L v := by
      funext k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
    rw [e, field_add hq1 (L1_smul _ hq.l1), field_smul]
  rw [hsh, integral_norm_sq hL hA, norm_sq_eq]
  refine tsum_congr fun k => ?_
  rw [Ac_apply]

end PVNP.Torus
