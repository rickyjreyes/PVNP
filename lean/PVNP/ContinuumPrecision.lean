import PVNP.TorusFlux
import PVNP.WCTSATScaling

/-!
# I-11: what is proved about the continuum computation equivalence

Remark `rem:infinite-compute` (I-11) concerns the identification of the physical WCT class with
`P_Turing`. The discrete equality `P_disc = P_TM` is proved (`PartIIUniform.P_disc_eq_P_TM`) and
does not identify the continuum evolution with Turing computation. This module records the two
facts about the frozen torus PDE that a resource-preserving equivalence needs, and states the
exact remaining obligation.

**1. An exact equality for a continuum subclass** (`zeroDev_languages_eq_P_TM`). For the charged
zero-mode devices of the frozen torus PDE (polynomial-time encoder, exact frozen evolution, fixed
detector, fixed margin; all resources charged), the decided languages are exactly `P_TM`.

**2. Precision is not the obstruction** (`readout_precision`, `decision_robust`,
`precision_suffices`). The detector reading is a Lipschitz function of the state on bounded sets
(`Jdet_lipschitz`, constant `C_χ = L⁻¹ Σ_k |χ̂_k|`), and frozen solutions depend Lipschitz-
continuously on their data with constant `e^{LF·T}` (`Torus.lipschitz_dependence`). Hence initial
data known to precision `δ = m / (4 R C_χ e^{LF·T})` determine the readout decision of a device with
margin `m` at time `T`. The number of bits, `log(1/δ) = LF·T + log(4 R C_χ / m)`, grows only
linearly in the evolution time.

**3. Stability of approximate trajectories** (`approx_trajectory_close`, `approx_readout`). An
approximate trajectory in the interaction picture with residual `‖W' − G(t, W)‖ ≤ ε`, initial error
`δ` and radius `R` stays within the Gronwall bound `δ e^{LF·t} + (ε/LF)(e^{LF·t} − 1)` of the true
solution, and its detector reading is accurate to `C_χ (‖W(T)‖ + R)` times that bound. So a
numerical scheme with certified residual decides correctly: stability is proved, and only
consistency with polynomial cost is left.

**Remaining obligation.** A Turing machine still has to produce such an approximate trajectory with
a certified residual: a finite-dimensional scheme for the infinite-dimensional nonlinear evolution
(mode truncation of the solution, not only of the data, with a residual bound in the norm in which
the detector is Lipschitz, plus exact-arithmetic costs), in time polynomial in the input length.
Neither that simulation nor a counterexample to it is proved, so the continuum equality
`P_phys = P_TM` for the full frozen-PDE class stays open (I-11 Restricted).
-/

namespace PVNP.ContinuumPrecision

open PVNP.Torus PVNP.WCTSATScaling PVNP.Discrete

variable {L κ β γ : ℝ}

/-! ### 1. The charged zero-mode class -/

/-- **The charged zero-mode frozen-torus devices decide exactly `P_TM`.** -/
theorem zeroDev_languages_eq_P_TM (hL : 0 < L) :
    {Lang | ∃ D : ZeroDev, ZDecides L κ β γ D Lang} = P_TM := by
  ext Lang
  constructor
  · rintro ⟨D, hD⟩
    exact zdecides_mem_P hL hD
  · intro h
    obtain ⟨D, hD, -⟩ := zero_charges_P (κ := κ) (β := β) (γ := γ) hL Lang h
    exact ⟨D, hD⟩

/-! ### 2. The readout decision is robust to finite precision -/

/-- The detector constant `C_χ = L⁻¹ Σ_k |χ̂_k|`. -/
noncomputable def Cdet (L : ℝ) (χv : ℓ2) : ℝ := L⁻¹ * ∑' j, ‖co L χv j‖

theorem Cdet_nonneg (hL : 0 < L) (χv : ℓ2) : 0 ≤ Cdet L χv :=
  mul_nonneg (inv_nonneg.2 hL.le) (tsum_nonneg fun _ => norm_nonneg _)

/-- **The detector is Lipschitz on bounded sets.** -/
theorem Jdet_lipschitz (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv) (v w : ℓ2) :
    |Jdet L χv v - Jdet L χv w| ≤ Cdet L χv * (‖v‖ + ‖w‖) * ‖v - w‖ := by
  rw [Jdet_eq_re hL hreal, Jdet_eq_re hL hreal, ← Complex.sub_re]
  have e : inner ℂ (Lc L v) (Lc L (mulH L χv v)) - inner ℂ (Lc L w) (Lc L (mulH L χv w)) =
      inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v)) +
        inner ℂ (Lc L w) (Lc L (mulH L χv (v - w))) := by
    rw [mulH_sub_right hL, map_sub, map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [e]
  have hC := Cdet_nonneg hL χv
  have h1 : ‖Lc L (mulH L χv v)‖ ≤ Cdet L χv * ‖v‖ :=
    (norm_Lc_mulH_le hL χv v).trans (mul_le_mul_of_nonneg_left (norm_Lc_le L v) hC)
  have h2 : ‖Lc L (mulH L χv (v - w))‖ ≤ Cdet L χv * ‖v - w‖ :=
    (norm_Lc_mulH_le hL χv (v - w)).trans (mul_le_mul_of_nonneg_left (norm_Lc_le L _) hC)
  calc |(inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v)) +
          inner ℂ (Lc L w) (Lc L (mulH L χv (v - w)))).re|
      ≤ ‖inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v)) +
          inner ℂ (Lc L w) (Lc L (mulH L χv (v - w)))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v))‖ +
          ‖inner ℂ (Lc L w) (Lc L (mulH L χv (v - w)))‖ := norm_add_le _ _
    _ ≤ ‖Lc L (v - w)‖ * ‖Lc L (mulH L χv v)‖ + ‖Lc L w‖ * ‖Lc L (mulH L χv (v - w))‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖v - w‖ * (Cdet L χv * ‖v‖) + ‖w‖ * (Cdet L χv * ‖v - w‖) := by
        gcongr
        · exact norm_Lc_le L _
        · exact norm_Lc_le L _
    _ = Cdet L χv * (‖v‖ + ‖w‖) * ‖v - w‖ := by ring

/-- **Readout precision along the frozen evolution.** For two frozen solutions whose conserved
data are bounded by `R`, the readings at time `T ≥ 0` differ by at most
`2 R C_χ e^{LF·T} ‖v(0) − u(0)‖`. -/
theorem readout_precision (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {u v : ℝ → ℓ2} (hu : IsSolution L κ β γ u)
    (hv : IsSolution L κ β γ v) {R : ℝ}
    (hRu : Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) ≤ R)
    (hRv : Rap κ β γ (mass L (v 0)) (ham L κ β γ (v 0)) ≤ R) {T : ℝ} (hT : 0 ≤ T) :
    |Jdet L χv (v T) - Jdet L χv (u T)| ≤
      2 * R * Cdet L χv * Real.exp (LF L β γ R * T) * ‖v 0 - u 0‖ := by
  have h1 := Jdet_lipschitz hL hreal (v T) (u T)
  have hvT : ‖v T‖ ≤ R := (apriori hL hγ hv T).trans hRv
  have huT : ‖u T‖ ≤ R := (apriori hL hγ hu T).trans hRu
  have hdist := lipschitz_dependence hL hγ hu hv hRu hRv (T := T) (t := T) ⟨by linarith, le_rfl⟩
  have hC := Cdet_nonneg hL χv
  have hR : 0 ≤ R := (norm_nonneg _).trans hvT
  calc |Jdet L χv (v T) - Jdet L χv (u T)| ≤ Cdet L χv * (‖v T‖ + ‖u T‖) * ‖v T - u T‖ := h1
    _ ≤ Cdet L χv * (R + R) * (‖v 0 - u 0‖ * Real.exp (LF L β γ R * T)) := by
        gcongr
    _ = 2 * R * Cdet L χv * Real.exp (LF L β γ R * T) * ‖v 0 - u 0‖ := by ring

/-- **The readout decision is robust.** If the reading of `u` at time `T` exceeds the threshold
`θ` by the margin `m`, every solution whose data are within
`m / (4 R C_χ e^{LF·T})` of `u(0)` (with conserved data bounded by `R`) still exceeds `θ` by
`m/2`. -/
theorem decision_robust (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {u v : ℝ → ℓ2} (hu : IsSolution L κ β γ u)
    (hv : IsSolution L κ β γ v) {R : ℝ}
    (hRu : Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) ≤ R)
    (hRv : Rap κ β γ (mass L (v 0)) (ham L κ β γ (v 0)) ≤ R) {T θ m : ℝ} (hT : 0 ≤ T)
    (hdec : θ + m ≤ Jdet L χv (u T))
    (hclose : 4 * R * Cdet L χv * Real.exp (LF L β γ R * T) * ‖v 0 - u 0‖ ≤ m) :
    θ + m / 2 ≤ Jdet L χv (v T) := by
  have h := readout_precision hL hγ hreal hu hv hRu hRv hT
  have := neg_abs_le (Jdet L χv (v T) - Jdet L χv (u T))
  linarith

/-- **Precision suffices.** With `δ = m / (4 R C_χ e^{LF·T})`, data known to precision `δ` fix
the decision of a device with margin `m > 0`, and the number of bits needed is
`log(1/δ) = LF·T + log(4 R C_χ / m)`, linear in the evolution time. -/
theorem precision_suffices (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {u v : ℝ → ℓ2} (hu : IsSolution L κ β γ u)
    (hv : IsSolution L κ β γ v) {R : ℝ}
    (hRu : Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) ≤ R)
    (hRv : Rap κ β γ (mass L (v 0)) (ham L κ β γ (v 0)) ≤ R) {T θ m : ℝ} (hT : 0 ≤ T)
    (hm : 0 < m) (hpos : 0 < R * Cdet L χv) (hdec : θ + m ≤ Jdet L χv (u T))
    (hδ : ‖v 0 - u 0‖ ≤ m / (4 * R * Cdet L χv * Real.exp (LF L β γ R * T))) :
    θ + m / 2 ≤ Jdet L χv (v T) ∧
      Real.log (1 / (m / (4 * R * Cdet L χv * Real.exp (LF L β γ R * T)))) =
        LF L β γ R * T + Real.log (4 * R * Cdet L χv / m) := by
  have h4 : 0 < 4 * R * Cdet L χv := by linarith
  have hden : 0 < 4 * R * Cdet L χv * Real.exp (LF L β γ R * T) :=
    mul_pos h4 (Real.exp_pos _)
  refine ⟨decision_robust hL hγ hreal hu hv hRu hRv hT hdec ?_, ?_⟩
  · rw [le_div_iff₀ hden] at hδ
    linarith
  · rw [one_div_div, show 4 * R * Cdet L χv * Real.exp (LF L β γ R * T) / m =
        Real.exp (LF L β γ R * T) * (4 * R * Cdet L χv / m) by ring,
      Real.log_mul (Real.exp_pos _).ne' (div_pos h4 hm).ne', Real.log_exp]

/-! ### 3. Stability of certified approximate trajectories

A numerical simulation produces an approximate trajectory, not an exact solution. Write it in
the interaction picture `W(t) = e^{-tA}ψ(t)`, where the frozen equation is `W' = G(t, W)`
(`Torus.ode_of_isSolution`). If the approximation has residual `‖W' − G(t, W)‖ ≤ ε`, starts within
`δ` of the data and stays in the ball of radius `R`, then its physical-picture state stays within
the Gronwall bound `δ e^{LF·t} + (ε/LF)(e^{LF·t} − 1)` of the true solution, and the detector reading
is accurate to `C_χ (‖W(T)‖ + R)` times that bound. Consistency (small residual) plus this
stability therefore gives a correct readout; what remains for a Turing simulation is to produce
such an approximation with a certified residual in polynomial time. -/

/-- **Approximate trajectories with small residual stay close to the frozen solution.** -/
theorem approx_trajectory_close (hL : 0 < L) (hγ : 0 < γ) {u : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u) {R : ℝ}
    (hRu : Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) ≤ R) {W W' : ℝ → ℓ2} {T ε δ : ℝ}
    (hc : ContinuousOn W (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt W (W' t) (Set.Ici t) t)
    (hres : ∀ t ∈ Set.Ico 0 T, ‖W' t - Gf L κ β γ t (W t)‖ ≤ ε)
    (hball : ∀ t ∈ Set.Ico 0 T, ‖W t‖ ≤ R) (h0 : ‖W 0 - u 0‖ ≤ δ) :
    ∀ t ∈ Set.Icc 0 T, ‖U L κ t (W t) - u t‖ ≤ gronwallBound δ (LF L β γ R) ε t := by
  have hK := LF_nonneg L β γ R
  have hWu := ode_of_isSolution hL hu
  have hcu : Continuous fun s => U L κ (-s) (u s) :=
    continuous_iff_continuousAt.2 fun s => (hWu s).continuousAt
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := Gf L κ β γ)
    (s := fun _ => Metric.closedBall (0 : ℓ2) R) (K := ⟨LF L β γ R, hK⟩) (a := 0) (b := T)
    (f := W) (g := fun s => U L κ (-s) (u s)) (f' := W')
    (g' := fun s => Gf L κ β γ s (U L κ (-s) (u s))) (εf := ε) (εg := 0) (δ := δ)
    (fun s _ => lipschitzOnWith_Gf hL s) hc (fun s hs => hd s hs)
    (fun s hs => by rw [dist_eq_norm]; exact hres s hs)
    (fun s hs => by rw [Metric.mem_closedBall, dist_zero_right]; exact hball s hs)
    hcu.continuousOn (fun s _ => (hWu s).hasDerivWithinAt)
    (fun s _ => by rw [dist_self])
    (fun s _ => by
      rw [Metric.mem_closedBall, dist_zero_right, norm_U]
      exact (apriori hL hγ hu s).trans hRu)
    (by
      rw [dist_eq_norm]
      show ‖W 0 - U L κ (-0) (u 0)‖ ≤ δ
      rw [neg_zero, U_zero]
      exact h0)
  intro t ht
  have h := key t ht
  rw [dist_eq_norm, NNReal.coe_mk, add_zero, sub_zero] at h
  calc ‖U L κ t (W t) - u t‖ = ‖U L κ t (W t - U L κ (-t) (u t))‖ := by
        rw [map_sub, U_U_neg]
    _ = ‖W t - U L κ (-t) (u t)‖ := norm_U _ _ _ _
    _ ≤ gronwallBound δ (LF L β γ R) ε t := h

/-- **A certified approximate trajectory determines the readout.** The detector reading of the
approximate state at time `T` is within `C_χ (‖W(T)‖ + R)` times the Gronwall bound of the true
reading. -/
theorem approx_readout (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) {R : ℝ}
    (hRu : Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) ≤ R) {W W' : ℝ → ℓ2} {T ε δ : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn W (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt W (W' t) (Set.Ici t) t)
    (hres : ∀ t ∈ Set.Ico 0 T, ‖W' t - Gf L κ β γ t (W t)‖ ≤ ε)
    (hball : ∀ t ∈ Set.Ico 0 T, ‖W t‖ ≤ R) (h0 : ‖W 0 - u 0‖ ≤ δ) :
    |Jdet L χv (U L κ T (W T)) - Jdet L χv (u T)| ≤
      Cdet L χv * (‖W T‖ + R) * gronwallBound δ (LF L β γ R) ε T := by
  have h1 := Jdet_lipschitz hL hreal (U L κ T (W T)) (u T)
  have h2 := approx_trajectory_close hL hγ hu hRu hc hd hres hball h0 T ⟨hT, le_rfl⟩
  have huT : ‖u T‖ ≤ R := (apriori hL hγ hu T).trans hRu
  have hC := Cdet_nonneg hL χv
  have hR : 0 ≤ R := (norm_nonneg _).trans huT
  have hCR : 0 ≤ Cdet L χv * (‖W T‖ + R) := mul_nonneg hC (add_nonneg (norm_nonneg _) hR)
  rw [norm_U] at h1
  calc |Jdet L χv (U L κ T (W T)) - Jdet L χv (u T)|
      ≤ Cdet L χv * (‖W T‖ + ‖u T‖) * ‖U L κ T (W T) - u T‖ := h1
    _ ≤ Cdet L χv * (‖W T‖ + R) * gronwallBound δ (LF L β γ R) ε T := by
        gcongr

end PVNP.ContinuumPrecision
