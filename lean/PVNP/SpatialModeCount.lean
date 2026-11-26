import PVNP.WeakGlobalComparison

/-!
# Spatial mode counts: analytic versus Sobolev tails

The weak-norm comparison (`weak_trajectory_error`) bounds the Galerkin error by
`gronwallBound δ LF η T ≤ (δ + ηT) e^{LF·T}`. Here `δ` is the initial tail, and `η` bounds the
omitted output tail along the Galerkin trajectory. This module shows that the required number of
modes depends on how fast those tails decay.

* `weighted_tail`: if every omitted mode has weight `ω_k ≥ Θ > 0`, then
  `‖P_S ψ − ψ‖_{L²} ≤ M/√Θ` whenever `Σ ω_k |ψ̂_k|² ≤ M²`. This is an effective tail bound for any
  weight.
* `analytic_tail`: with `ω_k = e^{2σ|k|}` (analytic or Gevrey-type decay) and every omitted mode
  of size at least `N`, the tail is at most `M e^{−σN}`.
* `gronwallBound_le`: `gronwallBound δ A η t ≤ (δ + ηt) e^{At}`.
* `analytic_mode_count`: if both tails are at most `M e^{−σN}`, then error `≤ ε` whenever
  `σN ≥ A T + log(M(1+T)/ε)`. A cutoff size *linear* in `T` absorbs the exponential
  amplification `e^{AT}`.
* `sobolev_count_lower`: if the tails are only known to be `M N^{−s}`, the same sufficient
  condition needs `N^s ≥ M(1+T) e^{AT}/ε`, which is exponential in `T`. This concerns the sufficient
  condition only; it is not a lower bound on the number of modes any method needs.
* `galerkin_error_of_tail`: the comparison for the actual Galerkin and PDE trajectories, given
  the two tail bounds.

Scope. The tail hypotheses along the trajectory are hypotheses. The conserved `H²` bound gives
only the Sobolev case (`weak_galerkin_residual`). Propagated analytic decay of the frozen flow,
uniform in `S`, is neither proved nor refuted here.
-/

open Complex Real
namespace PVNP.TorusGalerkin
open PVNP.Torus

/-- **Effective weighted tail.** -/
theorem weighted_tail (L : ℝ) (S : Finset Z2) (v : ℓ2) {ω : Z2 → ℝ} {Θ M : ℝ} (hΘ : 0 < Θ)
    (hM0 : 0 ≤ M) (hω : ∀ k, 0 ≤ ω k) (hcut : ∀ k ∉ S, Θ ≤ ω k)
    (hsum : Summable fun k => ω k * ‖co L v k‖ ^ 2)
    (hM : ∑' k, ω k * ‖co L v k‖ ^ 2 ≤ M ^ 2) :
    ‖Lc L (trunc S v - v)‖ ≤ M / Real.sqrt Θ := by
  have hp : ∀ k : Z2, ‖Lc L (trunc S v - v) k‖ ^ 2 ≤ Θ⁻¹ * (ω k * ‖co L v k‖ ^ 2) := by
    intro k
    rw [Lc_apply]
    have hco : co L (trunc S v - v) k = (if k ∈ S then 0 else -co L v k) := by
      simp only [co, lp.coeFn_sub, Pi.sub_apply, trunc_apply]
      split_ifs <;> ring
    rw [hco]
    split_ifs with hk
    · rw [norm_zero, zero_pow two_ne_zero]
      exact mul_nonneg (inv_nonneg.2 hΘ.le) (mul_nonneg (hω k) (sq_nonneg _))
    · rw [norm_neg]
      have h1 : Θ⁻¹ * ω k ≥ 1 := by
        rw [ge_iff_le, ← div_eq_inv_mul, one_le_div hΘ]; exact hcut k hk
      nlinarith [sq_nonneg ‖co L v k‖]
  have hs : Summable fun k => ‖Lc L (trunc S v - v) k‖ ^ 2 := summable_sq _
  have h := Summable.tsum_le_tsum hp hs (hsum.mul_left Θ⁻¹)
  rw [tsum_mul_left] at h
  apply norm_le_of_tsum_sq_le _ (by positivity)
  rw [div_pow, Real.sq_sqrt hΘ.le]
  calc ∑' k, ‖Lc L (trunc S v - v) k‖ ^ 2 ≤ Θ⁻¹ * ∑' k, ω k * ‖co L v k‖ ^ 2 := h
    _ ≤ Θ⁻¹ * M ^ 2 := mul_le_mul_of_nonneg_left hM (by positivity)
    _ = M ^ 2 / Θ := by ring

/-- **Analytic tails.** `size` is any size function on modes, for example `|k₁| + |k₂|`. -/
theorem analytic_tail (L : ℝ) (S : Finset Z2) (v : ℓ2) (size : Z2 → ℝ) {σ M N : ℝ}
    (hσ : 0 ≤ σ) (hM0 : 0 ≤ M) (hcut : ∀ k ∉ S, N ≤ size k)
    (hsum : Summable fun k => Real.exp (2 * σ * size k) * ‖co L v k‖ ^ 2)
    (hM : ∑' k, Real.exp (2 * σ * size k) * ‖co L v k‖ ^ 2 ≤ M ^ 2) :
    ‖Lc L (trunc S v - v)‖ ≤ M * Real.exp (-σ * N) := by
  have h := weighted_tail L S v (Θ := Real.exp (2 * σ * N)) (Real.exp_pos _) hM0
    (fun k => (Real.exp_pos _).le)
    (fun k hk => Real.exp_le_exp.2 (by nlinarith [hcut k hk])) hsum hM
  have e : Real.sqrt (Real.exp (2 * σ * N)) = Real.exp (σ * N) := by
    rw [show 2 * σ * N = σ * N + σ * N by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [e, div_eq_mul_inv, ← Real.exp_neg, neg_mul_eq_neg_mul] at h
  exact h

/-- `gronwallBound δ A η t ≤ (δ + ηt) e^{At}`. -/
theorem gronwallBound_le {δ A η t : ℝ} (hA : 0 ≤ A) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    gronwallBound δ A η t ≤ (δ + η * t) * Real.exp (A * t) := by
  have hE : 1 ≤ Real.exp (A * t) := Real.one_le_exp (mul_nonneg hA ht)
  rcases hA.lt_or_eq with hA' | hA'
  · rw [gronwallBound_of_K_ne_0 hA'.ne']
    have h1 := Real.add_one_le_exp (-(A * t))
    have h2 : Real.exp (A * t) * Real.exp (-(A * t)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : Real.exp (A * t) - 1 ≤ A * t * Real.exp (A * t) := by
      nlinarith [Real.exp_pos (A * t)]
    have h4 : η / A * (Real.exp (A * t) - 1) ≤ η * t * Real.exp (A * t) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hA']
      nlinarith [mul_le_mul_of_nonneg_left h3 hη]
    simp only
    nlinarith
  · subst hA'
    rw [gronwallBound_K0, zero_mul, Real.exp_zero, mul_one]

/-- **Analytic tails give a mode count linear in time.** -/
theorem analytic_mode_count {δ η A T M σ ε N : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T) (hM : 0 < M)
    (hε : 0 < ε) (hη : 0 ≤ η)
    (hδM : δ ≤ M * Real.exp (-σ * N)) (hηM : η ≤ M * Real.exp (-σ * N))
    (hN : A * T + Real.log (M * (1 + T) / ε) ≤ σ * N) :
    gronwallBound δ A η T ≤ ε := by
  refine (gronwallBound_le hA hη hT).trans ?_
  have hE := Real.exp_pos (A * T)
  have h1 : (δ + η * T) * Real.exp (A * T) ≤
      M * (1 + T) * Real.exp (-σ * N) * Real.exp (A * T) := by
    apply mul_le_mul_of_nonneg_right _ hE.le
    nlinarith [mul_le_mul_of_nonneg_right hηM hT]
  refine h1.trans ?_
  have hpos : 0 < M * (1 + T) / ε := by positivity
  have h2 : Real.exp (-σ * N) * Real.exp (A * T) ≤ ε / (M * (1 + T)) := by
    rw [← Real.exp_add]
    have : -σ * N + A * T ≤ -Real.log (M * (1 + T) / ε) := by linarith
    calc Real.exp (-σ * N + A * T) ≤ Real.exp (-Real.log (M * (1 + T) / ε)) :=
          Real.exp_le_exp.2 this
      _ = ε / (M * (1 + T)) := by
          rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  have hMT : 0 < M * (1 + T) := by positivity
  calc M * (1 + T) * Real.exp (-σ * N) * Real.exp (A * T)
      = M * (1 + T) * (Real.exp (-σ * N) * Real.exp (A * T)) := by ring
    _ ≤ M * (1 + T) * (ε / (M * (1 + T))) := mul_le_mul_of_nonneg_left h2 hMT.le
    _ = ε := by field_simp

/-- **Sobolev tails: the sufficient condition is exponential in time.** If the tails are only
bounded by `M N^{-s}`, the bound `(δ + ηT) e^{AT} ≤ ε` obtained from them requires
`N^s ≥ M(1+T) e^{AT}/ε`. -/
theorem sobolev_count_lower {A T M ε N s : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hN : 0 < N)
    (h : M * N ^ (-s) * (1 + T) * Real.exp (A * T) ≤ ε) :
    M * (1 + T) * Real.exp (A * T) / ε ≤ N ^ s := by
  have hNs : 0 < N ^ s := Real.rpow_pos_of_pos hN s
  have e : N ^ (-s) = (N ^ s)⁻¹ := Real.rpow_neg hN.le s
  rw [e] at h
  rw [div_le_iff₀ hε]
  have : M * (1 + T) * Real.exp (A * T) = (M * (N ^ s)⁻¹ * (1 + T) * Real.exp (A * T)) * N ^ s := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right h hNs.le |>.trans_eq (mul_comm _ _)

/-- **Mode count for the actual comparison.** Suppose the initial tail and the omitted output tail
along the Galerkin trajectory are at most `M e^{−σN}`. Then the weak Galerkin error at time `T` is at
most `ε` once `σN ≥ LF·T + log(M(1+T)/ε)`. -/
theorem galerkin_error_of_tail {L κ β γ R : ℝ} (hL : 0 < L) {S : Finset Z2}
    {W w : ℝ → ℓ2} {T M σ ε N : ℝ} (hT : 0 ≤ T) (hM : 0 < M) (hε : 0 < ε)
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t)
    (hbW : ∀ t, ‖W t‖ ≤ R) (hbw : ∀ t, ‖w t‖ ≤ R)
    (hres : ∀ t ∈ Set.Ico 0 T,
      ‖Lc L (galerkin S L κ β γ t (W t) - Gf L κ β γ t (W t))‖ ≤ M * Real.exp (-σ * N))
    (h0 : ‖Lc L (W 0 - w 0)‖ ≤ M * Real.exp (-σ * N))
    (hN : LF L β γ R * T + Real.log (M * (1 + T) / ε) ≤ σ * N) :
    ‖Lc L (W T - w T)‖ ≤ ε := by
  have h := weak_trajectory_error hL hW hw (fun t _ => hbW t) (fun t _ => hbw t) hres h0
    T ⟨hT, le_rfl⟩
  exact h.trans (analytic_mode_count (LF_nonneg L β γ R) hT hM hε (by positivity)
    le_rfl le_rfl hN)

end PVNP.TorusGalerkin
