import PVNP.GalerkinTaylorSeries

/-!
# A certified multi-step Taylor integrator for the frozen Galerkin flow

The integrator restarts the order-`q` Taylor step from computed values. Each computed step may
deviate from the exact Taylor polynomial by an arbitrary implementation error of size at most
`ρ`, which covers rounding of any kind. The global error after `N` steps is bounded explicitly.

* `flowSeries h v = Σ h^n c_n(v)` is the series flow, and `taylorStep q h v` is its degree-`q`
  truncation.
* `tail_bound`: `‖flowSeries h v − taylorStep q h v‖ ≤ 2K (λh)^{q+1}` for `‖v‖ ≤ K`, at any
  point of the ball, not only on the trajectory.
* `flowSeries_lipschitz`: for `‖v‖, ‖w‖ ≤ K` and `0 ≤ h < r`,
  `‖flowSeries h v − flowSeries h w‖ ≤ e^{L'h} ‖v − w‖` with `L' = Ω + LF(2K)`. The proof applies
  Gronwall's inequality to the two series solutions.
* `step_error`: one restarted step from `ṽ` near `u(t)` has error at most
  `e^{L'h}‖ṽ − u(t)‖ + 2K(λh)^{q+1}`. It uses the identification `galerkin_taylor_series`.
* `integrator_error`: if `‖ũ_{j+1} − taylorStep q h ũ_j‖ ≤ ρ`, then
  `‖ũ_j − u(jh)‖ ≤ E_j = A^j e₀ + (Σ_{i<j} A^i)(τ + ρ)` as long as `E_N ≤ 1`. Here `A = e^{L'h}`
  and `τ = 2K(λh)^{q+1}`.
* `certified_integrator`: explicit sufficient conditions for final error `≤ ε`. They are
  `h(2λ+2) ≤ 1`, `2^{q+1} ε ≥ 4KN e^{L'T}` and `2N e^{L'T} ρ ≤ ε`. The number of steps, the
  order and the required precision `log₂(1/ρ)` are therefore linear in `T` and in `log(1/ε)`.

Scope. These are statements about the exact Taylor map and arbitrary bounded per-step errors.
An operation count in a formal machine model is not given here.
-/

namespace PVNP.GalerkinTaylor

open Finset PVNP.Torus PVNP.TaylorMajorant PVNP.TorusGalerkin Complex

variable {L : ℝ}

/-- The series flow map `Ψ_h(v) = Σ_n h^n c_n(v)`. -/
noncomputable def flowSeries (L κ β γ : ℝ) (S : Finset Z2) (h : ℝ) (v : ℓ2) : ℓ2 :=
  ∑' n, h ^ n • coeff L κ β γ S v n

/-- One Taylor step of order `q`. -/
noncomputable def taylorStep (L κ β γ : ℝ) (S : Finset Z2) (q : ℕ) (h : ℝ) (v : ℓ2) : ℓ2 :=
  ∑ n ∈ range (q+1), h ^ n • coeff L κ β γ S v n

/-- The tail of a dominated Taylor series. -/
theorem tail_of_dom {c : ℕ → ℓ2} {K lam h : ℝ} (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (hc : Dom K lam c) (hlh : lam * |h| ≤ 1/2) (q : ℕ) :
    ‖∑' n, h ^ n • c n - ∑ n ∈ range (q+1), h ^ n • c n‖ ≤ 2 * K * (lam * |h|) ^ (q+1) := by
  have hs := hc.hasSum hK hlam (by linarith)
  have htail := (hasSum_nat_add_iff' (q+1)).mpr hs
  have e : ∑' n, h ^ n • c n - ∑ n ∈ range (q+1), h ^ n • c n =
      ∑' i, h ^ (i + (q+1)) • c (i + (q+1)) := htail.tsum_eq.symm
  rw [e]
  have hsn : Summable fun i => ‖h ^ (i + (q+1)) • c (i + (q+1))‖ :=
    (summable_nat_add_iff (f := fun n => ‖h ^ n • c n‖) (q+1)).mpr
      (hc.summable hK hlam (by linarith))
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) (fun N => ?_)
  have ht := taylor_tail_le (a := fun n => ‖c n‖) hK hlam (abs_nonneg h) hlh hc q (q + 1 + N)
  rw [Finset.sum_Ico_eq_sum_range, show q + 1 + N - (q + 1) = N by omega] at ht
  calc ∑ i ∈ range N, ‖h ^ (i + (q+1)) • c (i + (q+1))‖
      = ∑ k ∈ range N, ‖c (q + 1 + k)‖ * |h| ^ (q + 1 + k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_smul, norm_pow, Real.norm_eq_abs, mul_comm, add_comm k (q+1)]
    _ ≤ _ := ht

/-- **Local truncation error at any point of the ball.** -/
theorem tail_bound (hL : 0 < L) (κ β γ : ℝ) (S : Finset Z2) {v : ℓ2} {K Ω h : ℝ}
    (hK : 0 ≤ K) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω) (hv : ‖v‖ ≤ K) (hh : 0 ≤ h)
    (hlh : rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * h ≤ 1/2) (q : ℕ) :
    ‖flowSeries L κ β γ S h v - taylorStep L κ β γ S q h v‖ ≤
      2 * K * (rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * h) ^ (q+1) := by
  have hC := CA_nonneg hL
  have hlam : 0 ≤ rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) :=
    rate_nonneg hΩ (by positivity) (by positivity)
  have hc := coeff_dom hL κ β γ S hK hΩ hS hv
  have := tail_of_dom hK hlam hc (h := h) (by rwa [abs_of_nonneg hh]) q
  rwa [abs_of_nonneg hh] at this

theorem flowSeries_zero (L κ β γ : ℝ) (S : Finset Z2) (v : ℓ2) :
    flowSeries L κ β γ S 0 v = v := by
  unfold flowSeries
  rw [series_zero, coeff_zero]

/-- **Stability of the series flow.** Gronwall's inequality for the two series solutions. -/
theorem flowSeries_lipschitz (hL : 0 < L) (κ β γ : ℝ) (S : Finset Z2) {v w : ℓ2}
    {K Ω r h : ℝ} (hK : 0 ≤ K) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω) (hv : ‖v‖ ≤ K)
    (hw : ‖w‖ ≤ K) (hr : 0 < r) (hlr : rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * r ≤ 1/2)
    (hh0 : 0 ≤ h) (hhr : h < r) :
    ‖flowSeries L κ β γ S h v - flowSeries L κ β γ S h w‖ ≤
      ‖v - w‖ * Real.exp ((Ω + LF L β γ (2 * K)) * h) := by
  have hC := CA_nonneg hL
  have hlam : 0 ≤ rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) :=
    rate_nonneg hΩ (by positivity) (by positivity)
  have hcv := coeff_dom hL κ β γ S hK hΩ hS hv
  have hcw := coeff_dom hL κ β γ S hK hΩ hS hw
  have hsub : Set.Icc (0:ℝ) h ⊆ Set.Ioo (-r) r := fun y hy => ⟨by linarith [hy.1], by
    linarith [hy.2]⟩
  have hlh : ∀ y ∈ Set.Icc (0:ℝ) h, rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * |y| ≤ 1 := by
    intro y hy
    rw [abs_of_nonneg hy.1]
    have := mul_le_mul_of_nonneg_left (hy.2.trans hhr.le) hlam
    linarith
  have dv : ∀ y ∈ Set.Icc (0:ℝ) h, HasDerivAt (fun y => flowSeries L κ β γ S y v)
      (physField L κ β γ S (flowSeries L κ β γ S y v)) y := fun y hy =>
    series_solves hL κ β γ S hK hΩ hS hv hr hlr (hsub hy)
  have dw : ∀ y ∈ Set.Icc (0:ℝ) h, HasDerivAt (fun y => flowSeries L κ β γ S y w)
      (physField L κ β γ S (flowSeries L κ β γ S y w)) y := fun y hy =>
    series_solves hL κ β γ S hK hΩ hS hw hr hlr (hsub hy)
  have key := dist_le_of_trajectories_ODE_of_mem (v := fun _ => physField L κ β γ S)
    (s := fun _ => Metric.closedBall 0 (2 * K)) (K := Real.toNNReal (Ω + LF L β γ (2 * K)))
    (f := fun y => flowSeries L κ β γ S y v) (g := fun y => flowSeries L κ β γ S y w)
    (a := 0) (b := h) (δ := ‖v - w‖)
    (fun _ _ => physField_lipschitz hL κ β γ S hΩ hS)
    (fun y hy => (dv y hy).continuousAt.continuousWithinAt)
    (fun y hy => (dv y (Set.Ico_subset_Icc_self hy)).hasDerivWithinAt)
    (fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_series_le hK hlam hcv (hlh y (Set.Ico_subset_Icc_self hy)))
    (fun y hy => (dw y hy).continuousAt.continuousWithinAt)
    (fun y hy => (dw y (Set.Ico_subset_Icc_self hy)).hasDerivWithinAt)
    (fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_series_le hK hlam hcw (hlh y (Set.Ico_subset_Icc_self hy)))
    (by simp only [flowSeries_zero, dist_eq_norm, le_refl]) h ⟨hh0, le_rfl⟩
  rw [dist_eq_norm, Real.coe_toNNReal _ (add_nonneg hΩ (LF_nonneg L β γ (2 * K))),
    sub_zero] at key
  exact key

/-- **One restarted step.** -/
theorem step_error (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    {K₀ Ω r h : ℝ} (hK₀ : 0 ≤ K₀) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω)
    (hbd : ∀ t, ‖u t‖ ≤ K₀) (hr : 0 < r)
    (hlr : rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * r ≤ 1/2)
    (hh0 : 0 ≤ h) (hhr : h < r) (q : ℕ) (t : ℝ) {v : ℓ2} (hv : ‖v - u t‖ ≤ 1) :
    ‖taylorStep L κ β γ S q h v - u (t + h)‖ ≤
      Real.exp ((Ω + LF L β γ (2 * (K₀ + 1))) * h) * ‖v - u t‖ +
        2 * (K₀ + 1) * (rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * h) ^ (q+1) := by
  have hK : 0 ≤ K₀ + 1 := by linarith
  have hbd' : ∀ t, ‖u t‖ ≤ K₀ + 1 := fun t => (hbd t).trans (by linarith)
  have hvK : ‖v‖ ≤ K₀ + 1 := by
    have := norm_le_insert' v (u t)
    linarith [hbd t]
  have hC := CA_nonneg hL
  have hlam : 0 ≤ rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) :=
    rate_nonneg hΩ (by positivity) (by positivity)
  have hlh : rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * h ≤ 1/2 := by
    have := mul_le_mul_of_nonneg_left hhr.le hlam
    linarith
  have hid : flowSeries L κ β γ S h (u t) = u (t + h) :=
    (galerkin_taylor_series hL hu hK hΩ hS hbd' t hr hlr
      (by rw [abs_of_nonneg hh0]; exact hhr)).tsum_eq
  have h1 := tail_bound hL κ β γ S hK hΩ hS hvK hh0 hlh q
  have h2 := flowSeries_lipschitz hL κ β γ S hK hΩ hS hvK (hbd' t) hr hlr hh0 hhr
  calc ‖taylorStep L κ β γ S q h v - u (t + h)‖
      = ‖(flowSeries L κ β γ S h v - flowSeries L κ β γ S h (u t)) -
          (flowSeries L κ β γ S h v - taylorStep L κ β γ S q h v)‖ := by
        rw [hid]; congr 1; abel
    _ ≤ ‖flowSeries L κ β γ S h v - flowSeries L κ β γ S h (u t)‖ +
          ‖flowSeries L κ β γ S h v - taylorStep L κ β γ S q h v‖ := norm_sub_le _ _
    _ ≤ ‖v - u t‖ * Real.exp ((Ω + LF L β γ (2 * (K₀ + 1))) * h) +
          2 * (K₀ + 1) * (rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * h) ^ (q+1) :=
        add_le_add h2 h1
    _ = _ := by ring

/-- The discrete Gronwall bound `E_j = A^j e₀ + (Σ_{i<j} A^i) d`. -/
noncomputable def gronE (A e₀ d : ℝ) (j : ℕ) : ℝ := A ^ j * e₀ + (∑ i ∈ range j, A ^ i) * d

theorem gronE_succ (A e₀ d : ℝ) (j : ℕ) : gronE A e₀ d (j+1) = A * gronE A e₀ d j + d := by
  unfold gronE
  have hs : ∑ i ∈ range (j+1), A ^ i = A * ∑ i ∈ range j, A ^ i + 1 := by
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ']
  rw [hs, pow_succ]
  ring

theorem gronE_mono {A e₀ d : ℝ} (hA : 1 ≤ A) (he : 0 ≤ e₀) (hd : 0 ≤ d) {j k : ℕ}
    (hjk : j ≤ k) : gronE A e₀ d j ≤ gronE A e₀ d k := by
  unfold gronE
  have hA0 : 0 ≤ A := by linarith
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hjk) he
  · exact mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk)
        (fun i _ _ => pow_nonneg hA0 i)) hd

theorem gronE_le {A e₀ d : ℝ} (hA : 1 ≤ A) (hd : 0 ≤ d) (j : ℕ) :
    gronE A e₀ d j ≤ A ^ j * (e₀ + j * d) := by
  unfold gronE
  have hA0 : 0 ≤ A := by linarith
  have hs : ∑ i ∈ range j, A ^ i ≤ j * A ^ j := by
    calc ∑ i ∈ range j, A ^ i ≤ ∑ _i ∈ range j, A ^ j :=
          Finset.sum_le_sum fun i hi => pow_le_pow_right₀ hA (Finset.mem_range.mp hi).le
      _ = j * A ^ j := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_right hs hd, pow_nonneg hA0 j]

/-- **Global error of the restarted integrator** with arbitrary per-step errors `≤ ρ`. -/
theorem integrator_error (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    {K₀ Ω r h ρ e₀ : ℝ} (hK₀ : 0 ≤ K₀) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω)
    (hbd : ∀ t, ‖u t‖ ≤ K₀) (hr : 0 < r)
    (hlr : rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * r ≤ 1/2)
    (hh0 : 0 ≤ h) (hhr : h < r) (q N : ℕ) (hρ : 0 ≤ ρ) (he₀ : 0 ≤ e₀)
    {ũ : ℕ → ℓ2} (h0 : ‖ũ 0 - u 0‖ ≤ e₀)
    (hstep : ∀ j, ‖ũ (j+1) - taylorStep L κ β γ S q h (ũ j)‖ ≤ ρ)
    (hsmall : gronE (Real.exp ((Ω + LF L β γ (2 * (K₀ + 1))) * h)) e₀
      (2 * (K₀ + 1) * (rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * h) ^ (q+1) + ρ)
      N ≤ 1) :
    ∀ j ≤ N, ‖ũ j - u (j * h)‖ ≤ gronE (Real.exp ((Ω + LF L β γ (2 * (K₀ + 1))) * h)) e₀
      (2 * (K₀ + 1) * (rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * h) ^ (q+1) + ρ)
      j := by
  set A := Real.exp ((Ω + LF L β γ (2 * (K₀ + 1))) * h) with hAdef
  set τ := 2 * (K₀ + 1) * (rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * h) ^ (q+1)
    with hτdef
  have hC := CA_nonneg hL
  have hlam : 0 ≤ rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) :=
    rate_nonneg hΩ (by positivity) (by positivity)
  have hA : 1 ≤ A := by
    rw [hAdef]
    exact Real.one_le_exp (mul_nonneg (add_nonneg hΩ (LF_nonneg _ _ _ _)) hh0)
  have hτ : 0 ≤ τ := by rw [hτdef]; positivity
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.cast_zero, zero_mul]
    unfold gronE
    simpa using h0
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    have hsm : gronE A e₀ (τ + ρ) j ≤ 1 :=
      (gronE_mono hA he₀ (add_nonneg hτ hρ) (by omega)).trans hsmall
    have hv : ‖ũ j - u (j * h)‖ ≤ 1 := hprev.trans hsm
    have hs := step_error hL hu hK₀ hΩ hS hbd hr hlr hh0 hhr q (j * h) hv
    have ht : (((j + 1 : ℕ) : ℝ)) * h = j * h + h := by push_cast; ring
    rw [ht, gronE_succ]
    calc ‖ũ (j+1) - u (j * h + h)‖
        ≤ ‖ũ (j+1) - taylorStep L κ β γ S q h (ũ j)‖ +
            ‖taylorStep L κ β γ S q h (ũ j) - u (j * h + h)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ρ + (A * ‖ũ j - u (j * h)‖ + τ) := add_le_add (hstep j) hs
      _ ≤ ρ + (A * gronE A e₀ (τ + ρ) j + τ) := by
          gcongr
      _ = A * gronE A e₀ (τ + ρ) j + (τ + ρ) := by ring

/-- **Certified integrator: explicit parameters for accuracy `ε`.** Take `N` steps of size
`h = T/N` with `h(2λ+2) ≤ 1`, order `q` with `2^{q+1} ε ≥ 4KN e^{L'T}`, and per-step implementation
error `ρ` with `2N e^{L'T} ρ ≤ ε`, where `K = K₀ + 1`. Starting from the exact initial value,
the computed state at step `N` is within `ε` of the true state `u(T)`. -/
theorem certified_integrator (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    {K₀ Ω T ε ρ : ℝ} (hK₀ : 0 ≤ K₀) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω)
    (hbd : ∀ t, ‖u t‖ ≤ K₀) (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 ≤ ρ)
    (N q : ℕ) (hN : 1 ≤ N)
    (hstepsize : T / N * (2 * rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) + 2) ≤ 1)
    (horder : 4 * (K₀ + 1) * N * Real.exp ((Ω + LF L β γ (2 * (K₀ + 1))) * T) ≤
      2 ^ (q+1) * ε)
    (hprec : 2 * N * Real.exp ((Ω + LF L β γ (2 * (K₀ + 1))) * T) * ρ ≤ ε)
    {ũ : ℕ → ℓ2} (h0 : ũ 0 = u 0)
    (hstep : ∀ j, ‖ũ (j+1) - taylorStep L κ β γ S q (T / N) (ũ j)‖ ≤ ρ) :
    ‖ũ N - u T‖ ≤ ε := by
  set lam := rate (K₀ + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) with hlamdef
  set L' := Ω + LF L β γ (2 * (K₀ + 1)) with hL'def
  set h := T / N with hhdef
  have hC := CA_nonneg hL
  have hlam : 0 ≤ lam := rate_nonneg hΩ (by positivity) (by positivity)
  have hL' : 0 ≤ L' := add_nonneg hΩ (LF_nonneg _ _ _ _)
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hh0 : 0 ≤ h := div_nonneg hT hNpos.le
  obtain ⟨hr, hlr⟩ := radius_admissible hlam
  have hhr : h < 1 / (2 * lam + 1) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hlh : lam * h ≤ 1/2 := by nlinarith
  have hNh : (N:ℝ) * h = T := by rw [hhdef]; field_simp
  have hA : Real.exp (L' * h) ^ N = Real.exp (L' * T) := by
    rw [← Real.exp_nat_mul, ← hNh]; ring_nf
  -- the local truncation error
  have hτ : 2 * (K₀ + 1) * (lam * h) ^ (q+1) ≤ ε / (2 * N * Real.exp (L' * T)) := by
    have hp : (lam * h) ^ (q+1) ≤ (1/2) ^ (q+1) := pow_le_pow_left₀ (by positivity) hlh _
    have hE : 0 < Real.exp (L' * T) := Real.exp_pos _
    rw [le_div_iff₀ (by positivity)]
    have h2 : (1/2 : ℝ) ^ (q+1) * 2 ^ (q+1) = 1 := by
      rw [← mul_pow]; norm_num
    have hK1 : 0 ≤ K₀ + 1 := by linarith
    calc 2 * (K₀ + 1) * (lam * h) ^ (q+1) * (2 * N * Real.exp (L' * T))
        ≤ 2 * (K₀ + 1) * (1/2) ^ (q+1) * (2 * N * Real.exp (L' * T)) := by gcongr
      _ = (1/2) ^ (q+1) * (4 * (K₀ + 1) * N * Real.exp (L' * T)) := by ring
      _ ≤ (1/2) ^ (q+1) * (2 ^ (q+1) * ε) := by gcongr
      _ = ε := by rw [← mul_assoc, h2, one_mul]
  have hρ' : ρ ≤ ε / (2 * N * Real.exp (L' * T)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  -- the Gronwall sum
  have hG : gronE (Real.exp (L' * h)) 0 (2 * (K₀ + 1) * (lam * h) ^ (q+1) + ρ) N ≤ ε := by
    have hA1 : 1 ≤ Real.exp (L' * h) := Real.one_le_exp (mul_nonneg hL' hh0)
    refine (gronE_le hA1 (by positivity) N).trans ?_
    rw [hA, zero_add]
    have hd : 2 * (K₀ + 1) * (lam * h) ^ (q+1) + ρ ≤ ε / (N * Real.exp (L' * T)) := by
      have := add_le_add hτ hρ'
      calc _ ≤ ε / (2 * N * Real.exp (L' * T)) + ε / (2 * N * Real.exp (L' * T)) := this
        _ = ε / (N * Real.exp (L' * T)) := by field_simp; ring
    calc Real.exp (L' * T) * (N * (2 * (K₀ + 1) * (lam * h) ^ (q+1) + ρ))
        ≤ Real.exp (L' * T) * (N * (ε / (N * Real.exp (L' * T)))) := by gcongr
      _ = ε := by field_simp
  have herr := integrator_error hL hu hK₀ hΩ hS hbd hr hlr hh0 hhr q N hρ le_rfl
    (by rw [h0, sub_self, norm_zero]) hstep (hG.trans hε1) N le_rfl
  rw [hNh] at herr
  exact herr.trans hG

end PVNP.GalerkinTaylor
