import PVNP.AnalyticNorm

/-!
# Propagation of analytic regularity, uniformly over Galerkin truncations

Let `u` be a physical-picture Galerkin trajectory, `u' = −i(A_S u + P_S Fnl u)`, supported in
`S`. Every constant below is independent of `S`.

* `hasDerivAt_asq`, `deriv_asq_le`: `d/dt A_σ(u)² ≤ 2 A_σ(u) A_σ(Fnl u)`. The dispersion
  contributes nothing, because `Re⟨u_k, −i·om_k u_k⟩ = 0` (`inner_disp_zero`).
* `local_propagation`: if `A_σ(u(t₀)) ≤ M`, then `A_σ(u(t₀+s))² ≤ 4M²` for
  `0 ≤ s ≤ τ(M) = 1/(2(8|β|C_A²M² + 32|γ|C_A⁴M⁴ + 1))`. The proof is the comparison principle
  `image_le_of_deriv_right_lt_deriv_boundary` with barrier `2M²e^{ct}`.
* `global_propagation`: suppose `‖u(t)‖_{H²} ≤ R` for all `t` (true for actual trajectories by
  conservation of mass and Hamiltonian), `2R ≤ M` and `A_{σ₀}(u(0)) ≤ M`. Then for every `j`,
  `A_{σ₀/4^j}(u(jτ))² ≤ M²` and `A_{σ₀/4^j}(u(jτ+s))² ≤ 4M²` for `s ∈ [0, τ]`. At each restart
  the radius drops by the factor 4, using interpolation (`asq_interp`) with the conserved `H²`
  bound.
* `radius_at`: at every time `t ≥ 0`, `A_{σ(t)}(u(t))² ≤ 4M²` with
  `σ(t) = σ₀ 4^{−⌊t/τ⌋}`.

So the analyticity radius is bounded below by `σ₀ e^{−(ln 4)(t/τ + 1)}`. That is an exponential
decay rate polynomial in `M`, which can be taken polynomial in the conserved data and the
initial analytic norm.
-/

namespace PVNP.Analytic

open Finset Set PVNP.Torus PVNP.TorusGalerkin PVNP.GalerkinTaylor Complex

variable {L : ℝ}

theorem asq_eq_sum {S : Finset Z2} {v : ℓ2} (hv : Supported S v) (σ : ℝ) :
    asq σ v = ∑ k ∈ S, (aw σ k * ‖v k‖) ^ 2 := by
  unfold asq
  exact tsum_eq_sum fun k hk => by rw [hv k hk, norm_zero, mul_zero]; norm_num

/-- The derivative of `A_σ(u)²` along the physical-picture Galerkin flow. -/
theorem hasDerivAt_asq {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hs : ∀ t, Supported S (u t)) (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    (σ t : ℝ) :
    HasDerivAt (fun s => asq σ (u s))
      (∑ k ∈ S, (aw σ k) ^ 2 * (2 * inner ℝ (u t k) (physField L κ β γ S (u t) k))) t := by
  have e : (fun s => asq σ (u s)) = fun s => ∑ k ∈ S, (aw σ k) ^ 2 * ‖u s k‖ ^ 2 := by
    funext s
    rw [asq_eq_sum (hs s)]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  exact HasDerivAt.fun_sum fun k _ => ((hasDerivAt_apply (hu t) k).norm_sq).const_mul _

/-- **The dispersion does not contribute.** -/
theorem inner_disp_zero (r : ℝ) (z : ℂ) : inner ℝ z (-I * ((r : ℂ) * z)) = 0 := by
  rw [Complex.inner]
  have e : -I * ((r : ℂ) * z) * (starRingEnd ℂ) z = -I * ((r * Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_assoc, mul_assoc, Complex.mul_conj]; push_cast; ring
  rw [e]
  simp

theorem inner_physField_le (κ β γ : ℝ) (S : Finset Z2) (v : ℓ2) (k : Z2) :
    inner ℝ (v k) (physField L κ β γ S v k) ≤ ‖v k‖ * ‖trunc S (Fnl L β γ v) k‖ := by
  have e : physField L κ β γ S v k =
      -I * (omMul L κ S k * v k) + -I * trunc S (Fnl L β γ v) k := by
    simp only [physField, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add,
      Pi.add_apply, Aop_apply]
    ring
  rw [e, inner_add_right]
  have h0 : inner ℝ (v k) (-I * (omMul L κ S k * v k)) = 0 := by
    unfold omMul
    split_ifs
    · exact inner_disp_zero _ _
    · simp
  rw [h0, zero_add]
  calc inner ℝ (v k) (-I * trunc S (Fnl L β γ v) k)
      ≤ ‖v k‖ * ‖-I * trunc S (Fnl L β γ v) k‖ := real_inner_le_norm _ _
    _ = ‖v k‖ * ‖trunc S (Fnl L β γ v) k‖ := by
        rw [norm_mul, norm_neg, Complex.norm_I, one_mul]

/-- **Derivative bound.** `d/dt A_σ(u)² ≤ 2 A_σ(u) A_σ(Fnl u)`. -/
theorem deriv_asq_le (κ β γ : ℝ) {S : Finset Z2} {v : ℓ2} (hv : Supported S v) {σ : ℝ}
    (hF : ASum σ (Fnl L β γ v)) :
    ∑ k ∈ S, (aw σ k) ^ 2 * (2 * inner ℝ (v k) (physField L κ β γ S v k)) ≤
      2 * anorm σ v * anorm σ (Fnl L β γ v) := by
  set F := trunc S (Fnl L β γ v)
  have h1 : ∑ k ∈ S, (aw σ k) ^ 2 * (2 * inner ℝ (v k) (physField L κ β γ S v k)) ≤
      2 * ∑ k ∈ S, (aw σ k * ‖v k‖) * (aw σ k * ‖F k‖) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := inner_physField_le (L := L) κ β γ S v k
    have ha := sq_nonneg (aw σ k)
    nlinarith
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt S (fun k => aw σ k * ‖v k‖) (fun k => aw σ k * ‖F k‖)
  have hv' : Real.sqrt (∑ k ∈ S, (aw σ k * ‖v k‖) ^ 2) = anorm σ v := by
    rw [anorm, asq_eq_sum hv]
  have hF' : Real.sqrt (∑ k ∈ S, (aw σ k * ‖F k‖) ^ 2) ≤ anorm σ (Fnl L β γ v) := by
    rw [← asq_eq_sum (trunc_supported S _), anorm]
    exact Real.sqrt_le_sqrt (asq_trunc_le S hF)
  calc _ ≤ 2 * ∑ k ∈ S, (aw σ k * ‖v k‖) * (aw σ k * ‖F k‖) := h1
    _ ≤ 2 * (Real.sqrt (∑ k ∈ S, (aw σ k * ‖v k‖) ^ 2) *
          Real.sqrt (∑ k ∈ S, (aw σ k * ‖F k‖) ^ 2)) := by gcongr
    _ ≤ 2 * (anorm σ v * anorm σ (Fnl L β γ v)) := by
        rw [hv']; gcongr; exact anorm_nonneg σ v
    _ = 2 * anorm σ v * anorm σ (Fnl L β γ v) := by ring

/-- The rate of the local step. -/
noncomputable def grate (L β γ M : ℝ) : ℝ :=
  8 * (|β| * CA L ^ 2) * M ^ 2 + 32 * (|γ| * CA L ^ 4) * M ^ 4 + 1

/-- The local time step `τ(M) = 1/(2·grate)`. -/
noncomputable def tstep (L β γ M : ℝ) : ℝ := 1 / (2 * grate L β γ M)

theorem grate_pos (L β γ M : ℝ) : 0 < grate L β γ M := by
  unfold grate; positivity

theorem tstep_pos (L β γ M : ℝ) : 0 < tstep L β γ M := by
  unfold tstep; have := grate_pos L β γ M; positivity

theorem exp_half_le_two : Real.exp (1/2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp (1/2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1/2)]

/-- **Local propagation of analyticity**, uniform in `S`. -/
theorem local_propagation (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hs : ∀ t, Supported S (u t)) (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    {σ M t₀ : ℝ} (hσ : 0 ≤ σ) (hM : 0 < M) (h0 : asq σ (u t₀) ≤ M ^ 2) :
    ∀ s ∈ Icc 0 (tstep L β γ M), asq σ (u (t₀ + s)) ≤ 4 * M ^ 2 := by
  set c := grate L β γ M with hc
  have hc0 : 0 < c := grate_pos L β γ M
  have hC := CA_nonneg hL
  set D : ℝ → ℝ := fun s => ∑ k ∈ S, (aw σ k) ^ 2 *
      (2 * inner ℝ (u (t₀ + s) k) (physField L κ β γ S (u (t₀ + s)) k)) with hD
  have hder : ∀ s, HasDerivAt (fun s => asq σ (u (t₀ + s))) (D s) s := by
    intro s
    have h1 := hasDerivAt_asq hs hu σ (t₀ + s)
    have h2 := h1.scomp s ((hasDerivAt_id s).const_add t₀)
    rw [one_smul] at h2
    exact h2
  set Bf : ℝ → ℝ := fun s => 2 * M ^ 2 * Real.exp (c * s) with hBf
  have hBd : ∀ s, HasDerivAt Bf (2 * M ^ 2 * (Real.exp (c * s) * c)) s := by
    intro s
    have := ((hasDerivAt_id s).const_mul c).exp
    simp only [id, mul_one] at this
    exact this.const_mul _
  have key := image_le_of_deriv_right_lt_deriv_boundary
    (f := fun s => asq σ (u (t₀ + s))) (f' := D) (a := 0) (b := tstep L β γ M)
    (B := Bf) (B' := fun s => 2 * M ^ 2 * (Real.exp (c * s) * c))
    (fun s _ => (hder s).continuousAt.continuousWithinAt)
    (fun s _ => (hder s).hasDerivWithinAt)
    (by
      simp only [add_zero, hBf, mul_zero, Real.exp_zero, mul_one]
      nlinarith [sq_nonneg M])
    hBd
    (by
      intro s hs' heq
      simp only at heq
      have hsτ : s ≤ tstep L β γ M := hs'.2.le
      have hcs : c * s ≤ 1/2 := by
        have : c * tstep L β γ M = 1/2 := by
          rw [tstep, ← hc]; field_simp
        nlinarith [hs'.1]
      have hE : Real.exp (c * s) ≤ 2 := (Real.exp_le_exp.2 hcs).trans exp_half_le_two
      have hEp := Real.exp_pos (c * s)
      set y := asq σ (u (t₀ + s))
      have hy : y = 2 * M ^ 2 * Real.exp (c * s) := heq
      have hy0 : 0 < y := by rw [hy]; positivity
      have hy4 : y ≤ 4 * M ^ 2 := by rw [hy]; nlinarith [sq_nonneg M]
      -- the derivative bound
      have hasum := asum_of_supported (hs (t₀ + s)) σ
      obtain ⟨hF, hFle⟩ := anorm_Fnl_le hL hσ β γ hasum
      have hd := deriv_asq_le (L := L) κ β γ (hs (t₀ + s)) hF
      set a := anorm σ (u (t₀ + s))
      have ha0 : 0 ≤ a := anorm_nonneg _ _
      have ha2 : a ^ 2 = y := anorm_sq _ _
      have hDs : D s ≤ 2 * a * (|β| * CA L ^ 2 * a ^ 3 + |γ| * CA L ^ 4 * a ^ 5) := by
        refine hd.trans ?_
        exact mul_le_mul_of_nonneg_left hFle (by positivity)
      have hb := abs_nonneg β
      have hg := abs_nonneg γ
      have hB0 : 0 ≤ |β| * CA L ^ 2 := by positivity
      have hG0 : 0 ≤ |γ| * CA L ^ 4 := by positivity
      have hpoly : 2 * a * (|β| * CA L ^ 2 * a ^ 3 + |γ| * CA L ^ 4 * a ^ 5) =
          y * (2 * (|β| * CA L ^ 2) * y + 2 * (|γ| * CA L ^ 4) * y ^ 2) := by
        rw [← ha2]; ring
      have hlt : 2 * (|β| * CA L ^ 2) * y + 2 * (|γ| * CA L ^ 4) * y ^ 2 < c := by
        have hy2 : y ^ 2 ≤ 16 * M ^ 4 := by
          have := pow_le_pow_left₀ hy0.le hy4 2
          nlinarith
        rw [hc, grate]
        nlinarith [mul_le_mul_of_nonneg_left hy4 hB0, mul_le_mul_of_nonneg_left hy2 hG0]
      calc D s ≤ 2 * a * (|β| * CA L ^ 2 * a ^ 3 + |γ| * CA L ^ 4 * a ^ 5) := hDs
        _ = y * (2 * (|β| * CA L ^ 2) * y + 2 * (|γ| * CA L ^ 4) * y ^ 2) := hpoly
        _ < y * c := mul_lt_mul_of_pos_left hlt hy0
        _ = 2 * M ^ 2 * (Real.exp (c * s) * c) := by rw [hy]; ring)
  intro s hs'
  have h1 := key hs'
  simp only [hBf] at h1
  have hcs : c * s ≤ 1/2 := by
    have : c * tstep L β γ M = 1/2 := by
      rw [tstep, ← hc]; field_simp
    nlinarith [hs'.1, hs'.2]
  have hE : Real.exp (c * s) ≤ 2 := (Real.exp_le_exp.2 hcs).trans exp_half_le_two
  nlinarith [sq_nonneg M]

/-- **Global propagation with a shrinking radius**, uniform in `S`. -/
theorem global_propagation (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hs : ∀ t, Supported S (u t)) (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    {R M σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hM : 0 < M) (hR : ∀ t, ‖u t‖ ≤ R) (hRM : 2 * R ≤ M)
    (h0 : asq σ₀ (u 0) ≤ M ^ 2) (j : ℕ) :
    asq (σ₀ / 4 ^ j) (u (j * tstep L β γ M)) ≤ M ^ 2 ∧
      ∀ s ∈ Icc 0 (tstep L β γ M),
        asq (σ₀ / 4 ^ j) (u (j * tstep L β γ M + s)) ≤ 4 * M ^ 2 := by
  set τ := tstep L β γ M
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  induction j with
  | zero =>
    have hs0 : asq (σ₀ / 4 ^ 0) (u ((0:ℕ) * τ)) ≤ M ^ 2 := by
      simpa using h0
    exact ⟨hs0, local_propagation hL hs hu (by positivity) hM hs0⟩
  | succ j ih =>
    obtain ⟨_, hloc⟩ := ih
    set σj := σ₀ / 4 ^ j with hσj
    have hσj0 : 0 < σj := by positivity
    set σ' := σ₀ / 4 ^ (j+1) with hσ'
    have hσ'0 : 0 < σ' := by positivity
    have hσrel : σj = 4 * σ' := by rw [hσj, hσ', pow_succ]; field_simp
    have hτ : ((j + 1 : ℕ) : ℝ) * τ = j * τ + τ := by push_cast; ring
    have hend := hloc τ ⟨(tstep_pos L β γ M).le, le_rfl⟩
    have hasum := asum_of_supported (hs (j * τ + τ)) σj
    set N := Real.log 2 / (2 * σ')
    have hI := asq_interp (σ := σj) (σ' := σ') (N := N) hσ'0.le (by rw [hσrel]; linarith)
      hasum
    have e1 : Real.exp (2 * σ' * N) = 2 := by
      have : 2 * σ' * N = Real.log 2 := by
        simp only [N]; field_simp
      rw [this, Real.exp_log (by norm_num)]
    have e2 : Real.exp (-(2 * (σj - σ') * N)) = 1/8 := by
      have : -(2 * (σj - σ') * N) = -(3 * Real.log 2) := by
        rw [hσrel]; simp only [N]; field_simp; ring
      rw [this, Real.exp_neg, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
      norm_num
    have hu2 : ‖u (j * τ + τ)‖ ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hR _) 2
    have hstart : asq σ' (u (((j + 1 : ℕ) : ℝ) * τ)) ≤ M ^ 2 := by
      rw [hτ]
      calc asq σ' (u (j * τ + τ))
          ≤ Real.exp (2 * σ' * N) * ‖u (j * τ + τ)‖ ^ 2 +
              Real.exp (-(2 * (σj - σ') * N)) * asq σj (u (j * τ + τ)) := hI
        _ ≤ 2 * R ^ 2 + 1/8 * (4 * M ^ 2) := by
            rw [e1, e2]; gcongr
        _ ≤ M ^ 2 := by nlinarith
    exact ⟨hstart, local_propagation hL hs hu hσ'0.le hM hstart⟩

/-- **The analyticity radius at time `t`.** -/
theorem radius_at (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hs : ∀ t, Supported S (u t)) (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    {R M σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hM : 0 < M) (hR : ∀ t, ‖u t‖ ≤ R) (hRM : 2 * R ≤ M)
    (h0 : asq σ₀ (u 0) ≤ M ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    asq (σ₀ / 4 ^ (⌊t / tstep L β γ M⌋₊)) (u t) ≤ 4 * M ^ 2 := by
  set τ := tstep L β γ M
  have hτ := tstep_pos L β γ M
  set j := ⌊t / τ⌋₊
  have hj1 : (j : ℝ) ≤ t / τ := Nat.floor_le (div_nonneg ht hτ.le)
  have hj2 : t / τ < j + 1 := Nat.lt_floor_add_one _
  have hs1 : 0 ≤ t - j * τ := by
    have := mul_le_mul_of_nonneg_right hj1 hτ.le
    rw [div_mul_cancel₀ _ hτ.ne'] at this
    linarith
  have hs2 : t - j * τ ≤ τ := by
    have := mul_lt_mul_of_pos_right hj2 hτ
    rw [div_mul_cancel₀ _ hτ.ne'] at this
    linarith
  have h := (global_propagation hL hs hu hσ₀ hM hR hRM h0 j).2 (t - j * τ) ⟨hs1, hs2⟩
  rwa [add_sub_cancel] at h

end PVNP.Analytic
