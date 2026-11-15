import PVNP.ContinuumPrecision

/-!
# Finite Fourier vector fields, consistency, and residual certification

`galerkin S` is the finite Fourier compression of the actual interaction-picture cubic–quintic
vector field. The proofs distinguish pointwise consistency from a uniform effective rate.
An H² ball admits no uniform finite Fourier approximation in H². This does not rule out
simulation with weaker norms, adaptive representations, or additional regularity.
-/
open Filter Topology
namespace PVNP.TorusGalerkin
open PVNP.Torus PVNP.ContinuumPrecision

/-- Fourier projection is a contraction in the actual H² state norm. -/
theorem trunc_norm_le (S : Finset Z2) (v : ℓ2) : ‖trunc S v‖ ≤ ‖v‖ := by
  have h : ‖trunc S v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq]
    apply tsum_le_tsum _ (summable_sq _) (summable_sq _)
    intro k
    rw [trunc_apply]
    split_ifs <;> simp [sq_nonneg]
  nlinarith [norm_nonneg (trunc S v), norm_nonneg v]

theorem trunc_sub (S : Finset Z2) (v w : ℓ2) :
    trunc S (v - w) = trunc S v - trunc S w := by
  ext k
  simp only [trunc_apply, lp.coeFn_sub, Pi.sub_apply]
  split_ifs <;> simp

/-- Explicit finite-dimensional vector field, with zero derivative outside S. -/
noncomputable def galerkin (S : Finset Z2) (L κ β γ t : ℝ) (v : ℓ2) : ℓ2 :=
  trunc S (Gf L κ β γ t (trunc S v))

theorem galerkin_support (S : Finset Z2) (L κ β γ t : ℝ) (v : ℓ2)
    {k : Z2} (hk : k ∉ S) : galerkin S L κ β γ t v k = 0 := by
  simp [galerkin, trunc_apply, hk]

/-- Compression does not worsen the local Lipschitz constant. -/
theorem galerkin_lipschitz {L κ β γ R : ℝ} (hL : 0 < L)
    (S : Finset Z2) (t : ℝ) {v w : ℓ2} (hv : ‖v‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖galerkin S L κ β γ t v - galerkin S L κ β γ t w‖ ≤
      LF L β γ R * ‖v - w‖ := by
  unfold galerkin
  rw [← trunc_sub]
  calc
    _ ≤ ‖Gf L κ β γ t (trunc S v) - Gf L κ β γ t (trunc S w)‖ := trunc_norm_le _ _
    _ ≤ LF L β γ R * ‖trunc S v - trunc S w‖ :=
      norm_Gf_sub_le hL t ((trunc_norm_le S v).trans hv) ((trunc_norm_le S w).trans hw)
    _ ≤ LF L β γ R * ‖v - w‖ := by
      rw [← trunc_sub]
      exact mul_le_mul_of_nonneg_left (trunc_norm_le S (v - w)) (LF_nonneg L β γ R)

/-- Consistency error splits into the input tail and the nonlinear output tail. -/
theorem consistency_bound {L κ β γ R : ℝ} (hL : 0 < L)
    (S : Finset Z2) (t : ℝ) {v : ℓ2} (hv : ‖v‖ ≤ R) :
    ‖galerkin S L κ β γ t v - Gf L κ β γ t v‖ ≤
      LF L β γ R * ‖trunc S v - v‖ +
        ‖trunc S (Gf L κ β γ t v) - Gf L κ β γ t v‖ := by
  calc
    _ ≤ ‖galerkin S L κ β γ t v - trunc S (Gf L κ β γ t v)‖ +
        ‖trunc S (Gf L κ β γ t v) - Gf L κ β γ t v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ LF L β γ R * ‖trunc S v - v‖ +
        ‖trunc S (Gf L κ β γ t v) - Gf L κ β γ t v‖ := by
      apply add_le_add_right
      unfold galerkin
      rw [← trunc_sub]
      exact (trunc_norm_le S _).trans
        (norm_Gf_sub_le hL t ((trunc_norm_le S v).trans hv) hv)

/-- Pointwise consistency for every actual H² datum, without an assumed tail rate. -/
theorem galerkin_consistent {L κ β γ : ℝ} (hL : 0 < L) (t : ℝ) (v : ℓ2) :
    Tendsto (fun S : Finset Z2 => ‖galerkin S L κ β γ t v - Gf L κ β γ t v‖)
      atTop (𝓝 0) := by
  have h₁ : Tendsto (fun S : Finset Z2 => ‖trunc S v - v‖) atTop (𝓝 0) := by
    simpa using ((tendsto_trunc v).sub (show Tendsto (fun _ : Finset Z2 => v) atTop (𝓝 v) from tendsto_const_nhds)).norm
  have h₂ : Tendsto (fun S : Finset Z2 =>
      ‖trunc S (Gf L κ β γ t v) - Gf L κ β γ t v‖) atTop (𝓝 0) := by
    simpa using ((tendsto_trunc (Gf L κ β γ t v)).sub (show Tendsto (fun _ : Finset Z2 => Gf L κ β γ t v) atTop (𝓝 (Gf L κ β γ t v)) from tendsto_const_nhds)).norm
  exact squeeze_zero (fun _ => norm_nonneg _) (fun S => consistency_bound hL S t le_rfl)
    (by simpa using (h₁.const_mul (LF L β γ ‖v‖)).add h₂)

/-- A computable finite-system residual still needs a nonlinear tail certificate.
The two errors add; this is the residual required by `approx_readout`. -/
theorem residual_certificate (S : Finset Z2) (L κ β γ t : ℝ)
    (v dv : ℓ2) {η τ : ℝ}
    (hnumeric : ‖dv - trunc S (Gf L κ β γ t v)‖ ≤ η)
    (htail : ‖trunc S (Gf L κ β γ t v) - Gf L κ β γ t v‖ ≤ τ) :
    ‖dv - Gf L κ β γ t v‖ ≤ η + τ :=
  (norm_sub_le_norm_sub_add_norm_sub dv (trunc S (Gf L κ β γ t v)) _).trans (add_le_add hnumeric htail)

/-- A unit H² datum can sit entirely outside any proposed finite mode set. -/
theorem no_uniform_H2_cutoff (S : Finset Z2) :
    ∃ v : ℓ2, ‖v‖ = 1 ∧ trunc S v = 0 ∧ ‖trunc S v - v‖ = 1 := by
  obtain ⟨k, hk⟩ := Infinite.exists_not_mem_finset S
  let v : ℓ2 := lp.single 2 k (1 : ℂ)
  have hv : ‖v‖ = 1 := by
    simp only [v, lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one]
  have hz : trunc S v = 0 := by
    ext j
    rw [trunc_apply]
    by_cases hj : j ∈ S
    · rw [if_pos hj]
      have hkj : j ≠ k := by intro h; subst j; exact hk hj
      simp [v, lp.coeFn_single, Pi.single_eq_of_ne hkj]
    · simp [hj]
  exact ⟨v, hv, hz, by rw [hz, zero_sub, norm_neg, hv]⟩

/-- An explicit stronger-regularity budget gives an effective H² truncation bound.
The budget is the squared H⁴ norm in the repository's weighted Fourier coordinates.
It is an additional hypothesis, not a consequence of the conserved H² bound. -/
theorem higher_regularity_tail (L : ℝ) (S : Finset Z2) (v : ℓ2) {K B : ℝ}
    (hK : 0 < K) (hcut : ∀ k ∉ S, K ≤ wt L k)
    (hsum : Summable fun k => wt L k ^ 2 * ‖v k‖ ^ 2)
    (hbudget : (∑' k, wt L k ^ 2 * ‖v k‖ ^ 2) ≤ B) :
    ‖trunc S v - v‖ ^ 2 ≤ B / K ^ 2 := by
  have hp : ∀ k, K ^ 2 * ‖(trunc S v - v) k‖ ^ 2 ≤ wt L k ^ 2 * ‖v k‖ ^ 2 := by
    intro k
    simp only [lp.coeFn_sub, Pi.sub_apply, trunc_apply]
    by_cases hk : k ∈ S
    · simp only [if_pos hk, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      positivity
    · rw [if_neg hk, zero_sub, norm_neg]
      have hw := hcut k hk
      have hsq : K ^ 2 ≤ wt L k ^ 2 := by nlinarith [wt_pos L k]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have h := tsum_le_tsum hp ((summable_sq (trunc S v - v)).mul_left (K ^ 2)) hsum
  rw [tsum_mul_left, ← norm_sq_eq] at h
  apply (le_div_iff₀ (sq_pos_of_pos hK)).2
  nlinarith [h.trans hbudget]

/-- Numeric residual and Fourier tail certificates feed the frozen-flow detector theorem.
This is an a posteriori theorem, not a polynomial-time algorithm to obtain the certificates. -/
theorem certified_readout {L κ β γ : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    {χv : ℓ2} (hreal : rev (co L χv) = co L χv)
    {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) {R : ℝ}
    (hRu : Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0)) ≤ R)
    (S : Finset Z2) {W W' : ℝ → ℓ2} {T η τ δ : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn W (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt W (W' t) (Set.Ici t) t)
    (hnumeric : ∀ t ∈ Set.Ico 0 T, ‖W' t - trunc S (Gf L κ β γ t (W t))‖ ≤ η)
    (htail : ∀ t ∈ Set.Ico 0 T,
      ‖trunc S (Gf L κ β γ t (W t)) - Gf L κ β γ t (W t)‖ ≤ τ)
    (hball : ∀ t ∈ Set.Ico 0 T, ‖W t‖ ≤ R) (h0 : ‖W 0 - u 0‖ ≤ δ) :
    |Jdet L χv (U L κ T (W T)) - Jdet L χv (u T)| ≤
      Cdet L χv * (‖W T‖ + R) * gronwallBound δ (LF L β γ R) (η + τ) T := by
  apply approx_readout hL hγ hreal hu hRu hT hc hd _ hball h0
  intro t ht
  exact residual_certificate S L κ β γ t (W t) (W' t) (hnumeric t ht) (htail t ht)

end PVNP.TorusGalerkin
