import PVNP.FiniteNonlinearResidual

/-!
# Conservation for the actual finite Fourier Galerkin flow

Projection is orthogonal in the physical mass and kinetic pairings
and commutes with the free group. Hence the same Hamiltonian and mass
as the full PDE are conserved by the finite-support projected flow.
-/
open Complex Set Filter Topology InnerProductSpace
open scoped Real ENNReal NNReal
namespace PVNP.TorusGalerkin
open PVNP.Torus
variable {L κ β γ : ℝ}

theorem trunc_co (L : ℝ) (S : Finset Z2) (v : ℓ2) (k : Z2) :
    co L (trunc S v) k = if k ∈ S then co L v k else 0 := by
  unfold co
  rw [trunc_apply]
  split_ifs <;> simp

theorem trunc_comm_U (L κ t : ℝ) (S : Finset Z2) (v : ℓ2) :
    U L κ t (trunc S v) = trunc S (U L κ t v) := by
  ext k
  rw [U_apply, trunc_apply, trunc_apply, U_apply]
  split_ifs <;> simp

theorem trunc_smul (S : Finset Z2) (c : ℂ) (v : ℓ2) :
    trunc S (c • v) = c • trunc S v := by
  ext k
  simp only [trunc_apply, lp.coeFn_smul, Pi.smul_apply]
  split_ifs <;> simp

theorem supported_inner_Lc (L : ℝ) {S : Finset Z2} {v : ℓ2}
    (hv : Supported S v) (f : ℓ2) :
    inner ℂ (Lc L v) (Lc L (trunc S f)) = inner ℂ (Lc L v) (Lc L f) := by
  rw [inner_Lc, inner_Lc]
  apply tsum_congr
  intro k
  rw [trunc_co]
  by_cases hk : k ∈ S
  · simp [hk]
  · simp [hk, co, hv k hk]

theorem supported_inner_Ac (L κ : ℝ) {S : Finset Z2} {v : ℓ2}
    (hv : Supported S v) (f : ℓ2) :
    inner ℂ (Ac L κ v) (Ac L κ (trunc S f)) = inner ℂ (Ac L κ v) (Ac L κ f) := by
  rw [inner_Ac, inner_Ac]
  apply tsum_congr
  intro k
  rw [trunc_co]
  by_cases hk : k ∈ S
  · simp [hk]
  · simp [hk, co, hv k hk]

theorem projected_inner_Lc_self (L : ℝ) (S : Finset Z2) (f : ℓ2) :
    inner ℂ (Lc L f) (Lc L (trunc S f)) =
      inner ℂ (Lc L (trunc S f)) (Lc L (trunc S f)) := by
  rw [inner_Lc, inner_Lc]
  apply tsum_congr
  intro k
  simp only [trunc_co]
  split_ifs <;> simp

theorem U_galerkin (S : Finset Z2) (t : ℝ) {v : ℓ2}
    (hv : Supported S v) :
    U L κ t (galerkin S L κ β γ t v) =
      (-I) • trunc S (Fnl L β γ (U L κ t v)) := by
  unfold galerkin
  rw [supported_trunc_eq hv, trunc_comm_U, U_Gf, trunc_smul]

theorem galerkin_mass_deriv (hL : 0 < L) (S : Finset Z2)
    {w : ℝ → ℓ2} {t : ℝ} (hs : Supported S (w t))
    (hw : HasDerivAt w (galerkin S L κ β γ t (w t)) t) :
    HasDerivAt (fun s => mass L (w s)) 0 t := by
  have h := (hasDerivAt_Lc (L := L) hw).norm_sq
  simp_rw [mass_eq_norm_Lc]
  convert h using 1
  rw [real_inner_eq, galerkin, supported_trunc_eq hs, supported_inner_Lc L hs,
    Lc_Gf, inner_smul_right, inner_U_neg, ← Lc_U, re_neg_I_mul, inner_Lc,
    inner_Fnl_im hL, mul_zero]

theorem galerkin_ham_deriv (hL : 0 < L) (S : Finset Z2)
    {w : ℝ → ℓ2} {t : ℝ} (hs : Supported S (w t))
    (hw : HasDerivAt w (galerkin S L κ β γ t (w t)) t) :
    HasDerivAt (fun s => ham L κ β γ (U L κ s (w s))) 0 t := by
  have hk := (hasDerivAt_Ac (L := L) (κ := κ) hw).norm_sq
  have hp := hasDerivAt_pot_U (β := β) (γ := γ) (κ := κ) hL hw
  have h := hk.add hp
  have e : (fun s => ham L κ β γ (U L κ s (w s))) =
      fun s => ‖Ac L κ (w s)‖ ^ 2 + pot L β γ (U L κ s (w s)) := by
    funext s
    rw [ham_U]
  rw [e]
  convert h using 1
  set u := U L κ t (w t)
  have hc := inner_conj_symm (𝕜 := ℂ) (Ac L κ (Fnl L β γ u)) (Ac L κ u)
  have hkin : inner ℂ (Ac L κ (w t)) (Ac L κ (galerkin S L κ β γ t (w t))) =
      inner ℂ (Ac L κ (w t)) (Ac L κ (Gf L κ β γ t (w t))) := by
    unfold galerkin
    rw [supported_trunc_eq hs, supported_inner_Ac L κ hs]
  rw [real_inner_eq, hkin, Ac_Gf, inner_smul_right, inner_U_neg, ← Ac_U,
    U_galerkin S t hs, map_smul, inner_smul_right, projected_inner_Lc_self,
    Lw, Complex.add_re, re_neg_I_mul_inner_self, zero_add]
  rw [re_neg_I_mul, re_neg_I_mul, ← hc, Complex.conj_im]
  ring

theorem galerkin_conserved (hL : 0 < L) (S : Finset Z2) {W : ℝ → ℓ2}
    (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t) (t : ℝ) :
    mass L (W t) = mass L (W 0) ∧
      ham L κ β γ (U L κ t (W t)) = ham L κ β γ (W 0) := by
  constructor
  · exact is_const_of_deriv_eq_zero (f := fun s => mass L (W s))
      (fun s => (galerkin_mass_deriv hL S (hs s) (hW s)).differentiableAt)
      (fun s => (galerkin_mass_deriv hL S (hs s) (hW s)).deriv) t 0
  · have h := is_const_of_deriv_eq_zero
      (f := fun s => ham L κ β γ (U L κ s (W s)))
      (fun s => (galerkin_ham_deriv hL S (hs s) (hW s)).differentiableAt)
      (fun s => (galerkin_ham_deriv hL S (hs s) (hW s)).deriv) t 0
    rwa [U_zero] at h

theorem galerkin_apriori (hL : 0 < L) (hγ : 0 < γ) (S : Finset Z2)
    {W : ℝ → ℓ2} (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t) (t : ℝ) :
    ‖W t‖ ≤ Rap κ β γ (mass L (W 0)) (ham L κ β γ (W 0)) := by
  obtain ⟨hm, he⟩ := galerkin_conserved hL S hs hW t
  have h := norm_le_apriori (κ := κ) (β := β) hL hγ (U L κ t (W t))
  rw [norm_U, mass_U, hm, he] at h
  exact h

theorem exists_global_galerkin (hL : 0 < L) (hγ : 0 < γ) (S₀ : Finset Z2) (u₀ : ℓ2) (hs₀ : Supported S₀ u₀) :
    ∃ W : ℝ → ℓ2, W 0 = u₀ ∧ (∀ t, Supported S₀ (W t)) ∧
      ∀ t, HasDerivAt W (galerkin S₀ L κ β γ t (W t)) t := by
  set C₀ := Rap κ β γ (mass L u₀) (ham L κ β γ u₀) with hC₀
  have hbd : ∀ e : ℓ2, mass L e = mass L u₀ → ham L κ β γ e = ham L κ β γ u₀ → ‖e‖ ≤ C₀ := by
    intro e h1 h2
    have h := norm_le_apriori (κ := κ) (β := β) hL hγ e
    rwa [h1, h2] at h
  have hC₀0 : 0 ≤ C₀ := Rap_nonneg _ _ _ _ _
  obtain ⟨R, hR⟩ : ∃ R, R = C₀ + 1 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; linarith
  obtain ⟨W, hW0, hW⟩ := exists_global_clipped (κ := κ) (β := β) (γ := γ) hL S₀ hR0 u₀
  have hsupport : ∀ t, Supported S₀ (W t) := by
    intro t k hk
    exact clipped_trajectory_support hW hk (by rw [hW0]; exact hs₀ k hk) t
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hinner : ∀ s, ‖W s‖ ≤ R → HasDerivAt W (galerkin S₀ L κ β γ s (W s)) s := fun s hs => by
    have h := hW s
    rwa [clipped_eq_galerkin S₀ L κ β γ R s hs] at h
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
    have hder : ∀ x ∈ Metric.ball t ε, HasDerivAt W (galerkin S₀ L κ β γ x (W x)) x :=
      fun x hx => hinner x (hball hx).le
    have hpre : IsPreconnected (Metric.ball t ε) := (convex_ball t ε).isPreconnected
    have h1 : mass L (W s) = mass L (W t) :=
      Metric.isOpen_ball.is_const_of_deriv_eq_zero (f := fun x => mass L (W x)) hpre
        (fun x hx => (galerkin_mass_deriv hL S₀ (hsupport x) (hder x hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => (galerkin_mass_deriv hL S₀ (hsupport x) (hder x hx)).deriv) hs (Metric.mem_ball_self hε)
    have h2 : ham L κ β γ (U L κ s (W s)) = ham L κ β γ (U L κ t (W t)) :=
      Metric.isOpen_ball.is_const_of_deriv_eq_zero
        (f := fun x => ham L κ β γ (U L κ x (W x))) hpre
        (fun x hx => (galerkin_ham_deriv hL S₀ (hsupport x) (hder x hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => (galerkin_ham_deriv hL S₀ (hsupport x) (hder x hx)).deriv) hs (Metric.mem_ball_self hε)
    rw [hS] at ht ⊢
    exact ⟨h1.trans ht.1, h2.trans ht.2⟩
  have h0S : (0 : ℝ) ∈ S := by
    rw [hS]
    exact ⟨by rw [hW0], by rw [U_zero, hW0]⟩
  have hSu : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0S⟩
  refine ⟨W, hW0, hsupport, fun t => hinner t ?_⟩
  have ht : t ∈ S := by rw [hSu]; exact mem_univ t
  rw [hR]
  linarith [hSb t ht]

end PVNP.TorusGalerkin
