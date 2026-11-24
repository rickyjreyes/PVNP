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

end PVNP.TorusGalerkin
