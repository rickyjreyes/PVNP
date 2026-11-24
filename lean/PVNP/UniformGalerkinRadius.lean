import PVNP.WeakGlobalComparison

/-!
# A cutoff-independent radius and detector error

The initial H² norm alone bounds the conserved mass and Hamiltonian
of every Fourier projection. The resulting radius is independent of
the number of retained modes and applies to the exact flow as well.
-/

open Complex Set
namespace PVNP.TorusGalerkin
open PVNP.Torus PVNP.ContinuumPrecision

theorem kinetic_norm_bound (L κ : ℝ) (v : ℓ2) :
    ‖Ac L κ v‖ ≤ (|κ| + 1) * ‖v‖ := by
  apply norm_le_of_tsum_sq_le _ (by positivity)
  have h := tsum_sq_le_of_le
    (f := fun k => Ac L κ v k)
    (g := fun k => (|κ| + 1) * ‖v k‖)
    (by simpa only [mul_pow] using (summable_sq v).mul_left ((|κ|+1)^2))
    (fun k => by
      rw [Ac, dmul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_Ac_sym_le L κ k) (norm_nonneg _))
  calc
    _ ≤ ∑' k, ((|κ|+1) * ‖v k‖)^2 := h.2
    _ = _ := by simp only [mul_pow]; rw [tsum_mul_left, norm_sq_eq]

noncomputable def potBudget (L β γ B : ℝ) : ℝ :=
  3 * |β| * (L⁻¹ * Real.sqrt (SL L) * B)^2 +
    5 * |γ| * (L⁻¹ * Real.sqrt (SL L) * B)^4

theorem potBudget_nonneg (L β γ B : ℝ) : 0 ≤ potBudget L β γ B := by
  unfold potBudget
  positivity

theorem potential_zero (L β γ : ℝ) : pot L β γ 0 = 0 := by
  simp [pot, co_zero, field, nfun]

/-- Taylor at zero gives a convenient, not sharp, polynomial energy budget. -/
theorem potential_upper (hL : 0 < L) (β γ : ℝ) {v : ℓ2} {B : ℝ}
    (hv : ‖v‖ ≤ B) : pot L β γ v ≤ potBudget L β γ B * B^2 := by
  have hB := (norm_nonneg v).trans hv
  have h := pot_taylor hL β γ (e := 0) (f := v)
    (R := B) (by simpa using hB) hv
  simp only [potential_zero, Fnl_zero hL, co_zero, Pi.zero_apply,
    map_zero, zero_mul, tsum_zero, Complex.zero_re, mul_zero, sub_zero] at h
  change |pot L β γ v| ≤ potBudget L β γ B * mass L v at h
  have hm : mass L v ≤ B^2 := by
    rw [mass_eq_norm_Lc]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_Lc_le L v).trans hv) 2
  exact (le_abs_self _).trans (h.trans
    (mul_le_mul_of_nonneg_left hm (potBudget_nonneg L β γ B)))

noncomputable def energyBudget (L κ β γ B : ℝ) : ℝ :=
  ((|κ|+1)*B)^2 + potBudget L β γ B * B^2

theorem initial_energy_upper (hL : 0 < L) (κ β γ : ℝ) {v : ℓ2} {B : ℝ}
    (hv : ‖v‖ ≤ B) : ham L κ β γ v ≤ energyBudget L κ β γ B := by
  have h := (kinetic_norm_bound L κ v).trans
    (mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ |κ|+1))
  unfold ham energyBudget
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h 2)
    (potential_upper hL β γ hv)

noncomputable def uniformRadius (L κ β γ B : ℝ) : ℝ :=
  Rap κ β γ (B^2) (energyBudget L κ β γ B)

theorem uniformRadius_nonneg (L κ β γ B : ℝ) :
    0 ≤ uniformRadius L κ β γ B := Rap_nonneg _ _ _ _ _

theorem initial_radius_upper (hL : 0 < L) (hγ : 0 < γ)
    {κ β : ℝ} {v : ℓ2} {B : ℝ} (hv : ‖v‖ ≤ B) :
    Rap κ β γ (mass L v) (ham L κ β γ v) ≤ uniformRadius L κ β γ B := by
  have hm : mass L v ≤ B^2 := by
    rw [mass_eq_norm_Lc]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_Lc_le L v).trans hv) 2
  have he := initial_energy_upper hL κ β γ hv
  have hc : 0 ≤ 3*β^2/(16*γ) := by positivity
  unfold uniformRadius Rap
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (by positivity))
    (Real.sqrt_le_sqrt (add_le_add he (mul_le_mul_of_nonneg_left hm hc)))

/-- An actual global Galerkin trajectory, bounded independently of S. -/
theorem exists_uniform_galerkin {κ β : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    (S : Finset Z2) {u₀ : ℓ2} {B : ℝ} (hB : ‖u₀‖ ≤ B) :
    ∃ W : ℝ → ℓ2, W 0 = trunc S u₀ ∧
      (∀ t, Supported S (W t)) ∧
      (∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t) ∧
      ∀ t, ‖W t‖ ≤ uniformRadius L κ β γ B := by
  obtain ⟨W, h0, hs, hd⟩ := exists_global_galerkin
    (κ := κ) (β := β) hL hγ S (trunc S u₀) (trunc_supported S u₀)
  refine ⟨W,h0,hs,hd,fun t => ?_⟩
  apply (galerkin_apriori hL hγ S hs hd t).trans
  rw [h0]
  exact initial_radius_upper hL hγ ((trunc_norm_le S u₀).trans hB)

/-- The exact physical detector uses the weak global error, not H² error. -/
theorem weak_readout_error {L κ β γ R K T : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hK : 0 < K) (hT : 0 ≤ T) (S : Finset Z2)
    (hcut : ∀ k ∉ S, K ≤ wt L k) {χ : ℓ2}
    (hreal : rev (co L χ) = co L χ) {W w : ℝ → ℓ2}
    (hW0 : W 0 = trunc S (w 0))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t)
    (hs : ∀ t, Supported S (W t))
    (hbW : ∀ t, ‖W t‖ ≤ R) (hbw : ∀ t, ‖w t‖ ≤ R) :
    |Jdet L χ (U L κ T (W T)) - Jdet L χ (U L κ T (w T))| ≤
      Cdet L χ * (2*R) *
        gronwallBound (R/K) (LF L β γ R) (LF L β γ R * R/K) T := by
  have he := weak_galerkin_global_error hL hR hK S hcut hW0 hW hw hs hbW hbw
    T ⟨hT,le_rfl⟩
  have h := weak_detector_lipschitz hL hreal (U L κ T (W T)) (U L κ T (w T))
  rw [← map_sub, Lc_U, norm_U] at h
  have h1 := norm_Lc_le L (U L κ T (W T))
  have h2 := norm_Lc_le L (U L κ T (w T))
  rw [norm_U] at h1 h2
  have hsum : ‖Lc L (U L κ T (W T))‖ + ‖Lc L (U L κ T (w T))‖ ≤ 2*R := by
    linarith [hbW T, hbw T]
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hsum (Cdet_nonneg hL χ)) he
    (norm_nonneg _) (by positivity [Cdet_nonneg hL χ]))

end PVNP.TorusGalerkin
