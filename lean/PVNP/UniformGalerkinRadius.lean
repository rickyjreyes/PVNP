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
      beta_reduce
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
  have hf : ∀ x, Torus.field L 0 x = 0 := fun x => by simp [Torus.field]
  simp [pot, co_zero, hf, nfun]

/-- Taylor at zero gives a convenient, not sharp, polynomial energy budget. -/
theorem potential_upper {L : ℝ} (hL : 0 < L) (β γ : ℝ) {v : ℓ2} {B : ℝ}
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

theorem initial_energy_upper {L : ℝ} (hL : 0 < L) (κ β γ : ℝ) {v : ℓ2} {B : ℝ}
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

theorem initial_radius_upper {L γ : ℝ} (hL : 0 < L) (hγ : 0 < γ)
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
theorem exists_uniform_galerkin {L κ β γ : ℝ} (hL : 0 < L) (hγ : 0 < γ)
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
  have h1' := norm_Lc_le L (W T)
  have hsum : ‖Lc L (W T)‖ + ‖Lc L (U L κ T (w T))‖ ≤ 2*R := by
    linarith [hbW T, hbw T]
  have he' : ‖Lc L (U L κ T (W T - w T))‖ ≤
      gronwallBound (R/K) (LF L β γ R) (LF L β γ R * R/K) T := by
    rw [Lc_U, norm_U]; exact he
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hsum (Cdet_nonneg hL χ)) he'
    (norm_nonneg _) (mul_nonneg (Cdet_nonneg hL χ) (by positivity)))


/-- Simplify the Gronwall expression for a residual proportional to the
initial error. No division by a vanishing Lipschitz constant is needed. -/
theorem gronwall_proportional_le (d A t : ℝ) (hd : 0 ≤ d) (hA : 0 ≤ A) :
    gronwallBound d A (A*d) t ≤ 2*d*Real.exp (A*t) := by
  unfold gronwallBound
  by_cases h : A = 0
  · subst A
    simp <;> linarith
  · rw [if_neg h]
    have he : A*d/A = d := by field_simp
    rw [he]
    linarith

/-- Unconditional existence of the cutoff-independent Galerkin readout
approximation for an exact interaction-picture trajectory. -/
theorem exists_certified_galerkin_readout {L κ β γ B K T : ℝ}
    (hL : 0 < L) (hγ : 0 < γ) (hK : 0 < K) (hT : 0 ≤ T)
    (S : Finset Z2) (hcut : ∀ k ∉ S, K ≤ wt L k)
    {χ : ℓ2} (hreal : rev (co L χ) = co L χ) {w : ℝ → ℓ2}
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t)
    (hB : ‖w 0‖ ≤ B) :
    ∃ W : ℝ → ℓ2, W 0 = trunc S (w 0) ∧
      (∀ t, Supported S (W t)) ∧
      (∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t) ∧
      |Jdet L χ (U L κ T (W T)) - Jdet L χ (U L κ T (w T))| ≤
        Cdet L χ * (4 * (uniformRadius L κ β γ B)^2 *
          Real.exp (LF L β γ (uniformRadius L κ β γ B)*T) / K) := by
  let R := uniformRadius L κ β γ B
  have hR : 0 ≤ R := uniformRadius_nonneg L κ β γ B
  obtain ⟨W,h0,hs,hd,hb⟩ := exists_uniform_galerkin
    (κ := κ) (β := β) hL hγ S hB
  have hbw : ∀ t, ‖w t‖ ≤ R := by
    intro t
    obtain ⟨hm,he⟩ := conserved hL hw t
    have h := norm_le_apriori (κ := κ) (β := β) hL hγ (U L κ t (w t))
    rw [norm_U, mass_U, hm, he] at h
    exact h.trans (initial_radius_upper hL hγ hB)
  refine ⟨W,h0,hs,hd,?_⟩
  have h := weak_readout_error hL hR hK hT S hcut hreal h0 hd hw hs hb hbw
  have hg := gronwall_proportional_le (R/K) (LF L β γ R) T
    (div_nonneg hR hK.le) (LF_nonneg L β γ R)
  rw [show LF L β γ R * R/K = LF L β γ R * (R/K) by ring] at h
  calc
    _ ≤ Cdet L χ * (2*R) * (2*(R/K)*Real.exp (LF L β γ R*T)) :=
      h.trans (mul_le_mul_of_nonneg_left hg
        (mul_nonneg (Cdet_nonneg hL χ) (by positivity)))
    _ = _ := by dsimp [R]; ring


/-- A sufficient resource threshold for a robust positive or negative
detector decision. The error budget is half the original margin. -/
theorem detector_margin_from_cutoff {j jS C R A T K m : ℝ}
    (hK : 0 < K) (hm : 0 < m)
    (herr : |jS-j| ≤ C*(4*R^2*Real.exp (A*T)/K))
    (hcut : 8*C*R^2*Real.exp (A*T) ≤ m*K) :
    |jS-j| ≤ m/2 := by
  have hh : C*(4*R^2*Real.exp (A*T)/K) ≤ m/2 := by
    rw [show C*(4*R^2*Real.exp (A*T)/K) =
      (4*C*R^2*Real.exp (A*T))/K by ring]
    apply (div_le_iff₀ hK).2
    linarith
  exact herr.trans hh

theorem detector_decision_preserved {j jS θ m : ℝ} (hm : 0 < m)
    (herr : |jS-j| ≤ m/2) :
    (θ+m ≤ j → θ < jS) ∧ (j ≤ θ-m → jS < θ) := by
  have h1 := le_abs_self (jS-j)
  have h2 := neg_abs_le (jS-j)
  constructor <;> intro h <;> linarith

end PVNP.TorusGalerkin
