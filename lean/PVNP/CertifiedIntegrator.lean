import PVNP.FiniteNonlinearResidual

/-!
# Certified time slabs for the frozen Fourier flow

The diagonal free group has a quantitative time modulus on finite support.
The cubic–quintic field then has an explicit time modulus using the
frequency bounds of both the trial support and its nonlinear sumset.
A residual measured at one time can certify an entire affine time slab.
The result is conditional on charged frequency, radius and sample-error
bounds; it is not an effective global approximation or bit-cost theorem.
-/

open Complex Set
open scoped BigOperators
namespace PVNP.TorusGalerkin
open PVNP.Torus

/-- Time regularity of the actual free group on a bounded frequency support. -/
theorem finite_U_increment (L κ h : ℝ) {S : Finset Z2} {v : ℓ2} {M : ℝ}
    (hM : 0 ≤ M) (hv : Supported S v) (hfreq : ∀ k ∈ S, om L κ k ≤ M) :
    ‖U L κ h v - v‖ ≤ M * |h| * ‖v‖ := by
  have hp : ∀ k : Z2, ‖(U L κ h v - v) k‖ ^ 2 ≤
      (M * |h|) ^ 2 * ‖v k‖ ^ 2 := by
    intro k
    rw [lp.coeFn_sub, Pi.sub_apply, U_apply]
    by_cases hk : k ∈ S
    · have hphase : ‖ph L κ h k - 1‖ ≤ M * |h| :=
        (norm_ph_sub_one_le L κ h k).trans
          (mul_le_mul_of_nonneg_right (hfreq k hk) (abs_nonneg h))
      have he : ph L κ h k * v k - v k = (ph L κ h k - 1) * v k := by ring
      rw [he, norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hphase 2) (sq_nonneg _)
    · rw [hv k hk]
      simp
  have hh := tsum_le_tsum hp (summable_sq _) ((summable_sq v).mul_left ((M * |h|)^2))
  rw [tsum_mul_left, ← norm_sq_eq] at hh
  apply norm_le_of_tsum_sq_le _ (by positivity)
  simpa only [mul_pow] using hh

theorem finite_U_time_modulus (L κ s t : ℝ) {S : Finset Z2} {v : ℓ2} {M : ℝ}
    (hM : 0 ≤ M) (hv : Supported S v) (hfreq : ∀ k ∈ S, om L κ k ≤ M) :
    ‖U L κ s v - U L κ t v‖ ≤ M * |s - t| * ‖v‖ := by
  have hst : t + (s-t) = s := by ring
  have he : U L κ s v = U L κ t (U L κ (s-t) v) := by
    rw [← U_add, hst]
  rw [he, ← map_sub, norm_U]
  exact finite_U_increment L κ (s-t) hM hv hfreq

/-- Explicit time Lipschitz estimate for the full frozen nonlinearity.
M bounds the trial frequencies and N bounds its nonlinear sumset. -/
theorem finite_Gf_time_modulus {L κ β γ R M N : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hN : 0 ≤ N)
    {S : Finset Z2} {v : ℓ2} (hv : Supported S v) (hr : ‖v‖ ≤ R)
    (hm : ∀ k ∈ S, om L κ k ≤ M)
    (hn : ∀ k ∈ nonlinearSupport S, om L κ k ≤ N)
    (s t : ℝ) :
    ‖Gf L κ β γ s v - Gf L κ β γ t v‖ ≤
      LF L β γ R * R * (M + N) * |s - t| := by
  let A := Fnl L β γ (U L κ s v)
  let B := Fnl L β γ (U L κ t v)
  have hLF := LF_nonneg L β γ R
  have ha : ‖U L κ s v‖ ≤ R := by rwa [norm_U]
  have hb : ‖U L κ t v‖ ≤ R := by rwa [norm_U]
  have hAB : ‖A - B‖ ≤ LF L β γ R * (M * |s-t| * R) := by
    apply (norm_Fnl_sub_le hL β γ ha hb).trans
    apply mul_le_mul_of_nonneg_left _ hLF
    exact (finite_U_time_modulus L κ s t hM hv hm).trans
      (mul_le_mul_of_nonneg_left hr (mul_nonneg hM (abs_nonneg _)))
  have hB : ‖B‖ ≤ LF L β γ R * R := by
    apply (norm_Fnl_le hL β γ _).trans
    exact mul_le_mul (LF_mono hL β γ (norm_nonneg _) hb) hb (norm_nonneg _) hLF
  have hBs : Supported (nonlinearSupport S) B :=
    support_Fnl hL β γ (support_U L κ t hv)
  have htime : ‖U L κ (-s) B - U L κ (-t) B‖ ≤
      N * |s-t| * (LF L β γ R * R) := by
    have hh := finite_U_time_modulus L κ (-s) (-t) hN hBs hn
    have he : -s - -t = -(s-t) := by ring
    rw [he, abs_neg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hB (mul_nonneg hN (abs_nonneg _)))
  unfold Gf
  rw [← smul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul]
  change ‖U L κ (-s) A - U L κ (-t) B‖ ≤ _
  calc
    _ ≤ ‖U L κ (-s) A - U L κ (-s) B‖ +
          ‖U L κ (-s) B - U L κ (-t) B‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ LF L β γ R * (M * |s-t| * R) +
          N * |s-t| * (LF L β γ R * R) := by
        rw [← map_sub, norm_U]
        exact add_le_add hAB htime
    _ = _ := by ring

/-- Residual growth on a single affine numerical slab. The derivative is d.
The bound at the left endpoint may include certified evaluation/rounding
error; no equality with the Euler vector field is assumed. -/
theorem affine_slab_residual {L κ β γ R M N η : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hN : 0 ≤ N)
    {S : Finset Z2} {x d : ℓ2} (hx : Supported S x) (hr : ‖x‖ ≤ R)
    (hm : ∀ k ∈ S, om L κ k ≤ M)
    (hn : ∀ k ∈ nonlinearSupport S, om L κ k ≤ N)
    (a t : ℝ) (hball : ‖x + ((t-a : ℝ) : ℂ) • d‖ ≤ R)
    (hres : ‖d - Gf L κ β γ a x‖ ≤ η) :
    ‖d - Gf L κ β γ t (x + ((t-a : ℝ) : ℂ) • d)‖ ≤
      η + LF L β γ R * (‖d‖ + R * (M+N)) * |t-a| := by
  let y : ℓ2 := x + ((t-a : ℝ) : ℂ) • d
  have hy : ‖y‖ ≤ R := hball
  have hdist : ‖y - x‖ = |t-a| * ‖d‖ := by
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hspace := norm_Gf_sub_le (κ := κ) (β := β) (γ := γ) hL t hy hr
  rw [hdist] at hspace
  have htime := finite_Gf_time_modulus (κ := κ) (β := β) (γ := γ)
    hL hR hM hN hx hr hm hn t a
  rw [norm_sub_rev] at hspace htime
  change ‖d - Gf L κ β γ t y‖ ≤ _
  calc
    _ ≤ ‖d - Gf L κ β γ a x‖ +
          ‖Gf L κ β γ a x - Gf L κ β γ t y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖d - Gf L κ β γ a x‖ +
          (‖Gf L κ β γ a x - Gf L κ β γ t x‖ +
            ‖Gf L κ β γ t x - Gf L κ β γ t y‖) :=
        add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _
    _ ≤ η + (LF L β γ R * R * (M+N) * |t-a| +
          LF L β γ R * (|t-a| * ‖d‖)) :=
        add_le_add hres (add_le_add htime hspace)
    _ = _ := by ring

end PVNP.TorusGalerkin
