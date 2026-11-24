import Mathlib

/-!
# Scalar resource and decision budgets for restricted continuum simulation

These estimates are independent of the pending PDE modules. They are
sufficient polynomial envelopes, not a proof of a Turing refinement
or a complexity lower bound. P is a common positive majorant of the
charged numerical quantities (including the amplification factor).
-/
namespace PVNP.RestrictedResourceBudget

theorem cutoff_weight_lower {P L q : ℝ} (hP : 1 ≤ P)
    (hL : 0 < L) (hLP : L ≤ P) (hq : 4*P^4 ≤ q) :
    64*P^6 ≤ 1+(6*(q+1)/L)^2 := by
  have hp : 0 ≤ P := by linarith
  have hq0 : 0 ≤ q := (by positivity : 0 ≤ 4*P^4).trans hq
  have hdiv : 8*P^3 ≤ 6*(q+1)/L := by
    apply (le_div_iff₀ hL).2
    calc
      8*P^3*L ≤ 8*P^3*P := mul_le_mul_of_nonneg_left hLP (by positivity)
      _ = 2*(4*P^4) := by ring
      _ ≤ 2*q := mul_le_mul_of_nonneg_left hq (by norm_num)
      _ ≤ 6*(q+1) := by linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 8*P^3) hdiv 2
  nlinarith only [hs]

theorem spatial_budget {P C R E K m : ℝ} (hP : 1 ≤ P)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hCP : C ≤ P) (hRP : R ≤ P) (hEP : E ≤ P)
    (hK : 32*P^5 ≤ K) (hm : 1 ≤ m*P) :
    4*C*R^2*E/K ≤ m/8 := by
  have hp : 0 < P := by linarith
  have hk : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hmp : 0 ≤ m := by
    by_contra hn
    have hn' : m < 0 := lt_of_not_ge hn
    nlinarith [mul_neg_of_neg_of_pos hn' hp]
  have hnum : 4*C*R^2*E ≤ 4*P^4 := by
    calc
      _ ≤ 4*P*P^2*P := by gcongr
      _ = _ := by ring
  have hden : 32*P^4 ≤ m*K := by
    calc
      _ = (32*P^4)*1 := by ring
      _ ≤ (32*P^4)*(m*P) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = m*(32*P^5) := by ring
      _ ≤ m*K := mul_le_mul_of_nonneg_left hK hmp
  apply (div_le_iff₀ hk).2
  nlinarith only [hnum,hden]

/-- A polynomial step majorant when D,T,E,1/eps all have common
majorant P. N may be any positive real here; an integer >= the
displayed bound is selected in the executable. -/
theorem step_count_budget {P D T E eps N : ℝ} (hP : 1 ≤ P)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hDP : D ≤ P) (hTP : T ≤ P) (hEP : E ≤ P)
    (heps : 1 ≤ eps*P) (hN : 3*P^5 ≤ N) :
    D*(T/N)*T*E ≤ eps/3 := by
  have hp : 0 < P := by linarith
  have hn : 0 < N := lt_of_lt_of_le (by positivity) hN
  have he : 0 ≤ eps := by
    by_contra h
    have h' : eps < 0 := lt_of_not_ge h
    nlinarith [mul_neg_of_neg_of_pos h' hp]
  have hnum : D*T^2*E ≤ P^4 := by
    calc
      _ ≤ P*P^2*P := by gcongr
      _ = _ := by ring
  have hden : 3*P^4 ≤ eps*N := by
    calc
      _ = (3*P^4)*1 := by ring
      _ ≤ (3*P^4)*(eps*P) := mul_le_mul_of_nonneg_left heps (by positivity)
      _ = eps*(3*P^5) := by ring
      _ ≤ eps*N := mul_le_mul_of_nonneg_left hN he
  rw [show D*(T/N)*T*E = (D*T^2*E)/N by ring]
  apply (div_le_iff₀ hn).2
  nlinarith only [hnum,hden]

/-- Explicit finite-interval totality on a separated promise.
The margin need not be assumed to verify an individual sign, but
is needed to guarantee that the sign test cannot abstain. -/
theorem interval_decision_total {lo hi j θ m : ℝ}
    (hm : 0 < m) (hlo : lo ≤ j) (hhi : j ≤ hi)
    (hwidth : hi-lo < m) (hpromise : θ+m ≤ j ∨ j ≤ θ-m) :
    θ < lo ∨ hi < θ := by
  rcases hpromise with hp | hp
  · left; linarith
  · right; linarith

theorem expanded_interval_width {lo hi spatial numerical m : ℝ}
    (hm : 0 < m) (hwidth : hi-lo ≤ m/8)
    (hs : spatial ≤ m/8) (hn : numerical ≤ m/8) :
    (hi+spatial+numerical)-(lo-spatial-numerical) < m := by
  linarith

theorem expanded_interval_sound {lo hi approximate exact spatial numerical : ℝ}
    (hlo : lo ≤ approximate) (hhi : approximate ≤ hi)
    (herr : |approximate-exact| ≤ spatial+numerical) :
    lo-spatial-numerical ≤ exact ∧ exact ≤ hi+spatial+numerical := by
  have h := abs_le.mp herr
  constructor <;> linarith

end PVNP.RestrictedResourceBudget
