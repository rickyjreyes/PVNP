import PVNP.SeparatorPrice

/-!
# Phase XVI: amplitude-scaling obstruction to an unnormalized separator price

If a quadratic interface cost scales as E(a * psi) = a^2 E(psi),
and every positive amplitude scaling is admitted, then it is impossible
to impose a fixed positive lower bound on *every* nonzero scaled state.

This is a necessary-condition result, NOT a refutation of I-31 for a
frozen physical class with a normalized detector contrast. A fixed robust
readout gap or other amplitude lower bound can exclude the small-scaled
states used here, so all admissibility assumptions must be checked.
-/

namespace PVNP.SeparatorAmplitude

/-- An abstract quadratic cost on a positive amplitude ray has infimum
zero and admits no strictly positive uniform lower bound. The one-ray
coefficient e need only be finite and nonnegative. -/
theorem no_uniform_quadratic_price (e : ℝ) (he : 0 ≤ e) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → c ≤ a * a * e := by
  rintro ⟨c, hc, hbound⟩
  let a : ℝ := c / (2 * (e + c + 1))
  have hd : 0 < 2 * (e + c + 1) := by linarith
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hc hd
  have hmul : a * (2 * (e + c + 1)) = c := by
    dsimp [a]
    field_simp [ne_of_gt hd]
  have hal : a < 1 := by
    by_contra hh
    have hp : 0 ≤ (a - 1) * c :=
      mul_nonneg (by linarith) (by linarith)
    have hpe : 0 ≤ a * e :=
      mul_nonneg (le_of_lt ha) he
    nlinarith [hmul, hp, hpe]
  have hsmall : a * e < c := by
    have hp : 0 ≤ a * c :=
      mul_nonneg (le_of_lt ha) (le_of_lt hc)
    nlinarith [hmul, hp]
  have ha_sq : a * a ≤ a := by
    have hp : 0 ≤ a * (1 - a) :=
      mul_nonneg (le_of_lt ha) (by linarith)
    nlinarith [hp]
  have hcst : a * a * e ≤ a * e :=
    mul_le_mul_of_nonneg_right ha_sq he
  have hp := hbound a ha
  linarith

end PVNP.SeparatorAmplitude
