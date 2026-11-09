import Mathlib

/-! Arithmetic component of a charged physical simulation: local error
accumulation, readout gain and the number of accuracy bits. -/
namespace PVNP.ReadoutPrecision

theorem error_bound (e : ℕ → ℝ) (ε : ℝ) (k : ℕ) (hε : 0 ≤ ε) (h0 : e 0 ≤ ε)
    (step : ∀ t, e (t+1) ≤ (2:ℝ)^k * e t + ε) (t : ℕ) :
    e t ≤ (2:ℝ)^((k+1)*t)*ε := by
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    have hbig : 1 ≤ (2:ℝ)^(k+(k+1)*t) := one_le_pow₀ (by norm_num)
    rw [pow_add] at hbig
    have h := mul_le_mul_of_nonneg_left hbig hε
    calc e (t+1) ≤ (2:ℝ)^k * e t + ε := step t
         _ ≤ (2:ℝ)^k * ((2:ℝ)^((k+1)*t)*ε) + ε := by gcongr
         _ ≤ (2:ℝ)^((k+1)*(t+1))*ε := by
           rw [Nat.mul_succ,pow_add,pow_succ]; nlinarith

theorem same_sign (e : ℕ → ℝ) (ε exactValue approxValue : ℝ) (T k d q : ℕ)
    (hε : 0 ≤ ε) (h0 : e 0 ≤ ε)
    (step : ∀ t, e (t+1) ≤ (2:ℝ)^k * e t + ε)
    (precision : (2:ℝ)^((k+1)*T+d+q+1)*ε ≤ 1)
    (readout : |approxValue-exactValue| ≤ (2:ℝ)^d*e T)
    (margin : 1/(2:ℝ)^q ≤ |exactValue|) :
    0 < approxValue ↔ 0 < exactValue := by
  have he := error_bound e ε k hε h0 step T
  have h := readout.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hq : 0 < (2:ℝ)^q := by positivity
  have hnoise : |approxValue-exactValue| < 1/(2:ℝ)^q := by
    apply (lt_div_iff₀ hq).mpr
    have hmul := mul_le_mul_of_nonneg_right h hq.le
    rw [pow_succ,pow_add,pow_add] at precision
    nlinarith
  have hlt := hnoise.trans_le margin
  by_cases hpos : 0 < exactValue
  · rw [abs_of_pos hpos,abs_lt] at hlt; constructor <;> intro h' <;> linarith
  · rw [abs_of_nonpos (le_of_not_gt hpos),abs_lt] at hlt
    constructor <;> intro h' <;> linarith

end PVNP.ReadoutPrecision
