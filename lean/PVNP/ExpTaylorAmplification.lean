import Mathlib

/-!
# Exponential sensitivity is not exponential computational cost

`SidebandAmplification` proves that the constant-background sideband linearization of the frozen
PDE has genuine exponential modes (`λ² = −H(H+2c)`; explicitly `x(t) = y(t) = e^t`), so the
solution and its sensitivity to the data grow like `e^{λt}`. The Phase XXV first-order (Euler)
budget charges a step count proportional to `e^{A T}/ε`. This module shows that the exponential
factor is a property of that method, not of the computation: the exponential series reaches
relative precision `2^{-p}` after `⌈2x⌉ + p + 1` terms (`taylor_terms_for_precision`), a number
linear both in the growth exponent `x = λt` and in the number of precision bits `p`.

The tail bound (`exp_partial_sum_error`): if `2x ≤ K + 1` then the terms `x^k/k!` with `k ≥ K`
decrease at least geometrically with ratio `1/2`, so the error after `K + j` terms is at most
`2·2^{-j}·x^K/K! ≤ 2·2^{-j}·e^x`.

Scope. This is a statement about the linearized sideband dynamics (a scalar or diagonalizable
linear flow) and about arithmetic terms, not a bit-complexity theorem for the nonlinear PDE.
For the nonlinear flow, high-order time integration needs a lower bound on the time-analyticity
radius of the finite-dimensional flow, and the Phase XXV spatial cutoff `K ∝ e^{LF T}/m` is a
separate (Gronwall) estimate that this module does not improve.
-/

namespace PVNP.ExpTaylor

open Finset

/-- The exponential series. -/
theorem exp_eq_tsum (x : ℝ) : Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Ratio of consecutive terms. -/
theorem term_succ (x : ℝ) (k : ℕ) :
    x ^ (k+1) / ((k+1).factorial : ℝ) = (x ^ k / (k.factorial : ℝ)) * (x / ((k:ℝ) + 1)) := by
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have h1 : ((k:ℝ)+1) ≠ 0 := by positivity
  have h2 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  push_cast
  field_simp

/-- Beyond `K` with `2x ≤ K + 1`, each further term is at most half the previous one. -/
theorem term_shift_le {x : ℝ} (hx : 0 ≤ x) {K : ℕ} (hK : 2 * x ≤ K + 1) (j : ℕ) :
    x ^ (K + j) / ((K + j).factorial : ℝ) ≤ (x ^ K / (K.factorial : ℝ)) * (1/2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show K + (j+1) = (K + j) + 1 by ring, term_succ]
    have hr : x / (((K + j : ℕ) : ℝ) + 1) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity)]
      push_cast
      have : (0:ℝ) ≤ j := by positivity
      linarith
    have hr0 : 0 ≤ x / (((K + j : ℕ) : ℝ) + 1) := by positivity
    calc x ^ (K + j) / ((K + j).factorial : ℝ) * (x / (((K + j : ℕ) : ℝ) + 1))
        ≤ (x ^ K / (K.factorial : ℝ) * (1/2) ^ j) * (1/2) :=
          mul_le_mul ih hr hr0 (by positivity)
      _ = x ^ K / (K.factorial : ℝ) * (1/2) ^ (j+1) := by ring

/-- The error of the partial sum is the tail of the series. -/
theorem exp_sub_partial_eq (x : ℝ) (N : ℕ) :
    Real.exp x - ∑ k ∈ range N, x ^ k / (k.factorial : ℝ) =
      ∑' i : ℕ, x ^ (i + N) / ((i + N).factorial : ℝ) := by
  have h := (Real.summable_pow_div_factorial x).sum_add_tsum_nat_add N
  rw [exp_eq_tsum]
  linarith

/-- Geometric bound on the tail. -/
theorem exp_tail_le {x : ℝ} (hx : 0 ≤ x) {K : ℕ} (hK : 2 * x ≤ K + 1) (j : ℕ) :
    ∑' i : ℕ, x ^ (i + (K + j)) / ((i + (K + j)).factorial : ℝ) ≤
      2 * (1/2) ^ j * (x ^ K / (K.factorial : ℝ)) := by
  have hb : ∀ i : ℕ, x ^ (i + (K + j)) / ((i + (K + j)).factorial : ℝ) ≤
      (x ^ K / (K.factorial : ℝ)) * (1/2) ^ j * (1/2) ^ i := by
    intro i
    have h := term_shift_le hx hK (j + i)
    rw [show K + (j + i) = i + (K + j) by ring, pow_add (1/2 : ℝ) j i] at h
    calc _ ≤ x ^ K / (K.factorial : ℝ) * ((1/2) ^ j * (1/2) ^ i) := h
      _ = _ := by ring
  have hs : Summable (fun i : ℕ => (x ^ K / (K.factorial : ℝ)) * (1/2) ^ j * (1/2) ^ i) :=
    summable_geometric_two.mul_left _
  have hsum : Summable (fun i : ℕ => x ^ (i + (K + j)) / ((i + (K + j)).factorial : ℝ)) :=
    (summable_nat_add_iff (K + j)).2 (Real.summable_pow_div_factorial x)
  calc ∑' i : ℕ, x ^ (i + (K + j)) / ((i + (K + j)).factorial : ℝ)
      ≤ ∑' i : ℕ, (x ^ K / (K.factorial : ℝ)) * (1/2) ^ j * (1/2) ^ i :=
        hsum.tsum_le_tsum hb hs
    _ = (x ^ K / (K.factorial : ℝ)) * (1/2) ^ j * 2 := by
        rw [tsum_mul_left, tsum_geometric_two]
    _ = _ := by ring

/-- **Partial-sum error of the exponential.** If `2x ≤ K + 1`, the partial sum with `K + j`
terms underestimates `e^x` by at most `2·2^{-j}·e^x`. -/
theorem exp_partial_sum_error {x : ℝ} (hx : 0 ≤ x) {K : ℕ} (hK : 2 * x ≤ K + 1) (j : ℕ) :
    0 ≤ Real.exp x - ∑ k ∈ range (K + j), x ^ k / (k.factorial : ℝ) ∧
    Real.exp x - ∑ k ∈ range (K + j), x ^ k / (k.factorial : ℝ) ≤
      2 * (1/2) ^ j * Real.exp x := by
  rw [exp_sub_partial_eq]
  constructor
  · exact tsum_nonneg fun i => by positivity
  · exact (exp_tail_le hx hK j).trans
      (mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp x hx K) (by positivity))

/-- **Terms needed for `p` bits of relative precision.** `⌈2x⌉ + p + 1` terms of the
exponential series give `e^x` to relative precision `2^{-p}`: linear in the growth exponent and
in the precision, with no factor `e^x` or `2^p`. -/
theorem taylor_terms_for_precision {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    |Real.exp x - ∑ k ∈ range (⌈2 * x⌉₊ + (p + 1)), x ^ k / (k.factorial : ℝ)| ≤
      (1/2) ^ p * Real.exp x := by
  have hK : 2 * x ≤ (⌈2 * x⌉₊ : ℝ) + 1 := by
    have := Nat.le_ceil (2 * x)
    linarith
  obtain ⟨h0, h1⟩ := exp_partial_sum_error hx hK (p + 1)
  rw [abs_of_nonneg h0]
  calc _ ≤ 2 * (1/2) ^ (p+1) * Real.exp x := h1
    _ = (1/2) ^ p * Real.exp x := by ring

/-- **The unstable sideband growth is cheap to compute.** For growth rate `r ≥ 0` and time
`t ≥ 0`, the factor `e^{r t}` of an exponential sideband mode is computed to relative precision
`2^{-p}` with `⌈2 r t⌉ + p + 1` Taylor terms. The explicit unstable mode of
`SidebandAmplification.exponential_solution` is the case `r = 1`. -/
theorem sideband_growth_taylor {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) (p : ℕ) :
    |Real.exp (r * t) - ∑ k ∈ range (⌈2 * (r * t)⌉₊ + (p + 1)), (r * t) ^ k / (k.factorial : ℝ)|
      ≤ (1/2) ^ p * Real.exp (r * t) :=
  taylor_terms_for_precision (mul_nonneg hr ht) p

end PVNP.ExpTaylor
