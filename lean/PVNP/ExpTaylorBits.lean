import PVNP.ExpTaylorAmplification

/-!
# Finite-bit evaluation of the exponential partial sum

`ExpTaylorAmplification` counts Taylor *terms*: `⌈2x⌉ + p + 1` terms give `e^x` to relative
precision `2^{-p}`. This module turns the count into exact finite-bit data for a rational
argument `x = a/b` (`a ≥ 0`, `b ≥ 1`).

* **Exact integer form** (`partial_sum_eq`): with `Q(m,k) = m!/k!` (an integer for `k ≤ m`),
  `Σ_{k≤m} (a/b)^k/k! = N_m / D_m`, where
  `N_m = Σ_{k≤m} a^k b^{m−k} Q(m,k)` and `D_m = b^m · m!`.
* **Polynomial sizes** (`num_le_pow`, `den_le_pow`): if `max(a, b) ≤ 2^β` and `m + 1 ≤ 2^γ`,
  then `N_m, D_m ≤ 2^{γ + m(β+γ)}`. Both integers therefore have bit length at most
  `γ + m(β + γ)`, which is polynomial in `m` and in the bit lengths of `a`, `b` and `m`.
* **Rounding** (`round_error`): the dyadic `⌊2^p N/D⌋/2^p` is within `2^{-p}` of `N/D`.
* **End to end** (`exp_dyadic_approx`): with `m = ⌈2x⌉ + p` (so `m + 1` terms), the dyadic
  rounding of `N_m/D_m` approximates `e^x` within `2^{1−p}·e^x`, and its numerator is at most
  `2^p · 2^{γ+m(β+γ)}` (`dyadic_num_le`).

Scope. These are exact arithmetic identities and size bounds. They show that every
intermediate integer has polynomially many bits, so evaluating `N_m` (for example `m + 1`
products and a sum) and one integer division costs polynomially many bit operations with
schoolbook arithmetic. That cost statement is not itself formalized: no Turing-machine
implementation in the repository's `TM` model is given here. The term count `m` is polynomial
in the *value* of `x` (as in the physical time `T`), not in its bit length.
-/

namespace PVNP.ExpTaylorBits

open Finset

/-- `m!/k!`, an integer when `k ≤ m`. -/
def fallQ (m k : ℕ) : ℕ := m.factorial / k.factorial

theorem fallQ_mul {m k : ℕ} (hk : k ≤ m) : fallQ m k * k.factorial = m.factorial :=
  Nat.div_mul_cancel (Nat.factorial_dvd_factorial hk)

theorem fallQ_le (m k : ℕ) : fallQ m k ≤ m.factorial := Nat.div_le_self _ _

/-- Integer numerator of the degree-`m` partial sum at `a/b`. -/
def taylorNum (a b m : ℕ) : ℕ := ∑ k ∈ range (m+1), a^k * b^(m-k) * fallQ m k

/-- Denominator `b^m · m!`. -/
def taylorDen (b m : ℕ) : ℕ := b^m * m.factorial

theorem taylorDen_pos {b : ℕ} (hb : 0 < b) (m : ℕ) : 0 < taylorDen b m :=
  Nat.mul_pos (pow_pos hb m) (Nat.factorial_pos m)

/-- **Exact integer form of the partial sum.** -/
theorem partial_sum_eq (a : ℕ) {b : ℕ} (hb : 0 < b) (m : ℕ) :
    ∑ k ∈ range (m+1), ((a:ℝ)/b)^k / (k.factorial : ℝ) =
      (taylorNum a b m : ℝ) / (taylorDen b m : ℝ) := by
  unfold taylorNum taylorDen
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hbR : (b:ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hQ : (fallQ m k : ℝ) * (k.factorial : ℝ) = (m.factorial : ℝ) := by
    exact_mod_cast fallQ_mul hkm
  have hpow : (b:ℝ)^m = (b:ℝ)^(m-k) * (b:ℝ)^k := by
    rw [← pow_add, Nat.sub_add_cancel hkm]
  rw [hpow, ← hQ, div_pow]
  have hbk : (b:ℝ)^k ≠ 0 := pow_ne_zero _ hbR
  have hbmk : (b:ℝ)^(m-k) ≠ 0 := pow_ne_zero _ hbR
  have hQ0 : (fallQ m k : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hQ
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne') hQ.symm
  field_simp

/-- **Polynomial size of the numerator.** -/
theorem num_le_pow (a b m β γ : ℕ) (hM : max a b ≤ 2^β) (hm : m + 1 ≤ 2^γ) :
    taylorNum a b m ≤ 2 ^ (γ + m * (β + γ)) := by
  have hterm : ∀ k ∈ range (m+1), a^k * b^(m-k) * fallQ m k ≤ (2^β)^m * m^m := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have ha : a ≤ 2^β := (le_max_left a b).trans hM
    have hb : b ≤ 2^β := (le_max_right a b).trans hM
    have h1 : a^k * b^(m-k) ≤ (2^β)^m := by
      calc a^k * b^(m-k) ≤ (2^β)^k * (2^β)^(m-k) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left ha k) (Nat.pow_le_pow_left hb (m-k))
        _ = (2^β)^m := by rw [← pow_add, Nat.add_sub_cancel' hkm]
    exact Nat.mul_le_mul h1 ((fallQ_le m k).trans (Nat.factorial_le_pow m))
  have hsum := Finset.sum_le_card_nsmul (range (m+1)) _ _ hterm
  rw [card_range, smul_eq_mul] at hsum
  have hmm : m^m ≤ (2^γ)^m := Nat.pow_le_pow_left (by omega) m
  calc taylorNum a b m ≤ (m+1) * ((2^β)^m * m^m) := hsum
    _ ≤ 2^γ * ((2^β)^m * (2^γ)^m) :=
        Nat.mul_le_mul hm (Nat.mul_le_mul le_rfl hmm)
    _ = 2 ^ (γ + m * (β + γ)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring

/-- **Polynomial size of the denominator.** -/
theorem den_le_pow (b m β γ : ℕ) (hb : b ≤ 2^β) (hm : m + 1 ≤ 2^γ) :
    taylorDen b m ≤ 2 ^ (γ + m * (β + γ)) := by
  unfold taylorDen
  have hmm : m.factorial ≤ (2^γ)^m :=
    (Nat.factorial_le_pow m).trans (Nat.pow_le_pow_left (by omega) m)
  calc b^m * m.factorial ≤ (2^β)^m * (2^γ)^m :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hb m) hmm
    _ ≤ 2^γ * ((2^β)^m * (2^γ)^m) := Nat.le_mul_of_pos_left _ (by positivity)
    _ = 2 ^ (γ + m * (β + γ)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring

/-- The dyadic rounding `⌊2^p y⌋ / 2^p`. -/
noncomputable def dyadic (p : ℕ) (y : ℝ) : ℝ := (⌊(2:ℝ)^p * y⌋ : ℝ) / (2:ℝ)^p

/-- **Rounding error.** -/
theorem round_error (p : ℕ) (y : ℝ) : |y - dyadic p y| ≤ (1/2)^p := by
  unfold dyadic
  have h2 : (0:ℝ) < (2:ℝ)^p := by positivity
  have hf1 := Int.floor_le ((2:ℝ)^p * y)
  have hf2 := Int.lt_floor_add_one ((2:ℝ)^p * y)
  have hlo : 0 ≤ y - (⌊(2:ℝ)^p * y⌋ : ℝ) / (2:ℝ)^p := by
    rw [sub_nonneg, div_le_iff₀ h2]; linarith
  have hhi : y - (⌊(2:ℝ)^p * y⌋ : ℝ) / (2:ℝ)^p ≤ (1/2)^p := by
    rw [one_div_pow, sub_le_iff_le_add, div_add_div_same, le_div_iff₀ h2]
    linarith
  rw [abs_of_nonneg hlo]
  exact hhi

/-- **End-to-end finite-bit approximation of `e^{a/b}`.** With `m = ⌈2x⌉ + p` (so `m + 1`
terms), the dyadic rounding at `p` bits of the exact rational partial sum `N_m/D_m` is within
`2^{1-p}·e^x` of `e^x`. -/
theorem exp_dyadic_approx (a : ℕ) {b : ℕ} (hb : 0 < b) (p : ℕ) :
    let x : ℝ := (a:ℝ)/b
    let m := ⌈2 * x⌉₊ + p
    |Real.exp x - dyadic p ((taylorNum a b m : ℝ) / (taylorDen b m : ℝ))| ≤
      2 * (1/2)^p * Real.exp x := by
  intro x m
  have hx : 0 ≤ x := by positivity
  have h1 := ExpTaylor.taylor_terms_for_precision hx p
  have hm : ⌈2 * x⌉₊ + (p + 1) = m + 1 := by simp only [m]; ring
  rw [hm, partial_sum_eq a hb m] at h1
  have h2 := round_error p ((taylorNum a b m : ℝ) / (taylorDen b m : ℝ))
  have he : 1 ≤ Real.exp x := Real.one_le_exp hx
  have h3 : (1/2:ℝ)^p ≤ (1/2)^p * Real.exp x := le_mul_of_one_le_right (by positivity) he
  calc |Real.exp x - dyadic p ((taylorNum a b m : ℝ) / (taylorDen b m : ℝ))|
      ≤ |Real.exp x - (taylorNum a b m : ℝ) / (taylorDen b m : ℝ)| +
        |(taylorNum a b m : ℝ) / (taylorDen b m : ℝ) -
          dyadic p ((taylorNum a b m : ℝ) / (taylorDen b m : ℝ))| := abs_sub_le _ _ _
    _ ≤ (1/2)^p * Real.exp x + (1/2)^p * Real.exp x := add_le_add h1 (h2.trans h3)
    _ = 2 * (1/2)^p * Real.exp x := by ring

/-- **Output size.** The integer numerator `⌊2^p N/D⌋` of the dyadic output is at most
`2^p · N`, hence has at most `p + γ + m(β+γ)` bits under the size hypotheses. -/
theorem dyadic_num_le (a b m p β γ : ℕ) (hb : 0 < b) (hM : max a b ≤ 2^β) (hm : m + 1 ≤ 2^γ) :
    (⌊(2:ℝ)^p * ((taylorNum a b m : ℝ) / (taylorDen b m : ℝ))⌋ : ℝ) ≤
      (2:ℝ)^(p + (γ + m * (β + γ))) := by
  have hD : (1:ℝ) ≤ (taylorDen b m : ℝ) := by exact_mod_cast taylorDen_pos hb m
  have hN : (taylorNum a b m : ℝ) ≤ (2:ℝ)^(γ + m * (β + γ)) := by
    exact_mod_cast num_le_pow a b m β γ hM hm
  have hN0 : (0:ℝ) ≤ (taylorNum a b m : ℝ) := by positivity
  have hq : (taylorNum a b m : ℝ) / (taylorDen b m : ℝ) ≤ (taylorNum a b m : ℝ) :=
    div_le_self hN0 hD
  calc (⌊(2:ℝ)^p * ((taylorNum a b m : ℝ) / (taylorDen b m : ℝ))⌋ : ℝ)
      ≤ (2:ℝ)^p * ((taylorNum a b m : ℝ) / (taylorDen b m : ℝ)) := Int.floor_le _
    _ ≤ (2:ℝ)^p * (2:ℝ)^(γ + m * (β + γ)) :=
        mul_le_mul_of_nonneg_left (hq.trans hN) (by positivity)
    _ = _ := by rw [← pow_add]

end PVNP.ExpTaylorBits
