import Mathlib

/-!
# Fourier receivers: mode counts and non-preservation of finite support (issue #15)

1. `mode_count_le`: on a square periodic domain of side `L`, the lattice modes
   `k = (2π/L) j`, `j ∈ ℤ²`, with `|k| ≤ K` number at most
   `(2⌊LK/2π⌋ + 1)²`.  This bounds the complex receiver dimension `D` of a
   bandwidth-`K` receiver, *as a measurement assumption*.
2. `cubic_quintic_generates_new_modes`: the nonlinear term
   `-β|u|²u + γ|u|⁴u` of the maintained WCT Hamiltonian, applied to the
   two-mode trigonometric polynomial `u = e^{ix} + e^{2ix}`, has a nonzero
   Fourier coefficient at mode `3` or `4` whenever `(β, γ) ≠ (0, 0)`.  Hence the
   nonlinear vector field does **not** preserve the finite Fourier support
   `{1, 2}`: a bandwidth limit is a property of the *receiver*, not a theorem
   about the evolution.

Model for (2): real-coefficient trigonometric polynomials are elements of the
group algebra `AddMonoidAlgebra ℝ ℤ` (coefficient at `n` = Fourier coefficient
of `e^{inx}`); pointwise multiplication is convolution of coefficients, i.e.
the algebra product, and complex conjugation of a real-coefficient polynomial
reflects the modes `n ↦ -n`.
-/

namespace PVNP.FourierReceiver

open Finset

/-- Integer points with `j₁² + j₂² ≤ r²` lie in the box `[-⌊r⌋, ⌊r⌋]²`, so
there are at most `(2⌊r⌋ + 1)²` of them. -/
theorem mode_count_le (S : Finset (ℤ × ℤ)) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ j ∈ S, (j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2 ≤ r ^ 2) :
    S.card ≤ (2 * ⌊r⌋₊ + 1) ^ 2 := by
  set N : ℤ := (⌊r⌋₊ : ℤ)
  have hcoord : ∀ a : ℤ, (a : ℝ) ^ 2 ≤ r ^ 2 → -N ≤ a ∧ a ≤ N := by
    intro a ha
    have h1 : |(a : ℝ)| ≤ r := abs_le_of_sq_le_sq' ha hr |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
    have h2 : ((|a|).toNat : ℝ) ≤ r := by
      have : ((|a|).toNat : ℝ) = |(a : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.toNat_of_nonneg (abs_nonneg a)
      rw [this]; exact h1
    have h3 : (|a|).toNat ≤ ⌊r⌋₊ := Nat.le_floor h2
    have h4 : |a| ≤ N := by
      have := Int.toNat_of_nonneg (abs_nonneg a)
      omega
    exact abs_le.1 h4
  have hsub : S ⊆ (Icc (-N) N) ×ˢ (Icc (-N) N) := by
    intro j hj
    have hj' := h j hj
    have ha : (j.1 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg (j.2 : ℝ)]
    have hb : (j.2 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg (j.1 : ℝ)]
    simp only [mem_product, mem_Icc]
    exact ⟨hcoord _ ha, hcoord _ hb⟩
  calc S.card ≤ ((Icc (-N) N) ×ˢ (Icc (-N) N)).card := card_le_card hsub
    _ = (2 * ⌊r⌋₊ + 1) ^ 2 := by
      rw [card_product, Int.card_Icc]
      have : (N + 1 - -N).toNat = 2 * ⌊r⌋₊ + 1 := by omega
      rw [this, sq]

/-- Physical form: modes `k = (2π/L) j` of a side-`L` periodic square with
`|k| ≤ K` number at most `(2⌊LK/2π⌋ + 1)²`. -/
theorem receiver_mode_count (S : Finset (ℤ × ℤ)) {L K : ℝ} (hL : 0 < L) (hK : 0 ≤ K)
    (h : ∀ j ∈ S, (2 * Real.pi / L) ^ 2 * ((j.1 : ℝ) ^ 2 + (j.2 : ℝ) ^ 2) ≤ K ^ 2) :
    S.card ≤ (2 * ⌊L * K / (2 * Real.pi)⌋₊ + 1) ^ 2 := by
  apply mode_count_le S (by positivity)
  intro j hj
  have hj := h j hj
  have hc : (0 : ℝ) < (2 * Real.pi / L) ^ 2 := by positivity
  rw [div_pow, mul_pow, show L ^ 2 * K ^ 2 / ((2 * Real.pi) ^ 2) = K ^ 2 / (2 * Real.pi / L) ^ 2 by
    field_simp]
  rw [le_div_iff₀ hc]; linarith

/-! ### Nonlinear generation of new Fourier modes -/

open AddMonoidAlgebra

/-- The two-mode test state `u = e^{ix} + e^{2ix}`. -/
noncomputable def u : AddMonoidAlgebra ℝ ℤ := single 1 1 + single 2 1

/-- Its complex conjugate `ū = e^{-ix} + e^{-2ix}` (real coefficients). -/
noncomputable def uBar : AddMonoidAlgebra ℝ ℤ := single (-1) 1 + single (-2) 1

/-- `|u|²u`. -/
noncomputable def cubic : AddMonoidAlgebra ℝ ℤ := u * u * uBar

/-- `|u|⁴u`. -/
noncomputable def quintic : AddMonoidAlgebra ℝ ℤ := u * u * u * uBar * uBar

/-- The WCT Hamiltonian nonlinearity `-β|u|²u + γ|u|⁴u`. -/
noncomputable def nonlin (β γ : ℝ) : AddMonoidAlgebra ℝ ℤ := (-β) • cubic + γ • quintic

theorem one_apply' (n : ℤ) : (1 : AddMonoidAlgebra ℝ ℤ) n = if (0 : ℤ) = n then 1 else 0 := by
  rw [AddMonoidAlgebra.one_def, Finsupp.single_apply]

theorem u_support (n : ℤ) (hn : n ≠ 1 ∧ n ≠ 2) : u n = 0 := by
  simp [u, Ne.symm hn.1, Ne.symm hn.2]

theorem cubic_three : cubic 3 = 1 := by
  simp only [cubic, u, uBar, add_mul, mul_add, single_mul_single, Finsupp.add_apply,
    Finsupp.single_apply]
  norm_num [one_apply']

theorem cubic_four : cubic 4 = 0 := by
  simp only [cubic, u, uBar, add_mul, mul_add, single_mul_single, Finsupp.add_apply,
    Finsupp.single_apply]
  norm_num [one_apply']

theorem quintic_three : quintic 3 = 5 := by
  simp only [quintic, u, uBar, add_mul, mul_add, single_mul_single, Finsupp.add_apply,
    Finsupp.single_apply]
  norm_num [one_apply']

theorem quintic_four : quintic 4 = 1 := by
  simp only [quintic, u, uBar, add_mul, mul_add, single_mul_single, Finsupp.add_apply,
    Finsupp.single_apply]
  norm_num [one_apply']

/-- **Non-preservation of finite Fourier support.** For every nonzero choice
of the nonlinear coefficients, the nonlinear vector field at the two-mode
state `u` has a nonzero coefficient outside `supp u = {1, 2}`. -/
theorem cubic_quintic_generates_new_modes (β γ : ℝ) (h : β ≠ 0 ∨ γ ≠ 0) :
    ∃ n : ℤ, u n = 0 ∧ nonlin β γ n ≠ 0 := by
  by_cases hγ : γ = 0
  · refine ⟨3, u_support 3 (by norm_num), ?_⟩
    have hβ : β ≠ 0 := h.resolve_right (by simpa using hγ)
    simp [nonlin, cubic_three, quintic_three, hγ, hβ]
  · refine ⟨4, u_support 4 (by norm_num), ?_⟩
    simp [nonlin, cubic_four, quintic_four, hγ]

end PVNP.FourierReceiver
