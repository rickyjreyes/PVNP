import PVNP.TorusH2

/-!
# Resonance structure of the frozen dispersion

Normal forms and modified energies remove the *non-resonant* part of a nonlinear interaction. An
interaction quartet `k₁ − k₂ + k₃ = k` of the cubic term is resonant for the frozen dispersion
`ω(k) = (κ − q_L(k))²` when `Φ = ω(k₁) − ω(k₂) + ω(k₃) − ω(k) = 0`.

* `om_two_pi`: on the torus `L = 2π`, `ω(k) = (κ − (k₁² + k₂²))²`.
* `phase_int`: for integer `κ`, `Φ` is an integer, so a non-resonant quartet has `|Φ| ≥ 1`
  (`no_small_divisors`). There are no small divisors.
* `doubly_resonant_trivial`: a quartet resonant for both the Schrödinger phase
  `a − b + c − d` and the frozen phase is trivial: `{a, c} = {b, d}` for the squared moduli.
  Radial multipliers vanish on such quartets (`radial_vanish`).
* `nontrivial_resonance`: the frozen dispersion alone has **nontrivial** resonant quartets. For
  `κ = 0`, `k₁ = (−4,−3)`, `k₂ = (−4,−1)`, `k₃ = (−2,−2)`, `k = (−2,−4)` gives
  `|kᵢ|² = (25, 17, 8, 20)`, `Φ = 0`, and the `H¹` energy multiplier
  `(1+25) − (1+17) + (1+8) − (1+20) = −4 ≠ 0`.

Consequence. A modified `H^s` or analytic energy with a radial weight keeps a non-oscillating
resonant flux, and no normal-form correction removes it. The hypothesis "only trivial
resonances", which simplifies the analysis of some dispersive equations, fails here.
-/

namespace PVNP.FrozenResonance

open Real PVNP.Torus

/-- On `L = 2π` the frequencies are the integer modes. -/
theorem qf_two_pi (k : Z2) : qf (2 * π) k = ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) := by
  have hπ : (2 * π) ≠ 0 := by positivity
  simp only [qf, xi1, xi2]
  field_simp

theorem om_two_pi (κ : ℝ) (k : Z2) : om (2 * π) κ k = (κ - ((k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2)) ^ 2 := by
  rw [om, qf_two_pi]

/-- The integer frequency for integer `κ`. -/
def omZ (κ : ℤ) (k : Z2) : ℤ := (κ - (k.1 ^ 2 + k.2 ^ 2)) ^ 2

theorem om_cast (κ : ℤ) (k : Z2) : om (2 * π) κ k = (omZ κ k : ℝ) := by
  rw [om_two_pi, omZ]; push_cast; ring

/-- The resonance function of a quartet. -/
noncomputable def phase (L κ : ℝ) (k₁ k₂ k₃ k : Z2) : ℝ :=
  om L κ k₁ - om L κ k₂ + om L κ k₃ - om L κ k

theorem phase_int (κ : ℤ) (k₁ k₂ k₃ k : Z2) :
    phase (2 * π) κ k₁ k₂ k₃ k = ((omZ κ k₁ - omZ κ k₂ + omZ κ k₃ - omZ κ k : ℤ) : ℝ) := by
  rw [phase, om_cast, om_cast, om_cast, om_cast]; push_cast; ring

/-- **No small divisors**: a non-resonant quartet on `L = 2π` with integer `κ` has `|Φ| ≥ 1`. -/
theorem no_small_divisors (κ : ℤ) (k₁ k₂ k₃ k : Z2) (h : phase (2 * π) κ k₁ k₂ k₃ k ≠ 0) :
    1 ≤ |phase (2 * π) κ k₁ k₂ k₃ k| := by
  rw [phase_int] at h ⊢
  have hz : (omZ κ k₁ - omZ κ k₂ + omZ κ k₃ - omZ κ k) ≠ 0 := by
    intro h0; apply h; rw [h0]; simp
  have : (1 : ℤ) ≤ |omZ κ k₁ - omZ κ k₂ + omZ κ k₃ - omZ κ k| := Int.one_le_abs hz
  rw [← Int.cast_abs]
  exact_mod_cast this

/-- **Doubly resonant quartets are trivial.** If `a − b + c − d = 0` and
`(κ − a)² − (κ − b)² + (κ − c)² − (κ − d)² = 0`, then `{a, c} = {b, d}`. -/
theorem doubly_resonant_trivial (κ a b c d : ℝ) (h₂ : a - b + c - d = 0)
    (h₄ : (κ - a) ^ 2 - (κ - b) ^ 2 + (κ - c) ^ 2 - (κ - d) ^ 2 = 0) :
    (a = b ∧ c = d) ∨ (a = d ∧ c = b) := by
  have hsq : a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2 = 0 := by linear_combination h₄ + 2 * κ * h₂
  have hc : c = b + d - a := by linarith
  subst hc
  have hprod : (a - b) * (a - d) = 0 := by linear_combination hsq / 2
  rcases mul_eq_zero.mp hprod with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-- Radial multipliers vanish on trivial quartets. -/
theorem radial_vanish (w : ℝ → ℝ) {a b c d : ℝ} (h : (a = b ∧ c = d) ∨ (a = d ∧ c = b)) :
    w a - w b + w c - w d = 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> ring

/-- **A nontrivial resonance of the frozen dispersion** (`κ = 0`, `L = 2π`), on which the `H¹`
energy multiplier does not vanish. -/
theorem nontrivial_resonance :
    let k₁ : Z2 := (-4, -3)
    let k₂ : Z2 := (-4, -1)
    let k₃ : Z2 := (-2, -2)
    let k : Z2 := (-2, -4)
    k₁ - k₂ + k₃ = k ∧ omZ 0 k₁ - omZ 0 k₂ + omZ 0 k₃ - omZ 0 k = 0 ∧
      (1 + (k₁.1 ^ 2 + k₁.2 ^ 2)) - (1 + (k₂.1 ^ 2 + k₂.2 ^ 2)) +
        (1 + (k₃.1 ^ 2 + k₃.2 ^ 2)) - (1 + (k.1 ^ 2 + k.2 ^ 2)) = (-4 : ℤ) := by
  refine ⟨by decide, by decide, by decide⟩

/-- The same resonance as a real resonance of the frozen dispersion on `T²_{2π}`. -/
theorem nontrivial_resonance_real :
    phase (2 * π) (0 : ℤ) (-4, -3) (-4, -1) (-2, -2) (-2, -4) = 0 := by
  rw [phase_int]
  have : (omZ 0 (-4, -3) - omZ 0 (-4, -1) + omZ 0 (-2, -2) - omZ 0 (-2, -4) : ℤ) = 0 := by decide
  rw [this]; simp

end PVNP.FrozenResonance
