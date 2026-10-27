import Mathlib

/-!
# Part III — finite/algebraic counterexamples and Boolean influence bounds

No continuum PDE estimate, expander embedding lower bound, or P ≠ NP
conclusion is assumed as an axiom or claimed formalized here.
-/
namespace PVNP.PartIII

/-- Discrete symbolic analogue of distinct constant fields with a zero
Laplacian: this is NOT a full Sobolev-space formalization. -/
def zeroLaplacian (_ : Nat) : Nat := 0

theorem distinct_states_zero_curvature :
    (0 : Nat) ≠ 1 ∧ zeroLaplacian 0 = zeroLaplacian 1 := by
  decide

/-- The shifted denominator |ψ+ε| cannot be bounded below by ε>0
uniformly over all real ψ. -/
theorem shifted_denominator_no_uniform_gap (ε : ℝ) (hε : 0 < ε) :
    ¬ (∀ ψ : ℝ, ε ≤ |ψ + ε|) := by
  intro h
  have hz : ε ≤ |(-ε) + ε| := h (-ε)
  simp only [neg_add_cancel, abs_zero] at hz
  linarith

/-- A squared regularizer gives a strictly positive denominator. -/
theorem squared_regularizer_positive (ψ ε : ℝ) (hε : ε ≠ 0) :
    0 < ψ ^ 2 + ε ^ 2 := by
  have hsq : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
  nlinarith [sq_nonneg ψ]

/-- Any deterministic Boolean decider is an existential-witness
verifier simply by ignoring a Unit witness. -/
def ignoresWitness {Input : Type*} (f : Input → Bool)
    (x : Input) (_ : Unit) : Bool := f x

theorem deterministic_verifier_is_np_style
    {Input : Type*} (f : Input → Bool) (x : Input) :
    (∃ w : Unit, ignoresWitness f x w = true) ↔ f x = true := by
  constructor
  · rintro ⟨w, hw⟩
    simpa [ignoresWitness] using hw
  · intro hx
    exact ⟨(), by simpa [ignoresWitness] using hx⟩

/-- Abstract normalized influences pᵢ ≤ 1 have total influence ≤ n.
The theorem does NOT assert a relation to a physical curvature functional. -/
theorem total_influence_le_dimension {n : Nat} (p : Fin n → ℚ)
    (hp : ∀ i, p i ≤ 1) :
    (∑ i : Fin n, p i) ≤ (n : ℚ) := by
  have hle :
      (∑ i : Fin n, p i) ≤ ∑ _i : Fin n, (1 : ℚ) := by
    exact Finset.sum_le_sum (by intro i hi; exact hp i)
  simpa using hle

theorem total_influence_nonnegative {n : Nat} (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i) :
    0 ≤ ∑ i : Fin n, p i := by
  exact Finset.sum_nonneg (by intro i hi; exact hp i)

end PVNP.PartIII
