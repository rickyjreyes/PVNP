import Mathlib

/-!
# Communication cut lower bound for split SAT encodings

A deterministic protocol's accepting transcripts are monochromatic
rectangles. The set-disjointness fooling set (x, complement x) is
injective in the transcript space. We kernel-prove the 2^n transcript
lower bound. Turning this into B*T ≥ n requires a separately specified
B-bit/T-round transcript encoding.
-/

namespace PVNP.Communication

abbrev Bits (n : Nat) := Fin n → Bool

def disjoint {n : Nat} (a b : Bits n) : Prop :=
  ∀ i, a i = false ∨ b i = false

theorem diagonal_disjoint {n : Nat} (a : Bits n) :
    disjoint a (fun i => !a i) := by
  intro i
  cases h : a i <;> simp [h]

theorem cross_disjoint_implies_eq {n : Nat} (a b : Bits n)
    (hab : disjoint a (fun i => !b i))
    (hba : disjoint b (fun i => !a i)) : a = b := by
  funext i
  have h₁ := hab i
  have h₂ := hba i
  cases ha : a i <;> cases hb : b i <;>
    simp_all [disjoint]

/-- Each diagonal satisfying input must have a different accepted
transcript, provided transcript classes are rectangular and sound. -/
theorem fooling_set_transcript_injective
    {n : Nat} {Transcript : Type*}
    (transcript : Bits n → Bits n → Transcript)
    (accepts : Transcript → Prop)
    (hrectangle : ∀ a a' b b',
      transcript a b = transcript a' b' →
        transcript a b' = transcript a b ∧
        transcript a' b = transcript a b)
    (haccept : ∀ a, accepts (transcript a (fun i => !a i)))
    (hsound : ∀ a b, accepts (transcript a b) → disjoint a b) :
    Function.Injective (fun a => transcript a (fun i => !a i)) := by
  intro a b heq
  have hrect := hrectangle a b (fun i => !a i) (fun i => !b i) heq
  have hab : disjoint a (fun i => !b i) := by
    apply hsound
    rw [hrect.1]
    exact haccept a
  have hba : disjoint b (fun i => !a i) := by
    apply hsound
    rw [hrect.2]
    exact haccept a
  exact cross_disjoint_implies_eq a b hab hba

/-- All deterministic fixed-length exact transcripts together must have
at least 2^n distinct values. This is the communication bottleneck. -/
theorem disjointness_transcript_lower_bound
    {n : Nat} {Transcript : Type*} [Fintype Transcript]
    (transcript : Bits n → Bits n → Transcript)
    (accepts : Transcript → Prop)
    (hrectangle : ∀ a a' b b',
      transcript a b = transcript a' b' →
        transcript a b' = transcript a b ∧
        transcript a' b = transcript a b)
    (haccept : ∀ a, accepts (transcript a (fun i => !a i)))
    (hsound : ∀ a b, accepts (transcript a b) → disjoint a b) :
    2 ^ n ≤ Fintype.card Transcript := by
  have hinj := fooling_set_transcript_injective transcript accepts
    hrectangle haccept hsound
  have hcard := Fintype.card_le_of_injective
    (fun a : Bits n => transcript a (fun i => !a i)) hinj
  simpa [Bits, Fintype.card_fun] using hcard

end PVNP.Communication
