import PVNP.Communication
import PVNP.PartIExtended

/-!
# Split 3-CNF SAT and finite-alphabet channel lower bounds

This module closes the exact Boolean part of a physically constrained
communication-complexity argument.

For each i, Alice with aᵢ=1 contributes (zᵢ ∨ zᵢ ∨ zᵢ);
Bob with bᵢ=1 contributes (¬zᵢ ∨ ¬zᵢ ∨ ¬zᵢ).
Absent bits contribute no clauses. The formula is satisfiable exactly
when the two private sets are disjoint.

For an exact deterministic distributed protocol whose accepting
transcript classes are rectangles, and where m transcript positions
each have q distinguishable symbols, the fooling-set theorem proves
2^n ≤ q^m. This holds for every correct protocol *within that model*.

No universal curvature-to-bandwidth law, all-algorithm SAT separation,
or classical P != NP is asserted. General centralized SAT computation
and randomized / quantum / analog-with-arbitrary-precision protocols
are not ruled out.
-/

namespace PVNP.SplitSATCapacity

abbrev Bits (n : Nat) := PVNP.Communication.Bits n

/-- Repeating a literal three times converts a unit clause to a
width-three clause without changing its Boolean truth value. -/
theorem triple_clause_eq (v : Bool) :
    PVNP.PartI.clauseTrue v v v = v := by
  cases v <;> decide

/-- Satisfaction of the union of the two private lists of 3-CNF
clauses. At bit i the clause is present exactly if the corresponding
party's input bit is true. This is an indexed semantic presentation
of a 3-CNF with at most 2n clauses, each literally of width 3. -/
def splitThreeSat {n : Nat} (a b z : Bits n) : Prop :=
  ∀ i : Fin n,
    (a i = true →
      PVNP.PartI.clauseTrue (z i) (z i) (z i) = true) ∧
    (b i = true →
      PVNP.PartI.clauseTrue (!z i) (!z i) (!z i) = true)

/-- Exact, unrestricted Boolean satisfiability equivalence for this
indexed 3-CNF encoding (not a statement about PDE equilibria). -/
theorem split_three_sat_iff_disjoint {n : Nat} (a b : Bits n) :
    (∃ z : Bits n, splitThreeSat a b z) ↔
      PVNP.Communication.disjoint a b := by
  constructor
  · rintro ⟨z, hz⟩ i
    cases ha : a i <;> cases hb : b i
    · exact Or.inl ha
    · exact Or.inl ha
    · exact Or.inr hb
    · exfalso
      have hpos : z i = true := by
        simpa only [triple_clause_eq] using (hz i).1 ha
      have hneg : (!z i) = true := by
        simpa only [triple_clause_eq] using (hz i).2 hb
      simp [hpos] at hneg
  · intro hdisj
    refine ⟨a, ?_⟩
    intro i
    constructor
    · intro ha
      simpa only [triple_clause_eq] using ha
    · intro hb
      rcases hdisj i with ha | hbfalse
      · simp [triple_clause_eq, ha]
      · rw [hb] at hbfalse
        cases Bool.noConfusion hbfalse

/-- A diagonal complement pair always has a satisfying assignment. -/
theorem diagonal_split_sat {n : Nat} (a : Bits n) :
    ∃ z : Bits n, splitThreeSat a (fun i => !a i) z :=
  (split_three_sat_iff_disjoint a (fun i => !a i)).2
    (PVNP.Communication.diagonal_disjoint a)

/-- Every exact deterministic split-input 3-CNF SAT protocol with a
rectangular transcript map has at least 2^n distinct transcript words.
Each of its m slots ranges over Fin q. The correctness assumption is
about the SAME combined 3-CNF language defined above. -/
theorem distributed_three_sat_transcript_capacity
    {n m q : Nat}
    (protocol : Bits n → Bits n → (Fin m → Fin q))
    (accepts : (Fin m → Fin q) → Prop)
    (hrectangle : ∀ a a' b b',
      protocol a b = protocol a' b' →
        protocol a b' = protocol a b ∧
        protocol a' b = protocol a b)
    (hcorrect : ∀ a b, accepts (protocol a b) ↔
      ∃ z : Bits n, splitThreeSat a b z) :
    2 ^ n ≤ q ^ m := by
  have haccept : ∀ a, accepts (protocol a (fun i => !a i)) := by
    intro a
    exact (hcorrect a (fun i => !a i)).2 (diagonal_split_sat a)
  have hsound : ∀ a b, accepts (protocol a b) →
      PVNP.Communication.disjoint a b := by
    intro a b h
    exact (split_three_sat_iff_disjoint a b).1
      ((hcorrect a b).1 h)
  have hcard := PVNP.Communication.disjointness_transcript_lower_bound
    protocol accepts hrectangle haccept hsound
  simpa [Fintype.card_fun] using hcard

/-- Binary fixed-length transcript consequence, including interactive
deterministic protocols provided complete transcript classes are
rectangles and message timing is not a free signaling channel. -/
theorem distributed_three_sat_binary_slots
    {n m : Nat}
    (protocol : Bits n → Bits n → (Fin m → Bool))
    (accepts : (Fin m → Bool) → Prop)
    (hrectangle : ∀ a a' b b',
      protocol a b = protocol a' b' →
        protocol a b' = protocol a b ∧
        protocol a' b = protocol a b)
    (hcorrect : ∀ a b, accepts (protocol a b) ↔
      ∃ z : Bits n, splitThreeSat a b z) :
    n ≤ m := by
  have h := distributed_three_sat_transcript_capacity
    protocol accepts hrectangle hcorrect
  have hpow : (2 : Nat) ^ n ≤ 2 ^ m := by
    simpa [Fintype.card_bool] using h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : Nat))).mp hpow

end PVNP.SplitSATCapacity
