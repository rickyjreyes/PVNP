import PVNP.PartIIExtended

/-!
# A uniform radius-one communication lower bound

For the exact finite-lattice semantics in PartIIExtended, the state of cell
zero after t synchronous rounds cannot depend on the value at cell (t+1).
The proof quantifies over EVERY local rule and blank symbol. It presumes
a fixed direct input encoding and a fixed cell-zero readout, NOT arbitrary
input preprocessing or a globally observing decoder. In particular, this
does not show SAT or P versus NP hardness, nor a physical curvature bound.
-/

namespace PVNP.LocalityLowerBound

open PVNP.PartII

variable {S : Type}

def prefixAgree {n : Nat} (c d : Configuration n S) (k : Nat) : Prop :=
  ∀ i : Fin n, i.val < k → c i = d i

theorem sample_agree (M : RadiusOneMachine S) {n k : Nat}
    (c d : Configuration n S) (h : prefixAgree c d k)
    (j : Nat) (hj : j < k) :
    sample M c j = sample M d j := by
  by_cases hbound : j < n
  · simp only [sample, dif_pos hbound]
    exact h ⟨j, hbound⟩ hj
  · simp only [sample, dif_neg hbound]

theorem left_agree (M : RadiusOneMachine S) {n k : Nat}
    (c d : Configuration n S) (h : prefixAgree c d (k + 1))
    (i : Fin n) (hi : i.val < k) :
    left M c i = left M d i := by
  by_cases hz : i.val = 0
  · simp [left, hz]
  · simp only [left, hz, if_false]
    apply sample_agree M c d h
    omega

theorem right_agree (M : RadiusOneMachine S) {n k : Nat}
    (c d : Configuration n S) (h : prefixAgree c d (k + 1))
    (i : Fin n) (hi : i.val < k) :
    right M c i = right M d i := by
  apply sample_agree M c d h
  omega

/-- One locality step shrinks the guaranteed matching prefix by at most 1. -/
theorem prefix_agree_step (M : RadiusOneMachine S) {n k : Nat}
    (c d : Configuration n S) (h : prefixAgree c d (k + 1)) :
    prefixAgree (step M c) (step M d) k := by
  intro i hi
  apply local_update_only M c d i
  · exact left_agree M c d h i hi
  · apply h i
    omega
  · exact right_agree M c d h i hi

/-- Full causality theorem, uniform in the local rule and time horizon. -/
theorem prefix_agree_iterate (M : RadiusOneMachine S) {n : Nat}
    (c d : Configuration n S) :
    ∀ t k : Nat, prefixAgree c d (t + k) →
      prefixAgree (iterate (step M) t c) (iterate (step M) t d) k := by
  intro t
  induction t with
  | zero =>
      intro k h
      simpa [iterate] using h
  | succ t ih =>
      intro k h
      change prefixAgree
        (step M (iterate (step M) t c))
        (step M (iterate (step M) t d)) k
      apply prefix_agree_step M
      apply ih (k + 1)
      intro i hi
      exact h i (by omega)

/-- Two direct encodings of length t+2 that differ only at the last cell. -/
def allZero (t : Nat) : Configuration (t + 2) Bool := fun _ => false

def distantOne (t : Nat) : Configuration (t + 2) Bool :=
  fun i => decide (i.val = t + 1)

theorem distant_inputs_differ (t : Nat) :
    allZero t ⟨t + 1, by omega⟩ ≠
      distantOne t ⟨t + 1, by omega⟩ := by
  simp [allZero, distantOne]

/-- Unconditional adversarial pair: every radius-one machine has identical
    fixed-left-end readout after t rounds on two inputs differing at t+1. -/
theorem indistinguishable_far_input (t : Nat)
    (M : RadiusOneMachine Bool) :
    (iterate (step M) t (allZero t)) ⟨0, by omega⟩ =
    (iterate (step M) t (distantOne t)) ⟨0, by omega⟩ := by
  have hprefix : prefixAgree (allZero t) (distantOne t) (t + 1) := by
    intro i hi
    have hne : i.val ≠ t + 1 := by omega
    simp [allZero, distantOne, hne]
  have h := prefix_agree_iterate M (allZero t) (distantOne t)
    t 1 (by simpa using hprefix)
  exact h ⟨0, by omega⟩ (by omega)

/-- Decoding the left-end state does not evade the causal lower bound.
    A global output decoder or a nonlocal encoder would be a DIFFERENT model. -/
theorem every_local_rule_fails_far_bit_by_t
    (t : Nat) (M : RadiusOneMachine Bool) (decode : Bool → Bool) :
    ∃ c d : Configuration (t + 2) Bool,
      c ⟨t + 1, by omega⟩ ≠ d ⟨t + 1, by omega⟩ ∧
      decode ((iterate (step M) t c) ⟨0, by omega⟩) =
      decode ((iterate (step M) t d) ⟨0, by omega⟩) := by
  refine ⟨allZero t, distantOne t, distant_inputs_differ t, ?_⟩
  exact congrArg decode (indistinguishable_far_input t M)

end PVNP.LocalityLowerBound
