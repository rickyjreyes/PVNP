import PVNP.SplitSATCapacity
import PVNP.DiscreteMachines

/-!
# Part I: bounded crossing records for split 3-CNF SAT

A cut record with at most `m` observed states can be represented in `m` slots,
each with either a finite-control state or an end/unused marker. Under a
rectangularity (splicing) condition on the *actual* record map, correctness for
the split-SAT family forces `2^n <= (|Q|+1)^m`.

This is a restricted cut-information bound. It is not a proof of the splicing
condition for every ordinary TM, nor a superpolynomial SAT lower bound.
The extra `none` symbol explicitly charges variable record termination.
-/

namespace PVNP.CrossingCapacity

open PVNP.Discrete
open PVNP.SplitSATCapacity

/-- A bounded crossing-sequence record: each slot is either a machine
state or an explicit unused/termination marker. -/
abbrev CutRecord (m : Nat) (Q : Type*) := Fin m → Option Q

/-- Exact resource bound for sound and complete split 3-CNF SAT protocols
whose entire cut record has a rectangular transcript class.
Unlike the fixed-length q-ary result, a slot may be unused. -/
theorem bounded_crossing_record_capacity
    {n m : Nat} {Q : Type*} [Fintype Q]
    (record : Bits n → Bits n → CutRecord m Q)
    (accepts : CutRecord m Q → Prop)
    (hsplice : ∀ a a' b b',
      record a b = record a' b' →
        record a b' = record a b ∧ record a' b = record a b)
    (hcorrect : ∀ a b, accepts (record a b) ↔
      ∃ z : Bits n, splitThreeSat a b z) :
    2 ^ n ≤ (Fintype.card Q + 1) ^ m := by
  have h := distributed_three_sat_transcript_capacity record accepts hsplice hcorrect
  simpa [CutRecord, Fintype.card_fun, Fintype.card_option] using h

/-- If the record alphabet is too small for the number of diagonal
instances, no rectangular correct split-SAT protocol exists. -/
theorem no_short_crossing_record
    {n m : Nat} {Q : Type*} [Fintype Q]
    (hsmall : (Fintype.card Q + 1) ^ m < 2 ^ n)
    (record : Bits n → Bits n → CutRecord m Q)
    (accepts : CutRecord m Q → Prop) :
    ¬ ((∀ a a' b b',
      record a b = record a' b' →
        record a b' = record a b ∧ record a' b = record a b) ∧
      (∀ a b, accepts (record a b) ↔
        ∃ z : Bits n, splitThreeSat a b z)) := by
  rintro ⟨hsplice, hcorrect⟩
  have h := bounded_crossing_record_capacity record accepts hsplice hcorrect
  omega

/-! ## Actual one-tape transition locality

The following theorem concerns the ordinary finite-control single-tape TM
already defined in `DiscreteMachines`. A machine's next instruction cannot
read any tape cell other than the current head cell. This is a building
block for, but not itself, the full crossing-sequence splicing theorem.
-/

/-- Equal control states and equal currently scanned symbols imply the
same machine instruction, independent of all other tape cells. -/
theorem same_scanned_symbol_same_instruction
    (M : TM) (c d : M.Cfg)
    (hstate : c.q = d.q)
    (hscan : c.tape c.head = d.tape d.head) :
    M.δ c.q (c.tape c.head) = M.δ d.q (d.tape d.head) := by
  rw [hstate, hscan]

/-- The ordinary TM's head moves by at most one tape cell per step. -/
theorem one_tape_head_speed (M : TM) (c : M.Cfg) :
    c.head - 1 ≤ (M.next c).head ∧ (M.next c).head ≤ c.head + 1 := by
  unfold TM.next TM.step
  cases h : M.δ c.q (c.tape c.head) with
  | none =>
      simp [h]
  | some instr =>
      obtain ⟨q, w, move⟩ := instr
      cases move <;> simp [h, Dir.shift] <;> omega

/-- Crossing a rightward cut in one step entails arriving at the cell
immediately to the right of that cut. -/
theorem right_crossing_is_adjacent
    (M : TM) (c : M.Cfg) (cut : Int)
    (hleft : c.head < cut)
    (hright : cut ≤ (M.next c).head) :
    c.head = cut - 1 ∧ (M.next c).head = cut := by
  have hspeed := one_tape_head_speed M c
  omega

end PVNP.CrossingCapacity
