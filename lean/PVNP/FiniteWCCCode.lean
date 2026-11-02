import PVNP.MachineCode
import PVNP.PartIIExtended

/-!
# An explicit finite-alphabet WCC local-rule description

The legacy RadiusOneMachine carries an arbitrary function and an arbitrary
state Type; that by itself is NOT a machine code, a Fintype constraint,
or a uniform interpreter. This finite indexed specialization supplies
all of them as *finite bit-table data*. The global synchronous semantics
are exactly the existing PartII.step after forgetting the representation.

This file proves faithful data representation and algebraic step agreement;
it does not implement a tape TM running this table or claim TM runtime.
-/

namespace PVNP.FiniteWCCCode

open PVNP.PartII PVNP.MachineCode

structure FiniteWCC (s : Nat) where
  blank : Fin s
  localRule : Fin s → Fin s → Fin s → Fin s

def toRadiusOne {s : Nat} (M : FiniteWCC s) :
    RadiusOneMachine (Fin s) where
  blank := M.blank
  localRule := M.localRule

/-- Exact correspondence to the preexisting synchronous update. -/
theorem finiteStep_agrees {s n : Nat} (M : FiniteWCC s)
    (c : Configuration n (Fin s)) :
    step (toRadiusOne M) c =
      fun i => M.localRule
        (left (toRadiusOne M) c i)
        (c i)
        (right (toRadiusOne M) c i) := rfl

/-- Every table entry is encoded as s one-hot bits, including the blank.
    A four-dimensional rectangular bit array is a finite binary
    representation of the rule, not uncharged oracle access. -/
def finiteCode {s : Nat} (M : FiniteWCC s) :
    (Fin s → Bool) ×
      (Fin s → Fin s → Fin s → Fin s → Bool) :=
  (oneHot M.blank, fun a b c => oneHot (M.localRule a b c))

theorem finiteCode_injective {s : Nat} :
    Function.Injective (finiteCode (s := s)) := by
  intro M N h
  have hb : M.blank = N.blank :=
    oneHot_injective (congrArg Prod.fst h)
  have hr : M.localRule = N.localRule := by
    funext a b c
    have hbit := congrArg (fun code => code.2 a b c) h
    exact oneHot_injective hbit
  cases M with
  | mk mb mr =>
      cases N with
      | mk nb nr =>
          dsimp at hb hr
          subst nb
          subst nr
          rfl

/-- Binary table size: s blank bits plus s^3 outputs each of s bits. -/
def finiteCodeBitCount (s : Nat) : Nat := s + s ^ 4

theorem finiteCodeBitCount_exact (s : Nat) :
    finiteCodeBitCount s = s + s * s * s * s := by
  unfold finiteCodeBitCount
  ring

/-- Finite description size is polynomial in the alphabet cardinality;
    the alphabet cardinality itself must be charged for uniformity. -/
theorem finiteCodeBitCount_quartic (s : Nat) :
    finiteCodeBitCount s ≤ 2 * (s + 1) ^ 4 := by
  have hs : s ≤ s + 1 := by omega
  have hpow : s ^ 4 ≤ (s + 1) ^ 4 :=
    Nat.pow_le_pow_left hs 4
  have hlinear : s ≤ (s + 1) ^ 4 := by
    nlinarith [sq_nonneg ((s : ℤ) + 1)]
  unfold finiteCodeBitCount
  omega

end PVNP.FiniteWCCCode
