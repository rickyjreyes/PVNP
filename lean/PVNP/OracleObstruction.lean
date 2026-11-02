import PVNP.PartIIExtended

/-!
# Unrestricted mathematical rules are not finitely coded machines

The legacy RadiusOneMachine accepts State = Nat × Bool and an arbitrary
set-theoretic function (Nat → Bool) as its transition. Such a rule is
not necessarily computable. Any predicate can be installed as a
one-round rule, but Cantor diagonalization shows there is no
enumeration of all predicates by natural-number program codes.

This does NOT refute equivalence of the *finite encoded* WCC model;
it is a concrete obstruction to silently promoting the unrestricted
Lean type to an effective uniform Turing-machine class.
-/

namespace PVNP.OracleObstruction

open PVNP.PartII

/-- A mathematical local-rule oracle, not a finite instruction table. -/
def oracleRule (f : Nat → Bool) :
    RadiusOneMachine (Nat × Bool) where
  blank := (0, false)
  localRule := fun _ center _ => (center.1, f center.1)

def singletonInput (x : Nat) : Configuration 1 (Nat × Bool) :=
  fun _ => (x, false)

/-- Any Boolean predicate appears as an output after one update when
    arbitrary, potentially uncomputable local functions are allowed. -/
theorem oracleRule_one_round (f : Nat → Bool) (x : Nat) :
    ((step (oracleRule f) (singletonInput x)) ⟨0, by decide⟩).2 =
      f x := by
  rfl

/-- Diagonal argument: no enumeration by natural machine codes can
    contain every function Nat → Bool. No classical complexity-theory
    hypothesis is needed. -/
theorem all_predicates_not_enumerable
    (enumerate : Nat → Nat → Bool) :
    ∃ f : Nat → Bool, ∀ code : Nat, f ≠ enumerate code := by
  refine ⟨(fun n => !(enumerate n n)), ?_⟩
  intro code h
  have heq := congrFun h code
  cases hv : enumerate code code <;> simp [hv] at heq

end PVNP.OracleObstruction
