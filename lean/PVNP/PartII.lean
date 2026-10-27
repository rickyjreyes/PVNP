import Mathlib

/-!
# Part II — deterministic finite-step replay and semiconjugate simulation

These prove exact simulation identities. They do NOT establish polynomial
complexity for complete machines or PDE curvature-resource realizability.
-/
namespace PVNP.PartII

def iterate {State : Type*} (step : State → State) : Nat → State → State
  | 0, x => x
  | n + 1, x => step (iterate step n x)

theorem iterate_zero {State : Type*} (step : State → State) (x : State) :
    iterate step 0 x = x := rfl

theorem iterate_succ {State : Type*} (step : State → State) (n : Nat) (x : State) :
    iterate step (n + 1) x = step (iterate step n x) := rfl

/-- Exact one-step commuting encoding extends to every finite trajectory. -/
theorem encode_iterate
    {A B : Type*} (stepA : A → A) (stepB : B → B) (encode : A → B)
    (h : ∀ a, encode (stepA a) = stepB (encode a)) :
    ∀ n a, encode (iterate stepA n a) = iterate stepB n (encode a) := by
  intro n
  induction n with
  | zero =>
      intro a
      rfl
  | succ n ih =>
      intro a
      change encode (stepA (iterate stepA n a)) =
        stepB (iterate stepB n (encode a))
      calc
        encode (stepA (iterate stepA n a)) =
            stepB (encode (iterate stepA n a)) := h _
        _ = stepB (iterate stepB n (encode a)) := congrArg stepB (ih a)

/-- The precise extra hypothesis for wave-symbol trajectory correspondence. -/
theorem quantization_commutes
    {Wave Symbol : Type*} (F : Wave → Wave) (U : Symbol → Symbol)
    (Q : Wave → Symbol)
    (h : ∀ w, Q (F w) = U (Q w)) (n : Nat) (w : Wave) :
    Q (iterate F n w) = iterate U n (Q w) :=
  encode_iterate F U Q h n w

/-- Explicit counterexample to assuming quantized and reconstructed
dynamics commute without a compatibility condition. -/
def toyQ (x : Nat) : Bool := decide (0 < x)
def toyStep (x : Nat) : Nat := if x = 1 then 1 else 0
def toyRepresentative (b : Bool) : Nat := if b then 2 else 0
def toyU (b : Bool) : Bool := toyQ (toyStep (toyRepresentative b))

theorem representative_rule_can_fail :
    toyQ (toyStep 1) ≠ toyU (toyQ 1) := by
  decide

end PVNP.PartII
