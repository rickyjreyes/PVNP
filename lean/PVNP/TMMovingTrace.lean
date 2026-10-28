import PVNP.TMHeadStep

/-!
# Finite exact TM / compiled WCC trace correspondence for safe moves

The relational semantics below permits arbitrary mixtures of leftward
and rightward head motions with explicit in-bounds hypotheses at EVERY
step. Each trace step executes the independent Turing instruction,
including the complete tape write and next control state. All such
finite traces commute with the *actual* radius-one WCC compiler.

This is not yet the uniform finite-alphabet binary serializer and
polynomial TM interpreter theorem. Stay moves and explicit halt/error
boundary semantics are additional cases for the fully general trace.
-/

namespace PVNP.TMMovingTrace

open PVNP.PartII PVNP.TMCellCompiler PVNP.TMGlobal
open PVNP.TMHeadStep

variable {Q Gamma : Type}

/-- A genuine safe TM step with left/right motion: not a stationary
head shortcut. The destination and boundary proof are explicit. -/
inductive SafeMovingStep (T : TMTable Q Gamma) {n : Nat} :
    TMConfiguration n Q Gamma → TMConfiguration n Q Gamma → Prop where
  | right (c : TMConfiguration n Q Gamma)
      (hmove : (instruction T c).move = Move.right)
      (hbound : c.headPos.val + 1 < n) :
      SafeMovingStep T c
        (tmNextAt T c ⟨c.headPos.val + 1, hbound⟩)
  | left (c : TMConfiguration n Q Gamma)
      (hmove : (instruction T c).move = Move.left)
      (hbound : 0 < c.headPos.val) :
      SafeMovingStep T c
        (tmNextAt T c ⟨c.headPos.val - 1, by omega⟩)

/-- Every single safe moving-head TM transition is implemented exactly
by a radius-one synchronous WCC step on the whole configuration. -/
theorem safe_moving_step_encoded (T : TMTable Q Gamma) {n : Nat}
    {c d : TMConfiguration n Q Gamma}
    (h : SafeMovingStep T c d) :
    step (compile T) (encode c) = encode d := by
  cases h with
  | right c hmove hbound =>
      exact right_step_encoded T c hmove hbound
  | left c hmove hbound =>
      exact left_step_encoded T c hmove hbound

/-- Exact inductive execution traces of independently specified
bounded-tape moving-head TM configurations. -/
inductive SafeMovingTrace (T : TMTable Q Gamma) {n : Nat} :
    Nat → TMConfiguration n Q Gamma → TMConfiguration n Q Gamma → Prop where
  | zero (c : TMConfiguration n Q Gamma) :
      SafeMovingTrace T 0 c c
  | succ {t : Nat} {c mid d : TMConfiguration n Q Gamma}
      (hfirst : SafeMovingStep T c mid)
      (htail : SafeMovingTrace T t mid d) :
      SafeMovingTrace T (t + 1) c d

/-- Universal finite-trace semiconjugacy for safe nonstationary
head motion, with no per-step stationary-head assumption. -/
theorem safe_moving_trace_encoded (T : TMTable Q Gamma) {n : Nat}
    {t : Nat} {c d : TMConfiguration n Q Gamma}
    (h : SafeMovingTrace T t c d) :
    iterate (step (compile T)) t (encode c) = encode d := by
  induction h with
  | zero c => rfl
  | succ hfirst htail ih =>
      rw [Function.iterate_succ_apply]
      rw [safe_moving_step_encoded T hfirst]
      exact ih

end PVNP.TMMovingTrace
