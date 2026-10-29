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
  | right hmove hbound =>
      exact right_step_encoded T _ hmove hbound
  | left hmove hbound =>
      exact left_step_encoded T _ hmove hbound

/-- Exact inductive execution traces of independently specified
bounded-tape moving-head TM configurations. -/
inductive SafeMovingTrace (T : TMTable Q Gamma) {n : Nat} :
    Nat → TMConfiguration n Q Gamma → TMConfiguration n Q Gamma → Prop where
  | zero (c : TMConfiguration n Q Gamma) :
      SafeMovingTrace T 0 c c
  | succ {t : Nat} {c mid d : TMConfiguration n Q Gamma}
      (htail : SafeMovingTrace T t c mid)
      (hlast : SafeMovingStep T mid d) :
      SafeMovingTrace T (t + 1) c d

/-- Universal finite-trace semiconjugacy for safe nonstationary
head motion, with no per-step stationary-head assumption. -/
theorem safe_moving_trace_encoded (T : TMTable Q Gamma) {n : Nat}
    {t : Nat} {c d : TMConfiguration n Q Gamma}
    (h : SafeMovingTrace T t c d) :
    iterate (step (compile T)) t (encode c) = encode d := by
  induction h with
  | zero c => rfl
  | succ htail hlast ih =>
      rw [PVNP.PartII.iterate_succ]
      rw [ih]
      exact safe_moving_step_encoded T hlast


/-- For every finite trace of safe left/right moves, the compiled WCC
configuration has exactly the final TM head position and no other marker.
This is a trace-level global uniqueness theorem, not just a per-step fact. -/
theorem safe_moving_trace_head_iff (T : TMTable Q Gamma) {n : Nat}
    {t : Nat} {c d : TMConfiguration n Q Gamma}
    (h : SafeMovingTrace T t c d) (i : Fin n) :
    ((iterate (step (compile T)) t (encode c)) i).head ≠ none ↔
      i = d.headPos := by
  rw [safe_moving_trace_encoded T h]
  exact encode_head_unique d i

/-- A unique global marker survives every finite sequence of safe moves. -/
theorem safe_moving_trace_unique_head (T : TMTable Q Gamma) {n : Nat}
    {t : Nat} {c d : TMConfiguration n Q Gamma}
    (h : SafeMovingTrace T t c d) :
    ∃! i : Fin n,
      ((iterate (step (compile T)) t (encode c)) i).head ≠ none := by
  refine ⟨d.headPos, (safe_moving_trace_head_iff T h d.headPos).2 rfl, ?_⟩
  intro i hi
  exact (safe_moving_trace_head_iff T h i).1 hi

/-- The entire final tape, not only the marker trajectory, is recovered
from the compiled WCC execution after any safe moving-head finite trace. -/
theorem safe_moving_trace_tape (T : TMTable Q Gamma) {n : Nat}
    {t : Nat} {c d : TMConfiguration n Q Gamma}
    (h : SafeMovingTrace T t c d) :
    (fun i => ((iterate (step (compile T)) t (encode c)) i).symbol) = d.tape := by
  rw [safe_moving_trace_encoded T h]
  rfl

/-- Two independently presented safe-moving TM traces of the same
length from the same initial configuration have the same *complete*
final TM state. This uses exact WCC trace correspondence together
with injectivity of the canonical encoding, not an assumed TM
determinism axiom. -/
theorem safe_moving_trace_final_unique (T : TMTable Q Gamma) {n : Nat}
    {t : Nat} {c d e : TMConfiguration n Q Gamma}
    (hd : SafeMovingTrace T t c d) (he : SafeMovingTrace T t c e) :
    d = e := by
  apply encode_injective
  rw [← safe_moving_trace_encoded T hd,
      ← safe_moving_trace_encoded T he]

/-- Concatenation of two safe-moving traces preserves the exact
independent TM execution relation. The resulting WCC run uses the
sum of the two lengths, not two independent restarts. -/
theorem safe_moving_trace_append (T : TMTable Q Gamma) {n : Nat}
    {s t : Nat} {c mid d : TMConfiguration n Q Gamma}
    (hleft : SafeMovingTrace T s c mid)
    (hright : SafeMovingTrace T t mid d) :
    SafeMovingTrace T (s + t) c d := by
  induction hright with
  | zero =>
      simpa using hleft
  | succ htail hlast ih =>
      simpa only [Nat.add_assoc] using SafeMovingTrace.succ ih hlast

end PVNP.TMMovingTrace
