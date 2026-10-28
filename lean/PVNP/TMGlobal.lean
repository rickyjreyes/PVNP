import PVNP.TMCellCompiler

/-!
# A separate Turing configuration and the global tape-write law

This module defines a valid marked encoding from a Turing control/head/tape
triple, shows the encoding has exactly one marked head, and proves that
the compiled synchronous radius-one update writes precisely the tape
symbol required by the TM instruction at the head and nowhere else.
Global *head propagation* over changing positions, left/right
boundary safety, actual TM-trace equivalence, and binary description
serialization are separate proof obligations, not axioms.
-/

namespace PVNP.TMGlobal

open PVNP.PartII PVNP.TMCellCompiler

variable {Q Gamma : Type}

/-- A mathematical bounded-tape Turing configuration, independent of WCC. -/
structure TMConfiguration (n : Nat) (Q Gamma : Type) where
  tape : Configuration n Gamma
  headPos : Fin n
  control : Q

/-- Canonical direct head-marker encoding, using one control-bearing cell. -/
def encode {n : Nat} (c : TMConfiguration n Q Gamma) :
    Configuration n (TapeCell Q Gamma) :=
  fun i => { symbol := c.tape i
             head := if i = c.headPos then some c.control else none }

theorem encode_head_iff {n : Nat}
    (c : TMConfiguration n Q Gamma) (i : Fin n) :
    (encode c i).head = some c.control ↔ i = c.headPos := by
  simp [encode]

theorem encode_head_unique {n : Nat}
    (c : TMConfiguration n Q Gamma) (i : Fin n) :
    (encode c i).head ≠ none ↔ i = c.headPos := by
  by_cases h : i = c.headPos <;> simp [encode, h]

theorem encode_head_exists {n : Nat} (c : TMConfiguration n Q Gamma) :
    ∃ i : Fin n, (encode c i).head = some c.control := by
  exact ⟨c.headPos, (encode_head_iff c c.headPos).2 rfl⟩

/-- The true TM transition table is read once at the unique head. -/
def instruction {n : Nat}
    (T : TMTable Q Gamma) (c : TMConfiguration n Q Gamma) :
    Instruction Q Gamma :=
  T.transition c.control (c.tape c.headPos)

/-- Ordinary TM tape update, separate from the WCC local step. -/
def writeTape {n : Nat} (T : TMTable Q Gamma)
    (c : TMConfiguration n Q Gamma) : Configuration n Gamma :=
  fun i => if i = c.headPos then (instruction T c).write else c.tape i

/-- The local WCC compiler implements the globally specified TM *tape*
    update for all locations and all transitions, including moves. -/
theorem compiled_step_tape {n : Nat}
    (T : TMTable Q Gamma) (c : TMConfiguration n Q Gamma)
    (i : Fin n) :
    ((step (compile T) (encode c)) i).symbol =
      writeTape T c i := by
  by_cases hi : i = c.headPos
  · subst i
    simp [step, compile, encode, compiledRule, writeTape, instruction]
  · simp [step, compile, encode, compiledRule, writeTape, instruction, hi]

/-- Two TM configurations with the same encoding agree on each tape
    coordinate. (Injectivity of control and head is separate.) -/
theorem encoding_recovers_tape {n : Nat}
    (c d : TMConfiguration n Q Gamma) (h : encode c = encode d) :
    c.tape = d.tape := by
  funext i
  have he := congrArg (fun k => (k i).symbol) h
  simpa [encode] using he

end PVNP.TMGlobal
