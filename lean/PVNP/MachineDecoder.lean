import PVNP.MachineCode
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Executable one-hot and instruction decoder for finite TM descriptions

Unlike the earlier injectivity-only boolean grids, these definitions
recover finite-state symbols and whole instruction records by searching
explicit finite bit vectors. A complete flattened binary serializer
and an ordinary tape-TM instruction-count theorem remain open.
-/

namespace PVNP.MachineDecoder

open PVNP.TMCellCompiler PVNP.MachineCode

/-- Executable finite search for the first enabled bit. -/
def decodeOneHot {n : Nat} (bits : Fin n → Bool) : Option (Fin n) :=
  Fin.find (fun i => bits i = true)

/-- An honestly encoded one-hot state is decoded exactly. -/
theorem decodeOneHot_oneHot {n : Nat} (i : Fin n) :
    decodeOneHot (oneHot i) = some i := by
  have he : i ∈ Fin.find (fun j : Fin n => oneHot i j = true) :=
    (Fin.mem_find_iff).2
      ⟨by simp [oneHot], by
        intro j hj
        have hji : j = i := by simpa [oneHot] using hj
        exact le_of_eq hji.symm⟩
  simpa [decodeOneHot] using he

/-- Fully validated one-hot decoding: reject all-zero AND multi-hot
bit fields rather than silently choosing the first enabled index. -/
def decodeStrictOneHot {n : Nat} (bits : Fin n → Bool) :
    Option (Fin n) :=
  match decodeOneHot bits with
  | none => none
  | some i => if bits = oneHot i then some i else none

/-- Valid one-hot values remain exactly decodable, including the
empty-domain edge case where no index exists. -/
theorem decodeStrictOneHot_oneHot {n : Nat} (i : Fin n) :
    decodeStrictOneHot (oneHot i) = some i := by
  simp [decodeStrictOneHot, decodeOneHot_oneHot]

/-- The invalid two-hot 2-bit field is rejected by the strict parser. -/
theorem decodeStrictOneHot_reject_two_hot :
    decodeStrictOneHot (fun _ : Fin 2 => true) = none := by
  decide

/-- An explicit inverse of the three finite movement tags. -/
def moveFromIndex (i : Fin 3) : Move :=
  if i = 0 then Move.left else if i = 1 then Move.stay else Move.right

theorem moveFromIndex_moveIndex (m : Move) :
    moveFromIndex (moveIndex m) = m := by
  cases m <;> decide

/-- Executable decoder for a finite instruction record. Malformed
one-hot fields (including all-zero fields) can be rejected. -/
def decodeInstructionBits {q g : Nat}
    (bits : InstructionBits q g) : Option (Instruction (Fin q) (Fin g)) := do
  let next ← decodeStrictOneHot bits.1
  let write ← decodeStrictOneHot bits.2.1
  let movement ← decodeStrictOneHot bits.2.2
  return ⟨next, write, moveFromIndex movement⟩

/-- Round-trip correctness for every finite instruction, not merely
injectivity of its encoded bit tuple. -/
theorem decodeInstructionBits_roundtrip {q g : Nat}
    (ins : Instruction (Fin q) (Fin g)) :
    decodeInstructionBits (instructionBits ins) = some ins := by
  cases ins with
  | mk next write move =>
      simp [decodeInstructionBits, instructionBits,
        decodeStrictOneHot_oneHot, moveFromIndex_moveIndex]

/-- Correct decoders imply uniqueness of the source instructions. -/
theorem instructionBits_roundtrip_injective {q g : Nat}
    (a b : Instruction (Fin q) (Fin g))
    (h : instructionBits a = instructionBits b) : a = b := by
  have hd := congrArg decodeInstructionBits h
  rw [decodeInstructionBits_roundtrip, decodeInstructionBits_roundtrip] at hd
  exact Option.some.inj hd

end PVNP.MachineDecoder
