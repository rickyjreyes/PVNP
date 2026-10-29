import PVNP.MachineTableDecoder

/-!
# PVNP #11: soundness of the finite executable machine-code parser

The previous decoder work proves round-trip completeness on valid
one-hot encodings. Here we prove the converse at the instruction level:
every accepted record IS the canonical one-hot encoding of the decoded
instruction. This rules out silently accepting noncanonical instruction
bits. A flattened linear tape serialization and its TM instruction
cost remain separate open obligations.
-/

namespace PVNP.MachineDecoderSound

open PVNP.TMCellCompiler PVNP.MachineCode PVNP.MachineDecoder

/-- Every accepted strict one-hot word is exactly the canonical
one-hot encoding of its decoded index, not merely a word whose
first set bit agrees with that index. -/
theorem decodeStrictOneHot_sound {n : Nat}
    (bits : Fin n → Bool) (i : Fin n)
    (h : decodeStrictOneHot bits = some i) :
    bits = oneHot i := by
  cases hd : decodeOneHot bits with
  | none =>
      simp [decodeStrictOneHot, hd] at h
  | some j =>
      by_cases hb : bits = oneHot j
      · have hji : j = i := by
          simpa [decodeStrictOneHot, hd, hb] using h
        simpa [hji] using hb
      · simp [decodeStrictOneHot, hd, hb] at h

/-- The encoding of the decoded movement matches every finite
three-bit one-hot tag. -/
theorem moveIndex_moveFromIndex (i : Fin 3) :
    moveIndex (moveFromIndex i) = i := by
  fin_cases i <;> decide

/-- The decoder of a complete instruction accepts ONLY the canonical
bit representation of the recovered instruction. Invalid multi-hot,
zero-hot and noncanonical records cannot be accidentally accepted. -/
theorem decodeInstructionBits_sound {q g : Nat}
    (bits : InstructionBits q g)
    (ins : Instruction (Fin q) (Fin g))
    (h : decodeInstructionBits bits = some ins) :
    instructionBits ins = bits := by
  rcases bits with ⟨bn, bw, bm⟩
  cases hn : decodeStrictOneHot bn with
  | none =>
      simp [decodeInstructionBits, hn] at h
  | some next =>
      cases hw : decodeStrictOneHot bw with
      | none =>
          simp [decodeInstructionBits, hn, hw] at h
      | some write =>
          cases hm : decodeStrictOneHot bm with
          | none =>
              simp [decodeInstructionBits, hn, hw, hm] at h
          | some move =>
              have hrecord :
                  (⟨next, write, moveFromIndex move⟩ :
                    Instruction (Fin q) (Fin g)) = ins := by
                simpa [decodeInstructionBits, hn, hw, hm] using h
              cases hrecord
              have hbn := decodeStrictOneHot_sound bn next hn
              have hbw := decodeStrictOneHot_sound bw write hw
              have hbm := decodeStrictOneHot_sound bm move hm
              simp [instructionBits, moveIndex_moveFromIndex,
                hbn, hbw, hbm]

end PVNP.MachineDecoderSound
