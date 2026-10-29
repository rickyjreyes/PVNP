import PVNP.MachineDecoder

/-!
# PVNP #11: executable decoder for complete finite TM table bit grids

The previous MachineDecoder recovers an individual instruction from
one-hot state/write/movement fields. This module constructs a total
*whole-table* decoder over every state/symbol pair, and proves that
well-formed encoded tables round-trip exactly.

Each finite-domain record must have a valid instruction before the
table is accepted. The default instruction is never used on a valid
encoding. This is a rectangular binary grid decoder, not the still
missing flattened tape serializer or ordinary TM instruction-cost proof.
-/

namespace PVNP.MachineTableDecoder

open PVNP.TMCellCompiler PVNP.MachineCode PVNP.MachineDecoder

/-- One explicit finite rectangular binary-grid representation of the
blank symbol and every transition instruction. -/
abbrev TableBits (q g : Nat) :=
  (Fin g → Bool) × (Fin q → Fin g → InstructionBits q g)

/-- A total executable table decoder for nonempty state and tape
alphabets. Malformed records are rejected; valid records are decoded
by the earlier checked one-hot instruction decoder. -/
def decodeTableBits {q g : Nat} [NeZero q] [NeZero g]
    (bits : TableBits q g) : Option (FiniteTable q g) :=
  match decodeOneHot bits.1 with
  | none => none
  | some blank =>
      if decide (∀ state : Fin q, ∀ symbol : Fin g,
          (decodeInstructionBits (bits.2 state symbol)).isSome) then
        some {
          blank := blank
          transition := fun state symbol =>
            (decodeInstructionBits (bits.2 state symbol)).getD
              ⟨0, 0, Move.stay⟩
        }
      else none

/-- Every valid full finite deterministic transition table is recovered
exactly, including its blank and every transition field. This is
stronger than proving injectivity of each record in isolation. -/
theorem decodeTableBits_roundtrip {q g : Nat} [NeZero q] [NeZero g]
    (T : FiniteTable q g) :
    decodeTableBits (tableBits T) = some T := by
  cases T with
  | mk blank transition =>
      simp [decodeTableBits, tableBits, decodeOneHot_oneHot,
        decodeInstructionBits_roundtrip]

/-- The complete encoded table is injective as a direct consequence
of the executable round-trip decoder, not an abstract injection axiom. -/
theorem tableBits_injective_by_decoder
    {q g : Nat} [NeZero q] [NeZero g]
    (T U : FiniteTable q g)
    (h : tableBits T = tableBits U) : T = U := by
  have hd := congrArg decodeTableBits h
  rw [decodeTableBits_roundtrip, decodeTableBits_roundtrip] at hd
  exact Option.some.inj hd

end PVNP.MachineTableDecoder
