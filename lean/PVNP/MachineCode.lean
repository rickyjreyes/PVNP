import PVNP.TMGlobal

/-!
# A finite binary description of *every finite transition table*

Every control state and tape symbol is encoded as a one-hot finite bit
vector, and each instruction has a three-bit move tag. The entire finite
table is represented as an indexed binary grid. Its encoding is injective
and its allocated bit count is explicit and cubic in the number of states
and symbols. This proves a uniform *data representation*, NOT a
serialization or an instruction-count theorem for a tape TM decoder.
-/

namespace PVNP.MachineCode

open PVNP.TMCellCompiler

/-- Finite one-hot binary code of an alphabet symbol. -/
def oneHot {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

theorem oneHot_injective {n : Nat} :
    Function.Injective (oneHot : Fin n → Fin n → Bool) := by
  intro a b h
  have hbit := congrFun h a
  simpa [oneHot] using hbit

def moveIndex : Move → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

theorem moveIndex_injective : Function.Injective moveIndex := by
  intro a b h
  cases a <;> cases b <;> simp_all [moveIndex]

abbrev InstructionBits (q g : Nat) :=
  (Fin q → Bool) × ((Fin g → Bool) × (Fin 3 → Bool))

def instructionBits {q g : Nat}
    (ins : Instruction (Fin q) (Fin g)) : InstructionBits q g :=
  (oneHot ins.next, (oneHot ins.write, oneHot (moveIndex ins.move)))

theorem instructionBits_injective {q g : Nat} :
    Function.Injective (instructionBits (q := q) (g := g)) := by
  intro a b h
  have hnext : a.next = b.next :=
    oneHot_injective (congrArg Prod.fst h)
  have hwrite : a.write = b.write :=
    oneHot_injective (congrArg (fun z : InstructionBits q g => z.2.1) h)
  have hmove : a.move = b.move := moveIndex_injective
    (oneHot_injective (congrArg
      (fun z : InstructionBits q g => z.2.2) h))
  cases a with
  | mk an aw am =>
      cases b with
      | mk bn bw bm =>
          dsimp at hnext hwrite hmove
          subst bn
          subst bw
          subst bm
          rfl

/-- Explicit FINITE machine description, no code evaluated by an oracle. -/
structure FiniteTable (q g : Nat) where
  blank : Fin g
  transition : Fin q → Fin g → Instruction (Fin q) (Fin g)

/-- Its entire transition table and blank are encoded into fixed-size
    Boolean arrays, independent of any input instance. -/
def tableBits {q g : Nat} (T : FiniteTable q g) :
    (Fin g → Bool) ×
      (Fin q → Fin g → InstructionBits q g) :=
  (oneHot T.blank, fun state symbol =>
    instructionBits (T.transition state symbol))

theorem tableBits_injective {q g : Nat} :
    Function.Injective (tableBits (q := q) (g := g)) := by
  intro A B h
  have hb : A.blank = B.blank :=
    oneHot_injective (congrArg Prod.fst h)
  have ht : A.transition = B.transition := by
    funext state symbol
    have hpair := congrArg
      (fun z => z.2 state symbol) h
    exact instructionBits_injective hpair
  cases A with
  | mk ab at =>
      cases B with
      | mk bb bt =>
          dsimp at hb ht
          subst bb
          subst bt
          rfl

/-- Allocated bits for the one-hot blank plus q*g records, where each
    record has q+g+3 binary positions (move has a 3-bit one-hot code). -/
def tableBitCount (q g : Nat) : Nat :=
  g + q * g * (q + g + 3)

theorem tableBitCount_cubic (q g : Nat) :
    tableBitCount q g ≤ 2 * (q + g + 3) ^ 3 := by
  let B := q + g + 3
  have hq : q ≤ B := by dsimp [B]; omega
  have hg : g ≤ B := by dsimp [B]; omega
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hprod : q * g ≤ B * B := Nat.mul_le_mul hq hg
  have hterm : q * g * B ≤ B * B * B :=
    Nat.mul_le_mul_right B hprod
  have hsq : B ≤ B * B := by
    simpa [mul_one] using (Nat.mul_le_mul_left B hB)
  have hcub : B * B ≤ B * B * B := by
    simpa [mul_one] using (Nat.mul_le_mul_left (B * B) hB)
  have hB3 : B ≤ B * B * B := le_trans hsq hcub
  dsimp [tableBitCount]
  calc
    g + q * g * (q + g + 3) ≤
        B * B * B + B * B * B := by
          dsimp [B] at hterm hg hB3 ⊢
          omega
    _ = 2 * (q + g + 3) ^ 3 := by
          dsimp [B]
          ring

end PVNP.MachineCode
