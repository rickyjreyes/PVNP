import PVNP.TMHeadUniqueLeft

/-!
# Exact moving-head one-step TM ↔ compiled WCC simulation

For safe bounded-tape transitions moving left or right, the entire
compiled synchronous update equals the independent TM successor
configuration encoded as head-marker cells. This proves much more than
head existence: symbol writes, exact head position and new control agree
at every cell. The full arbitrary trace, boundary policy, uniform
description compiler and polynomial interpreter costs remain separate.
-/

namespace PVNP.TMHeadStep

open PVNP.PartII PVNP.TMCellCompiler PVNP.TMGlobal
open PVNP.TMHeadMotion PVNP.TMHeadUniqueRight PVNP.TMHeadUniqueLeft

variable {Q Gamma : Type}

/-- The independent TM state after writing and moving to a given
in-bounds successor location. -/
def tmNextAt (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma) (destination : Fin n) :
    TMConfiguration n Q Gamma :=
  { tape := writeTape T c
    headPos := destination
    control := (instruction T c).next }

/-- Exact whole-configuration correspondence for any safe right step. -/
theorem right_step_encoded
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.right)
    (hbound : c.headPos.val + 1 < n) :
    step (compile T) (encode c) =
      encode (tmNextAt T c ⟨c.headPos.val + 1, hbound⟩) := by
  funext i
  apply TapeCell.ext
  · simpa [encode, tmNextAt] using compiled_step_tape T c i
  · let dest : Fin n := ⟨c.headPos.val + 1, hbound⟩
    by_cases hi : i = dest
    · subst i
      have hhead := right_destination_has_head T c hmove hbound
      simpa [dest, encode, tmNextAt] using hhead
    · have hnone : ((step (compile T) (encode c)) i).head = none := by
        by_contra hnot
        have hv := (right_move_head_iff T c hmove hbound i).1 hnot
        exact hi (Fin.ext hv)
      simpa [dest, encode, tmNextAt, hi] using hnone

/-- Exact whole-configuration correspondence for any safe left step. -/
theorem left_step_encoded
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.left)
    (hbound : 0 < c.headPos.val) :
    step (compile T) (encode c) =
      encode (tmNextAt T c ⟨c.headPos.val - 1, by omega⟩) := by
  funext i
  apply TapeCell.ext
  · simpa [encode, tmNextAt] using compiled_step_tape T c i
  · let dest : Fin n := ⟨c.headPos.val - 1, by omega⟩
    by_cases hi : i = dest
    · subst i
      have hhead := left_destination_has_head T c hmove hbound
      simpa [dest, encode, tmNextAt] using hhead
    · have hnone : ((step (compile T) (encode c)) i).head = none := by
        by_contra hnot
        have hv := (left_move_head_iff T c hmove hbound i).1 hnot
        have heq : i = dest := by
          apply Fin.ext
          dsimp [dest]
          omega
        exact hi heq
      simpa [dest, encode, tmNextAt, hi] using hnone

end PVNP.TMHeadStep
