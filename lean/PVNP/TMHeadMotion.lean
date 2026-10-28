import PVNP.TMGlobal

/-!
# Actual head movement in compiled bounded-tape WCC steps

The Turing instruction is chosen from the independent TM configuration.
These lemmas verify that the compiled radius-one rule deposits the head
at the actual left/right neighbor under explicit interior conditions,
and vacates the original head position for non-stay transitions. These
are local-to-global one-step obligations, NOT a full trace or P/NP theorem.
-/

namespace PVNP.TMHeadMotion

open PVNP.PartII PVNP.TMCellCompiler PVNP.TMGlobal

variable {Q Gamma : Type}

theorem right_destination_has_head (T : TMTable Q Gamma)
    {n : Nat} (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.right)
    (hbound : c.headPos.val + 1 < n) :
    ((step (compile T) (encode c))
      ⟨c.headPos.val + 1, hbound⟩).head =
      some (instruction T c).next := by
  let dest : Fin n := ⟨c.headPos.val + 1, hbound⟩
  have hleft : left (compile T) (encode c) dest =
      encode c c.headPos := by
    simp [dest, left, sample, compile]
  have hne : dest ≠ c.headPos := by
    intro eq
    have hv := congrArg Fin.val eq
    dsimp [dest] at hv
    omega
  have hc : (encode c dest).head = none := by
    simp [encode, hne]
  have hl : (left (compile T) (encode c) dest).head =
      some c.control := by simp [hleft, encode]
  have hm : (T.transition c.control
      (left (compile T) (encode c) dest).symbol).move =
      Move.right := by
    simpa [hleft, encode, instruction] using hmove
  have harrival := right_move_arrives T c.control
    (left (compile T) (encode c) dest)
    (encode c dest)
    (right (compile T) (encode c) dest)
    hc hl hm
  change (compiledRule T
    (left (compile T) (encode c) dest)
    (encode c dest)
    (right (compile T) (encode c) dest)).head =
      some (instruction T c).next
  simpa [hleft, encode, instruction] using harrival

theorem left_destination_has_head (T : TMTable Q Gamma)
    {n : Nat} (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.left)
    (hbound : 0 < c.headPos.val) :
    ((step (compile T) (encode c))
      ⟨c.headPos.val - 1, by omega⟩).head =
      some (instruction T c).next := by
  let dest : Fin n := ⟨c.headPos.val - 1, by omega⟩
  have hright : right (compile T) (encode c) dest =
      encode c c.headPos := by
    have hj : c.headPos.val - 1 + 1 = c.headPos.val := by omega
    simp [dest, right, sample, compile, hj]
  have hne : dest ≠ c.headPos := by
    intro eq
    have hv := congrArg Fin.val eq
    dsimp [dest] at hv
    omega
  have hc : (encode c dest).head = none := by
    simp [encode, hne]
  have hleft_none :
      (left (compile T) (encode c) dest).head = none := by
    by_cases hz : dest.val = 0
    · simp [left, hz, compile]
    · have hprev : dest.val - 1 < n := by omega
      have hneprev : (⟨dest.val - 1, hprev⟩ : Fin n) ≠
          c.headPos := by
        intro eq
        have hv := congrArg Fin.val eq
        dsimp [dest] at hv
        omega
      simp [left, hz, sample, hprev, encode, hneprev]
  have hr : (right (compile T) (encode c) dest).head =
      some c.control := by simp [hright, encode]
  have hm : (T.transition c.control
      (right (compile T) (encode c) dest).symbol).move =
      Move.left := by
    simpa [hright, encode, instruction] using hmove
  have harrival := left_move_arrives T c.control
    (left (compile T) (encode c) dest)
    (encode c dest)
    (right (compile T) (encode c) dest)
    hc hleft_none hr hm
  change (compiledRule T
    (left (compile T) (encode c) dest)
    (encode c dest)
    (right (compile T) (encode c) dest)).head =
      some (instruction T c).next
  simpa [hright, encode, instruction] using harrival

/-- Every non-stationary transition clears the original head site. -/
theorem moving_head_vacates_origin (T : TMTable Q Gamma)
    {n : Nat} (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move ≠ Move.stay) :
    ((step (compile T) (encode c)) c.headPos).head = none := by
  simp [step, compile, encode, compiledRule, instruction]
  all_goals simpa [instruction] using hmove

/-- Every stationary transition keeps the head at the same site. -/
theorem stationary_head_retained (T : TMTable Q Gamma)
    {n : Nat} (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.stay) :
    ((step (compile T) (encode c)) c.headPos).head =
      some (instruction T c).next := by
  simp [step, compile, encode, compiledRule, instruction, hmove]

end PVNP.TMHeadMotion
