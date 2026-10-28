import PVNP.TMHeadUniqueRight

/-!
# Unique compiled head after a bounded left-moving TM step

Global existence and uniqueness of the successor head marker under the
explicit left-boundary condition. Combined with the previously verified
right-moving case, this advances the moving-head simulation invariant,
but it is not yet full trace or complexity equivalence.
-/

namespace PVNP.TMHeadUniqueLeft

open PVNP.PartII PVNP.TMCellCompiler PVNP.TMGlobal
open PVNP.TMHeadMotion PVNP.TMHeadSupport

variable {Q Gamma : Type}

/-- A left-moving head cannot also generate a marker at the original
right-neighbor cell: the left-arrival condition is false there. -/
theorem right_neighbor_headless_on_left_move
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma) (i : Fin n)
    (hnext : i.val = c.headPos.val + 1)
    (hmove : (instruction T c).move = Move.left) :
    ((step (compile T) (encode c)) i).head = none := by
  have hcenter : i ≠ c.headPos := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  have hc : (encode c i).head = none := by
    simp [encode, hcenter]
  have hz : i.val ≠ 0 := by omega
  have hp : i.val - 1 < n := by omega
  have hleftidx : (⟨i.val - 1, hp⟩ : Fin n) = c.headPos := by
    apply Fin.ext
    omega
  have hl : (left (compile T) (encode c) i).head =
      some c.control := by
    simp [left, hz, sample, hp, hleftidx, encode]
  have hls : (left (compile T) (encode c) i).symbol =
      c.tape c.headPos := by
    simp [left, hz, sample, hp, hleftidx, encode]
  have hr : (right (compile T) (encode c) i).head = none := by
    by_cases hbound : i.val + 1 < n
    · have hne : (⟨i.val + 1, hbound⟩ : Fin n) ≠ c.headPos := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp at hv
        omega
      simp [right, sample, hbound, encode, hne]
    · simp [right, sample, hbound, compile]
  have hnot : (T.transition c.control
      (left (compile T) (encode c) i).symbol).move ≠ Move.right := by
    rw [hls]
    change (T.transition c.control (c.tape c.headPos)).move = Move.left at hmove
    rw [hmove]
    decide
  have hnone :
      (compiledRule T
        (left (compile T) (encode c) i)
        (encode c i)
        (right (compile T) (encode c) i)).head = none := by
    simp [compiledRule, hc, hl, hr, hnot]
  simpa only [step, compile] using hnone

/-- The only possible head-bearing output cell is the left destination
for a left-moving instruction that stays within the tape bounds. -/
theorem left_move_head_iff
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.left)
    (hbound : 0 < c.headPos.val) (i : Fin n) :
    ((step (compile T) (encode c)) i).head ≠ none ↔
      i.val + 1 = c.headPos.val := by
  constructor
  · intro hi
    rcases head_marker_support T c i hi with hcenter | hright | hleft
    · subst i
      have hn := moving_head_vacates_origin T c (by
        intro hh
        rw [hmove] at hh
        cases hh)
      exact False.elim (hi hn)
    · exact False.elim
        (hi (right_neighbor_headless_on_left_move T c i hright hmove))
    · exact hleft
  · intro hi
    have hv : i.val = c.headPos.val - 1 := by omega
    have heq : i = (⟨c.headPos.val - 1, by omega⟩ : Fin n) :=
      Fin.ext hv
    rw [heq, left_destination_has_head T c hmove hbound]
    simp

/-- A safe left-moving transition preserves exactly one global
head marker, with no spurious right-neighbor marker. -/
theorem left_move_preserves_exactly_one_head
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.left)
    (hbound : 0 < c.headPos.val) :
    ∃! i : Fin n, ((step (compile T) (encode c)) i).head ≠ none := by
  let dest : Fin n := ⟨c.headPos.val - 1, by omega⟩
  refine ⟨dest, ?_, ?_⟩
  · apply (left_move_head_iff T c hmove hbound dest).2
    dsimp [dest]
    omega
  · intro i hi
    apply Fin.ext
    have hv := (left_move_head_iff T c hmove hbound i).1 hi
    dsimp [dest]
    omega

end PVNP.TMHeadUniqueLeft
