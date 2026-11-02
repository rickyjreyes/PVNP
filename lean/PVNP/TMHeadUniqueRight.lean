import PVNP.TMHeadSupport

/-!
# Unique compiled head after a bounded right-moving TM step

An exact one-step global head invariant for the right-moving subclass.
Unlike support-only results, this proves existence AND uniqueness of
the successor head under the explicit right-boundary safety condition.
It does not yet establish left-moving trace correspondence.
-/

namespace PVNP.TMHeadUniqueRight

open PVNP.PartII PVNP.TMCellCompiler PVNP.TMGlobal PVNP.TMHeadMotion PVNP.TMHeadSupport

variable {Q Gamma : Type}

/-- A rightward-moving head cannot also generate a marker at the
predecessor's left neighboring cell. -/
theorem left_neighbor_headless_on_right_move
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma) (i : Fin n)
    (hprev : i.val + 1 = c.headPos.val)
    (hmove : (instruction T c).move = Move.right) :
    ((step (compile T) (encode c)) i).head = none := by
  have hcenter : i ≠ c.headPos := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  have hc : (encode c i).head = none := by
    simp [encode, hcenter]
  have hp : i.val + 1 < n := by
    rw [hprev]
    exact c.headPos.isLt
  have hrightidx : (⟨i.val + 1, hp⟩ : Fin n) = c.headPos :=
    Fin.ext hprev
  have hr : (right (compile T) (encode c) i).head =
      some c.control := by
    simp [right, sample, hp, hrightidx, encode]
  have hrs : (right (compile T) (encode c) i).symbol =
      c.tape c.headPos := by
    simp [right, sample, hp, hrightidx, encode]
  have hl : (left (compile T) (encode c) i).head = none := by
    by_cases hz : i.val = 0
    · simp [left, hz, compile]
    · have hbound : i.val - 1 < n := by omega
      have hne : (⟨i.val - 1, hbound⟩ : Fin n) ≠ c.headPos := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp at hv
        omega
      simp [left, hz, sample, hbound, encode, hne]
  have hnot :
      (T.transition c.control
        (right (compile T) (encode c) i).symbol).move ≠ Move.left := by
    rw [hrs]
    change (T.transition c.control (c.tape c.headPos)).move = Move.right at hmove
    rw [hmove]
    decide
  have hnone :
      (compiledRule T
        (left (compile T) (encode c) i)
        (encode c i)
        (right (compile T) (encode c) i)).head = none := by
    simp [compiledRule, hc, hl, hr, hnot]
  simpa only [step, compile] using hnone

/-- Every and only right destination carries a successor head for
a safe right-moving compiled step; no spurious head is created. -/
theorem right_move_head_iff
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.right)
    (hbound : c.headPos.val + 1 < n) (i : Fin n) :
    ((step (compile T) (encode c)) i).head ≠ none ↔
      i.val = c.headPos.val + 1 := by
  constructor
  · intro hi
    rcases head_marker_support T c i hi with hcenter | hright | hleft
    · subst i
      have hn := moving_head_vacates_origin T c (by
        intro hh
        rw [hmove] at hh
        cases hh)
      exact False.elim (hi hn)
    · exact hright
    · exact False.elim
        (hi (left_neighbor_headless_on_right_move T c i hleft hmove))
  · intro hi
    have heq : i = (⟨c.headPos.val + 1, hbound⟩ : Fin n) :=
      Fin.ext hi
    rw [heq, right_destination_has_head T c hmove hbound]
    simp

/-- Complete global uniqueness of the compiled head after one
right-moving TM instruction when the destination is in bounds. -/
theorem right_move_preserves_exactly_one_head
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma)
    (hmove : (instruction T c).move = Move.right)
    (hbound : c.headPos.val + 1 < n) :
    ∃! i : Fin n, ((step (compile T) (encode c)) i).head ≠ none := by
  let dest : Fin n := ⟨c.headPos.val + 1, hbound⟩
  refine ⟨dest, ?_, ?_⟩
  · exact (right_move_head_iff T c hmove hbound dest).2 rfl
  · intro i hi
    apply Fin.ext
    exact (right_move_head_iff T c hmove hbound i).1 hi

end PVNP.TMHeadUniqueRight
