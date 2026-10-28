import PVNP.TMGlobal

/-!
# An honest complete TM-to-WCC trajectory theorem for stationary-head machines

This restricted class has finite symbolic tape and arbitrary control/symbol
transition tables, but every instruction stays at the same head position.
It is a useful full-trajectory correctness theorem for the actual compiled
radius-one WCC local rule. It is NOT a universal Turing simulation theorem:
left/right head motion, finite boundary safety, halting, description coding,
and TM instruction costs are still unproved.
-/

namespace PVNP.TMStayTrace

open PVNP.PartII PVNP.TMCellCompiler PVNP.TMGlobal

variable {Q Gamma : Type}

/-- A machine whose head does not move. -/
def Stationary (T : TMTable Q Gamma) : Prop :=
  ∀ q a, (T.transition q a).move = Move.stay

/-- An independent Turing step for the stationary subclass. -/
def tmStayStep {n : Nat} (T : TMTable Q Gamma)
    (c : TMConfiguration n Q Gamma) : TMConfiguration n Q Gamma :=
  { tape := writeTape T c
    headPos := c.headPos
    control := (instruction T c).next }

/-- Without left/right moves, a headless WCC cell stays headless, even
    when either or both neighbors contain a head. -/
theorem headless_noarrival (T : TMTable Q Gamma)
    (hs : Stationary T) (l c r : TapeCell Q Gamma)
    (hc : c.head = none) :
    (compiledRule T l c r).head = none := by
  cases hl : l.head with
  | none =>
      cases hr : r.head with
      | none => simp [compiledRule, hc, hl, hr]
      | some q => simp [compiledRule, hc, hl, hr, hs q r.symbol]
  | some q =>
      cases hr : r.head with
      | none => simp [compiledRule, hc, hl, hr, hs q l.symbol]
      | some q' =>
          simp [compiledRule, hc, hl, hr,
                hs q l.symbol, hs q' r.symbol]

theorem stayStep_encoded (T : TMTable Q Gamma)
    (hs : Stationary T) {n : Nat}
    (c : TMConfiguration n Q Gamma) :
    step (compile T) (encode c) = encode (tmStayStep T c) := by
  funext i
  apply TapeCell.ext
  · simpa [encode, tmStayStep] using compiled_step_tape T c i
  · by_cases hi : i = c.headPos
    · subst i
      simp [step, compile, encode, compiledRule,
            tmStayStep, instruction]
      all_goals exact hs c.control (c.tape c.headPos)
    · have hc : (encode c i).head = none := by
        simp [encode, hi]
      have hno := headless_noarrival T hs
        (left (compile T) (encode c) i)
        (encode c i)
        (right (compile T) (encode c) i) hc
      simpa [step, compile, encode, tmStayStep, hi] using hno

/-- All finite execution traces commute with the actual compiled local
    update. This is universal over stationary transition tables only. -/
theorem stay_trace_correct (T : TMTable Q Gamma)
    (hs : Stationary T) {n : Nat}
    (c : TMConfiguration n Q Gamma) (t : Nat) :
    iterate (step (compile T)) t (encode c) =
      encode (iterate (tmStayStep T) t c) := by
  exact (encode_iterate (tmStayStep T) (step (compile T))
    encode (fun cfg => (stayStep_encoded T hs cfg).symm) t c).symm

/-- The unique encoded head exists at every simulated step for the
    stationary subclass, directly from the trajectory correspondence. -/
theorem stay_trace_head_exists (T : TMTable Q Gamma)
    (hs : Stationary T) {n : Nat}
    (c : TMConfiguration n Q Gamma) (t : Nat) :
    ∃ i : Fin n,
      ((iterate (step (compile T)) t (encode c)) i).head =
        some (iterate (tmStayStep T) t c).control := by
  rw [stay_trace_correct T hs c t]
  exact encode_head_exists _

end PVNP.TMStayTrace
