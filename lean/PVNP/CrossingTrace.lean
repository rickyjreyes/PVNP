import PVNP.CrossingCapacity

/-!
# Phase VII: crossing traces extracted from the actual single-tape machine
Crossings are computed from Discrete.TM.next and its genuine execution.
No external crossing-sequence oracle or SAT hardness axiom is introduced.
-/

namespace PVNP.CrossingTrace

open PVNP.Discrete PVNP.CrossingCapacity PVNP.SplitSATCapacity

def CrossRight (M : TM) (cut : ℤ) (c : M.Cfg) : Prop :=
  c.head < cut ∧ cut ≤ (M.next c).head

def CrossLeft (M : TM) (cut : ℤ) (c : M.Cfg) : Prop :=
  cut ≤ c.head ∧ (M.next c).head < cut

instance (M : TM) (cut : ℤ) (c : M.Cfg) : Decidable (CrossRight M cut c) := by
  unfold CrossRight; infer_instance

instance (M : TM) (cut : ℤ) (c : M.Cfg) : Decidable (CrossLeft M cut c) := by
  unfold CrossLeft; infer_instance

/-- Post-transition control state and direction of a real crossing. -/
def event (M : TM) (cut : ℤ) (c : M.Cfg) : Option (M.Λ × Dir) :=
  if CrossRight M cut c then some ((M.next c).q, .R)
  else if CrossLeft M cut c then some ((M.next c).q, .L)
  else none

theorem event_right (M : TM) (cut : ℤ) (c : M.Cfg)
    (h : CrossRight M cut c) :
    event M cut c = some ((M.next c).q, .R) := by
  simp [event, h]

theorem event_left (M : TM) (cut : ℤ) (c : M.Cfg)
    (h : CrossLeft M cut c) :
    event M cut c = some ((M.next c).q, .L) := by
  have hn : ¬ CrossRight M cut c := by
    intro hr
    exact (not_lt_of_ge h.1) hr.1
  simp [event, hn, h]

theorem left_crossing_adjacent (M : TM) (cut : ℤ) (c : M.Cfg)
    (h : CrossLeft M cut c) :
    c.head = cut ∧ (M.next c).head = cut - 1 := by
  have hs := one_tape_head_speed M c
  rcases h with ⟨hbefore, hafter⟩
  omega

theorem right_crossing_adjacent (M : TM) (cut : ℤ) (c : M.Cfg)
    (h : CrossRight M cut c) :
    c.head = cut - 1 ∧ (M.next c).head = cut :=
  right_crossing_is_adjacent M c cut h.1 h.2

/-- Chronologically ordered crossing events in the first t steps. -/
def trace (M : TM) (cut : ℤ) : M.Cfg → Nat → List (M.Λ × Dir)
  | _, 0 => []
  | c, t + 1 =>
      match event M cut c with
      | none => trace M cut (M.next c) t
      | some v => v :: trace M cut (M.next c) t

/-- The event list is bounded by actual machine steps. -/
theorem trace_length_le (M : TM) (cut : ℤ) :
    ∀ (c : M.Cfg) (t : Nat), (trace M cut c t).length ≤ t := by
  intro c t
  induction t generalizing c with
  | zero => simp [trace]
  | succ t ih =>
      simp only [trace]
      cases h : event M cut c with
      | none =>
          simpa [h] using le_trans (ih (M.next c)) (Nat.le_succ t)
      | some v =>
          simpa [h] using Nat.succ_le_succ (ih (M.next c))

/-- Record events from an actual input configuration. -/
def inputTrace (M : TM) (cut : ℤ) (x : List Bool) (t : Nat) :
    List (M.Λ × Dir) :=
  trace M cut (M.init x) t

theorem inputTrace_length_le (M : TM) (cut : ℤ) (x : List Bool) (t : Nat) :
    (inputTrace M cut x t).length ≤ t :=
  trace_length_le M cut (M.init x) t

/-- Fixed-size record with an explicit termination symbol. -/
def record (M : TM) (cut : ℤ) (x : List Bool) (t : Nat) :
    CutRecord t (M.Λ × Dir) :=
  fun i => (inputTrace M cut x t)[i.val]?

/-- Split-SAT capacity of a genuine TM execution-derived record.
Rectangular splicing and correctness remain explicit assumptions. -/
theorem actual_trace_split_sat_capacity
    (M : TM) (cut : ℤ) {n t : Nat}
    (encode : Bits n → Bits n → List Bool)
    (accepts : CutRecord t (M.Λ × Dir) → Prop)
    (hsplice : ∀ a a' b b',
      record M cut (encode a b) t = record M cut (encode a' b') t →
      record M cut (encode a b') t = record M cut (encode a b) t ∧
      record M cut (encode a' b) t = record M cut (encode a b) t)
    (hcorrect : ∀ a b, accepts (record M cut (encode a b) t) ↔
      ∃ z : Bits n, splitThreeSat a b z) :
    2 ^ n ≤ (Fintype.card (M.Λ × Dir) + 1) ^ t := by
  exact bounded_crossing_record_capacity
    (fun a b => record M cut (encode a b) t) accepts hsplice hcorrect

end PVNP.CrossingTrace
