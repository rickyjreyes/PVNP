import PVNP.DiscreteMachines

/-!
# Ordinary TM → discrete WCC, exact real-time simulation (issue #11, direction 1)

Every ordinary single-tape TM `M` is compiled to a radius-one finite-alphabet
quiescent WCC `M.toWCC` with cell alphabet `M.Γ × Option M.Λ` (tape symbol plus
an optional head/state marker).

Main results (all cases: left, right, stay moves and halting):

* `TM.toWCC_step_encode`: one synchronous WCC update of the encoding of *any*
  configuration equals the encoding of the TM successor (a halted
  configuration is a fixed point on both sides).
* `TM.toWCC_run_encode`: the same for every finite number of steps.
* `TM.toWCC_decides`: if `M` decides `L` in time `T`, then `M.toWCC` decides `L`
  in exactly the same time `T` (overhead factor 1, no space overhead).

The tape is bi-infinite, so no boundary case arises; a unique head marker is
built into the encoding and therefore preserved by every step.
-/

namespace PVNP.Discrete

namespace TM

variable (M : TM)

/-- State delivered to the cell on the right by a head moving right. -/
def arriveFromLeft (l : M.Γ × Option M.Λ) : Option M.Λ :=
  match l.2 with
  | none => none
  | some q =>
    match M.δ q l.1 with
    | some (q', _, Dir.R) => some q'
    | _ => none

/-- State delivered to the cell on the left by a head moving left. -/
def arriveFromRight (r : M.Γ × Option M.Λ) : Option M.Λ :=
  match r.2 with
  | none => none
  | some q =>
    match M.δ q r.1 with
    | some (q', _, Dir.L) => some q'
    | _ => none

/-- The compiled radius-one local rule. -/
def cellRule (l c r : M.Γ × Option M.Λ) : M.Γ × Option M.Λ :=
  match c.2 with
  | some q =>
    match M.δ q c.1 with
    | none => c
    | some (q', a, d) => if d = Dir.S then (a, some q') else (a, none)
  | none =>
    match M.arriveFromLeft l with
    | some q' => (c.1, some q')
    | none =>
      match M.arriveFromRight r with
      | some q' => (c.1, some q')
      | none => c

/-- Accepting cells: those carrying the head in an accepting state. -/
def cellAcc (c : M.Γ × Option M.Λ) : Bool :=
  match c.2 with
  | some q => M.acc q
  | none => false

/-- Rejecting cells: those carrying the head in a rejecting state. -/
def cellRej (c : M.Γ × Option M.Λ) : Bool :=
  match c.2 with
  | some q => M.rej q
  | none => false

/-- The compiled discrete WCC. -/
def toWCC : WCC where
  S := M.Γ × Option M.Λ
  blank := (M.blank, none)
  rule := M.cellRule
  quiescent := by simp [cellRule, arriveFromLeft, arriveFromRight]
  inp b := (M.inp b, none)
  origin
    | none => (M.blank, some M.start)
    | some b => (M.inp b, some M.start)
  acc := M.cellAcc
  rej := M.cellRej

/-- Encoding of a TM configuration as a WCC configuration: exactly one cell
(the head cell) carries the control state. -/
def encode (c : M.Cfg) : ℤ → M.Γ × Option M.Λ :=
  fun i => (c.tape i, if i = c.head then some c.q else none)

theorem encode_head_unique (c : M.Cfg) (i : ℤ) :
    (M.encode c i).2.isSome ↔ i = c.head := by
  by_cases h : i = c.head <;> simp [encode, h]

theorem encode_injective : Function.Injective M.encode := by
  intro c d h
  have hhead : c.head = d.head := by
    have := (M.encode_head_unique d c.head).1
    have h2 : (M.encode c c.head).2.isSome := (M.encode_head_unique c c.head).2 rfl
    rw [h] at h2
    exact this h2
  have hq : c.q = d.q := by
    have := congrFun h c.head
    simp [encode, hhead] at this
    exact this.2
  have htape : c.tape = d.tape := funext fun i => by
    have := congrFun h i
    simp [encode] at this
    exact this.1
  cases c; cases d; simp_all

/-- Exact one-step correspondence for every configuration and every case of
the transition function (halt, left, stay, right). -/
theorem toWCC_step_encode (c : M.Cfg) :
    M.toWCC.step (M.encode c) = M.encode (M.next c) := by
  funext i
  simp only [WCC.step, toWCC]
  rcases hδ : M.δ c.q (c.tape c.head) with _ | ⟨q', a, d⟩
  · -- halted: everything is fixed
    have hn : M.next c = c := by simp [next, step, hδ]
    rw [hn]
    by_cases hi : i = c.head
    · subst hi
      simp [cellRule, encode, hδ]
    · have hl : M.arriveFromLeft (M.encode c (i - 1)) = none := by
        by_cases h1 : i - 1 = c.head
        · rw [h1]; simp [arriveFromLeft, encode, hδ]
        · simp [arriveFromLeft, encode, h1]
      have hr : M.arriveFromRight (M.encode c (i + 1)) = none := by
        by_cases h1 : i + 1 = c.head
        · rw [h1]; simp [arriveFromRight, encode, hδ]
        · simp [arriveFromRight, encode, h1]
      have hc : M.encode c i = (c.tape i, none) := by simp [encode, hi]
      simp only [cellRule, hc, hl, hr]
  · have hn : M.next c = ⟨q', Function.update c.tape c.head a, c.head + d.shift⟩ := by
      simp [next, step, hδ]
    rw [hn]
    by_cases hi : i = c.head
    · subst hi
      cases d <;> simp [cellRule, encode, hδ, Dir.shift]
    · have htape : Function.update c.tape c.head a i = c.tape i := by
        simp [Function.update, hi]
      have hl : M.arriveFromLeft (M.encode c (i - 1)) =
          if i - 1 = c.head ∧ d = Dir.R then some q' else none := by
        by_cases h1 : i - 1 = c.head
        · rw [h1]; cases d <;> simp [arriveFromLeft, encode, hδ]
        · simp [arriveFromLeft, encode, h1]
      have hr : M.arriveFromRight (M.encode c (i + 1)) =
          if i + 1 = c.head ∧ d = Dir.L then some q' else none := by
        by_cases h1 : i + 1 = c.head
        · rw [h1]; cases d <;> simp [arriveFromRight, encode, hδ]
        · simp [arriveFromRight, encode, h1]
      have hc : M.encode c i = (c.tape i, none) := by simp [encode, hi]
      simp only [cellRule, hc, hl, hr]
      simp only [encode, htape]
      cases d <;> simp only [Dir.shift] <;>
        by_cases h1 : i - 1 = c.head <;> by_cases h2 : i + 1 = c.head <;>
        simp_all <;> omega

/-- Exact correspondence for every finite execution. -/
theorem toWCC_run_encode (c : M.Cfg) (t : ℕ) :
    M.toWCC.run (M.encode c) t = M.encode (M.run c t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [WCC.run_succ, ih, toWCC_step_encode, run_succ]

theorem toWCC_init (x : List Bool) : M.toWCC.init x = M.encode (M.init x) := by
  funext i
  simp only [WCC.init, encode, init, inputTape]
  by_cases h0 : i = 0
  · subst h0
    cases x with
    | nil => simp [toWCC]
    | cons b x => simp [toWCC]
  · have hpos : (0 < i ∧ i < (x.length : ℤ)) ↔ (0 ≤ i ∧ i < (x.length : ℤ)) := by
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨le_of_lt h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm h0), h2⟩
    by_cases hr : 0 ≤ i ∧ i < (x.length : ℤ)
    · simp [h0, hr, hpos.2 hr, toWCC]
    · have : ¬ (0 < i ∧ i < (x.length : ℤ)) := fun h => hr (hpos.1 h)
      simp [h0, hr, this, toWCC]

theorem toWCC_outCfg (c : M.Cfg) : M.toWCC.outCfg (M.encode c) = M.ans c := by
  have hA : (∃ i, M.toWCC.acc (M.encode c i) = true) ↔ M.acc c.q = true := by
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i = c.head
      · simpa [toWCC, cellAcc, encode, h] using hi
      · simp [toWCC, cellAcc, encode, h] at hi
    · intro h; exact ⟨c.head, by simpa [toWCC, cellAcc, encode] using h⟩
  have hR : (∃ i, M.toWCC.rej (M.encode c i) = true) ↔ M.rej c.q = true := by
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i = c.head
      · simpa [toWCC, cellRej, encode, h] using hi
      · simp [toWCC, cellRej, encode, h] at hi
    · intro h; exact ⟨c.head, by simpa [toWCC, cellRej, encode] using h⟩
  unfold WCC.outCfg ans
  congr 1
  · exact Bool.eq_iff_iff.2 (by simpa using hA)
  · exact Bool.eq_iff_iff.2 (by simpa using hR)

/-- The output streams coincide step by step. -/
theorem toWCC_out (x : List Bool) : M.toWCC.out x = M.out x := by
  funext s
  simp [WCC.out, out, toWCC_init, toWCC_run_encode, toWCC_outCfg]

/-- Real-time simulation: same language, same time bound. -/
theorem toWCC_decides {L : Set (List Bool)} {T : ℕ → ℕ} (h : M.Decides L T) :
    M.toWCC.Decides L T := by
  intro x
  rw [toWCC_out]
  exact h x

end TM

/-- `P_TM ⊆ P_WCC`, with the identical polynomial. -/
theorem P_TM_subset_P_WCC : P_TM ⊆ P_WCC := by
  rintro L ⟨M, p, h⟩
  exact ⟨M.toWCC, p, M.toWCC_decides h⟩

end PVNP.Discrete
