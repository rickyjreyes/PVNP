import PVNP.CrossingDiagonal

/-!
# Phase VIII: the complete crossing-sequence splicing theorem for `Discrete.TM`

This is the global (Hennie-type) cut-and-paste theorem for the repository's ordinary
deterministic single-tape machine `Discrete.TM`, derived from its transition function
`TM.next` alone.  No rectangularity of crossing records is assumed.

Fix a cut `κ`: cells `i < κ` form the left half, cells `i ≥ κ` the right half.  The crossing
trace `CrossingTrace.trace M κ c t` lists, in chronological order, the post-transition control
state and the direction of every step among the first `t` that moves the head across the cut.

**Theorem (`splice_core`).**  Let `A` (the *active* run) and `P` (the *passive* run) start on the
same side `s` of the cut, with equal crossing traces over windows `ta`, `tp`, and with no
answer displayed before the end of the windows.  Run the machine from the *mixed*
configuration whose control state and head are those of `A` and whose tape is `A`'s tape on
side `s` and `P`'s tape on the other side.  Then, within `ta + tp` steps, the mixed run
displays no answer before some time `tz`, and at `tz` it displays the final answer of `A` if
the common trace has even length and the final answer of `P` if it has odd length.

The proof is an induction over the common list of crossing events.  At every crossing the
roles of the two runs are exchanged; the invariant keeps track of

* the side currently scanned (`OnSide`),
* control-state continuity (the post-crossing states agree because the traces agree),
* the head position (both crossings land on the cell adjacent to the cut),
* tape modifications on both halves (the passive half is frozen while the head is away:
  `run_offSide_tape`),
* first-answer semantics and variable segment lengths.

**Theorem (`hennie`).**  For inputs `u ++ v` and `u' ++ v'` with `|u| = |u'| ≥ 1` and the cut at
`κ = |u|`, equal crossing traces up to the respective first answers force the input `u ++ v'` to
display its first answer within `sx + sy` steps, equal to the answer of the side on which the
last segment runs.  `splice_mem` is the decision-language corollary: if both inputs belong to
a language decided by `M`, so does `u ++ v'`.
-/

namespace PVNP.CrossingHennie

open PVNP.Discrete PVNP.CrossingTrace PVNP.CrossingSplice PVNP.CrossingCapacity

section Splice

variable (M : TM) (κ : ℤ)

/-- Side `true` is the left half `h < κ`; side `false` is the right half `κ ≤ h`. -/
def OnSide (s : Bool) (h : ℤ) : Prop := if s then h < κ else κ ≤ h

/-- The mixed tape: the active tape `act` on side `s`, the passive tape `pas` elsewhere. -/
def mixS {A : Type*} (s : Bool) (act pas : ℤ → A) : ℤ → A :=
  if s then mixTape κ act pas else mixTape κ pas act

variable {M κ}

theorem onSide_not (s : Bool) (h : ℤ) : OnSide κ (!s) h ↔ ¬ OnSide κ s h := by
  cases s <;> simp [OnSide]

theorem mixS_on {A : Type*} {s : Bool} (act pas : ℤ → A) {i : ℤ} (hi : OnSide κ s i) :
    mixS κ s act pas i = act i := by
  cases s
  · simp only [OnSide, Bool.false_eq_true, ↓reduceIte] at hi
    simp only [mixS, Bool.false_eq_true, ↓reduceIte]
    exact mixTape_right κ pas act i hi
  · simp only [OnSide, ↓reduceIte] at hi
    simp only [mixS, ↓reduceIte]
    exact mixTape_left κ act pas i hi

theorem mixS_off {A : Type*} {s : Bool} (act pas : ℤ → A) {i : ℤ} (hi : ¬ OnSide κ s i) :
    mixS κ s act pas i = pas i := by
  cases s
  · simp only [OnSide, Bool.false_eq_true, ↓reduceIte, not_le] at hi
    simp only [mixS, Bool.false_eq_true, ↓reduceIte]
    exact mixTape_left κ pas act i hi
  · simp only [OnSide, ↓reduceIte, not_lt] at hi
    simp only [mixS, ↓reduceIte]
    exact mixTape_right κ act pas i hi

/-- Run splicing on either side. -/
theorem run_splice_side (s : Bool) (c : M.Cfg) (p : ℤ → M.Γ) (t : ℕ)
    (hside : ∀ r < t, OnSide κ s (M.run c r).head) :
    M.run {c with tape := mixS κ s c.tape p} t =
      {M.run c t with tape := mixS κ s (M.run c t).tape p} := by
  cases s
  · simp only [mixS, Bool.false_eq_true, ↓reduceIte]
    exact run_splice_right M κ c p t (fun r hr => by
      have := hside r hr; simpa [OnSide] using this)
  · simp only [mixS, ↓reduceIte]
    exact run_splice_left M κ c p t (fun r hr => by
      have := hside r hr; simpa [OnSide] using this)

theorem next_tape_ne (c : M.Cfg) {i : ℤ} (hi : i ≠ c.head) : (M.next c).tape i = c.tape i := by
  unfold TM.next TM.step
  cases h : M.δ c.q (c.tape c.head) with
  | none => simp
  | some instr =>
    simp only [Option.map_some, Option.getD_some]
    exact Function.update_of_ne hi _ _

/-- Cells on the other side of the cut are frozen while the head stays on side `s`. -/
theorem run_offSide_tape (s : Bool) (c : M.Cfg) :
    ∀ t : ℕ, (∀ r < t, OnSide κ s (M.run c r).head) →
      ∀ i, ¬ OnSide κ s i → (M.run c t).tape i = c.tape i := by
  intro t
  induction t with
  | zero => intro _ i _; rfl
  | succ t ih =>
    intro hside i hi
    rw [M.run_succ]
    have hne : i ≠ (M.run c t).head := by
      intro h
      exact hi (h ▸ hside t (by omega))
    rw [next_tape_ne _ hne]
    exact ih (fun r hr => hside r (by omega)) i hi

theorem ans_with_tape (c : M.Cfg) (tp : ℤ → M.Γ) : M.ans {c with tape := tp} = M.ans c := rfl

theorem run_succ_left (c : M.Cfg) (r : ℕ) : M.run c (r + 1) = M.run (M.next c) r := by
  simp only [TM.run, Function.iterate_succ_apply]

/-! ### Single steps and crossing events -/

theorem stay_of_no_event {s : Bool} {c : M.Cfg} (hc : OnSide κ s c.head)
    (he : event M κ c = none) : OnSide κ s (M.next c).head := by
  cases s
  · simp only [OnSide, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    by_contra hlt
    push_neg at hlt
    have hl : CrossLeft M κ c := ⟨hc, hlt⟩
    rw [event_left M κ c hl] at he
    exact Option.noConfusion he
  · simp only [OnSide, ↓reduceIte] at hc ⊢
    by_contra hge
    push_neg at hge
    have hr : CrossRight M κ c := ⟨hc, hge⟩
    rw [event_right M κ c hr] at he
    exact Option.noConfusion he

/-- A crossing from side `s` lands on the cell adjacent to the cut, with the recorded state. -/
theorem cross_of_event {s : Bool} {c : M.Cfg} {e : M.Λ × Dir} (hc : OnSide κ s c.head)
    (he : event M κ c = some e) :
    (M.next c).head = (if s then κ else κ - 1) ∧ (M.next c).q = e.1 := by
  cases s
  · simp only [OnSide, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    have hnr : ¬ CrossRight M κ c := fun h => (not_lt_of_ge hc) h.1
    unfold event at he
    rw [if_neg hnr] at he
    by_cases hl : CrossLeft M κ c
    · rw [if_pos hl] at he
      cases he
      exact ⟨(left_crossing_adjacent M κ c hl).2, rfl⟩
    · rw [if_neg hl] at he
      exact Option.noConfusion he
  · simp only [OnSide, ↓reduceIte] at hc ⊢
    unfold event at he
    by_cases hr : CrossRight M κ c
    · rw [if_pos hr] at he
      cases he
      exact ⟨(right_crossing_adjacent M κ c hr).2, rfl⟩
    · rw [if_neg hr] at he
      have hnl : ¬ CrossLeft M κ c := fun h => (not_lt_of_ge h.1) hc
      rw [if_neg hnl] at he
      exact Option.noConfusion he

theorem onSide_after_cross (s : Bool) :
    OnSide κ (!s) (if s then κ else κ - 1) := by
  cases s <;> simp [OnSide]

/-- No crossing events in a window keeps the head on its side. -/
theorem stays_side {s : Bool} {c : M.Cfg} (hc : OnSide κ s c.head) {k : ℕ}
    (hno : ∀ r < k, event M κ (M.run c r) = none) : ∀ r ≤ k, OnSide κ s (M.run c r).head := by
  intro r
  induction r with
  | zero => intro _; exact hc
  | succ r ih =>
    intro hr
    rw [M.run_succ]
    exact stay_of_no_event (ih (by omega)) (hno r (by omega))

/-! ### Decomposing a crossing trace -/

theorem trace_nil_events {c : M.Cfg} {t : ℕ} (h : trace M κ c t = []) :
    ∀ r < t, event M κ (M.run c r) = none := by
  induction t generalizing c with
  | zero => intro r hr; omega
  | succ t ih =>
    intro r hr
    cases he : event M κ c with
    | some v =>
      simp only [trace, he] at h
      exact List.noConfusion h
    | none =>
      simp only [trace, he] at h
      rcases r with _ | r
      · exact he
      · rw [run_succ_left]
        exact ih h r (by omega)

theorem trace_cons_events {c : M.Cfg} {t : ℕ} {e : M.Λ × Dir} {rest : List (M.Λ × Dir)}
    (h : trace M κ c t = e :: rest) :
    ∃ s < t, (∀ r < s, event M κ (M.run c r) = none) ∧ event M κ (M.run c s) = some e ∧
      trace M κ (M.run c (s + 1)) (t - (s + 1)) = rest := by
  induction t generalizing c with
  | zero => simp [trace] at h
  | succ t ih =>
    cases he : event M κ c with
    | some v =>
      simp only [trace, he, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, by omega, fun r hr => by omega, he, ?_⟩
      simp only [zero_add, Nat.add_sub_cancel]
      rfl
    | none =>
      simp only [trace, he] at h
      obtain ⟨s, hs, hno, hev, htr⟩ := ih h
      refine ⟨s + 1, by omega, fun r hr => ?_, ?_, ?_⟩
      · rcases r with _ | r
        · exact he
        · rw [run_succ_left]; exact hno r (by omega)
      · rw [run_succ_left]; exact hev
      · rw [run_succ_left, show t + 1 - (s + 1 + 1) = t - (s + 1) by omega]; exact htr

/-! ### The splicing theorem -/

/-- **The complete alternating crossing-sequence splicing theorem.** -/
theorem splice_core : ∀ (rest : List (M.Λ × Dir)) (s : Bool) (A P : M.Cfg) (ta tp : ℕ),
    OnSide κ s A.head → OnSide κ s P.head →
    trace M κ A ta = rest → trace M κ P tp = rest →
    (∀ r < ta, M.ans (M.run A r) = none) → (∀ r < tp, M.ans (M.run P r) = none) →
    ∃ tz ≤ ta + tp,
      (∀ r < tz, M.ans (M.run {A with tape := mixS κ s A.tape P.tape} r) = none) ∧
      M.ans (M.run {A with tape := mixS κ s A.tape P.tape} tz) =
        (if Even rest.length then M.ans (M.run A ta) else M.ans (M.run P tp)) := by
  intro rest
  induction rest with
  | nil =>
    intro s A P ta tp hA _ htA _ hansA _
    have hside := stays_side hA (trace_nil_events htA)
    refine ⟨ta, by omega, fun r hr => ?_, ?_⟩
    · rw [run_splice_side s A P.tape r (fun r' hr' => hside r' (by omega)), ans_with_tape]
      exact hansA r hr
    · rw [run_splice_side s A P.tape ta (fun r' hr' => hside r' hr'.le), ans_with_tape]
      simp
  | cons e rest ih =>
    intro s A P ta tp hA hP htA htP hansA hansP
    obtain ⟨sA, hsA, hnoA, hevA, htrA⟩ := trace_cons_events htA
    obtain ⟨sP, hsP, hnoP, hevP, htrP⟩ := trace_cons_events htP
    have hsideA := stays_side hA hnoA
    have hsideP := stays_side hP hnoP
    obtain ⟨hhA, hqA⟩ := cross_of_event (hsideA sA le_rfl) hevA
    obtain ⟨hhP, hqP⟩ := cross_of_event (hsideP sP le_rfl) hevP
    rw [← M.run_succ] at hhA hqA hhP hqP
    set A' := M.run P (sP + 1) with hA'def
    set P' := M.run A (sA + 1) with hP'def
    have hA' : OnSide κ (!s) A'.head := by rw [hhP]; exact onSide_after_cross s
    have hP' : OnSide κ (!s) P'.head := by rw [hhA]; exact onSide_after_cross s
    -- the mixed run after the first segment
    have hz1 : M.run {A with tape := mixS κ s A.tape P.tape} (sA + 1) =
        {A' with tape := mixS κ (!s) A'.tape P'.tape} := by
      rw [run_splice_side s A P.tape (sA + 1) (fun r hr => hsideA r (by omega))]
      have hfrozen := run_offSide_tape s P (sP + 1) (fun r hr => hsideP r (by omega))
      cases hP'eq : P' with
      | mk q₁ T₁ h₁ =>
      cases hA'eq : A' with
      | mk q₂ T₂ h₂ =>
      have hq : q₁ = q₂ := by
        have h1 : P'.q = e.1 := hqA
        have h2 : A'.q = e.1 := hqP
        rw [hP'eq] at h1; rw [hA'eq] at h2
        simp only at h1 h2
        rw [h1, h2]
      have hh : h₁ = h₂ := by
        have h1 : P'.head = (if s then κ else κ - 1) := hhA
        have h2 : A'.head = (if s then κ else κ - 1) := hhP
        rw [hP'eq] at h1; rw [hA'eq] at h2
        simp only at h1 h2
        rw [h1, h2]
      have hT : mixS κ s T₁ P.tape = mixS κ (!s) T₂ T₁ := by
        funext i
        by_cases hi : OnSide κ s i
        · rw [mixS_on _ _ hi, mixS_off _ _ (by rw [onSide_not, not_not]; exact hi)]
        · rw [mixS_off _ _ hi, mixS_on _ _ (by rw [onSide_not]; exact hi)]
          have := hfrozen i hi
          rw [← hA'def, hA'eq] at this
          exact this.symm
      have e1 : M.run A (sA + 1) = ⟨q₁, T₁, h₁⟩ := by rw [← hP'def]; exact hP'eq
      rw [e1]
      simp only [hq, hh, hT]
    -- the induction hypothesis on the remaining crossings, with the roles exchanged
    obtain ⟨tz', htz', hnone', hans'⟩ := ih (!s) A' P' (tp - (sP + 1)) (ta - (sA + 1)) hA' hP'
      htrP htrA
      (fun r hr => by rw [hA'def, ← TM.run_add]; exact hansP _ (by omega))
      (fun r hr => by rw [hP'def, ← TM.run_add]; exact hansA _ (by omega))
    refine ⟨sA + 1 + tz', by omega, fun r hr => ?_, ?_⟩
    · by_cases hr' : r < sA + 1
      · rw [run_splice_side s A P.tape r (fun r' hr'' => hsideA r' (by omega)), ans_with_tape]
        exact hansA r (by omega)
      · obtain ⟨r', rfl⟩ : ∃ r', r = sA + 1 + r' := ⟨r - (sA + 1), by omega⟩
        rw [TM.run_add, hz1]
        exact hnone' r' (by omega)
    · rw [TM.run_add, hz1, hans']
      have eA : M.run A' (tp - (sP + 1)) = M.run P tp := by
        rw [hA'def, ← TM.run_add, show sP + 1 + (tp - (sP + 1)) = tp by omega]
      have eP : M.run P' (ta - (sA + 1)) = M.run A ta := by
        rw [hP'def, ← TM.run_add, show sA + 1 + (ta - (sA + 1)) = ta by omega]
      rw [eA, eP]
      simp only [List.length_cons, Nat.even_add_one]
      by_cases hev : Even rest.length
      · simp [hev]
      · simp [hev]

end Splice

/-! ### Inputs -/

section Inputs

variable (M : TM)

theorem inputTape_append_mix (u v u' v' : List Bool) (hu : u'.length = u.length) :
    M.inputTape (u ++ v') =
      mixTape (u.length : ℤ) (M.inputTape (u ++ v)) (M.inputTape (u' ++ v')) := by
  funext i
  unfold mixTape TM.inputTape
  by_cases hi : i < (u.length : ℤ)
  · rw [if_pos hi]
    by_cases h0 : 0 ≤ i
    · have hn : i.toNat < u.length := by omega
      rw [if_pos ⟨h0, by simp; omega⟩, if_pos ⟨h0, by simp; omega⟩,
        List.getD_append _ _ _ _ hn, List.getD_append _ _ _ _ hn]
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h0 h.1)]
  · rw [if_neg hi]
    have h0 : 0 ≤ i := by omega
    have hn : u.length ≤ i.toNat := by omega
    have hn' : u'.length ≤ i.toNat := by omega
    simp only [List.length_append]
    by_cases hlt : i < ((u.length + v'.length : ℕ) : ℤ)
    · rw [if_pos ⟨h0, by push_cast at hlt ⊢; omega⟩, if_pos ⟨h0, by push_cast at hlt ⊢; omega⟩,
        List.getD_append_right _ _ _ _ hn, List.getD_append_right _ _ _ _ hn', hu]
    · rw [if_neg (fun h => hlt (by push_cast at h ⊢; omega)),
        if_neg (fun h => hlt (by push_cast at h ⊢; omega))]

theorem init_append_mix (u v u' v' : List Bool) (hu : u'.length = u.length) :
    M.init (u ++ v') = {M.init (u ++ v) with
      tape := mixTape (u.length : ℤ) (M.init (u ++ v)).tape (M.init (u' ++ v')).tape} := by
  simp only [TM.init, inputTape_append_mix M u v u' v' hu]

/-- **Hennie's crossing-sequence theorem for `Discrete.TM`.**  If the inputs `u ++ v` and
`u' ++ v'` (with `|u| = |u'| ≥ 1`) display their first answers `bx`, `by` at times `sx`, `sy`,
and their crossing traces at the cut `|u|` up to those times are equal, then the mixed input
`u ++ v'` displays its first answer within `sx + sy` steps; the answer is `bx` if the common
trace has even length (the last segment runs on the left) and `by` otherwise. -/
theorem hennie (u v u' v' : List Bool) (hu0 : 0 < u.length) (hu : u'.length = u.length)
    {sx sy : ℕ} {bx by' : Bool}
    (hx : M.out (u ++ v) sx = some bx) (hx0 : ∀ r < sx, M.out (u ++ v) r = none)
    (hy : M.out (u' ++ v') sy = some by') (hy0 : ∀ r < sy, M.out (u' ++ v') r = none)
    (htr : trace M (u.length : ℤ) (M.init (u ++ v)) sx =
      trace M (u.length : ℤ) (M.init (u' ++ v')) sy) :
    ∃ sz ≤ sx + sy, (∀ r < sz, M.out (u ++ v') r = none) ∧
      M.out (u ++ v') sz =
        some (if Even (trace M (u.length : ℤ) (M.init (u ++ v)) sx).length then bx else by') := by
  have hA : OnSide (u.length : ℤ) true (M.init (u ++ v)).head := by
    simp only [OnSide, ↓reduceIte, TM.init]; omega
  have hP : OnSide (u.length : ℤ) true (M.init (u' ++ v')).head := by
    simp only [OnSide, ↓reduceIte, TM.init]; omega
  obtain ⟨tz, htz, hnone, hans⟩ := splice_core _ true _ _ sx sy hA hP rfl htr.symm hx0 hy0
  refine ⟨tz, htz, fun r hr => ?_, ?_⟩
  · have := hnone r hr
    simp only [mixS, ↓reduceIte] at this
    rw [TM.out, init_append_mix M u v u' v' hu]
    exact this
  · simp only [mixS, ↓reduceIte] at hans
    rw [TM.out, init_append_mix M u v u' v' hu, hans]
    unfold TM.out at hx hy
    split_ifs with h
    · exact hx
    · exact hy

/-! ### Decision-language corollary -/

theorem firstAnswer_unique {out : ℕ → Option Bool} {T : ℕ} {b b' : Bool} {s : ℕ}
    (h : FirstAnswer out T b) (hs : out s = some b') (hs0 : ∀ r < s, out r = none) : b = b' := by
  obtain ⟨s₀, -, h₀, h₀'⟩ := h
  rcases lt_trichotomy s₀ s with hlt | heq | hgt
  · rw [hs0 s₀ hlt] at h₀; exact Option.noConfusion h₀
  · subst heq; rw [h₀] at hs; exact Option.some.inj hs
  · rw [h₀' s hgt] at hs; exact Option.noConfusion hs

/-- If `M` decides `L` and two members of `L` have equal crossing traces at the cut `|u|` up to
their first answers, then the mixed input `u ++ v'` belongs to `L`. -/
theorem splice_mem {L : Set (List Bool)} {T : ℕ → ℕ} (hM : M.Decides L T)
    (u v u' v' : List Bool) (hu0 : 0 < u.length) (hu : u'.length = u.length)
    {sx sy : ℕ}
    (hx : M.out (u ++ v) sx = some true) (hx0 : ∀ r < sx, M.out (u ++ v) r = none)
    (hy : M.out (u' ++ v') sy = some true) (hy0 : ∀ r < sy, M.out (u' ++ v') r = none)
    (htr : trace M (u.length : ℤ) (M.init (u ++ v)) sx =
      trace M (u.length : ℤ) (M.init (u' ++ v')) sy) :
    u ++ v' ∈ L := by
  obtain ⟨sz, -, hz0, hz⟩ := hennie M u v u' v' hu0 hu hx hx0 hy hy0 htr
  simp only [ite_self] at hz
  obtain ⟨b, hfa, hb⟩ := hM (u ++ v')
  have := firstAnswer_unique hfa hz hz0
  exact hb.1 this

end Inputs

end PVNP.CrossingHennie
