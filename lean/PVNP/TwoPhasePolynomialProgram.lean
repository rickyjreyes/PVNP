import PVNP.TwoPhasePolynomialState

/-!
# II-10: the assembled programs and their loops

The writers' programs are produced by the small assembler of `TwoPhasePolynomialWriter`
(`putI`, `setI`, `word`, `repeated`, `horner`). This file connects that assembler with the
instruction-level semantics.

* `runL` runs an assembler fragment on a list of instructions. `Emits f Q` says that `f` only
  appends code, and that every program containing that code at that address satisfies `Q` at the
  fragment's entry point. Fragments compose (`Emits.bind`).
* `word_emits`: a `word` appends its bits to the output.
* `repeated_emits`: a `repeated` block appends its bits once per accumulator mark.
* `horner_emits`: one Horner stage replaces the accumulator `a` by `a·n + c`, where `n` is the
  input length. The proof is by the loop invariants of the outer and inner counters
  (`inner_loop`, `outer_loop`).
* `stages_emits`: the stages of a coefficient list, executed last coefficient first, leave the
  Horner value `hv cs n` in the accumulator.
-/

namespace PVNP.TwoPhasePolynomialWriter

open PartIITuring

/-! ## Running assembler fragments on lists -/

/-- Run a fragment on a list of instructions. -/
def runL {α : Type} (f : Asm α) (l : List Inst) : α × List Inst :=
  ((Id.run (f.run l.toArray)).1, (Id.run (f.run l.toArray)).2.toList)

theorem runL_pure {α : Type} (a : α) (l : List Inst) : runL (pure a : Asm α) l = (a, l) := by
  simp [runL]

theorem runL_bind {α β : Type} (x : Asm α) (f : α → Asm β) (l : List Inst) :
    runL (x >>= f) l = runL (f (runL x l).1) (runL x l).2 := by
  simp [runL]

theorem runL_putI (i : Inst) (l : List Inst) : runL (putI i) l = (l.length, l ++ [i]) := by
  simp [runL, putI]

theorem runL_setI (i : ℕ) (v : Inst) (l : List Inst) : runL (setI i v) l = ((), l.set i v) := by
  simp [runL, setI]

theorem set_mid (l r : List Inst) (a v : Inst) : (l ++ a :: r).set l.length v = l ++ v :: r := by
  rw [List.set_append_right _ _ (le_refl _)]
  simp

/-! ## Code inside a program -/

/-- The program contains `code` from address `B` on. -/
def HasCode (P : ℕ × Array Inst) (B : ℕ) (code : List Inst) : Prop :=
  ∀ (j : ℕ) (hj : j < code.length), P.2[B + j]? = some code[j]

theorem HasCode.left {P : ℕ × Array Inst} {B : ℕ} {c1 c2 : List Inst}
    (h : HasCode P B (c1 ++ c2)) : HasCode P B c1 := by
  intro j hj
  have := h j (by rw [List.length_append]; omega)
  rwa [List.getElem_append_left hj] at this

theorem HasCode.right {P : ℕ × Array Inst} {B : ℕ} {c1 c2 : List Inst}
    (h : HasCode P B (c1 ++ c2)) : HasCode P (B + c1.length) c2 := by
  intro j hj
  have := h (c1.length + j) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rwa [Nat.add_assoc]

theorem HasCode.head {P : ℕ × Array Inst} {B : ℕ} {i : Inst} {c : List Inst}
    (h : HasCode P B (i :: c)) : P.2[B]? = some i := by
  simpa using h 0 (by simp)

theorem HasCode.tail {P : ℕ × Array Inst} {B : ℕ} {i : Inst} {c : List Inst}
    (h : HasCode P B (i :: c)) : HasCode P (B + 1) c :=
  HasCode.right (c1 := [i]) h

/-- `f` appends code, and every program containing it satisfies `Q` at the entry point. -/
def Emits (f : Asm ℕ) (Q : ℕ × Array Inst → ℕ → Prop) : Prop :=
  ∀ l : List Inst, ∃ e code, runL f l = (e, l ++ code) ∧ ∀ P, HasCode P l.length code → Q P e

theorem Emits.bind {f : Asm ℕ} {g : ℕ → Asm ℕ} {Q1 : ℕ × Array Inst → ℕ → Prop}
    {Q2 : ℕ → ℕ × Array Inst → ℕ → Prop} {Q : ℕ × Array Inst → ℕ → Prop} (h1 : Emits f Q1)
    (h2 : ∀ e, Emits (g e) (Q2 e)) (hQ : ∀ P e1 e2, Q1 P e1 → Q2 e1 P e2 → Q P e2) :
    Emits (f >>= g) Q := by
  intro l
  obtain ⟨e1, c1, hr1, hq1⟩ := h1 l
  obtain ⟨e2, c2, hr2, hq2⟩ := h2 e1 (l ++ c1)
  refine ⟨e2, c1 ++ c2, ?_, fun P hP => ?_⟩
  · rw [runL_bind, hr1, hr2, List.append_assoc]
  · refine hQ P e1 e2 (hq1 P hP.left) (hq2 P ?_)
    rw [List.length_append]
    exact hP.right

theorem Emits.mono {f : Asm ℕ} {Q Q' : ℕ × Array Inst → ℕ → Prop} (h : Emits f Q)
    (hQ : ∀ P e, Q P e → Q' P e) : Emits f Q' := by
  intro l
  obtain ⟨e, c, hr, hq⟩ := h l
  exact ⟨e, c, hr, fun P hP => hQ P e (hq P hP)⟩

theorem Emits.pure (a : ℕ) : Emits (pure a) (fun _ e => e = a) :=
  fun l => ⟨a, [], by rw [runL_pure, List.append_nil], fun _ _ => rfl⟩

theorem Emits.putI (i : Inst) : Emits (putI i) (fun P e => P.2[e]? = some i) :=
  fun l => ⟨l.length, [i], runL_putI i l, fun _ hP => hP.head⟩

/-! ## Output words -/

/-- Append output bits. -/
def St.emitAll (s : St) (bits : List Bool) : St :=
  {s with out := s.out ++ bits, len := max s.len (s.out.length + bits.length)}

/-- **`word`** appends its bits to the output and continues at `next`. -/
theorem word_emits (bits : List Bool) (next : ℕ) :
    Emits (word bits next) (fun P e => ∀ s : St, Exec P e s next (s.emitAll bits) bits.length) := by
  induction bits with
  | nil =>
    intro l
    refine ⟨next, [], ?_, fun P _ s => ?_⟩
    · show runL (List.foldrM (fun bit j => putI (.emit bit j)) next []) l = _
      rw [List.foldrM_nil, runL_pure, List.append_nil]
    · refine (Exec.refl next s).to (fun hw => ?_)
      have := hw.2.2.2.2.2
      ext <;> simp [St.emitAll]
      omega
  | cons b rest ih =>
    intro l
    obtain ⟨e, code, hr, hq⟩ := ih l
    refine ⟨(l ++ code).length, code ++ [.emit b e], ?_, fun P hP s => ?_⟩
    · show runL (List.foldrM (fun bit j => putI (.emit bit j)) next (b :: rest)) l = _
      have hr' : runL (List.foldrM (fun bit j => putI (.emit bit j)) next rest) l =
          (e, l ++ code) := hr
      rw [List.foldrM_cons, runL_bind]
      simp only [hr', runL_putI, List.append_assoc]
    · have h1 : P.2[(l ++ code).length]? = some (.emit b e) := by
        have := hP.right.head
        rwa [← List.length_append] at this
      have h2 := hq P hP.left (s.emitAll [b])
      refine (((Exec.emit h1 s).trans h2).mono (m' := (b :: rest).length)
        (by simp; omega)).to (fun _ => ?_)
      ext <;> simp [St.emitAll]
      omega

theorem length_flatten_replicate (r : ℕ) (bits : List Bool) :
    ((List.replicate r bits).flatten).length = r * bits.length := by
  induction r with
  | zero => simp
  | succ r ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

/-! ## `repeated` -/

/-- The loop of a `repeated` block: one copy of `bits` per remaining outer mark. -/
theorem repeated_loop {P : ℕ × Array Inst} {B yes next : ℕ} {bits : List Bool}
    (hT : P.2[B]? = some (.take .outer yes next))
    (hW : ∀ s : St, Exec P yes s B (s.emitAll bits) bits.length) :
    ∀ (r : ℕ) (s : St), s.oLo + r = s.oHi →
      Exec P B s next
        { s with
          oLo := s.oHi
          out := s.out ++ (List.replicate r bits).flatten
          len := max s.len (s.out.length + r * bits.length) }
        (r * (bits.length + 1) + 1) := by
  intro r
  induction r with
  | zero =>
    intro s hs
    refine ((Exec.take_outer_miss hT s (by omega)).mono (by omega)).to (fun hw => ?_)
    have := hw.2.2.2.2.2
    ext <;> simp
    all_goals omega
  | succ r ih =>
    intro s hs
    have h1 := Exec.take_outer_hit hT s (by omega)
    have h2 := hW {s with oLo := s.oLo + 1}
    have h3 := ih (({s with oLo := s.oLo + 1} : St).emitAll bits)
      (by show s.oLo + 1 + r = s.oHi; omega)
    refine (((h1.trans h2).trans h3).mono (le_of_eq (by ring))).to (fun _ => ?_)
    have e : (r + 1) * bits.length = r * bits.length + bits.length := Nat.succ_mul _ _
    ext <;> simp [St.emitAll, List.replicate_succ]
    all_goals omega

/-- A `repeated` block: `outer := acc`, then the loop. -/
theorem repeated_sem {P : ℕ × Array Inst} {B yes next cp : ℕ} {bits : List Bool}
    (hT : P.2[B]? = some (.take .outer yes next))
    (hW : ∀ s : St, Exec P yes s B (s.emitAll bits) bits.length)
    (hC : P.2[cp]? = some (.copy (.mark .acc) .outer B)) (s : St) :
    Exec P cp s next
      { s with
        oLo := s.acc
        oHi := s.acc
        out := s.out ++ (List.replicate s.acc bits).flatten
        len := max s.len (s.out.length + s.acc * bits.length) }
      (s.acc * (bits.length + 1) + 2) := by
  have h1 := Exec.copy_acc_outer hC s
  have h2 := repeated_loop hT hW s.acc {s with oLo := 0, oHi := s.acc} (by simp)
  exact (h1.trans h2).mono (by omega)

/-- **`repeated`** appends `bits` once per accumulator mark. -/
theorem repeated_emits (bits : List Bool) (next : ℕ) :
    Emits (repeated bits next) (fun P e => ∀ s : St, Exec P e s next
      { s with
        oLo := s.acc
        oHi := s.acc
        out := s.out ++ (List.replicate s.acc bits).flatten
        len := max s.len (s.out.length + s.acc * bits.length) }
      (s.acc * (bits.length + 1) + 2)) := by
  intro l
  obtain ⟨yes, cw, hrw, hqw⟩ := word_emits bits l.length (l ++ [.finish])
  refine ⟨(l ++ Inst.take .outer yes next :: cw).length,
    Inst.take .outer yes next :: cw ++ [.copy (.mark .acc) .outer l.length], ?_, fun P hP s => ?_⟩
  · unfold repeated
    simp only [runL_bind, runL_putI, runL_setI, hrw]
    have e1 : l ++ [Inst.finish] ++ cw = l ++ Inst.finish :: cw := by simp
    rw [e1, set_mid]
    simp
  · have hT : P.2[l.length]? = some (.take .outer yes next) := hP.left.head
    have hW := hqw P (by simpa using hP.left.tail)
    have hC : P.2[(l ++ Inst.take .outer yes next :: cw).length]? =
        some (.copy (.mark .acc) .outer l.length) := by
      have := hP.right.head
      rwa [← List.length_append] at this
    exact repeated_sem hT hW hC s

/-! ## One Horner stage -/

/-- `dest := dest + c`. -/
def St.incN (s : St) (c : ℕ) : St := {s with dst := s.dst + c, len := max s.len (s.dst + c)}

/-- The chain of `c` increments. -/
theorem incs_emits (c e0 : ℕ) :
    Emits ((List.range c).foldlM (fun j _ => putI (.inc j)) e0)
      (fun P e => ∀ s : St, Exec P e s e0 (s.incN c) c) := by
  induction c with
  | zero =>
    intro l
    refine ⟨e0, [], ?_, fun P _ s => ?_⟩
    · rw [List.range_zero, List.foldlM_nil, runL_pure, List.append_nil]
    · refine (Exec.refl e0 s).to (fun hw => ?_)
      have := hw.2.2.1
      ext <;> simp [St.incN]
      omega
  | succ c ih =>
    have e : (List.range (c + 1)).foldlM (fun j _ => putI (.inc j)) e0 =
        (List.range c).foldlM (fun j _ => putI (.inc j)) e0 >>= fun j => putI (.inc j) := by
      rw [List.range_succ, List.foldlM_append]
      rfl
    rw [e]
    refine Emits.bind ih (fun j => Emits.putI (.inc j)) (fun P e1 e2 h1 h2 s => ?_)
    refine (((Exec.inc h2 s).trans (h1 _)).mono (m' := c + 1) (by omega)).to (fun _ => ?_)
    ext <;> simp [St.incN]
    all_goals omega

/-- The inner loop: one increment per remaining inner mark. -/
theorem inner_loop {P : ℕ × Array Inst} {inner incL outer : ℕ}
    (hI : P.2[inner]? = some (.take .inner incL outer)) (hInc : P.2[incL]? = some (.inc inner)) :
    ∀ (r : ℕ) (s : St), s.iLo + r = s.iHi →
      Exec P inner s outer
        { s with
          iLo := s.iHi
          dst := s.dst + r
          len := max s.len (s.dst + r) }
        (2 * r + 1) := by
  intro r
  induction r with
  | zero =>
    intro s hs
    refine ((Exec.take_inner_miss hI s (by omega)).mono (by omega)).to (fun hw => ?_)
    have := hw.2.2.1
    ext <;> simp
    all_goals omega
  | succ r ih =>
    intro s hs
    have h1 := Exec.take_inner_hit hI s (by omega)
    have h2 := Exec.inc hInc {s with iLo := s.iLo + 1}
    have h3 := ih {s with iLo := s.iLo + 1, dst := s.dst + 1, len := max s.len (s.dst + 1)}
      (by show s.iLo + 1 + r = s.iHi; omega)
    refine (((h1.trans h2).trans h3).mono (by omega)).to (fun _ => ?_)
    ext <;> simp
    all_goals omega

/-- The outer loop: one pass of the inner loop per remaining outer mark. -/
theorem outer_loop {P : ℕ × Array Inst} {outer enter addC inner incL : ℕ}
    (hO : P.2[outer]? = some (.take .outer enter addC))
    (hE : P.2[enter]? = some (.copy .input .inner inner))
    (hI : P.2[inner]? = some (.take .inner incL outer)) (hInc : P.2[incL]? = some (.inc inner)) :
    ∀ (r : ℕ) (s : St), s.oLo + r = s.oHi →
      ∃ s', Exec P outer s addC s' (r * (2 * s.x.length + 3) + 1) ∧ s'.x = s.x ∧
        s'.acc = s.acc ∧ s'.out = s.out ∧ s'.dst = s.dst + r * s.x.length ∧
        s'.len ≤ max s.len (s.dst + r * s.x.length) := by
  intro r
  induction r with
  | zero =>
    intro s hs
    exact ⟨s, (Exec.take_outer_miss hO s (by omega)).mono (by omega), rfl, rfl, rfl, by simp,
      le_max_left _ _⟩
  | succ r ih =>
    intro s hs
    have h1 := Exec.take_outer_hit hO s (by omega)
    have h2 := Exec.copy_input_inner hE {s with oLo := s.oLo + 1}
    have h3 := inner_loop hI hInc s.x.length
      {s with oLo := s.oLo + 1, iLo := 0, iHi := s.x.length} (by simp)
    obtain ⟨s', h4, hx, ha, ho, hd, hl⟩ := ih
      { s with
        oLo := s.oLo + 1
        iLo := s.x.length
        iHi := s.x.length
        dst := s.dst + s.x.length
        len := max s.len (s.dst + s.x.length) }
      (by show s.oLo + 1 + r = s.oHi; omega)
    have e : (r + 1) * s.x.length = r * s.x.length + s.x.length := Nat.succ_mul _ _
    refine ⟨s', (((h1.trans h2).trans h3).trans h4).mono (le_of_eq (by ring)), hx, ha, ho, ?_, ?_⟩
    · rw [hd]
      show s.dst + s.x.length + r * s.x.length = s.dst + (r + 1) * s.x.length
      omega
    · refine le_trans hl ?_
      show max (max s.len (s.dst + s.x.length)) (s.dst + s.x.length + r * s.x.length) ≤
        max s.len (s.dst + (r + 1) * s.x.length)
      omega

/-- What one Horner stage with coefficient `c` does: `acc := acc · n + c`. -/
def StageSpec (P : ℕ × Array Inst) (e next c : ℕ) : Prop :=
  ∀ s : St, ∃ s', Exec P e s next s' (s.acc * (2 * s.x.length + 3) + c + 4) ∧ s'.x = s.x ∧
    s'.acc = s.acc * s.x.length + c ∧ s'.out = s.out ∧
    s'.len ≤ max s.len (s.acc * s.x.length + c)

theorem stage_sem {P : ℕ × Array Inst} {e clear outer enter inner incL addC endS next c : ℕ}
    (hEntry : P.2[e]? = some (.copy (.mark .acc) .outer clear))
    (hClear : P.2[clear]? = some (.copy .zero .dest outer))
    (hO : P.2[outer]? = some (.take .outer enter addC))
    (hE : P.2[enter]? = some (.copy .input .inner inner))
    (hI : P.2[inner]? = some (.take .inner incL outer)) (hInc : P.2[incL]? = some (.inc inner))
    (hAdd : ∀ s : St, Exec P addC s endS (s.incN c) c)
    (hEnd : P.2[endS]? = some (.copy (.mark .dest) .acc next)) : StageSpec P e next c := by
  intro s
  have h1 := Exec.copy_acc_outer hEntry s
  have h2 := Exec.clear_dest hClear {s with oLo := 0, oHi := s.acc}
  obtain ⟨s3, h3, hx, ha, ho, hd, hl⟩ := outer_loop hO hE hI hInc s.acc
    {s with oLo := 0, oHi := s.acc, dst := 0} (by simp)
  have h4 := hAdd s3
  have h5 := Exec.copy_dest_acc hEnd (s3.incN c)
  refine ⟨{s3.incN c with acc := (s3.incN c).dst}, ((((h1.trans h2).trans h3).trans h4).trans
    h5).mono ?_, hx, ?_, ho, ?_⟩
  · show 1 + 1 + (s.acc * (2 * s.x.length + 3) + 1) + c + 1 ≤ s.acc * (2 * s.x.length + 3) + c + 4
    omega
  · show s3.dst + c = s.acc * s.x.length + c
    rw [hd]
    show 0 + s.acc * s.x.length + c = _
    omega
  · show max s3.len (s3.dst + c) ≤ max s.len (s.acc * s.x.length + c)
    have hd' : s3.dst = s.acc * s.x.length := by rw [hd]; show 0 + s.acc * s.x.length = _; omega
    have hl' : s3.len ≤ max s.len (s.acc * s.x.length) := by
      refine le_trans hl ?_
      show max s.len (0 + s.acc * s.x.length) ≤ _
      omega
    omega

/-- The fixed tail of a Horner stage: its six control instructions. -/
def hornerTail (addC : ℕ) : Asm ℕ := do
  let outer ← putI .finish
  let inner ← putI .finish
  let inc ← putI (.inc inner)
  setI inner (.take .inner inc outer)
  let enter ← putI (.copy .input .inner inner)
  setI outer (.take .outer enter addC)
  let clear ← putI (.copy .zero .dest outer)
  putI (.copy (.mark .acc) .outer clear)

theorem horner_eq (next c : ℕ) : horner next c =
    (putI (.copy (.mark .dest) .acc next) >>= fun endStage =>
      (List.range c).foldlM (fun j _ => putI (.inc j)) endStage >>= fun addC =>
        hornerTail addC) := rfl

theorem set_at (X Y : List Inst) (j : ℕ) (v : Inst) :
    (X ++ Y).set (X.length + j) v = X ++ Y.set j v := by
  rw [List.set_append_right _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem runL_hornerTail (addC : ℕ) (X : List Inst) :
    runL (hornerTail addC) X = (X.length + 5,
      X ++ [.take .outer (X.length + 3) addC, .take .inner (X.length + 2) X.length,
        .inc (X.length + 1), .copy .input .inner (X.length + 1), .copy .zero .dest X.length,
        .copy (.mark .acc) .outer (X.length + 4)]) := by
  unfold hornerTail
  simp only [runL_bind, runL_putI, runL_setI]
  have e1 : X ++ [Inst.finish] ++ [Inst.finish] ++ [Inst.inc (X ++ [Inst.finish]).length] =
      X ++ [Inst.finish, Inst.finish, Inst.inc (X.length + 1)] := by simp
  have e2 : (X ++ [Inst.finish]).length = X.length + 1 := by simp
  have e3 : (X ++ [Inst.finish] ++ [Inst.finish]).length = X.length + 2 := by simp
  rw [e1, e2, e3, set_at]
  simp only [List.set_cons_succ, List.set_cons_zero]
  have e4 : (X ++ [Inst.finish, Inst.take Mark.inner (X.length + 2) X.length,
      Inst.inc (X.length + 1)]).length = X.length + 3 := by simp
  rw [e4]
  have e5 : X ++ [Inst.finish, Inst.take Mark.inner (X.length + 2) X.length,
      Inst.inc (X.length + 1)] ++ [Inst.copy Source.input Mark.inner (X.length + 1)] =
      X ++ [Inst.finish, Inst.take Mark.inner (X.length + 2) X.length,
        Inst.inc (X.length + 1), Inst.copy Source.input Mark.inner (X.length + 1)] := by simp
  rw [e5]
  rw [set_mid]
  simp

/-- **`horner next c`** emits a stage computing `acc := acc · n + c`. -/
theorem horner_emits (next c : ℕ) : Emits (horner next c) (fun P e => StageSpec P e next c) := by
  intro l
  obtain ⟨addC, ci, hri, hqi⟩ := incs_emits c l.length (l ++ [.copy (.mark .dest) .acc next])
  have hXl : (l ++ [Inst.copy (.mark .dest) .acc next] ++ ci).length =
      l.length + ([Inst.copy (.mark .dest) .acc next] ++ ci).length := by
    simp only [List.length_append]; omega
  generalize hX : l ++ [Inst.copy (.mark .dest) .acc next] ++ ci = X at hXl hri
  refine ⟨X.length + 5, [Inst.copy (.mark .dest) .acc next] ++ ci ++
    [.take .outer (X.length + 3) addC, .take .inner (X.length + 2) X.length,
      .inc (X.length + 1), .copy .input .inner (X.length + 1), .copy .zero .dest X.length,
      .copy (.mark .acc) .outer (X.length + 4)], ?_, fun P hP s => ?_⟩
  · rw [horner_eq]
    simp only [runL_bind, runL_putI, hri, runL_hornerTail]
    rw [← hX]
    simp
  · have hEnd : P.2[l.length]? = some (.copy (.mark .dest) .acc next) := hP.left.left.head
    have hAdd := hqi P (by
      have := hP.left.right
      simpa using this)
    have h6 := hP.right
    rw [← hXl] at h6
    exact stage_sem (e := X.length + 5) (clear := X.length + 4) (outer := X.length)
      (enter := X.length + 3) (inner := X.length + 1) (incL := X.length + 2)
      h6.tail.tail.tail.tail.tail.head h6.tail.tail.tail.tail.head h6.head h6.tail.tail.tail.head
      h6.tail.head h6.tail.tail.head hAdd hEnd s

/-! ## All stages -/

/-- Horner value of a coefficient list, low-order coefficient first. -/
def hv (cs : List ℕ) (n : ℕ) : ℕ := cs.foldr (fun c a => a * n + c) 0

/-- Number of instructions executed by the stages. -/
def ic : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: rest, n => ic rest n + (hv rest n * (2 * n + 3) + c + 4)

/-- Largest counter value reached by the stages. -/
def hb : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: rest, n => max (hb rest n) (hv rest n * n + c)

theorem hv_cons (c : ℕ) (rest : List ℕ) (n : ℕ) : hv (c :: rest) n = hv rest n * n + c := rfl

/-- What the stages of `cs` do from an empty accumulator. -/
def StagesSpec (P : ℕ × Array Inst) (e start : ℕ) (cs : List ℕ) : Prop :=
  ∀ s : St, s.acc = 0 → ∃ s', Exec P e s start s' (ic cs s.x.length) ∧ s'.x = s.x ∧
    s'.acc = hv cs s.x.length ∧ s'.out = s.out ∧ s'.len ≤ max s.len (hb cs s.x.length)

/-- **The machine executes Horner's rule.** The stages of the coefficient list `cs`, run from
an empty accumulator, leave exactly `hv cs n` accumulator marks, `n` the input length. -/
theorem stages_emits (cs : List ℕ) : ∀ start : ℕ,
    Emits (cs.foldlM horner start) (fun P e => StagesSpec P e start cs) := by
  induction cs with
  | nil =>
    intro start
    rw [List.foldlM_nil]
    refine (Emits.pure start).mono (fun P e he s hs => ?_)
    subst he
    exact ⟨s, Exec.refl _ _, rfl, hs, rfl, le_max_left _ _⟩
  | cons c rest ih =>
    intro start
    rw [List.foldlM_cons]
    refine Emits.bind (horner_emits start c) (fun e1 => ih e1) (fun P e1 e2 h1 h2 s hs => ?_)
    obtain ⟨s1, hx1, hsx1, ha1, ho1, hl1⟩ := h2 s hs
    obtain ⟨s2, hx2, hsx2, ha2, ho2, hl2⟩ := h1 s1
    rw [hsx1, ha1] at hx2 ha2 hl2
    refine ⟨s2, hx1.trans hx2, hsx2.trans hsx1, ?_, ho2.trans ho1, ?_⟩
    · rw [ha2, hv_cons]
    · refine le_trans hl2 ?_
      show max s1.len (hv rest s.x.length * s.x.length + c) ≤
        max s.len (max (hb rest s.x.length) (hv rest s.x.length * s.x.length + c))
      omega

end PVNP.TwoPhasePolynomialWriter
