import PVNP.TwoPhasePolynomialProgram

/-!
# II-10: first-halt outputs of the original polynomial writers

`assemble cs body` puts the Horner stages of the coefficient list `cs` in front of a body. This
file proves, for the actual machine `build (assemble cs body)`:

* `normalize_steps`: the normalization phase ends on the work-region tape of the initial state
  after exactly `2n + 4` transitions;
* `windowBody_emits`, `inputBodyG_emits`: the two bodies append the lattice word and the
  configuration word to the output and reach their `finish` instruction;
* `assemble_outputs`: the machine halts for the first time with exactly the body's word on the
  tape, under the `MTM.Outputs` convention, within an explicit transition bound.
-/

namespace PVNP.TwoPhasePolynomialWriter

open PartIITuring

/-! ## Output segments -/

/-- From `e` to `tgt` the machine appends `W x acc` to the output, keeps the input and the
accumulator, and executes at most `cnt x acc` instructions. -/
def Seg (P : ℕ × Array Inst) (e tgt : ℕ) (W : List Bool → ℕ → List Bool)
    (cnt : List Bool → ℕ → ℕ) : Prop :=
  ∀ s : St, ∃ s', Exec P e s tgt s' (cnt s.x s.acc) ∧ s'.x = s.x ∧ s'.acc = s.acc ∧
    s'.out = s.out ++ W s.x s.acc ∧ s'.len ≤ max s.len (s.out.length + (W s.x s.acc).length)

theorem Seg.of_word {P : ℕ × Array Inst} {e next : ℕ} {bits : List Bool}
    (h : ∀ s : St, Exec P e s next (s.emitAll bits) bits.length) :
    Seg P e next (fun _ _ => bits) (fun _ _ => bits.length) :=
  fun s => ⟨s.emitAll bits, h s, rfl, rfl, rfl, le_rfl⟩

theorem Seg.of_repeated {P : ℕ × Array Inst} {e next : ℕ} {bits : List Bool}
    (h : ∀ s : St, Exec P e s next
      { s with
        oLo := s.acc
        oHi := s.acc
        out := s.out ++ (List.replicate s.acc bits).flatten
        len := max s.len (s.out.length + s.acc * bits.length) }
      (s.acc * (bits.length + 1) + 2)) :
    Seg P e next (fun _ R => (List.replicate R bits).flatten)
      (fun _ R => R * (bits.length + 1) + 2) :=
  fun s => ⟨_, h s, rfl, rfl, rfl, by
    show max s.len (s.out.length + s.acc * bits.length) ≤
      max s.len (s.out.length + ((List.replicate s.acc bits).flatten).length)
    rw [length_flatten_replicate]⟩

theorem Seg.comp {P : ℕ × Array Inst} {e mid tgt : ℕ} {W1 W2 : List Bool → ℕ → List Bool}
    {c1 c2 : List Bool → ℕ → ℕ} (h1 : Seg P e mid W1 c1) (h2 : Seg P mid tgt W2 c2) :
    Seg P e tgt (fun x R => W1 x R ++ W2 x R) (fun x R => c1 x R + c2 x R) := by
  intro s
  obtain ⟨s1, he1, hx1, ha1, ho1, hl1⟩ := h1 s
  obtain ⟨s2, he2, hx2, ha2, ho2, hl2⟩ := h2 s1
  rw [hx1, ha1] at he2 ho2 hl2
  refine ⟨s2, he1.trans he2, hx2.trans hx1, ha2.trans ha1, ?_, ?_⟩
  · rw [ho2, ho1, List.append_assoc]
  · rw [ho1] at hl2
    simp only [List.length_append] at hl2 ⊢
    omega

theorem Seg.congr {P : ℕ × Array Inst} {e tgt : ℕ} {W W' : List Bool → ℕ → List Bool}
    {c c' : List Bool → ℕ → ℕ} (h : Seg P e tgt W c) (hW : ∀ x R, W x R = W' x R)
    (hc : ∀ x R, c x R ≤ c' x R) : Seg P e tgt W' c' := by
  intro s
  obtain ⟨s1, he1, hx1, ha1, ho1, hl1⟩ := h s
  rw [hW] at ho1 hl1
  exact ⟨s1, he1.mono (hc _ _), hx1, ha1, ho1, hl1⟩

/-- A body: its entry leads to a `finish` instruction after appending `W x acc`. -/
def BodySpec (W : List Bool → ℕ → List Bool) (cnt : List Bool → ℕ → ℕ) (P : ℕ × Array Inst)
    (e : ℕ) : Prop :=
  ∃ fin, P.2[fin]? = some .finish ∧ Seg P e fin W cnt

theorem Emits.bind_exists {f : Asm ℕ} {g : ℕ → Asm ℕ} {Q1 : ℕ × Array Inst → ℕ → Prop}
    {Q2 : ℕ → ℕ × Array Inst → ℕ → Prop} (h1 : Emits f Q1) (h2 : ∀ e, Emits (g e) (Q2 e)) :
    Emits (f >>= g) (fun P e2 => ∃ e1, Q1 P e1 ∧ Q2 e1 P e2) :=
  Emits.bind h1 h2 (fun _ e1 _ a b => ⟨e1, a, b⟩)

/-! ## The lattice-window body -/

/-- Output of the window body for accumulator value `R`. -/
def winTail (R : ℕ) : List Bool :=
  (List.replicate R [true]).flatten ++ [true, false, false] ++
    (List.replicate R [true, true]).flatten ++ [true, false]

/-- **The window body** writes `1^R · 100 · (11)^R · 10` and reaches its `finish`. -/
theorem windowBody_emits :
    Emits windowBody (BodySpec (fun _ R => winTail R) (fun _ R => 5 * R + 9)) := by
  have hc : Emits windowBody (fun P e =>
      ∃ endWord, P.2[endWord]? = some .finish ∧
      ∃ tail, (∀ s : St, Exec P tail s endWord (s.emitAll [true, false]) [true, false].length) ∧
      ∃ middle, (∀ s : St, Exec P middle s tail
          { s with
            oLo := s.acc
            oHi := s.acc
            out := s.out ++ (List.replicate s.acc [true, true]).flatten
            len := max s.len (s.out.length + s.acc * [true, true].length) }
          (s.acc * ([true, true].length + 1) + 2)) ∧
      ∃ header, (∀ s : St, Exec P header s middle (s.emitAll [true, false, false])
          [true, false, false].length) ∧
        ∀ s : St, Exec P e s header
          { s with
            oLo := s.acc
            oHi := s.acc
            out := s.out ++ (List.replicate s.acc [true]).flatten
            len := max s.len (s.out.length + s.acc * [true].length) }
          (s.acc * ([true].length + 1) + 2)) :=
    Emits.bind_exists (Emits.putI .finish) (fun endWord =>
      Emits.bind_exists (word_emits [true, false] endWord) (fun tail =>
        Emits.bind_exists (repeated_emits [true, true] tail) (fun middle =>
          Emits.bind_exists (word_emits [true, false, false] middle) (fun header =>
            repeated_emits [true] header))))
  refine hc.mono (fun P e h => ?_)
  obtain ⟨endWord, hfin, tail, h2, middle, h3, header, h4, h5⟩ := h
  refine ⟨endWord, hfin, ?_⟩
  refine ((((Seg.of_repeated h5).comp (Seg.of_word h4)).comp (Seg.of_repeated h3)).comp
    (Seg.of_word h2)).congr (fun _ _ => rfl) (fun _ R => ?_)
  show R * ([true].length + 1) + 2 + [true, false, false].length +
    (R * ([true, true].length + 1) + 2) + [true, false].length ≤ 5 * R + 9
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## The initial-configuration body -/

/-- The input body for arbitrary fixed cell words `blk symbol head`. -/
def inputBodyG (blk : Option Bool → Bool → List Bool) : Asm ℕ := do
  let endWord ← putI .finish
  let loop ← putI .finish
  let b ← word (blk none false) loop
  let z ← word (blk (some false) false) loop
  let o ← word (blk (some true) false) loop
  setI loop (.nextInput b z o endWord)
  let right ← putI (.copy (.mark .acc) .outer loop)
  let hb ← word (blk none true) right
  let hz ← word (blk (some false) true) right
  let ho ← word (blk (some true) true) right
  let center ← putI (.headInput hb hz ho)
  repeated (blk none false) center

/-- The append-only part of the input body. -/
def inputTail (blk : Option Bool → Bool → List Bool) (loop : ℕ) : Asm ℕ := do
  let right ← putI (.copy (.mark .acc) .outer loop)
  let hb ← word (blk none true) right
  let hz ← word (blk (some false) true) right
  let ho ← word (blk (some true) true) right
  let center ← putI (.headInput hb hz ho)
  repeated (blk none false) center

theorem inputBodyG_eq (blk : Option Bool → Bool → List Bool) : inputBodyG blk =
    (putI .finish >>= fun endWord => putI .finish >>= fun loop =>
      word (blk none false) loop >>= fun b => word (blk (some false) false) loop >>= fun z =>
        word (blk (some true) false) loop >>= fun o =>
          setI loop (.nextInput b z o endWord) >>= fun _ => inputTail blk loop) := rfl

/-- Output of the input body: `R` blank cells, the head cell, and the cells `1 … R`. -/
def inW (blk : Option Bool → Bool → List Bool) (x : List Bool) (R : ℕ) : List Bool :=
  (List.replicate R (blk none false)).flatten ++ blk x[0]? true ++
    (List.range R).flatMap (fun i => blk x[i + 1]? false)

theorem length_flatMap_range {f : ℕ → List Bool} {w : ℕ} (hf : ∀ i, (f i).length = w) (r : ℕ) :
    ((List.range r).flatMap f).length = r * w := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hf]
    ring

section InputSem

variable {P : ℕ × Array Inst} {blk : Option Bool → Bool → List Bool} {w : ℕ}

/-- The word selected by an optional input bit. -/
theorem sel_word {b z o tgt : ℕ} {head : Bool} (hblk : ∀ v h, (blk v h).length = w)
    (hb : ∀ s : St, Exec P b s tgt (s.emitAll (blk none head)) (blk none head).length)
    (hz : ∀ s : St, Exec P z s tgt (s.emitAll (blk (some false) head))
      (blk (some false) head).length)
    (ho : ∀ s : St, Exec P o s tgt (s.emitAll (blk (some true) head))
      (blk (some true) head).length) (v : Option Bool) (s : St) :
    Exec P (sel3 v b z o) s tgt (s.emitAll (blk v head)) w := by
  rcases v with _ | (_ | _)
  · have := hb s; rwa [hblk] at this
  · have := hz s; rwa [hblk] at this
  · have := ho s; rwa [hblk] at this

/-- The loop over the cells to the right of the head. -/
theorem input_loop {loop b z o endWord : ℕ} (hblk : ∀ v h, (blk v h).length = w)
    (hN : P.2[loop]? = some (.nextInput b z o endWord))
    (hb : ∀ s : St, Exec P b s loop (s.emitAll (blk none false)) (blk none false).length)
    (hz : ∀ s : St, Exec P z s loop (s.emitAll (blk (some false) false))
      (blk (some false) false).length)
    (ho : ∀ s : St, Exec P o s loop (s.emitAll (blk (some true) false))
      (blk (some true) false).length) :
    ∀ (r : ℕ) (s : St), s.oLo + r = s.oHi →
      ∃ s', Exec P loop s endWord s' (r * (w + 1) + 1) ∧ s'.x = s.x ∧ s'.acc = s.acc ∧
        s'.out = s.out ++ (List.range r).flatMap (fun i => blk s.x[s.oLo + i + 1]? false) ∧
        s'.len ≤ max s.len (s.out.length + r * w) := by
  intro r
  induction r with
  | zero =>
    intro s hs
    exact ⟨s, (Exec.next_miss hN s (by omega)).mono (by omega), rfl, rfl, by simp,
      le_max_left _ _⟩
  | succ r ih =>
    intro s hs
    have h1 := Exec.next_hit hN s (by omega)
    have h2 := sel_word hblk hb hz ho s.x[s.oLo + 1]? {s with oLo := s.oLo + 1}
    obtain ⟨s', h3, hx, ha, ho', hl⟩ := ih
      (({s with oLo := s.oLo + 1} : St).emitAll (blk s.x[s.oLo + 1]? false))
      (by show s.oLo + 1 + r = s.oHi; omega)
    have e : (r + 1) * w = r * w + w := Nat.succ_mul _ _
    refine ⟨s', ((h1.trans h2).trans h3).mono (le_of_eq (by ring)), hx, ha, ?_, ?_⟩
    · rw [ho']
      show s.out ++ blk s.x[s.oLo + 1]? false ++
          (List.range r).flatMap (fun i => blk s.x[s.oLo + 1 + i + 1]? false) =
        s.out ++ (List.range (r + 1)).flatMap (fun i => blk s.x[s.oLo + i + 1]? false)
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.append_assoc]
      congr 2
      apply List.flatMap_congr
      intro i _
      show blk s.x[s.oLo + 1 + i + 1]? false = blk s.x[s.oLo + (i + 1) + 1]? false
      rw [show s.oLo + 1 + i + 1 = s.oLo + (i + 1) + 1 by omega]
    · refine le_trans hl ?_
      show max (max s.len (s.out.length + (blk s.x[s.oLo + 1]? false).length))
          ((s.out ++ blk s.x[s.oLo + 1]? false).length + r * w) ≤
        max s.len (s.out.length + (r + 1) * w)
      rw [List.length_append, hblk]
      omega

/-- From the instruction after the head cell to the end: the cells `1 … R`. -/
theorem right_seg {right loop b z o endWord : ℕ} (hblk : ∀ v h, (blk v h).length = w)
    (hC : P.2[right]? = some (.copy (.mark .acc) .outer loop))
    (hN : P.2[loop]? = some (.nextInput b z o endWord))
    (hb : ∀ s : St, Exec P b s loop (s.emitAll (blk none false)) (blk none false).length)
    (hz : ∀ s : St, Exec P z s loop (s.emitAll (blk (some false) false))
      (blk (some false) false).length)
    (ho : ∀ s : St, Exec P o s loop (s.emitAll (blk (some true) false))
      (blk (some true) false).length) :
    Seg P right endWord (fun x R => (List.range R).flatMap (fun i => blk x[i + 1]? false))
      (fun _ R => R * (w + 1) + 2) := by
  intro s
  have h1 := Exec.copy_acc_outer hC s
  obtain ⟨s', h2, hx, ha, ho', hl⟩ := input_loop hblk hN hb hz ho s.acc
    {s with oLo := 0, oHi := s.acc} (by simp)
  refine ⟨s', (h1.trans h2).mono (by
    show 1 + (s.acc * (w + 1) + 1) ≤ s.acc * (w + 1) + 2
    omega), hx, ha, ?_, ?_⟩
  · rw [ho']
    show s.out ++ (List.range s.acc).flatMap (fun i => blk s.x[0 + i + 1]? false) = _
    simp
  · refine le_trans hl ?_
    show max s.len (s.out.length + s.acc * w) ≤ _
    rw [length_flatMap_range (fun i => hblk _ _)]

/-- The head cell. -/
theorem center_seg {center hb hz ho right : ℕ} (hblk : ∀ v h, (blk v h).length = w)
    (hH : P.2[center]? = some (.headInput hb hz ho))
    (hwb : ∀ s : St, Exec P hb s right (s.emitAll (blk none true)) (blk none true).length)
    (hwz : ∀ s : St, Exec P hz s right (s.emitAll (blk (some false) true))
      (blk (some false) true).length)
    (hwo : ∀ s : St, Exec P ho s right (s.emitAll (blk (some true) true))
      (blk (some true) true).length) :
    Seg P center right (fun x _ => blk x[0]? true) (fun _ _ => 1 + w) :=
  fun s => ⟨s.emitAll (blk s.x[0]? true),
    (Exec.head hH s).trans (sel_word hblk hwb hwz hwo s.x[0]? s), rfl, rfl, rfl, le_rfl⟩

end InputSem

/-- Everything the append-only part of the input body provides. -/
theorem inputTail_collect (blk : Option Bool → Bool → List Bool) (loop : ℕ) :
    Emits (inputTail blk loop) (fun P e =>
      ∃ right, P.2[right]? = some (.copy (.mark .acc) .outer loop) ∧
      ∃ hb, (∀ s : St, Exec P hb s right (s.emitAll (blk none true)) (blk none true).length) ∧
      ∃ hz, (∀ s : St, Exec P hz s right (s.emitAll (blk (some false) true))
          (blk (some false) true).length) ∧
      ∃ ho, (∀ s : St, Exec P ho s right (s.emitAll (blk (some true) true))
          (blk (some true) true).length) ∧
      ∃ center, P.2[center]? = some (.headInput hb hz ho) ∧
        ∀ s : St, Exec P e s center
          { s with
            oLo := s.acc
            oHi := s.acc
            out := s.out ++ (List.replicate s.acc (blk none false)).flatten
            len := max s.len (s.out.length + s.acc * (blk none false).length) }
          (s.acc * ((blk none false).length + 1) + 2)) :=
  Emits.bind_exists (Emits.putI _) (fun right =>
    Emits.bind_exists (word_emits _ right) (fun hb =>
      Emits.bind_exists (word_emits _ right) (fun hz =>
        Emits.bind_exists (word_emits _ right) (fun ho =>
          Emits.bind_exists (Emits.putI (.headInput hb hz ho))
            (fun center => repeated_emits _ center)))))

theorem HasCode.cast {P : ℕ × Array Inst} {B B' : ℕ} {c : List Inst} (h : HasCode P B c)
    (e : B = B') : HasCode P B' c := e ▸ h

/-- **The input body** writes the canonical initial configuration and reaches its `finish`. -/
theorem inputBodyG_emits (blk : Option Bool → Bool → List Bool) (w : ℕ)
    (hblk : ∀ v h, (blk v h).length = w) :
    Emits (inputBodyG blk) (BodySpec (inW blk) (fun _ R => 2 * R * (w + 1) + w + 5)) := by
  intro l
  obtain ⟨b, cb, hrb, hqb⟩ := word_emits (blk none false) (l ++ [Inst.finish]).length
    (l ++ [Inst.finish] ++ [Inst.finish])
  obtain ⟨z, cz, hrz, hqz⟩ := word_emits (blk (some false) false) (l ++ [Inst.finish]).length
    (l ++ [Inst.finish] ++ [Inst.finish] ++ cb)
  obtain ⟨o, co, hro, hqo⟩ := word_emits (blk (some true) false) (l ++ [Inst.finish]).length
    (l ++ [Inst.finish] ++ [Inst.finish] ++ cb ++ cz)
  obtain ⟨e, ct, hrt, hqt⟩ := inputTail_collect blk (l ++ [Inst.finish]).length
    (l ++ [Inst.finish] ++ Inst.nextInput b z o l.length :: (cb ++ cz ++ co))
  refine ⟨e, [Inst.finish, Inst.nextInput b z o l.length] ++ cb ++ cz ++ co ++ ct, ?_,
    fun P hP => ?_⟩
  · rw [inputBodyG_eq]
    simp only [runL_bind, runL_putI, runL_setI, hrb, hrz, hro]
    have e1 : l ++ [Inst.finish] ++ [Inst.finish] ++ cb ++ cz ++ co =
        l ++ [Inst.finish] ++ Inst.finish :: (cb ++ cz ++ co) := by simp
    rw [e1, set_mid, hrt]
    simp
  · have hfin : P.2[l.length]? = some .finish := hP.left.left.left.left.head
    have hN : P.2[(l ++ [Inst.finish]).length]? = some (.nextInput b z o l.length) := by
      have := hP.left.left.left.left.tail.head
      simpa using this
    have hb := hqb P (hP.left.left.left.right.cast (by simp))
    have hz := hqz P (hP.left.left.right.cast (by simp))
    have ho := hqo P (hP.left.right.cast (by simp))
    obtain ⟨right, hC, hb', hwb, hz', hwz, ho', hwo, center, hH, hrep⟩ :=
      hqt P (hP.right.cast (by simp))
    refine ⟨l.length, hfin, ?_⟩
    refine (((Seg.of_repeated hrep).comp (center_seg hblk hH hwb hwz hwo)).comp
      (right_seg hblk hC hN hb hz ho)).congr (fun _ _ => rfl) (fun _ R => ?_)
    show R * ((blk none false).length + 1) + 2 + (1 + w) + (R * (w + 1) + 2) ≤
      2 * R * (w + 1) + w + 5
    rw [hblk]
    have : 2 * R * (w + 1) = R * (w + 1) + R * (w + 1) := by ring
    omega

/-! ## From the initial configuration to the first halt -/

/-- The state right after normalization: the input and nothing else. -/
def St.init (x : List Bool) : St := ⟨x, x.length, 0, 0, 0, 0, 0, 0, []⟩

theorem St.init_wf (x : List Bool) : (St.init x).WF := by
  simp [St.init, St.WF]

theorem normalized_tape (x : List Bool) :
    partiallyNormalizedTape x x.length = tapeOf (cells (St.init x)) := by
  funext i
  unfold partiallyNormalizedTape tapeOf
  by_cases h1 : i = -1
  · simp [h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : 0 ≤ i ∧ i < (x.length : ℤ)
    · have h3 : 0 ≤ i ∧ i < ((cells (St.init x)).length : ℤ) := by simpa [St.init] using h2
      rw [if_pos h2, if_pos h3]
      congr 1
      have hj : i.toNat < x.length := by omega
      rw [List.getD_eq_getElem (cells (St.init x)) emptyCell (by simpa [St.init] using hj),
        cells_get]
      refine Cell.ext' ?_ (funext fun k => ?_) ?_
      · show some (x.getD i.toNat false) = x[i.toNat]?
        rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
      · cases k <;> simp [emptyCell, cellAt, St.flag, St.init]
      · show (none : Option Bool) = ([] : List Bool)[i.toNat]?
        simp
    · have h3 : ¬ (0 ≤ i ∧ i < ((cells (St.init x)).length : ℤ)) := by simpa [St.init] using h2
      rw [if_neg h2, if_neg h2, if_neg h3]

/-- **Normalization.** After exactly `2n + 4` transitions the machine scans cell `0` at its
program entry, on the work-region tape of the initial state. -/
theorem normalize_steps (P : ℕ × Array Inst) (x : List Bool) :
    Steps P ((build P).init x)
      (⟨tapeOf (cells (St.init x)), 0, .scan (addr P.2 P.1)⟩ : (build P).Cfg)
      (2 * x.length + 4) := by
  have hA : Steps P ((build P).init x)
      (⟨partiallyNormalizedTape x x.length, (x.length : ℤ), .normalize⟩ : (build P).Cfg)
      (x.length + 2) := by
    refine ⟨run_normalizes_input P x x.length le_rfl, fun t ht => ?_⟩
    rcases t with _ | _ | k
    · show (State.start : State P.2.size) ≠ State.done
      simp
    · rw [MTM.run_succ, MTM.run_zero, start_to_mark]
      simp
    · have := run_normalizes_input P x k (by omega)
      rw [show k + 1 + 1 = k + 2 from rfl, this]
      simp
  have hblank : partiallyNormalizedTape x x.length (x.length : ℤ) = .blank := by
    unfold partiallyNormalizedTape
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hB := Steps.one_same (P := P) (partiallyNormalizedTape x x.length) (x.length : ℤ)
    .normalize (.ret (addr P.2 P.1)) .L (by rw [hblank]; rfl) (by simp)
  have e : (x.length : ℤ) + Mv.L.shift = (x.length : ℤ) - 1 := by simp [Mv.shift]; ring
  rw [e, normalized_tape] at hB
  have hC := ret_walk (P := P) (addr P.2 P.1) (cells (St.init x)) x.length (by simp [St.init])
  rw [normalized_tape] at hA
  exact ((hA.trans hB).trans hC).cast (by omega)

/-- The whole assembled program: stages, then the body, up to the `finish` instruction. -/
theorem assemble_spec (cs : List ℕ) {body : Asm ℕ} {W : List Bool → ℕ → List Bool}
    {cnt : List Bool → ℕ → ℕ} (hbody : Emits body (BodySpec W cnt)) :
    ∃ fin, (assemble cs body).2[fin]? = some .finish ∧ ∀ s : St, s.acc = 0 →
      ∃ s', Exec (assemble cs body) (assemble cs body).1 s fin s'
          (ic cs s.x.length + cnt s.x (hv cs s.x.length)) ∧
        s'.out = s.out ++ W s.x (hv cs s.x.length) ∧
        s'.len ≤ max (max s.len (hb cs s.x.length))
          (s.out.length + (W s.x (hv cs s.x.length)).length) := by
  have hE : Emits (body >>= fun start => cs.foldlM horner start) (fun P e =>
      ∃ fin, P.2[fin]? = some .finish ∧ ∀ s : St, s.acc = 0 →
        ∃ s', Exec P e s fin s' (ic cs s.x.length + cnt s.x (hv cs s.x.length)) ∧
          s'.out = s.out ++ W s.x (hv cs s.x.length) ∧
          s'.len ≤ max (max s.len (hb cs s.x.length))
            (s.out.length + (W s.x (hv cs s.x.length)).length)) :=
    Emits.bind hbody (fun start => stages_emits cs start) (fun P start e hB hS => by
      obtain ⟨fin, hfin, hseg⟩ := hB
      refine ⟨fin, hfin, fun s hs => ?_⟩
      obtain ⟨s1, he1, hx1, ha1, ho1, hl1⟩ := hS s hs
      obtain ⟨s2, he2, hx2, ha2, ho2, hl2⟩ := hseg s1
      rw [hx1, ha1] at he2 ho2 hl2
      refine ⟨s2, he1.trans he2, ?_, ?_⟩
      · rw [ho2, ho1]
      · rw [ho1] at hl2
        omega)
  obtain ⟨e, code, hr, hq⟩ := hE []
  have hP1 : (assemble cs body).1 = e := congrArg Prod.fst hr
  have hP2 : (assemble cs body).2.toList = code := by
    have := congrArg Prod.snd hr
    simpa using this
  have hcode : HasCode (assemble cs body) 0 code := by
    intro j hj
    rw [Nat.zero_add]
    have h1 : (assemble cs body).2[j]? = (assemble cs body).2.toList[j]? := by simp
    rw [h1]
    simp only [hP2]
    exact List.getElem?_eq_getElem hj
  rw [hP1]
  exact hq _ hcode

/-- **First-halt output of an assembled writer.** On every input `x` the machine
`build (assemble cs body)` halts for the first time with the body's word for the accumulator
value `hv cs |x|` on its tape, followed by a blank, within the stated number of transitions. -/
theorem assemble_outputs (cs : List ℕ) {body : Asm ℕ} {W : List Bool → ℕ → List Bool}
    {cnt : List Bool → ℕ → ℕ} (hbody : Emits body (BodySpec W cnt)) (x : List Bool) :
    (build (assemble cs body)).Outputs x (W x (hv cs x.length))
      (2 * x.length + 4 + (ic cs x.length + cnt x (hv cs x.length)) *
        (2 * (x.length + hb cs x.length + (W x (hv cs x.length)).length) + 4) +
        ((W x (hv cs x.length)).length + 1)) := by
  obtain ⟨fin, hfin, hrun⟩ := assemble_spec cs hbody
  obtain ⟨s', he, hout, hlen⟩ := hrun (St.init x) rfl
  obtain ⟨hw', -, k, hsteps, hk⟩ := he (St.init_wf x)
  obtain ⟨T, hfinal, hT1, hT2⟩ := finish_state hfin s' hw'
  have hout' : s'.out = W x (hv cs x.length) := by rw [hout]; rfl
  have hall := ((normalize_steps (assemble cs body) x).trans hsteps).trans hfinal
  have hlen' : s'.len ≤ x.length + hb cs x.length + (W x (hv cs x.length)).length := by
    have : s'.len ≤ max (max x.length (hb cs x.length))
        (0 + (W x (hv cs x.length)).length) := hlen
    omega
  have hk' : k ≤ (ic cs x.length + cnt x (hv cs x.length)) *
      (2 * (x.length + hb cs x.length + (W x (hv cs x.length)).length) + 4) :=
    le_trans hk (Nat.mul_le_mul_left _ (by omega))
  refine ⟨2 * x.length + 4 + k + (s'.out.length + 1), ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hout']
    exact Nat.add_le_add (Nat.add_le_add_left hk' _) le_rfl
  · rw [hall.1]
    exact Or.inl rfl
  · intro t ht h
    exact hall.2 t ht (h.elim id id)
  · intro i hi
    rw [hall.1]
    rw [← hout'] at hi ⊢
    exact hT1 i hi
  · rw [hall.1, ← hout']
    exact hT2

end PVNP.TwoPhasePolynomialWriter
