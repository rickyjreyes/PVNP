import PVNP.WCCDSweep

/-!
# D-1: exact semantics of each instruction of the WCCD sweep program

For every instruction of `PVNP.WCCDSweep.prog` we compute the data list after
one round trip, the decisive buffer flags, the successor instruction and the
exact TM cost `2ℓ + 2 (+1)`.
-/

namespace PVNP.Discrete.WCCDSweep

open PVNP.Discrete PVNP.Discrete.Sweep

variable {d : ℕ} (A : WCCD d)

abbrev L (A : WCCD d) := List (Cell A.S d)

/-! ### Generic scan lemmas -/

section Generic
variable {D B : Type}

theorem fscan_map_of (f : B → D → D × B) (g : D → D) (hf : ∀ b a, f b a = (g a, b)) :
    ∀ (b : B) (l : List D), fscan f b l = (l.map g, b)
  | b, [] => rfl
  | b, a :: l => by simp [fscan, hf, fscan_map_of f g hf b l]

theorem bscan_id_of (f : B → D → D × B) (hf : ∀ b a, f b a = (a, b)) :
    ∀ (b : B) (l : List D), bscan f b l = (l, b)
  | b, [] => rfl
  | b, a :: l => by simp [bscan, hf, bscan_id_of f hf b l]

end Generic

theorem trip_eq (i : Ins d) (l : L A) :
    (prog A).trip i l = bscan (bwd A i) (fscan (fwd A i) (buf0 A) l).2
      ((fscan (fwd A i) (buf0 A) l).1 ++ (ext A i (fscan (fwd A i) (buf0 A) l).2).toList) := rfl

theorem tripCost_eq (i : Ins d) (l : L A) :
    (prog A).tripCost i l =
      2 * l.length + 2 + (ext A i (fscan (fwd A i) (buf0 A) l).2).toList.length := rfl

theorem stepP_of {i i' : Ins d} {l l' : L A}
    (h1 : (prog A).next i ((prog A).trip i l).2 = .inl i') (h2 : ((prog A).trip i l).1 = l') :
    (prog A).stepP (i, l) = .inl (i', l') := by
  simp only [Prog.stepP, h1, h2]

/-- A pure-map instruction. -/
theorem trip_map {i : Ins d} (g : Cell A.S d → Cell A.S d)
    (hf : ∀ b a, fwd A i b a = (g a, b)) (hb : ∀ b a, bwd A i b a = (a, b))
    (he : ∀ b, ext A i b = none) (l : L A) :
    (prog A).trip i l = (l.map g, buf0 A) ∧ (prog A).tripCost i l = 2 * l.length + 2 := by
  have hs := fscan_map_of (fwd A i) g hf (buf0 A) l
  refine ⟨?_, ?_⟩
  · rw [trip_eq, hs]
    simp only [he, Option.toList_none, List.append_nil]
    exact bscan_id_of _ hb _ _
  · rw [tripCost_eq, hs]; simp [he]

/-! ### Pure-map instructions -/

def gIgm (a : Cell A.S d) : Cell A.S d := {a with gm := a.fst, rp := a.fst, ptr := a.fst}
def gCopy (k : Fin (d + 1)) (a : Cell A.S d) : Cell A.S d := {a with bb := a.ref k.castSucc}
def gRset (k : Fin (d + 1)) (a : Cell A.S d) : Cell A.S d :=
  {a with ref := Function.update a.ref k.succ a.mv, mv := a.fst}
def gXfin (a : Cell A.S d) : Cell A.S d := {a with cur := cval A a}
def gSpread (a : Cell A.S d) : Cell A.S d := {a with win := fun _ => a.cur}
def gApp (a : Cell A.S d) : Cell A.S d := {a with cur := A.rule fun v => a.win (Fin.cons v.1 v.2)}
def gGrst (a : Cell A.S d) : Cell A.S d := {a with rp := a.fst}

theorem step_igm (l : L A) :
    (prog A).stepP (.igm, l) = .inl (.r0, l.map (gIgm A)) ∧
      (prog A).tripCost .igm l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .igm) (gIgm A) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  exact ⟨stepP_of A (by rw [h1]; rfl) (by rw [h1]), h2⟩

theorem step_rcopy (k : Fin (d + 1)) (l : L A) :
    (prog A).stepP (.rcopy k, l) = .inl (.rchk k, l.map (gCopy A k)) ∧
      (prog A).tripCost (.rcopy k) l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .rcopy k) (gCopy A k) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  exact ⟨stepP_of A (by rw [h1]; rfl) (by rw [h1]), h2⟩

theorem step_lcopy (k : Fin (d + 1)) (l : L A) :
    (prog A).stepP (.lcopy k, l) = .inl (.lchk k, l.map (gCopy A k)) ∧
      (prog A).tripCost (.lcopy k) l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .lcopy k) (gCopy A k) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  exact ⟨stepP_of A (by rw [h1]; rfl) (by rw [h1]), h2⟩

theorem step_rcopyR (k : Fin (d + 1)) (l : L A) :
    (prog A).stepP (.rcopyR k, l) = .inl (.rchkR k, l.map (gCopy A k)) ∧
      (prog A).tripCost (.rcopyR k) l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .rcopyR k) (gCopy A k) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  exact ⟨stepP_of A (by rw [h1]; rfl) (by rw [h1]), h2⟩

theorem step_rset (k : Fin (d + 1)) (l : L A) :
    (prog A).stepP (.rset k, l) =
      .inl ((match nextAxis k with | some k' => .rcopy k' | none => .xfin), l.map (gRset A k)) ∧
      (prog A).tripCost (.rset k) l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .rset k) (gRset A k) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  refine ⟨stepP_of A ?_ (by rw [h1]), h2⟩
  rw [h1]
  show next A (.rset k) (buf0 A) = _
  simp only [next]
  cases nextAxis k <;> rfl

theorem step_xfin (l : L A) :
    (prog A).stepP (.xfin, l) = .inl (.chk, l.map (gXfin A)) ∧
      (prog A).tripCost .xfin l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .xfin) (gXfin A) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  exact ⟨stepP_of A (by rw [h1]; rfl) (by rw [h1]), h2⟩

theorem step_spread (l : L A) :
    (prog A).stepP (.spread, l) = .inl (.lcopy 0, l.map (gSpread A)) ∧
      (prog A).tripCost .spread l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .spread) (gSpread A) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  exact ⟨stepP_of A (by rw [h1]; rfl) (by rw [h1]), h2⟩

theorem step_app (l : L A) :
    (prog A).stepP (.app, l) = .inl (.rnd, l.map (gApp A)) ∧
      (prog A).tripCost .app l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .app) (gApp A) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  exact ⟨stepP_of A (by rw [h1]; rfl) (by rw [h1]), h2⟩

theorem step_grst (l : L A) :
    (prog A).stepP (.grst, l) = .inl (.r0, l.map (gGrst A)) ∧
      (prog A).tripCost .grst l = 2 * l.length + 2 := by
  obtain ⟨h1, h2⟩ := trip_map A (i := .grst) (gGrst A) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) l
  exact ⟨stepP_of A (by rw [h1]; rfl) (by rw [h1]), h2⟩

/-! ### Marker shifts -/

/-- `bb` moved one cell to the left. -/
def bbLeft (l : L A) : L A :=
  l.mapIdx fun i a => {a with bb := if h : i + 1 < l.length then l[i + 1].bb else false}

theorem bbLeft_length (l : L A) : (bbLeft A l).length = l.length := by simp [bbLeft]

theorem bbLeft_get (l : L A) (i : ℕ) (h : i < (bbLeft A l).length) :
    (bbLeft A l)[i] = {l[i]'(by simpa [bbLeft] using h) with
      bb := if h' : i + 1 < l.length then l[i + 1].bb else false} := by
  simp [bbLeft]

/-- Backward scan of the `bb`-left transducer. -/
theorem bscan_bbLeft (l : L A) (b : Buf A.S d) (hb : b.f1 = false)
    (bw : Buf A.S d → Cell A.S d → Cell A.S d × Buf A.S d)
    (hbw : ∀ b a, bw b a = ({a with bb := b.f1}, {b with f1 := a.bb})) :
    (bscan bw b l).1 = bbLeft A l := by
  apply List.ext_getElem (by simp [bscan_length, bbLeft_length])
  intro i h1 h2
  rw [bscan_getElem bw b l i (by simpa [bscan_length] using h1), bbLeft_get, hbw]
  congr 1
  by_cases hi : i + 1 < l.length
  · rw [dif_pos hi, bbuf_pred bw b l i hi, hbw]
  · rw [dif_neg hi, bbuf_last bw b l i (by omega), hb]

theorem step_mov {i : Ins d} {i' : Ins d}
    (hf : ∀ b a, fwd A i b a = (a, b)) (he : ∀ b, ext A i b = none)
    (hbw : ∀ b a, bwd A i b a = ({a with bb := b.f1}, {b with f1 := a.bb}))
    (hn : ∀ b, next A i b = .inl i') (l : L A) :
    (prog A).stepP (i, l) = .inl (i', bbLeft A l) ∧ (prog A).tripCost i l = 2 * l.length + 2 := by
  have hs := fscan_map_of (fwd A i) id (by simpa using hf) (buf0 A) l
  simp only [List.map_id] at hs
  refine ⟨stepP_of A (hn _) ?_, ?_⟩
  · rw [trip_eq, hs]
    simp only [he, Option.toList_none, List.append_nil]
    exact bscan_bbLeft A l (buf0 A) rfl (bwd A i) hbw
  · rw [tripCost_eq, hs]; simp [he]

theorem step_rmov (k : Fin (d + 1)) (l : L A) :
    (prog A).stepP (.rmov k, l) = .inl (.rchk k, bbLeft A l) ∧
      (prog A).tripCost (.rmov k) l = 2 * l.length + 2 :=
  step_mov A (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) l

theorem step_lmov (k : Fin (d + 1)) (l : L A) :
    (prog A).stepP (.lmov k, l) = .inl (.lchk k, bbLeft A l) ∧
      (prog A).tripCost (.lmov k) l = 2 * l.length + 2 :=
  step_mov A (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) l

theorem step_rmovR (k : Fin (d + 1)) (l : L A) :
    (prog A).stepP (.rmovR k, l) = .inl (.rchkR k, bbLeft A l) ∧
      (prog A).tripCost (.rmovR k) l = 2 * l.length + 2 :=
  step_mov A (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) l

/-- `rp` moved one cell to the right. -/
def rpRight (l : L A) : L A :=
  l.mapIdx fun i a => {a with rp := if h : 0 < i ∧ i - 1 < l.length then l[i - 1].rp else false}

theorem rpRight_length (l : L A) : (rpRight A l).length = l.length := by simp [rpRight]

theorem step_rnd (l : L A) :
    (prog A).stepP (.rnd, l) = .inl (.chk, rpRight A l) ∧
      (prog A).tripCost .rnd l = 2 * l.length + 2 := by
  have hfs : (fscan (fwd A .rnd) (buf0 A) l).1 = rpRight A l := by
    apply List.ext_getElem (by simp [fscan_length, rpRight_length])
    intro i h1 h2
    have hi : i < l.length := by simpa [fscan_length] using h1
    rw [fscan_getElem (fwd A .rnd) (buf0 A) l i hi]
    simp only [rpRight, List.getElem_mapIdx]
    show ({l[i] with rp := (fbuf (fwd A .rnd) (buf0 A) l i).f1} : Cell A.S d) = _
    congr 1
    cases i with
    | zero => simp [fbuf_zero, buf0]
    | succ i =>
      rw [fbuf_succ _ _ _ i (by omega)]
      have h3 : 0 < i + 1 ∧ i + 1 - 1 < l.length := by omega
      rw [dif_pos h3]
      simp [fwd]
  refine ⟨stepP_of A (by rfl) ?_, ?_⟩
  · rw [trip_eq]
    simp only [show ext A .rnd (fscan (fwd A .rnd) (buf0 A) l).2 = none from rfl,
      Option.toList_none, List.append_nil, hfs]
    exact (bscan_id_of _ (fun _ _ => rfl) _ _).symm ▸ rfl
  · rw [tripCost_eq]; simp [ext]

/-! ### Generic helpers for buffered passes -/

/-- An instruction whose backward pass is the identity. -/
theorem trip_fwd_only {i : Ins d} (hb : ∀ b a, bwd A i b a = (a, b)) (l : L A) :
    (prog A).trip i l =
      ((fscan (fwd A i) (buf0 A) l).1 ++ (ext A i (fscan (fwd A i) (buf0 A) l).2).toList,
        (fscan (fwd A i) (buf0 A) l).2) := by
  rw [trip_eq, bscan_id_of (bwd A i) hb]

/-- A backward pass whose buffer never changes acts as a map. -/
theorem bscan_const_of {D B : Type} (f : B → D → D × B) (hf : ∀ b a, (f b a).2 = b) :
    ∀ (b : B) (l : List D), bscan f b l = (l.map fun a => (f b a).1, b)
  | b, [] => rfl
  | b, a :: l => by
    simp only [bscan]
    rw [bscan_const_of f hf b l]
    simp [hf]

theorem decide_iff_eq {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := decide_eq_decide.2 h

/-! ### Initialization -/

def setI0 (j : ℕ) (a : Cell A.S d) : Cell A.S d := {a with cnt := true, fst := decide (j = 0)}

def gI0 (l : L A) : L A := l.mapIdx (setI0 A)

theorem gI0_length (l : L A) : (gI0 A l).length = l.length := by simp [gI0]

theorem step_i0 (l : L A) :
    (prog A).stepP (.i0, l) = .inl (.iext 0, gI0 A l) ∧
      (prog A).tripCost .i0 l = 2 * l.length + 2 := by
  have hbuf : ∀ k, k ≤ l.length → (fbuf (fwd A .i0) (buf0 A) l k).f1 = decide (0 < k) := by
    intro k hk
    induction k with
    | zero => simp [fbuf_zero, buf0]
    | succ k ih => rw [fbuf_succ _ _ _ k (by omega)]; simp [fwd]
  have hfs : (fscan (fwd A .i0) (buf0 A) l).1 = gI0 A l := by
    apply List.ext_getElem (by simp [fscan_length, gI0])
    intro j h1 h2
    have hj : j < l.length := by simpa [fscan_length] using h1
    rw [fscan_getElem _ _ _ j hj]
    simp only [gI0, List.getElem_mapIdx, setI0, fwd]
    rw [hbuf j (by omega)]
    cases j <;> simp
  have ht := trip_fwd_only A (i := .i0) (fun _ _ => rfl) l
  refine ⟨stepP_of A rfl ?_, ?_⟩
  · rw [ht, hfs]; simp [ext]
  · rw [tripCost_eq]; simp [ext]

/-- The cell appended by `iext`. -/
def extCell (empty : Bool) : Cell A.S d := {dflt A with cnt := true, fst := empty}

def iextNext (r : Fin 3) : Ins d :=
  if h : r.val = 2 then .igm else .iext ⟨r.val + 1, by have := r.isLt; omega⟩

theorem step_iext (r : Fin 3) (l : L A) :
    (prog A).stepP (.iext r, l) = .inl (iextNext r, l ++ [extCell A (decide (l.length = 0))]) ∧
      (prog A).tripCost (.iext r) l = 2 * l.length + 3 := by
  have hfin : ∀ (b : Buf A.S d) (l : L A),
      fscan (fwd A (.iext r)) b l = (l, if l = [] then b else {b with f1 := true}) := by
    intro b l
    induction l generalizing b with
    | nil => simp [fscan]
    | cons a l ih =>
      simp only [fscan, fwd, ih]
      cases l <;> simp
  have hext : ext A (.iext r) (fscan (fwd A (.iext r)) (buf0 A) l).2 =
      some (extCell A (decide (l.length = 0))) := by
    rw [hfin]
    cases l with
    | nil => rfl
    | cons a l => simp [ext, extCell, buf0]
  have ht := trip_fwd_only A (i := .iext r) (fun _ _ => rfl) l
  refine ⟨stepP_of A ?_ ?_, ?_⟩
  · change next A (.iext r) ((prog A).trip (.iext r) l).2 = _
    simp only [next, iextNext]
    split_ifs <;> rfl
  · rw [ht, hext, hfin]; simp
  · rw [tripCost_eq, hext]; simp

/-! ### Reference construction -/

def setR0 (j : ℕ) (a : Cell A.S d) : Cell A.S d :=
  {a with ref := fun k => decide (k = 0) && decide (j = 1), mv := a.fst}

def gR0 (l : L A) : L A := l.mapIdx (setR0 A)

theorem gR0_length (l : L A) : (gR0 A l).length = l.length := by simp [gR0]

theorem step_r0 (l : L A) (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0)) :
    (prog A).stepP (.r0, l) = .inl (.rcopy 0, gR0 A l) ∧
      (prog A).tripCost .r0 l = 2 * l.length + 2 := by
  have hbuf : ∀ k, k ≤ l.length → (fbuf (fwd A .r0) (buf0 A) l k).f1 = decide (k = 1) := by
    intro k hk
    induction k with
    | zero => simp [fbuf_zero, buf0]
    | succ k ih =>
      rw [fbuf_succ _ _ _ k (by omega)]
      simp only [fwd]
      rw [hfst k (by omega)]
      simp
  have hfs : (fscan (fwd A .r0) (buf0 A) l).1 = gR0 A l := by
    apply List.ext_getElem (by simp [fscan_length, gR0])
    intro j h1 h2
    have hj : j < l.length := by simpa [fscan_length] using h1
    rw [fscan_getElem _ _ _ j hj]
    simp only [gR0, List.getElem_mapIdx, setR0, fwd]
    rw [hbuf j (by omega)]
  have ht := trip_fwd_only A (i := .r0) (fun _ _ => rfl) l
  refine ⟨stepP_of A rfl ?_, ?_⟩
  · rw [ht, hfs]; simp [ext]
  · rw [tripCost_eq]; simp [ext]

/-- The forward buffer of `rchk` once the pass is known to continue. -/
def rchkBuf (v : Bool) : Buf A.S d := {buf0 A with f1 := false, f2 := v}

def doneBuf : Buf A.S d := {buf0 A with f1 := true, f2 := false}

theorem step_rchk_done (k : Fin (d + 1)) (l : L A) (hl : 0 < l.length)
    (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0)) (hbb : l[0].bb = true) :
    (prog A).stepP (.rchk k, l) = .inl (.rnext k, l) ∧
      (prog A).tripCost (.rchk k) l = 2 * l.length + 2 := by
  have hbuf : ∀ j, 1 ≤ j → j ≤ l.length → fbuf (fwd A (.rchk k)) (buf0 A) l j = doneBuf A := by
    intro j hj1 hj2
    induction j with
    | zero => omega
    | succ j ih =>
      rw [fbuf_succ _ _ _ j (by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        simp [fwd, fbuf_zero, hfst 0 hl, hbb, doneBuf]
      · rw [ih (by omega) (by omega)]
        simp [fwd, hfst j (by omega), hj0, doneBuf]
  have hcells : (fscan (fwd A (.rchk k)) (buf0 A) l).1 = l := by
    apply List.ext_getElem (by simp [fscan_length])
    intro j h1 h2
    rw [fscan_getElem _ _ _ j h2]
    by_cases hj0 : j = 0
    · subst hj0; simp [fwd, fbuf_zero, hfst 0 hl, hbb]
    · rw [hbuf j (by omega) (by omega)]; simp [fwd, hfst j h2, hj0, doneBuf]
  have hfin : (fscan (fwd A (.rchk k)) (buf0 A) l).2 = doneBuf A := by
    rw [fscan_snd, hbuf _ (by omega) le_rfl]
  have hext : ext A (.rchk k) (fscan (fwd A (.rchk k)) (buf0 A) l).2 = none := by
    rw [hfin]; rfl
  have ht := trip_fwd_only A (i := .rchk k) (fun _ _ => rfl) l
  refine ⟨stepP_of A ?_ ?_, ?_⟩
  · rw [ht, hfin]; rfl
  · rw [ht, hext, hcells]; simp
  · rw [tripCost_eq, hext]; simp

/-- `mv` moved one cell to the right; a new cell is appended if `mv` leaves
the segment. -/
def setMv (l : L A) (j : ℕ) (a : Cell A.S d) : Cell A.S d :=
  {a with mv := if h : 0 < j ∧ j - 1 < l.length then l[j - 1].mv else false}

def mvRight (l : L A) (hl : 0 < l.length) : L A :=
  l.mapIdx (setMv A l) ++ (if l[l.length - 1].mv then [{dflt A with mv := true}] else [])

theorem step_rchk_move (k : Fin (d + 1)) (l : L A) (hl : 0 < l.length)
    (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0)) (hbb : l[0].bb = false) :
    (prog A).stepP (.rchk k, l) = .inl (.rmov k, mvRight A l hl) ∧
      (prog A).tripCost (.rchk k) l =
        2 * l.length + 2 + (if l[l.length - 1].mv then 1 else 0) := by
  have hbuf : ∀ j, j ≤ l.length → fbuf (fwd A (.rchk k)) (buf0 A) l j =
      rchkBuf A (if h : 0 < j ∧ j - 1 < l.length then l[j - 1].mv else false) := by
    intro j hj
    induction j with
    | zero => simp [fbuf_zero, buf0, rchkBuf]
    | succ j ih =>
      rw [fbuf_succ _ _ _ j (by omega), ih (by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [fwd, hfst 0 hl, hbb, rchkBuf]
        have h1 : 0 < 0 + 1 ∧ 0 + 1 - 1 < l.length := by omega
        rw [dif_pos h1]
        simp
      · simp [fwd, hfst j (by omega), hj0, rchkBuf, show 0 < j + 1 ∧ j < l.length by omega]
  have hcells : (fscan (fwd A (.rchk k)) (buf0 A) l).1 = l.mapIdx (setMv A l) := by
    apply List.ext_getElem (by simp [fscan_length])
    intro j h1 h2
    have hj : j < l.length := by simpa using h2
    rw [fscan_getElem _ _ _ j hj, hbuf j (by omega), List.getElem_mapIdx]
    by_cases hj0 : j = 0
    · subst hj0; simp [fwd, hfst 0 hl, hbb, setMv, rchkBuf]
    · simp [fwd, hfst j hj, hj0, setMv, rchkBuf]
  have hfin : (fscan (fwd A (.rchk k)) (buf0 A) l).2 = rchkBuf A l[l.length - 1].mv := by
    rw [fscan_snd, hbuf _ le_rfl, dif_pos ⟨hl, by omega⟩]
  have hext : ext A (.rchk k) (fscan (fwd A (.rchk k)) (buf0 A) l).2 =
      if l[l.length - 1].mv then some {dflt A with mv := true} else none := by
    rw [hfin]; simp [ext, rchkBuf]
  have ht := trip_fwd_only A (i := .rchk k) (fun _ _ => rfl) l
  refine ⟨stepP_of A ?_ ?_, ?_⟩
  · rw [ht, hfin]; rfl
  · rw [ht, hext, hcells, mvRight]
    split_ifs <;> simp
  · rw [tripCost_eq, hext]
    split_ifs <;> simp

/-! ### Outer-loop pointer -/

def setPtr (t : ℕ) (j : ℕ) (a : Cell A.S d) : Cell A.S d := {a with ptr := decide (j = t)}

theorem step_rnext (k : Fin (d + 1)) (l : L A) (M p : ℕ) (hl : 0 < l.length)
    (hM : M ≤ l.length) (hp : p < M)
    (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0))
    (hcnt : ∀ j (h : j < l.length), l[j].cnt = decide (j < M))
    (hptr : ∀ j (h : j < l.length), l[j].ptr = decide (j = p)) :
    (prog A).stepP (.rnext k, l) =
      .inl ((if p + 1 = M then .rset k else .rcopy k),
        l.mapIdx (setPtr A (if p + 1 = M then 0 else p + 1))) ∧
      (prog A).tripCost (.rnext k) l = 2 * l.length + 2 := by
  have hbuf : ∀ j, j ≤ l.length → (fbuf (fwd A (.rnext k)) (buf0 A) l j).f1 =
      decide (p < j ∧ (p + 1 = M ∨ j = p + 1)) := by
    intro j hj
    induction j with
    | zero => simp [fbuf_zero, buf0]
    | succ j ih =>
      rw [fbuf_succ _ _ _ j (by omega)]
      simp only [fwd]
      rw [ih (by omega), hptr j (by omega), hcnt j (by omega)]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not]
      omega
  have hfin : (fscan (fwd A (.rnext k)) (buf0 A) l).2.f1 = decide (p + 1 = M) := by
    rw [fscan_snd, hbuf _ le_rfl]
    apply decide_iff_eq; omega
  have hcells : (fscan (fwd A (.rnext k)) (buf0 A) l).1 =
      l.mapIdx (fun j a => {a with ptr := decide (j = p + 1 ∧ p + 1 < M)}) := by
    apply List.ext_getElem (by simp [fscan_length])
    intro j h1 h2
    have hj : j < l.length := by simpa using h2
    rw [fscan_getElem _ _ _ j hj, List.getElem_mapIdx]
    simp only [fwd]
    rw [hbuf j (by omega), hcnt j hj]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hext : ext A (.rnext k) (fscan (fwd A (.rnext k)) (buf0 A) l).2 = none := rfl
  have htrip : (prog A).trip (.rnext k) l =
      (l.mapIdx (setPtr A (if p + 1 = M then 0 else p + 1)),
        (fscan (fwd A (.rnext k)) (buf0 A) l).2) := by
    rw [trip_eq, hext]
    simp only [Option.toList_none, List.append_nil]
    rw [bscan_const_of (bwd A (.rnext k)) (fun _ _ => rfl), hcells]
    refine Prod.ext ?_ rfl
    apply List.ext_getElem (by simp)
    intro j h1 h2
    have hj : j < l.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_mapIdx, bwd, setPtr, hfin, hfst j hj]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    split_ifs with h3 <;> omega
  refine ⟨stepP_of A ?_ ?_, by rw [tripCost_eq, hext]; simp⟩
  · rw [htrip]
    show next A (.rnext k) _ = _
    simp only [next, hfin]
    by_cases h3 : p + 1 = M <;> simp [h3]
  · rw [htrip]

theorem fscan_fst_of_id {D B : Type} (f : B → D → D × B) (hf : ∀ b a, (f b a).1 = a) :
    ∀ (b : B) (l : List D), (fscan f b l).1 = l
  | b, [] => rfl
  | b, a :: l => by simp [fscan, hf, fscan_fst_of_id f hf _ l]

/-! ### Output check -/

/-- The answer of the cyclic array (blank exterior included). -/
def arrAns (l : L A) : Option Bool :=
  answerOf (A.acc A.blank || decide (∃ i, ∃ h : i < l.length, A.acc l[i].cur = true))
    (A.rej A.blank || decide (∃ i, ∃ h : i < l.length, A.rej l[i].cur = true))

theorem step_chk (l : L A) (G t : ℕ) (hlen : G + 1 < l.length) (ht : t ≤ G)
    (hgm : ∀ j (h : j < l.length), l[j].gm = decide (j ≤ G))
    (hrp : ∀ j (h : j < l.length), l[j].rp = decide (j = t)) :
    (prog A).stepP (.chk, l) =
      (match arrAns A l with
        | some b => .inr (b, l)
        | none => .inl ((if t = G then .ggm else .spread), l)) ∧
      (prog A).tripCost .chk l = 2 * l.length + 2 := by
  have hbuf : ∀ j (hj : j ≤ l.length),
      (fbuf (fwd A .chk) (buf0 A) l j).f1 = decide (∃ i, ∃ h : i < j, A.acc (l[i]'(by omega)).cur = true) ∧
      (fbuf (fwd A .chk) (buf0 A) l j).f2 = decide (∃ i, ∃ h : i < j, A.rej (l[i]'(by omega)).cur = true) ∧
      (fbuf (fwd A .chk) (buf0 A) l j).f3 = decide (0 < j ∧ j - 1 = t) ∧
      (fbuf (fwd A .chk) (buf0 A) l j).f4 = decide (t + 1 < j ∧ t = G) := by
    intro j hj
    induction j with
    | zero => simp [fbuf_zero, buf0]
    | succ j ih =>
      obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
      rw [fbuf_succ _ _ _ j (by omega)]
      simp only [fwd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [i1]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨i, hi, h⟩ | h)
          · exact ⟨i, by omega, h⟩
          · exact ⟨j, by omega, h⟩
        · rintro ⟨i, hi, h⟩
          by_cases hij : i < j
          · exact Or.inl ⟨i, hij, h⟩
          · right; have : i = j := by omega
            subst this; exact h
      · rw [i2]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨i, hi, h⟩ | h)
          · exact ⟨i, by omega, h⟩
          · exact ⟨j, by omega, h⟩
        · rintro ⟨i, hi, h⟩
          by_cases hij : i < j
          · exact Or.inl ⟨i, hij, h⟩
          · right; have : i = j := by omega
            subst this; exact h
      · rw [hrp j (by omega)]
        apply decide_iff_eq; omega
      · rw [i4, i3, hgm j (by omega)]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not]
        omega
  have hcells : (fscan (fwd A .chk) (buf0 A) l).1 = l := fscan_fst_of_id _ (fun _ _ => rfl) _ _
  have hb := hbuf l.length le_rfl
  have hf3 : (fbuf (fwd A .chk) (buf0 A) l l.length).f3 = false := by
    rw [hb.2.2.1]; simp only [decide_eq_false_iff_not]; omega
  have hf4 : (fbuf (fwd A .chk) (buf0 A) l l.length).f4 = decide (t = G) := by
    rw [hb.2.2.2]; apply decide_iff_eq; omega
  have ht' := trip_fwd_only A (i := .chk) (fun _ _ => rfl) l
  rw [hcells, fscan_snd] at ht'
  simp only [show ∀ b, ext A .chk b = none from fun _ => rfl, Option.toList_none,
    List.append_nil] at ht'
  have hnext : (prog A).next .chk (fbuf (fwd A .chk) (buf0 A) l l.length) =
      (match arrAns A l with
        | some b => .inr b
        | none => .inl (if t = G then .ggm else .spread)) := by
    change next A .chk _ = _
    simp only [next, arrAns, answerOf, hb.1, hb.2.1, hf3, hf4, Bool.or_false]
    split_ifs <;> simp_all
  refine ⟨?_, by rw [tripCost_eq]; simp [ext]⟩
  simp only [Prog.stepP, ht']
  rw [hnext]
  cases arrAns A l <;> rfl

/-! ### Window rotations -/

theorem bscan_absorb {D B : Type} (f : B → D → D × B) (b : B) (hf : ∀ a, f b a = (a, b)) :
    ∀ l : List D, bscan f b l = (l, b)
  | [] => rfl
  | a :: l => by simp only [bscan]; rw [bscan_absorb f b hf l]; simp [hf]

/-- Buffer of `lchk` after the first cell. -/
def lchkBuf (v : Bool) (w : Nb d → A.S) : Buf A.S d := {buf0 A with f1 := v, w := w}

theorem lchk_fbuf (k : Fin (d + 1)) (l : L A) (hl : 0 < l.length)
    (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0)) :
    ∀ j, 1 ≤ j → j ≤ l.length → fbuf (fwd A (.lchk k)) (buf0 A) l j = lchkBuf A l[0].bb l[0].win := by
  intro j hj1 hj2
  induction j with
  | zero => omega
  | succ j ih =>
    rw [fbuf_succ _ _ _ j (by omega)]
    by_cases hj0 : j = 0
    · subst hj0
      simp [fwd, fbuf_zero, hfst 0 hl, lchkBuf]
    · rw [ih (by omega) (by omega)]
      simp [fwd, hfst j (by omega), hj0]

/-- Window tracks: take `w` on the tracks with `u k = c`, else `w'`. -/
def winSel (k : Fin (d + 1)) (c : Fin 3) (w w' : Nb d → A.S) : Nb d → A.S :=
  fun u => if u k = c then w u else w' u

/-- Left rotation by one of the window tracks selected by `u k = 2`. -/
def rotL (k : Fin (d + 1)) (l : L A) : L A :=
  l.mapIdx fun j a => {a with win := winSel A k 2 (l.getD ((j + 1) % l.length) (dflt A)).win a.win}

/-- Right rotation by one of the window tracks selected by `u k = 0`. -/
def rotR (k : Fin (d + 1)) (l : L A) : L A :=
  l.mapIdx fun j a =>
    {a with win := winSel A k 0 (l.getD ((j + l.length - 1) % l.length) (dflt A)).win a.win}

theorem rotL_length (k : Fin (d + 1)) (l : L A) : (rotL A k l).length = l.length := by simp [rotL]
theorem rotR_length (k : Fin (d + 1)) (l : L A) : (rotR A k l).length = l.length := by simp [rotR]

theorem step_lchk_done (k : Fin (d + 1)) (l : L A) (hl : 0 < l.length)
    (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0)) (hbb : l[0].bb = true) :
    (prog A).stepP (.lchk k, l) = .inl (.rcopyR k, l) ∧
      (prog A).tripCost (.lchk k) l = 2 * l.length + 2 := by
  have hcells : (fscan (fwd A (.lchk k)) (buf0 A) l).1 = l :=
    fscan_fst_of_id _ (fun b a => by simp only [fwd]; split_ifs <;> rfl) _ _
  have hfin : (fscan (fwd A (.lchk k)) (buf0 A) l).2 = lchkBuf A l[0].bb l[0].win := by
    rw [fscan_snd, lchk_fbuf A k l hl hfst _ (by omega) le_rfl]
  have htrip : (prog A).trip (.lchk k) l = (l, lchkBuf A l[0].bb l[0].win) := by
    rw [trip_eq, hfin, hcells]
    simp only [show ∀ b, ext A (.lchk k) b = none from fun _ => rfl, Option.toList_none,
      List.append_nil]
    exact bscan_absorb _ _ (fun a => by simp [bwd, lchkBuf, hbb]) l
  refine ⟨stepP_of A ?_ (by rw [htrip]), by rw [tripCost_eq]; simp [ext]⟩
  rw [htrip]
  simp [prog, next, lchkBuf, hbb]

theorem step_lchk_rot (k : Fin (d + 1)) (l : L A) (hl : 0 < l.length)
    (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0)) (hbb : l[0].bb = false) :
    (prog A).stepP (.lchk k, l) = .inl (.lmov k, rotL A k l) ∧
      (prog A).tripCost (.lchk k) l = 2 * l.length + 2 := by
  have hcells : (fscan (fwd A (.lchk k)) (buf0 A) l).1 = l :=
    fscan_fst_of_id _ (fun b a => by simp only [fwd]; split_ifs <;> rfl) _ _
  have hfin : (fscan (fwd A (.lchk k)) (buf0 A) l).2 = lchkBuf A false l[0].win := by
    rw [fscan_snd, lchk_fbuf A k l hl hfst _ (by omega) le_rfl, hbb]
  -- backward buffers
  have hbb' : ∀ m j, j + m + 1 = l.length →
      bbuf (bwd A (.lchk k)) (lchkBuf A false l[0].win) l j =
        lchkBuf A false (l.getD ((j + 1) % l.length) (dflt A)).win := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [bbuf_last _ _ _ j (by omega)]
      rw [show (j + 1) % l.length = 0 by rw [show j + 1 = l.length by omega, Nat.mod_self],
        List.getD_eq_getElem _ _ hl]
    | succ m ih =>
      intro j hj
      rw [bbuf_pred _ _ _ j (by omega), ih (j + 1) (by omega)]
      rw [show (j + 1) % l.length = j + 1 from Nat.mod_eq_of_lt (by omega),
        List.getD_eq_getElem l (dflt A) (show j + 1 < l.length by omega)]
      simp [bwd, lchkBuf]
  have htrip : ((prog A).trip (.lchk k) l).1 = rotL A k l ∧
      ((prog A).trip (.lchk k) l).2.f1 = false := by
    rw [trip_eq, hfin, hcells]
    simp only [show ∀ b, ext A (.lchk k) b = none from fun _ => rfl, Option.toList_none,
      List.append_nil]
    refine ⟨?_, ?_⟩
    · apply List.ext_getElem (by simp [bscan_length, rotL])
      intro j h1 h2
      have hj : j < l.length := by simpa [bscan_length] using h1
      refine (bscan_getElem (bwd A (.lchk k)) _ l j hj).trans ?_
      rw [hbb' (l.length - 1 - j) j (by omega)]
      simp [bwd, rotL, lchkBuf]
      rfl
    · rw [bscan_snd_cons _ _ _ hl, hbb' (l.length - 1) 0 (by omega)]
      simp [bwd, lchkBuf]
  refine ⟨stepP_of A ?_ htrip.1, by rw [tripCost_eq]; simp [ext]⟩
  have h2 := htrip.2
  simp only [prog] at h2 ⊢
  simp [next, h2]

theorem step_rchkR_done (k : Fin (d + 1)) (l : L A) (hl : 0 < l.length)
    (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0)) (hbb : l[0].bb = true) :
    (prog A).stepP (.rchkR k, l) =
      .inl ((match nextAxis k with | some k' => .lcopy k' | none => .app), l) ∧
      (prog A).tripCost (.rchkR k) l = 2 * l.length + 2 := by
  have hbuf : ∀ j, 1 ≤ j → j ≤ l.length →
      fbuf (fwd A (.rchkR k)) (buf0 A) l j = lchkBuf A true (buf0 A).w := by
    intro j hj1 hj2
    induction j with
    | zero => omega
    | succ j ih =>
      rw [fbuf_succ _ _ _ j (by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        simp [fwd, fbuf_zero, hfst 0 hl, hbb, lchkBuf]
      · rw [ih (by omega) (by omega)]
        simp [fwd, hfst j (by omega), hj0, lchkBuf]
  have hcells : (fscan (fwd A (.rchkR k)) (buf0 A) l).1 = l := by
    apply List.ext_getElem (by simp [fscan_length])
    intro j h1 h2
    rw [fscan_getElem _ _ _ j h2]
    by_cases hj0 : j = 0
    · subst hj0; simp [fwd, fbuf_zero, hfst 0 hl, hbb]
    · rw [hbuf j (by omega) (by omega)]; simp [fwd, hfst j h2, hj0, lchkBuf]
  have hfin : (fscan (fwd A (.rchkR k)) (buf0 A) l).2 = lchkBuf A true (buf0 A).w := by
    rw [fscan_snd, hbuf _ (by omega) le_rfl]
  have htrip : (prog A).trip (.rchkR k) l = (l, lchkBuf A true (buf0 A).w) := by
    rw [trip_eq, hfin, hcells]
    simp only [show ∀ b, ext A (.rchkR k) b = none from fun _ => rfl, Option.toList_none,
      List.append_nil]
    exact bscan_absorb _ _ (fun a => by simp [bwd, lchkBuf]) l
  refine ⟨stepP_of A ?_ (by rw [htrip]), by rw [tripCost_eq]; simp [ext]⟩
  rw [htrip]
  simp only [prog, next, lchkBuf, if_true]
  cases nextAxis k <;> rfl

/-- The old window of the previous cell (blank for cell `0`). -/
def prevWin (l : L A) (j : ℕ) : Nb d → A.S :=
  if h : 0 < j ∧ j - 1 < l.length then l[j - 1].win else (buf0 A).w

theorem step_rchkR_rot (k : Fin (d + 1)) (l : L A) (hl : 0 < l.length)
    (hfst : ∀ j (h : j < l.length), l[j].fst = decide (j = 0)) (hbb : l[0].bb = false) :
    (prog A).stepP (.rchkR k, l) = .inl (.rmovR k, rotR A k l) ∧
      (prog A).tripCost (.rchkR k) l = 2 * l.length + 2 := by
  -- buffer before cell `j`: the old window of cell `j-1`
  have hbuf : ∀ j, j ≤ l.length → fbuf (fwd A (.rchkR k)) (buf0 A) l j =
      lchkBuf A false (if h : 0 < j ∧ j - 1 < l.length then l[j - 1].win else (buf0 A).w) := by
    intro j hj
    induction j with
    | zero => simp [fbuf_zero, lchkBuf, buf0]
    | succ j ih =>
      rw [fbuf_succ _ _ _ j (by omega), ih (by omega)]
      rw [dif_pos (show 0 < j + 1 ∧ j + 1 - 1 < l.length by omega)]
      by_cases hj0 : j = 0
      · subst hj0
        simp [fwd, hfst 0 hl, hbb, lchkBuf]
      · simp [fwd, hfst j (by omega), hj0, lchkBuf]
  -- cells after the forward pass
  have hfcell : ∀ j (hj : j < l.length), (fscan (fwd A (.rchkR k)) (buf0 A) l).1[j]'(by
      rw [fscan_length]; exact hj) = {l[j] with win := winSel A k 0 (prevWin A l j) l[j].win} := by
    intro j hj
    refine (fscan_getElem _ _ _ j hj).trans ?_
    rw [hbuf j (by omega)]
    by_cases hj0 : j = 0
    · subst hj0; simp [fwd, hfst 0 hl, hbb, lchkBuf, prevWin]; rfl
    · simp [fwd, hfst j hj, hj0, lchkBuf, prevWin]; rfl
  have hfin : (fscan (fwd A (.rchkR k)) (buf0 A) l).2 = lchkBuf A false l[l.length - 1].win := by
    rw [fscan_snd, hbuf _ le_rfl, dif_pos ⟨hl, by omega⟩]
  have hconst : ∀ b a, (bwd A (.rchkR k) b a).2 = b := by
    intro b a; simp only [bwd]; split_ifs <;> rfl
  have htrip : ((prog A).trip (.rchkR k) l).1 = rotR A k l ∧
      ((prog A).trip (.rchkR k) l).2.f1 = false := by
    rw [trip_eq, hfin]
    simp only [show ∀ b, ext A (.rchkR k) b = none from fun _ => rfl, Option.toList_none,
      List.append_nil]
    rw [bscan_const_of (bwd A (.rchkR k)) hconst]
    refine ⟨?_, by simp [lchkBuf]⟩
    apply List.ext_getElem (by simp [rotR, fscan_length])
    intro j h1 h2
    have hj : j < l.length := by simpa [rotR] using h2
    rw [List.getElem_map, hfcell j hj]
    simp only [rotR, List.getElem_mapIdx]
    by_cases hj0 : j = 0
    · subst hj0
      have hidx : (0 + l.length - 1) % l.length = l.length - 1 := by
        rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [hidx, List.getD_eq_getElem l (dflt A) (show l.length - 1 < l.length by omega)]
      simp [bwd, lchkBuf, hfst 0 hl, prevWin]
      congr 1
      funext u
      simp only [winSel]
      split_ifs <;> rfl
    · have hidx : (j + l.length - 1) % l.length = j - 1 := by
        rw [show j + l.length - 1 = (j - 1) + l.length by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hidx, List.getD_eq_getElem l (dflt A) (show j - 1 < l.length by omega)]
      simp [bwd, lchkBuf, hfst j hj, hj0, prevWin, show 0 < j ∧ j - 1 < l.length by omega]
  refine ⟨stepP_of A ?_ htrip.1, by rw [tripCost_eq]; simp [ext]⟩
  have h2 := htrip.2
  simp only [prog] at h2 ⊢
  simp [next, h2]

/-! ### Restart marking -/

theorem fwd_ggm (b : Buf A.S d) (a : Cell A.S d) :
    fwd A .ggm b a = ({a with gm := a.gm || !b.f1}, {b with f1 := b.f1 || !a.gm}) := by
  obtain ⟨w, f1, f2, f3, f4⟩ := b
  obtain ⟨inp, fst, cnt, gm, rp, ptr, mv, bb, ref, cur, win⟩ := a
  cases f1 <;> cases gm <;> rfl

theorem fwd_gcnt (r : Fin 2) (b : Buf A.S d) (a : Cell A.S d) :
    fwd A (.gcnt r) b a = ({a with cnt := a.cnt || !b.f1}, {b with f1 := b.f1 || !a.cnt}) := by
  obtain ⟨w, f1, f2, f3, f4⟩ := b
  obtain ⟨inp, fst, cnt, gm, rp, ptr, mv, bb, ref, cur, win⟩ := a
  cases f1 <;> cases cnt <;> rfl

theorem step_ggm (l : L A) (G : ℕ) (hlen : G + 1 < l.length)
    (hgm : ∀ j (h : j < l.length), l[j].gm = decide (j ≤ G)) :
    (prog A).stepP (.ggm, l) =
      .inl (.gcnt 0, l.mapIdx (fun j a => {a with gm := decide (j ≤ G + 1)})) ∧
      (prog A).tripCost .ggm l = 2 * l.length + 2 := by
  have hbuf : ∀ j, j ≤ l.length → (fbuf (fwd A .ggm) (buf0 A) l j).f1 = decide (G + 1 < j) := by
    intro j hj
    induction j with
    | zero => simp [fbuf_zero, buf0]
    | succ j ih =>
      rw [fbuf_succ _ _ _ j (by omega), fwd_ggm]
      simp only [ih (by omega), hgm j (by omega)]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      omega
  have hcells : (fscan (fwd A .ggm) (buf0 A) l).1 =
      l.mapIdx (fun j a => {a with gm := decide (j ≤ G + 1)}) := by
    apply List.ext_getElem (by simp [fscan_length])
    intro j h1 h2
    have hj : j < l.length := by simpa using h2
    rw [fscan_getElem _ _ _ j hj, List.getElem_mapIdx, fwd_ggm]
    simp only [hbuf j (by omega), hgm j hj]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  have ht := trip_fwd_only A (i := .ggm) (fun _ _ => rfl) l
  refine ⟨stepP_of A rfl ?_, by rw [tripCost_eq]; simp [ext]⟩
  rw [ht, hcells]; simp [ext]

theorem step_gcnt (r : Fin 2) (l : L A) (M : ℕ) (hM : M ≤ l.length)
    (hcnt : ∀ j (h : j < l.length), l[j].cnt = decide (j < M)) :
    (prog A).stepP (.gcnt r, l) =
      .inl ((if r.val = 0 then .gcnt 1 else .grst),
        l.mapIdx (fun j a => {a with cnt := decide (j < M + 1)}) ++
          (if M = l.length then [{dflt A with cnt := true}] else [])) ∧
      (prog A).tripCost (.gcnt r) l = 2 * l.length + 2 + (if M = l.length then 1 else 0) := by
  have hbuf : ∀ j, j ≤ l.length → (fbuf (fwd A (.gcnt r)) (buf0 A) l j).f1 = decide (M < j) := by
    intro j hj
    induction j with
    | zero => simp [fbuf_zero, buf0]
    | succ j ih =>
      rw [fbuf_succ _ _ _ j (by omega), fwd_gcnt]
      simp only [ih (by omega), hcnt j (by omega)]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      omega
  have hcells : (fscan (fwd A (.gcnt r)) (buf0 A) l).1 =
      l.mapIdx (fun j a => {a with cnt := decide (j < M + 1)}) := by
    apply List.ext_getElem (by simp [fscan_length])
    intro j h1 h2
    have hj : j < l.length := by simpa using h2
    rw [fscan_getElem _ _ _ j hj, List.getElem_mapIdx, fwd_gcnt]
    simp only [hbuf j (by omega), hcnt j hj]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  have hfin : (fscan (fwd A (.gcnt r)) (buf0 A) l).2.f1 = decide (M < l.length) := by
    rw [fscan_snd, hbuf _ le_rfl]
  have hext : ext A (.gcnt r) (fscan (fwd A (.gcnt r)) (buf0 A) l).2 =
      if M = l.length then some {dflt A with cnt := true} else none := by
    simp only [ext, hfin]
    by_cases h : M = l.length
    · simp [h]
    · simp [h, show M < l.length by omega]
  have ht := trip_fwd_only A (i := .gcnt r) (fun _ _ => rfl) l
  refine ⟨stepP_of A ?_ ?_, ?_⟩
  · simp only [prog, next]
    split_ifs <;> rfl
  · rw [ht, hcells, hext]
    split_ifs <;> simp
  · rw [tripCost_eq, hext]
    split_ifs <;> simp

end PVNP.Discrete.WCCDSweep
