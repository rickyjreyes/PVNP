import PVNP.CookLevinMain

/-!
# CL-1, part 2e: the column labels of the tableau window

Before the main loop, the generator writes the label `labOf x Q T c` on every cell `c < W T`
(`W T = 2T + 3`).  When `2|x| + 1 + Q ≤ T`, the window splits into four regions:

* `c ≤ T`: left of the origin (`labL`);
* `T + 1 ≤ c ≤ T + 1 + 2|x|`: the cells of `pre x`, a tag and a data cell per input bit and a
  terminator (`labTag`, `labDat`, `labTerm`);
* the next `Q` cells: the witness (`labWit`);
* the rest, ending with the last column `2T + 2` (`labR`).

A pointer `pc` walks the window.  The left region ends where the unary row track `ut` ends.  The
input cursor `ci` reads `x`.  The cursor `cq` walks the unary track `uq` of length `Q`.  The
cursor `cj = c − (T + 1)` finds the last column where it leaves `ut`.  The phase ends by putting
the five cursors of the main loop on cell `0`, which establishes the main-loop invariant `TI`.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim PVNP.PartI PVNP.CookLevin

/-! ## The word `pre x` -/

theorem pre_cons (b : Bool) (x : List Bool) : pre (b :: x) = true :: b :: pre x := by
  simp [pre]

theorem pre_getD_tag : ∀ (x : List Bool) (i : ℕ), i < x.length → (pre x).getD (2 * i) false = true
  | [], _, h => absurd h (by simp)
  | b :: x, 0, _ => by simp [pre_cons]
  | b :: x, i + 1, h => by
    rw [pre_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
    simp only [List.getD_cons_succ]
    exact pre_getD_tag x i (by simp at h; omega)

theorem pre_getD_dat : ∀ (x : List Bool) (i : ℕ) (h : i < x.length),
    (pre x).getD (2 * i + 1) false = x[i]
  | [], _, h => absurd h (by simp)
  | b :: x, 0, _ => by simp [pre_cons]
  | b :: x, i + 1, h => by
    rw [pre_cons, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring]
    simp only [List.getD_cons_succ, List.getElem_cons_succ]
    exact pre_getD_dat x i (by simp at h; omega)

theorem pre_getD_ge : ∀ (x : List Bool) (d : ℕ), 2 * x.length ≤ d → (pre x).getD d false = false
  | [], d, _ => by cases d <;> simp [pre]
  | b :: x, d, h => by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by simp at h; omega⟩
    rw [pre_cons]
    simp only [List.getD_cons_succ]
    exact pre_getD_ge x d' (by simp at h; omega)

theorem pre_getD_zero (x : List Bool) : (pre x).getD 0 false = decide (0 < x.length) := by
  cases x <;> simp [pre]

/-! ## The labels of the four regions -/

/-- Left region. -/
def labL (fst nz : Bool) : CLab := ⟨fst, false, false, nz, false, false⟩
/-- Tag cell of `pre x`. -/
def labTag (orig : Bool) : CLab := ⟨false, false, true, true, orig, false⟩
/-- Data cell of `pre x`. -/
def labDat (v : Bool) : CLab := ⟨false, false, true, v, false, false⟩
/-- Terminator of `pre x`. -/
def labTerm (orig : Bool) : CLab := ⟨false, false, true, false, orig, false⟩
/-- Witness cell. -/
def labWit : CLab := ⟨false, false, false, false, false, true⟩
/-- Right region; `lst` marks the last column. -/
def labR (lst : Bool) : CLab := ⟨false, lst, false, false, false, false⟩

section Values

variable {x : List Bool} {Q T : ℕ}

theorem labOf_left {c : ℕ} (hc : c < T + 1) :
    labOf x Q T c = labL (decide (c = 0)) (decide (0 < x.length)) := by
  have ht : ((c : ℤ) - (T + 1)).toNat = 0 := Int.toNat_eq_zero.2 (by omega)
  unfold labOf labL
  rw [ht, pre_getD_zero]
  congr 1
  · simp only [decide_eq_false_iff_not, W]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_false_iff_not, isWit]; omega

/-- Labels right of the origin, by the offset `d = c − (T + 1)`. -/
theorem labOf_right {c d : ℕ} (hc : c = T + 1 + d) :
    labOf x Q T c = ⟨false, decide (c + 1 = W T), decide (d < 2 * x.length + 1),
      (pre x).getD d false, decide (d = 0),
      decide (2 * x.length < d ∧ d ≤ 2 * x.length + Q)⟩ := by
  subst hc
  have e : ((↑(T + 1 + d) : ℤ) - (↑T + 1)) = (d : ℤ) := by push_cast; ring
  unfold labOf
  rw [e]
  simp only [Int.toNat_natCast, pre_length]
  congr 1
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_decide]; omega
  · simp only [decide_eq_decide]; omega
  · simp only [isWit, decide_eq_decide]; omega

theorem labOf_tag (hT : 2 * x.length + 1 + Q ≤ T) {i : ℕ} (hi : i < x.length) :
    labOf x Q T (T + 1 + 2 * i) = labTag (decide (i = 0)) := by
  rw [labOf_right rfl, pre_getD_tag x i hi]
  unfold labTag
  congr 1
  · simp only [decide_eq_false_iff_not, W]; omega
  · simp only [decide_eq_true_eq]; omega
  · simp only [decide_eq_decide]; omega
  · simp only [decide_eq_false_iff_not]; omega

theorem labOf_dat (hT : 2 * x.length + 1 + Q ≤ T) {i : ℕ} (hi : i < x.length) :
    labOf x Q T (T + 1 + 2 * i + 1) = labDat x[i] := by
  rw [labOf_right (show T + 1 + 2 * i + 1 = T + 1 + (2 * i + 1) by ring), pre_getD_dat x i hi]
  unfold labDat
  congr 1
  · simp only [decide_eq_false_iff_not, W]; omega
  · simp only [decide_eq_true_eq]; omega
  · simp only [decide_eq_false_iff_not]; omega

theorem labOf_term (hT : 2 * x.length + 1 + Q ≤ T) :
    labOf x Q T (T + 1 + 2 * x.length) = labTerm (decide (x.length = 0)) := by
  rw [labOf_right rfl, pre_getD_ge x _ le_rfl]
  unfold labTerm
  congr 1
  · simp only [decide_eq_false_iff_not, W]; omega
  · simp only [decide_eq_true_eq]; omega
  · simp only [decide_eq_decide]; omega
  · simp only [decide_eq_false_iff_not]; omega

theorem labOf_wit (hT : 2 * x.length + 1 + Q ≤ T) {q : ℕ} (hq : q < Q) :
    labOf x Q T (T + 2 + 2 * x.length + q) = labWit := by
  rw [labOf_right (show T + 2 + 2 * x.length + q = T + 1 + (2 * x.length + 1 + q) by ring),
    pre_getD_ge x _ (by omega)]
  unfold labWit
  congr 1
  · simp only [decide_eq_false_iff_not, W]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_true_eq]; omega

theorem labOf_rgt {j : ℕ} (hj : 2 * x.length + 1 + Q ≤ j) :
    labOf x Q T (T + 1 + j) = labR (decide (j = T + 1)) := by
  rw [labOf_right rfl, pre_getD_ge x _ (by omega)]
  unfold labR
  congr 1
  · simp only [decide_eq_decide, W]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_false_iff_not]; omega

end Values

/-! ## The label program -/

/-- Control states of the label phase. -/
inductive LSt where
  | i0 | i1 | i2 | i3 | i4
  | a0 (fst nz : Bool) | a1 (fst nz : Bool) | a2 (nz : Bool)
  | b0 (orig : Bool) | b1 (orig v : Bool) | b2 (v : Bool) | b3 (v : Bool) | b4 (v : Bool)
  | b5 | b6 | b7
  | c0 (orig : Bool) | c1 | c2
  | d0 | d1 | d2 | d3 | d4
  | e0 | e1 | e2 | e3 | e4 | e5
  | f0 | f1 | f2 | f3 | f4
  deriving DecidableEq, Fintype

/-- The bit of an input read. -/
def ires : RRes → Option Bool
  | .o v => v
  | _ => none

/-- **The label program**, ending with the five main-loop cursors on cell `0`. -/
def labCtrl : Ctrl where
  C := LSt
  start := .i0
  op
    | .i0 => .first .pc
    | .i1 => .first .ci
    | .i2 => .first .cj
    | .i3 => .first .cq
    | .i4 => .read (.inp .ci)
    | .a0 _ _ => .read (.mark .pc .ut)
    | .a1 fst nz => .setCl .pc (labL fst nz)
    | .a2 _ => .shift .pc
    | .b0 _ => .read (.inp .ci)
    | .b1 orig _ => .setCl .pc (labTag orig)
    | .b2 _ => .shift .pc
    | .b3 _ => .shift .cj
    | .b4 v => .setCl .pc (labDat v)
    | .b5 => .shift .pc
    | .b6 => .shift .cj
    | .b7 => .shift .ci
    | .c0 orig => .setCl .pc (labTerm orig)
    | .c1 => .shift .pc
    | .c2 => .shift .cj
    | .d0 => .read (.mark .cq .uq)
    | .d1 => .setCl .pc labWit
    | .d2 => .shift .pc
    | .d3 => .shift .cj
    | .d4 => .shift .cq
    | .e0 => .read (.mark .cj .ut)
    | .e1 => .setCl .pc (labR false)
    | .e2 => .shift .pc
    | .e3 => .shift .cj
    | .e4 => .setCl .pc (labR true)
    | .e5 => .shift .pc
    | .f0 => .first .rk
    | .f1 => .first .ck
    | .f2 => .first .rv
    | .f3 => .first .cv
    | .f4 => .first .op
  nxt
    | .i0, _ => .inl .i1
    | .i1, _ => .inl .i2
    | .i2, _ => .inl .i3
    | .i3, _ => .inl .i4
    | .i4, r => .inl (.a0 true (ires r).isSome)
    | .a0 fst nz, r => if bres r then .inl (.a1 fst nz) else .inl (.b0 true)
    | .a1 _ nz, _ => .inl (.a2 nz)
    | .a2 nz, _ => .inl (.a0 false nz)
    | .b0 orig, r => match ires r with
        | some v => .inl (.b1 orig v)
        | none => .inl (.c0 orig)
    | .b1 _ v, _ => .inl (.b2 v)
    | .b2 v, _ => .inl (.b3 v)
    | .b3 v, _ => .inl (.b4 v)
    | .b4 _, _ => .inl .b5
    | .b5, _ => .inl .b6
    | .b6, _ => .inl .b7
    | .b7, _ => .inl (.b0 false)
    | .c0 _, _ => .inl .c1
    | .c1, _ => .inl .c2
    | .c2, _ => .inl .d0
    | .d0, r => if bres r then .inl .d1 else .inl .e0
    | .d1, _ => .inl .d2
    | .d2, _ => .inl .d3
    | .d3, _ => .inl .d4
    | .d4, _ => .inl .d0
    | .e0, r => if bres r then .inl .e1 else .inl .e4
    | .e1, _ => .inl .e2
    | .e2, _ => .inl .e3
    | .e3, _ => .inl .e0
    | .e4, _ => .inl .e5
    | .e5, _ => .inl .f0
    | .f0, _ => .inl .f1
    | .f1, _ => .inl .f2
    | .f2, _ => .inl .f3
    | .f3, _ => .inl .f4
    | .f4, _ => .inr true

theorem lstep {c c' : LSt} {o : Op} (l : List Cell) (hop : labCtrl.op c = o)
    (hn : ∀ r, labCtrl.nxt c r = .inl c') : RN labCtrl.prog (c, l) (c', o.eff l) 1 := by
  have := Ctrl.step_of labCtrl c c' l (hn _)
  rwa [hop] at this

theorem lread {c c' : LSt} {k : RKind} (l : List Cell) (hop : labCtrl.op c = .read k)
    (hn : labCtrl.nxt c ((Op.read k).res l) = .inl c') : RN labCtrl.prog (c, l) (c', l) 1 := by
  have := Ctrl.step_of labCtrl c c' l (by rw [hop]; exact hn)
  rwa [hop, eff_read] at this

/-! ## The label invariant -/

/-- Tape before the label phase. -/
structure PL (x : List Bool) (Q T : ℕ) (l : List Cell) : Prop where
  ut : Run l .ut (T + 1)
  uq : Run l .uq Q
  inl : x.length ≤ l.length
  pos : 0 < l.length
  inp : ∀ (c : ℕ) (hc : c < l.length), l[c].inp = x[c]?
  out : ∀ (c : ℕ) (hc : c < l.length), l[c].out = none

/-- Label invariant: cells `< p` are labelled; cursors `pc = p`, `ci = i`, `cj = j`, `cq = q`. -/
structure LI (x : List Bool) (Q T p i j q : ℕ) (l : List Cell) : Prop where
  ut : Run l .ut (T + 1)
  uq : Run l .uq Q
  inl : x.length ≤ l.length
  inp : ∀ (c : ℕ) (hc : c < l.length), l[c].inp = x[c]?
  labs : ∀ (c : ℕ) (hc : c < l.length), c < p → l[c].cl = some (labOf x Q T c)
  pc : Uniq l .pc p
  ci : Uniq l .ci i
  cj : Uniq l .cj j
  cq : Uniq l .cq q
  out : ∀ (c : ℕ) (hc : c < l.length), l[c].out = none

section Inv

variable {x : List Bool} {Q T : ℕ}

theorem inp_frS {l l' : List Cell} {S : Mk → Bool} (hf : Fr (AgS S) l l')
    (hl : x.length ≤ l.length) (hi : ∀ (c : ℕ) (hc : c < l.length), l[c].inp = x[c]?) :
    ∀ (c : ℕ) (hc : c < l'.length), l'[c].inp = x[c]? := by
  intro c hc
  rw [(hf.2 c hc).2.1]
  by_cases hcl : c < l.length
  · rw [List.getD_eq_getElem _ _ hcl, hi]
  · rw [List.getD_eq_default _ _ (by omega), List.getElem?_eq_none (by omega)]; rfl

theorem out_frS {l l' : List Cell} {S : Mk → Bool} (hf : Fr (AgS S) l l')
    (ho : ∀ (c : ℕ) (hc : c < l.length), l[c].out = none) :
    ∀ (c : ℕ) (hc : c < l'.length), l'[c].out = none := by
  intro c hc
  rw [(hf.2 c hc).2.2.2]
  by_cases hcl : c < l.length
  · rw [List.getD_eq_getElem _ _ hcl, ho]
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

/-- Moving the cursors `ci, cj, cq` (and others outside `ut, uq, pc`). -/
theorem LI.frS {p i j q : ℕ} {l l' : List Cell} (h : LI x Q T p i j q l) {S : Mk → Bool}
    (hf : Fr (AgS S) l l') (hut : S .ut = false) (huq : S .uq = false) (hpc : S .pc = false)
    {i' j' q' : ℕ} (hci : Uniq l' .ci i') (hcj : Uniq l' .cj j') (hcq : Uniq l' .cq q') :
    LI x Q T p i' j' q' l' where
  ut := h.ut.frS hf hut
  uq := h.uq.frS hf huq
  inl := le_trans h.inl hf.1
  inp := inp_frS hf h.inl h.inp
  labs c hc hcp := by
    rw [(hf.2 c hc).2.2.1]
    have := h.pc.1
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact h.labs c _ hcp
  pc := h.pc.frS hf hpc
  ci := hci
  cj := hcj
  cq := hcq
  out := out_frS hf h.out

theorem setCl_getD {l : List Cell} {p : ℕ} (hu : Uniq l .pc p) (lab : CLab) (c : ℕ) :
    (Op.eff (.setCl .pc lab) l).getD c dflt =
      if c = p then { l.getD c dflt with cl := some lab } else l.getD c dflt := by
  by_cases hc : c < l.length
  · have hc1 : c < (Op.eff (.setCl .pc lab) l).length := by simpa [eff_setCl] using hc
    rw [List.getD_eq_getElem _ _ hc1, List.getD_eq_getElem _ _ hc,
      eff_map_get (eff_setCl .pc lab)]
    simp only [hu.2 c hc, decide_eq_true_eq]
  · rw [List.getD_eq_default _ _ (by simpa [eff_setCl] using hc),
      List.getD_eq_default _ _ (by omega)]
    have := hu.1
    rw [if_neg (by omega)]

/-- **Writing one label** at the pointer and advancing it. -/
theorem LI.wr {p i j q : ℕ} {l : List Cell} (h : LI x Q T p i j q l) {lab : CLab}
    (hlab : labOf x Q T p = lab) :
    LI x Q T (p + 1) i j q (Op.eff (.shift .pc) (Op.eff (.setCl .pc lab) l)) := by
  have g1 := setCl_getD h.pc lab
  have hlen1 : (Op.eff (.setCl .pc lab) l).length = l.length := by simp [eff_setCl]
  generalize Op.eff (.setCl .pc lab) l = l1 at g1 hlen1 ⊢
  have hu1 : Uniq l1 .pc p := uniq_of_getD h.pc (by omega) (fun c hc => by
    rw [← List.getD_eq_getElem _ dflt hc, g1 c]; split_ifs <;> rfl)
  have hu2 := (shift_uniq hu1).1
  have f2 : Fr (AgK .pc) l1 (Op.eff (.shift .pc) l1) := fr_shift .pc l1
  generalize Op.eff (.shift .pc) l1 = l2 at hu2 f2 ⊢
  have hlen : l.length ≤ l2.length := by have := f2.1; omega
  have hm : ∀ t, t ≠ .pc → ∀ (c : ℕ) (hc : c < l2.length), l2[c].m t = (l.getD c dflt).m t := by
    intro t ht c hc
    rw [(f2.2 c hc).1 t ht, g1 c]; split_ifs <;> rfl
  refine ⟨run_of_getD h.ut hlen (hm .ut (by decide)), run_of_getD h.uq hlen (hm .uq (by decide)),
    le_trans h.inl hlen, ?_, ?_, hu2, uniq_of_getD h.ci hlen (hm .ci (by decide)),
    uniq_of_getD h.cj hlen (hm .cj (by decide)), uniq_of_getD h.cq hlen (hm .cq (by decide)), ?_⟩
  · intro c hc
    rw [(f2.2 c hc).2.1, g1 c]
    have : (l.getD c dflt).inp = x[c]? := by
      by_cases hcl : c < l.length
      · rw [List.getD_eq_getElem _ _ hcl, h.inp]
      · rw [List.getD_eq_default _ _ (by omega)]
        have := h.inl
        rw [List.getElem?_eq_none (by omega)]; rfl
    split_ifs <;> exact this
  · intro c hc hcp
    rw [(f2.2 c hc).2.2.1, g1 c]
    have := h.pc.1
    by_cases hcP : c = p
    · subst hcP; rw [if_pos rfl, hlab]
    · rw [if_neg hcP, List.getD_eq_getElem _ _ (by omega)]
      exact h.labs c _ (by omega)
  · intro c hc
    rw [(f2.2 c hc).2.2.2, g1 c]
    have : (l.getD c dflt).out = none := by
      by_cases hcl : c < l.length
      · rw [List.getD_eq_getElem _ _ hcl, h.out]
      · rw [List.getD_eq_default _ _ (by omega)]; rfl
    split_ifs <;> exact this

/-- Cursor frames of the label phase. -/
def labS (t : Mk) : Bool := decide (t = .ci) || decide (t = .cj) || decide (t = .cq)

theorem LI.shift_ci {p i j q : ℕ} {l : List Cell} (h : LI x Q T p i j q l) :
    LI x Q T p (i + 1) j q (Op.eff (.shift .ci) l) := by
  have f := fr_shift .ci l
  exact h.frS (Fr.agK_agS (S := labS) (by decide) f) (by decide) (by decide) (by decide)
    (shift_uniq h.ci).1 (h.cj.fr f (by decide)) (h.cq.fr f (by decide))

theorem LI.shift_cj {p i j q : ℕ} {l : List Cell} (h : LI x Q T p i j q l) :
    LI x Q T p i (j + 1) q (Op.eff (.shift .cj) l) := by
  have f := fr_shift .cj l
  exact h.frS (Fr.agK_agS (S := labS) (by decide) f) (by decide) (by decide) (by decide)
    (h.ci.fr f (by decide)) (shift_uniq h.cj).1 (h.cq.fr f (by decide))

theorem LI.shift_cq {p i j q : ℕ} {l : List Cell} (h : LI x Q T p i j q l) :
    LI x Q T p i j (q + 1) (Op.eff (.shift .cq) l) := by
  have f := fr_shift .cq l
  exact h.frS (Fr.agK_agS (S := labS) (by decide) f) (by decide) (by decide) (by decide)
    (h.ci.fr f (by decide)) (h.cj.fr f (by decide)) (shift_uniq h.cq).1

end Inv

/-! ## The phases -/

section Phases

variable {x : List Bool} {Q T : ℕ}

theorem isSome_zero (x : List Bool) : (x[0]?).isSome = decide (0 < x.length) := by
  cases x <;> simp

/-- The pointers start on cell `0`; one read records whether `x` is empty. -/
theorem lab_start {l : List Cell} (h : PL x Q T l) :
    ∃ l', RN labCtrl.prog (.i0, l) (.a0 true (decide (0 < x.length)), l') 5 ∧
      LI x Q T 0 0 0 0 l' := by
  have f1 := fr_first .pc l
  have f2 := fr_first .ci (Op.eff (.first .pc) l)
  have f3 := fr_first .cj (Op.eff (.first .ci) (Op.eff (.first .pc) l))
  have f4 := fr_first .cq (Op.eff (.first .cj) (Op.eff (.first .ci) (Op.eff (.first .pc) l)))
  set l4 := Op.eff (.first .cq) (Op.eff (.first .cj) (Op.eff (.first .ci)
    (Op.eff (.first .pc) l))) with hl4
  have hl : ∀ k, 0 < (Op.eff (.first k) l).length := fun k => by
    rw [eff_first_length]; exact h.pos
  have hl2 : 0 < (Op.eff (.first .ci) (Op.eff (.first .pc) l)).length := by
    rw [eff_first_length]; exact hl _
  have hl3 : 0 < (Op.eff (.first .cj) (Op.eff (.first .ci) (Op.eff (.first .pc) l))).length := by
    rw [eff_first_length]; exact hl2
  let S : Mk → Bool := fun t => decide (t = .pc) || labS t
  have F : Fr (AgS S) l l4 := by
    have g := fun {k : Mk} (hk : S k = true) {a b : List Cell} (hf : Fr (AgK k) a b) =>
      Fr.agK_agS (S := S) hk hf
    have t1 := (g (by decide) f1).trans (g (by decide) f2)
    have t2 := (t1.trans (g (by decide) f3)).trans (g (by decide) f4)
    exact t2.mono (fun _ _ hab => hab.mono (fun k hk => by
      revert hk; simp only [Bool.or_eq_true]; tauto))
  have I : LI x Q T 0 0 0 0 l4 := by
    refine ⟨h.ut.frS F (by decide), h.uq.frS F (by decide), le_trans h.inl F.1,
      inp_frS F h.inl h.inp, fun c _ hc => absurd hc (Nat.not_lt_zero _), ?_, ?_, ?_,
      first_uniq hl3, out_frS F h.out⟩
    · exact ((first_uniq h.pos).fr f2 (by decide)).fr f3 (by decide) |>.fr f4 (by decide)
    · exact ((first_uniq (hl _)).fr f3 (by decide)).fr f4 (by decide)
    · exact (first_uniq hl2).fr f4 (by decide)
  have s1 : RN labCtrl.prog (.i0, l) (.i1, Op.eff (.first .pc) l) 1 := lstep l rfl (fun _ => rfl)
  have s2 : RN labCtrl.prog (.i1, Op.eff (.first .pc) l)
      (.i2, Op.eff (.first .ci) (Op.eff (.first .pc) l)) 1 := lstep _ rfl (fun _ => rfl)
  have s3 : RN labCtrl.prog (.i2, Op.eff (.first .ci) (Op.eff (.first .pc) l))
      (.i3, Op.eff (.first .cj) (Op.eff (.first .ci) (Op.eff (.first .pc) l))) 1 :=
    lstep _ rfl (fun _ => rfl)
  have s4 : RN labCtrl.prog (.i3, Op.eff (.first .cj) (Op.eff (.first .ci) (Op.eff (.first .pc) l)))
      (.i4, l4) 1 := lstep _ rfl (fun _ => rfl)
  have s5 : RN labCtrl.prog (.i4, l4) (.a0 true (decide (0 < x.length)), l4) 1 :=
    lread l4 rfl (by rw [read_inp I.ci, I.inp 0 I.ci.1, ← isSome_zero x]; rfl)
  exact ⟨l4, (((s1.trans s2).trans s3).trans s4).trans s5, I⟩

theorem lthen {s : labCtrl.prog.I × List labCtrl.prog.D} {c c' : LSt} {o : Op} {l : List Cell}
    {k : ℕ} (h : RN labCtrl.prog s (c, l) k) (hop : labCtrl.op c = o)
    (hn : ∀ r, labCtrl.nxt c r = .inl c') : RN labCtrl.prog s (c', o.eff l) (k + 1) :=
  h.trans (lstep l hop hn)

/-- The left region. -/
theorem left_loop : ∀ (m p : ℕ) (l : List Cell), p + m = T + 1 → LI x Q T p 0 0 0 l →
    ∃ l', RN labCtrl.prog (.a0 (decide (p = 0)) (decide (0 < x.length)), l) (.b0 true, l')
      (3 * m + 1) ∧ LI x Q T (T + 1) 0 0 0 l' := by
  intro m
  induction m with
  | zero =>
    intro p l hp h
    refine ⟨l, lread l rfl (by
      rw [read_mark h.pc, h.ut.2, decide_eq_false (by omega : ¬ p < T + 1)]; rfl), ?_⟩
    rwa [show T + 1 = p by omega]
  | succ m ih =>
    intro p l hp h
    have r0 : RN labCtrl.prog (.a0 (decide (p = 0)) (decide (0 < x.length)), l)
        (.a1 (decide (p = 0)) (decide (0 < x.length)), l) 1 :=
      lread l rfl (by rw [read_mark h.pc, h.ut.2, decide_eq_true (by omega : p < T + 1)]; rfl)
    have r1 := lthen r0 (o := .setCl .pc (labL (decide (p = 0)) (decide (0 < x.length)))) rfl
      (fun _ => rfl)
    have r2 := lthen r1 (o := .shift .pc) rfl (fun _ => rfl)
    have I := h.wr (labOf_left (x := x) (Q := Q) (by omega))
    obtain ⟨l', r3, I'⟩ := ih (p + 1) _ (by omega) I
    rw [show decide (p + 1 = 0) = false by simp] at r3
    exact ⟨l', RN.cast_k (r2.trans r3) (by ring), I'⟩

/-- The cells of `pre x`. -/
theorem pre_loop (hT : 2 * x.length + 1 + Q ≤ T) : ∀ (m i : ℕ) (l : List Cell),
    i + m = x.length → LI x Q T (T + 1 + 2 * i) i (2 * i) 0 l →
    ∃ l', RN labCtrl.prog (.b0 (decide (i = 0)), l) (.d0, l') (8 * m + 4) ∧
      LI x Q T (T + 2 + 2 * x.length) x.length (2 * x.length + 1) 0 l' := by
  intro m
  induction m with
  | zero =>
    intro i l hi h
    have hin : i = x.length := by omega
    subst hin
    have r0 : RN labCtrl.prog (.b0 (decide (x.length = 0)), l)
        (.c0 (decide (x.length = 0)), l) 1 :=
      lread l rfl (by rw [read_inp h.ci, h.inp _ h.ci.1, List.getElem?_eq_none le_rfl]; rfl)
    have r1 := lthen r0 (o := .setCl .pc (labTerm (decide (x.length = 0)))) rfl (fun _ => rfl)
    have r2 := lthen r1 (o := .shift .pc) rfl (fun _ => rfl)
    have r3 := lthen r2 (o := .shift .cj) rfl (fun _ => rfl)
    have I := (h.wr (labOf_term hT)).shift_cj
    refine ⟨_, r3, ?_⟩
    rwa [show T + 1 + 2 * x.length + 1 = T + 2 + 2 * x.length by ring] at I
  | succ m ih =>
    intro i l hi h
    have hix : i < x.length := by omega
    have r0 : RN labCtrl.prog (.b0 (decide (i = 0)), l) (.b1 (decide (i = 0)) x[i], l) 1 :=
      lread l rfl (by rw [read_inp h.ci, h.inp _ h.ci.1, List.getElem?_eq_getElem hix]; rfl)
    have r1 := lthen r0 (o := .setCl .pc (labTag (decide (i = 0)))) rfl (fun _ => rfl)
    have r2 := lthen r1 (o := .shift .pc) rfl (fun _ => rfl)
    have r3 := lthen r2 (o := .shift .cj) rfl (fun _ => rfl)
    have r4 := lthen r3 (o := .setCl .pc (labDat x[i])) rfl (fun _ => rfl)
    have r5 := lthen r4 (o := .shift .pc) rfl (fun _ => rfl)
    have r6 := lthen r5 (o := .shift .cj) rfl (fun _ => rfl)
    have r7 := lthen r6 (o := .shift .ci) rfl (fun _ => rfl)
    have I5 := ((((h.wr (labOf_tag hT hix)).shift_cj).wr (labOf_dat hT hix)).shift_cj).shift_ci
    have e1 : T + 1 + 2 * i + 1 + 1 = T + 1 + 2 * (i + 1) := by ring
    have e2 : 2 * i + 1 + 1 = 2 * (i + 1) := by ring
    rw [e1, e2] at I5
    obtain ⟨l', r8, I'⟩ := ih (i + 1) _ (by omega) I5
    rw [show decide (i + 1 = 0) = false by simp] at r8
    exact ⟨l', RN.cast_k (r7.trans r8) (by ring), I'⟩

/-- The witness cells. -/
theorem wit_loop (hT : 2 * x.length + 1 + Q ≤ T) : ∀ (m q : ℕ) (l : List Cell), q + m = Q →
    LI x Q T (T + 2 + 2 * x.length + q) x.length (2 * x.length + 1 + q) q l →
    ∃ l', RN labCtrl.prog (.d0, l) (.e0, l') (5 * m + 1) ∧
      LI x Q T (T + 2 + 2 * x.length + Q) x.length (2 * x.length + 1 + Q) Q l' := by
  intro m
  induction m with
  | zero =>
    intro q l hq h
    have hq' : q = Q := by omega
    subst hq'
    exact ⟨l, lread l rfl (by
      rw [read_mark h.cq, h.uq.2, decide_eq_false (lt_irrefl q)]; rfl), h⟩
  | succ m ih =>
    intro q l hq h
    have r0 : RN labCtrl.prog (.d0, l) (.d1, l) 1 :=
      lread l rfl (by rw [read_mark h.cq, h.uq.2, decide_eq_true (by omega : q < Q)]; rfl)
    have r1 := lthen r0 (o := .setCl .pc labWit) rfl (fun _ => rfl)
    have r2 := lthen r1 (o := .shift .pc) rfl (fun _ => rfl)
    have r3 := lthen r2 (o := .shift .cj) rfl (fun _ => rfl)
    have r4 := lthen r3 (o := .shift .cq) rfl (fun _ => rfl)
    have I3 := ((h.wr (labOf_wit hT (by omega : q < Q))).shift_cj).shift_cq
    rw [show T + 2 + 2 * x.length + q + 1 = T + 2 + 2 * x.length + (q + 1) by ring,
      show 2 * x.length + 1 + q + 1 = 2 * x.length + 1 + (q + 1) by ring] at I3
    obtain ⟨l', r5, I'⟩ := ih (q + 1) _ (by omega) I3
    exact ⟨l', RN.cast_k (r4.trans r5) (by ring), I'⟩

/-- The right region, ending with the last column. -/
theorem right_loop : ∀ (m j : ℕ) (l : List Cell),
    j + m = T + 1 → 2 * x.length + 1 + Q ≤ j → LI x Q T (T + 1 + j) x.length j Q l →
    ∃ l', RN labCtrl.prog (.e0, l) (.f0, l') (4 * m + 3) ∧
      LI x Q T (2 * T + 3) x.length (T + 1) Q l' := by
  intro m
  induction m with
  | zero =>
    intro j l hj hj0 h
    have hj' : j = T + 1 := by omega
    subst hj'
    have r0 : RN labCtrl.prog (.e0, l) (.e4, l) 1 :=
      lread l rfl (by rw [read_mark h.cj, h.ut.2, decide_eq_false (lt_irrefl _)]; rfl)
    have r1 := lthen r0 (o := .setCl .pc (labR true)) rfl (fun _ => rfl)
    have r2 := lthen r1 (o := .shift .pc) rfl (fun _ => rfl)
    have I := h.wr (by rw [labOf_rgt hj0, decide_eq_true rfl])
    refine ⟨_, r2, ?_⟩
    rwa [show T + 1 + (T + 1) + 1 = 2 * T + 3 by ring] at I
  | succ m ih =>
    intro j l hj hj0 h
    have r0 : RN labCtrl.prog (.e0, l) (.e1, l) 1 :=
      lread l rfl (by rw [read_mark h.cj, h.ut.2, decide_eq_true (by omega : j < T + 1)]; rfl)
    have r1 := lthen r0 (o := .setCl .pc (labR false)) rfl (fun _ => rfl)
    have r2 := lthen r1 (o := .shift .pc) rfl (fun _ => rfl)
    have r3 := lthen r2 (o := .shift .cj) rfl (fun _ => rfl)
    have I2 := (h.wr (by rw [labOf_rgt hj0, decide_eq_false (by omega : ¬ j = T + 1)])).shift_cj
    rw [show T + 1 + j + 1 = T + 1 + (j + 1) by ring] at I2
    obtain ⟨l', r4, I'⟩ := ih (j + 1) _ (by omega) (by omega) I2
    exact ⟨l', RN.cast_k (r3.trans r4) (by ring), I'⟩

/-- The main-loop cursors go to cell `0`; with the final `first op` the main-loop invariant holds. -/
theorem lab_tail {M : TM} {l : List Cell} (h : LI x Q T (2 * T + 3) x.length (T + 1) Q l) :
    ∃ l', RN labCtrl.prog (.f0, l) (.f4, l') 4 ∧
      TI (M := M) x Q T 0 0 0 (Op.eff (.first .op) l') := by
  have hl : 0 < l.length := by have := h.pc.1; omega
  set l1 := Op.eff (.first .rk) l with hl1
  set l2 := Op.eff (.first .ck) l1 with hl2
  set l3 := Op.eff (.first .rv) l2 with hl3
  set l4 := Op.eff (.first .cv) l3 with hl4
  set l5 := Op.eff (.first .op) l4 with hl5
  have f1 : Fr (AgK .rk) l l1 := fr_first .rk l
  have f2 : Fr (AgK .ck) l1 l2 := fr_first .ck l1
  have f3 : Fr (AgK .rv) l2 l3 := fr_first .rv l2
  have f4 : Fr (AgK .cv) l3 l4 := fr_first .cv l3
  have f5 : Fr (AgK .op) l4 l5 := fr_first .op l4
  have e1 : l1.length = l.length := eff_first_length _ _
  have e2 : l2.length = l1.length := eff_first_length _ _
  have e3 : l3.length = l2.length := eff_first_length _ _
  have e4 : l4.length = l3.length := eff_first_length _ _
  have e5 : l5.length = l4.length := eff_first_length _ _
  let S : Mk → Bool := fun t => decide (t = .rk) || decide (t = .ck) || decide (t = .rv) ||
    decide (t = .cv) || decide (t = .op)
  have F : Fr (AgS S) l l5 := by
    have g := fun {k : Mk} (hk : S k = true) {a b : List Cell} (hf : Fr (AgK k) a b) =>
      Fr.agK_agS (S := S) hk hf
    have t := ((((g (by decide) f1).trans (g (by decide) f2)).trans (g (by decide) f3)).trans
      (g (by decide) f4)).trans (g (by decide) f5)
    exact t.mono (fun _ _ hab => hab.mono (fun k hk => by
      revert hk; simp only [Bool.or_eq_true]; tauto))
  have s1 := lstep (c := .f0) (c' := .f1) l rfl (fun _ => rfl)
  have s2 := lstep (c := .f1) (c' := .f2) l1 rfl (fun _ => rfl)
  have s3 := lstep (c := .f2) (c' := .f3) l2 rfl (fun _ => rfl)
  have s4 := lstep (c := .f3) (c' := .f4) l3 rfl (fun _ => rfl)
  refine ⟨l4, ((s1.trans s2).trans s3).trans s4, ?_⟩
  show TI (M := M) x Q T 0 0 0 l5
  have u1 : Uniq l1 .rk 0 := first_uniq hl
  have u2 : Uniq l2 .ck 0 := first_uniq (by omega)
  have u3 : Uniq l3 .rv 0 := first_uniq (by omega)
  have u4 : Uniq l4 .cv 0 := first_uniq (by omega)
  have u5 : Uniq l5 .op 0 := first_uniq (by omega)
  refine ⟨h.ut.frS F (by decide), ?_, ?_, ?_, ?_, ?_, ?_, u5, ?_⟩
  · have := h.pc.1; unfold W; have := F.1; omega
  · intro c hc hcW
    rw [(F.2 c hc).2.2.1]
    have := h.pc.1
    rw [List.getD_eq_getElem _ _ (by unfold W at hcW; omega)]
    exact h.labs c _ (by unfold W at hcW; omega)
  · rw [(rc_zero T).1]; exact ((((u1.fr f2 (by decide)).fr f3 (by decide)).fr f4 (by decide)).fr f5
      (by decide))
  · rw [(rc_zero T).2]; exact (((u2.fr f3 (by decide)).fr f4 (by decide)).fr f5 (by decide))
  · rw [(rc_zero T).1]; exact ((u3.fr f4 (by decide)).fr f5 (by decide))
  · rw [(rc_zero T).2]; exact (u4.fr f5 (by decide))
  · intro c hc
    rw [out_frS F h.out c hc]
    simp

/-- **The label phase.**  From the tape after the Horner phases it reaches its last state
within `8T + 21` round trips; its exit (`first op`) establishes the main-loop invariant. -/
theorem label_phase {M : TM} (hT : 2 * x.length + 1 + Q ≤ T) {l : List Cell} (h : PL x Q T l) :
    ∃ l' k, RN labCtrl.prog (labCtrl.start, l) (.f4, l') k ∧ k ≤ 8 * T + 21 ∧
      TI (M := M) x Q T 0 0 0 (Op.eff (.first .op) l') := by
  obtain ⟨l1, r1, I1⟩ := lab_start h
  obtain ⟨l2, r2, I2⟩ := left_loop (x := x) (Q := Q) (T := T) (T + 1) 0 l1 (by omega) I1
  obtain ⟨l3, r3, I3⟩ := pre_loop (x := x) (Q := Q) (T := T) hT x.length 0 l2 (by omega)
    (by simpa using I2)
  obtain ⟨l4, r4, I4⟩ := wit_loop (x := x) (Q := Q) (T := T) hT Q 0 l3 (by omega)
    (by simpa using I3)
  obtain ⟨l5, r5, I5⟩ := right_loop (x := x) (Q := Q) (T := T)
    (T + 1 - (2 * x.length + 1 + Q)) (2 * x.length + 1 + Q) l4
    (by omega) le_rfl (by
      rw [show T + 1 + (2 * x.length + 1 + Q) = T + 2 + 2 * x.length + Q by ring]; exact I4)
  obtain ⟨l6, r6, I6⟩ := lab_tail (M := M) I5
  refine ⟨l6, _, ((((r1.trans r2).trans r3).trans r4).trans r5).trans r6, ?_, I6⟩
  omega

/-- The exit of the label phase. -/
theorem lab_exit (l : List Cell) : labCtrl.nxt .f4 ((labCtrl.op .f4).res l) = .inr true := rfl

end Phases

end PVNP.CookLevin.Gen
