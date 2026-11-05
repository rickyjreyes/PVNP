import PVNP.SweepTM
import PVNP.WCCDCyclic

/-!
# D-1: an explicit sweep program simulating a `(1+d)`-dimensional WCC

The program keeps, on one tape segment, a cyclic array of length
`N ≥ M^(d+1) + 1` (`M = n + 2G + 3`) holding the flattened configuration of
`PVNP.WCCDCyclic`, together with finite-state bookkeeping tracks:

* `cnt`: a unary counter of length `M`; `gm`: a unary range `0..G`;
* `rp`: the round pointer; `ptr`, `mv`, `bb`: loop markers;
* `ref k`: a marker at cell `M^k` (`k ≤ d+1`), built for each horizon `G`;
* `cur`: the cyclic configuration; `win u`: the neighbourhood window tracks.

One round rotates the window tracks by `±M^k` (count-down loops driven by
`ref k`), then applies the WCC rule cell by cell.  Horizons `G = 0, 1, 2, …`
are tried in turn; for horizon `G` the rounds `0..G` are exact
(`WCCD.cyclic_exact`).  All loops use one-cell marker moves; nothing uses
random access or unbounded registers.

This file defines the program.  Its correctness and cost are proved in
`PVNP.WCCDSweepCorrect`.
-/

namespace PVNP.Discrete.WCCDSweep

open PVNP.Discrete PVNP.Discrete.Sweep

/-- Window index: one digit in `{0,1,2}` per axis (axis `0` first). -/
abbrev Nb (d : ℕ) := Fin (d + 1) → Fin 3

/-- A data cell of the simulator. -/
structure Cell (S : Type) (d : ℕ) where
  inp : Option Bool
  fst : Bool
  cnt : Bool
  gm : Bool
  rp : Bool
  ptr : Bool
  mv : Bool
  bb : Bool
  ref : Fin (d + 2) → Bool
  cur : S
  win : Nb d → S
  deriving DecidableEq

/-- Buffers of the simulator's transducers. -/
structure Buf (S : Type) (d : ℕ) where
  w : Nb d → S
  f1 : Bool
  f2 : Bool
  f3 : Bool
  f4 : Bool
  deriving DecidableEq

section Fin
variable (S : Type) (d : ℕ)

/-- `Cell` as a product type (for the finiteness instance). -/
def Cell.equiv : Cell S d ≃
    Option Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool ×
      (Fin (d + 2) → Bool) × S × (Nb d → S) where
  toFun c := (c.inp, c.fst, c.cnt, c.gm, c.rp, c.ptr, c.mv, c.bb, c.ref, c.cur, c.win)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Buf.equiv : Buf S d ≃ (Nb d → S) × Bool × Bool × Bool × Bool where
  toFun b := (b.w, b.f1, b.f2, b.f3, b.f4)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype S] [DecidableEq S] : Fintype (Cell S d) := Fintype.ofEquiv _ (Cell.equiv S d).symm
instance [Fintype S] [DecidableEq S] : Fintype (Buf S d) := Fintype.ofEquiv _ (Buf.equiv S d).symm
end Fin

/-- Instructions of the simulator. -/
inductive Ins (d : ℕ) where
  | i0
  | iext (r : Fin 3)
  | igm
  | r0
  | rcopy (k : Fin (d + 1))
  | rchk (k : Fin (d + 1))
  | rmov (k : Fin (d + 1))
  | rnext (k : Fin (d + 1))
  | rset (k : Fin (d + 1))
  | xfin
  | chk
  | spread
  | lcopy (k : Fin (d + 1))
  | lchk (k : Fin (d + 1))
  | lmov (k : Fin (d + 1))
  | rcopyR (k : Fin (d + 1))
  | rchkR (k : Fin (d + 1))
  | rmovR (k : Fin (d + 1))
  | app
  | rnd
  | ggm
  | gcnt (r : Fin 2)
  | grst
  deriving DecidableEq, Fintype

variable {d : ℕ} (A : WCCD d)

/-- The default (fresh) cell. -/
def dflt : Cell A.S d :=
  ⟨none, false, false, false, false, false, false, false, fun _ => false, A.blank, fun _ => A.blank⟩

/-- The all-false buffer. -/
def buf0 : Buf A.S d := ⟨fun _ => A.blank, false, false, false, false⟩

/-- Initial cyclic value of a cell (`WCCD.cinit`). -/
def cval (a : Cell A.S d) : A.S :=
  if a.fst then A.origin a.inp else
    match a.inp with
    | some b => A.inp b
    | none => A.blank

/-- The next axis after `k`, if any. -/
def nextAxis (k : Fin (d + 1)) : Option (Fin (d + 1)) :=
  if h : k.val + 1 < d + 1 then some ⟨k.val + 1, h⟩ else none

/-- Forward transducers. -/
def fwd : Ins d → Buf A.S d → Cell A.S d → Cell A.S d × Buf A.S d
  | .i0, b, a => ({a with cnt := true, fst := !b.f1}, {b with f1 := true})
  | .iext _, b, a => (a, {b with f1 := true})
  | .igm, b, a => ({a with gm := a.fst, rp := a.fst, ptr := a.fst}, b)
  | .r0, b, a =>
      ({a with ref := fun k => decide (k = 0) && b.f1, mv := a.fst}, {b with f1 := a.fst})
  | .rcopy k, b, a => ({a with bb := a.ref k.castSucc}, b)
  | .rchk _, b, a =>
      if (if a.fst then a.bb else b.f1) then (a, {b with f1 := true, f2 := false})
      else ({a with mv := b.f2}, {b with f1 := false, f2 := a.mv})
  | .rmov _, b, a => (a, b)
  | .rnext _, b, a =>
      ({a with ptr := b.f1 && a.cnt}, {b with f1 := a.ptr || (b.f1 && !a.cnt)})
  | .rset k, b, a => ({a with ref := Function.update a.ref k.succ a.mv, mv := a.fst}, b)
  | .xfin, b, a => ({a with cur := cval A a}, b)
  | .chk, b, a =>
      (a, { b with
        f1 := b.f1 || A.acc a.cur
        f2 := b.f2 || A.rej a.cur
        f3 := a.rp
        f4 := b.f4 || (b.f3 && !a.gm) })
  | .spread, b, a => ({a with win := fun _ => a.cur}, b)
  | .lcopy k, b, a => ({a with bb := a.ref k.castSucc}, b)
  | .lchk _, b, a => if a.fst then (a, {b with f1 := a.bb, w := a.win}) else (a, b)
  | .lmov _, b, a => (a, b)
  | .rcopyR k, b, a => ({a with bb := a.ref k.castSucc}, b)
  | .rchkR k, b, a =>
      if (if a.fst then a.bb else b.f1) then (a, {b with f1 := true})
      else ({a with win := fun u => if u k = 0 then b.w u else a.win u},
        {b with f1 := false, w := a.win})
  | .rmovR _, b, a => (a, b)
  | .app, b, a => ({a with cur := A.rule fun v => a.win (Fin.cons v.1 v.2)}, b)
  | .rnd, b, a => ({a with rp := b.f1}, {b with f1 := a.rp})
  | .ggm, b, a => if !b.f1 && !a.gm then ({a with gm := true}, {b with f1 := true}) else (a, b)
  | .gcnt _, b, a =>
      if !b.f1 && !a.cnt then ({a with cnt := true}, {b with f1 := true}) else (a, b)
  | .grst, b, a => ({a with rp := a.fst}, b)

/-- Right-end extensions. -/
def ext : Ins d → Buf A.S d → Option (Cell A.S d)
  | .iext _, b => some {dflt A with cnt := true, fst := !b.f1}
  | .rchk _, b => if !b.f1 && b.f2 then some {dflt A with mv := true} else none
  | .gcnt _, b => if b.f1 then none else some {dflt A with cnt := true}
  | _, _ => none

/-- Backward transducers. -/
def bwd : Ins d → Buf A.S d → Cell A.S d → Cell A.S d × Buf A.S d
  | .rmov _, b, a => ({a with bb := b.f1}, {b with f1 := a.bb})
  | .lmov _, b, a => ({a with bb := b.f1}, {b with f1 := a.bb})
  | .rmovR _, b, a => ({a with bb := b.f1}, {b with f1 := a.bb})
  | .rnext _, b, a => ({a with ptr := a.ptr || (b.f1 && a.fst)}, b)
  | .lchk k, b, a =>
      if b.f1 then (a, b)
      else ({a with win := fun u => if u k = 2 then b.w u else a.win u}, {b with w := a.win})
  | .rchkR k, b, a =>
      if b.f1 then (a, b)
      else if a.fst then ({a with win := fun u => if u k = 0 then b.w u else a.win u}, b)
      else (a, b)
  | _, b, a => (a, b)

/-- Initial forward buffers (all instructions start from `buf0`). -/
def init : Ins d → Buf A.S d := fun _ => buf0 A

/-- Control flow. -/
def next : Ins d → Buf A.S d → Ins d ⊕ Bool
  | .i0, _ => .inl (.iext 0)
  | .iext r, _ => if h : r.val = 2 then .inl .igm
      else .inl (.iext ⟨r.val + 1, by have := r.isLt; omega⟩)
  | .igm, _ => .inl .r0
  | .r0, _ => .inl (.rcopy 0)
  | .rcopy k, _ => .inl (.rchk k)
  | .rchk k, b => if b.f1 then .inl (.rnext k) else .inl (.rmov k)
  | .rmov k, _ => .inl (.rchk k)
  | .rnext k, b => if b.f1 then .inl (.rset k) else .inl (.rcopy k)
  | .rset k, _ => match nextAxis k with
      | some k' => .inl (.rcopy k')
      | none => .inl .xfin
  | .xfin, _ => .inl .chk
  | .chk, b =>
      if A.acc A.blank || b.f1 then .inr true
      else if A.rej A.blank || b.f2 then .inr false
      else if b.f4 || b.f3 then .inl .ggm
      else .inl .spread
  | .spread, _ => .inl (.lcopy 0)
  | .lcopy k, _ => .inl (.lchk k)
  | .lchk k, b => if b.f1 then .inl (.rcopyR k) else .inl (.lmov k)
  | .lmov k, _ => .inl (.lchk k)
  | .rcopyR k, _ => .inl (.rchkR k)
  | .rchkR k, b => if b.f1 then
        (match nextAxis k with
         | some k' => .inl (.lcopy k')
         | none => .inl .app)
      else .inl (.rmovR k)
  | .rmovR k, _ => .inl (.rchkR k)
  | .app, _ => .inl .rnd
  | .rnd, _ => .inl .chk
  | .ggm, _ => .inl (.gcnt 0)
  | .gcnt r, _ => if r.val = 0 then .inl (.gcnt 1) else .inl .grst
  | .grst, _ => .inl .r0

/-- How a raw input bit is stored. -/
def liftB (x : Bool) : Cell A.S d := {dflt A with inp := some x}

/-- **The simulating sweep program.** -/
def prog : Prog where
  D := Cell A.S d
  I := Ins d
  B := Buf A.S d
  lift := liftB A
  start := .i0
  init := init A
  fwd := fwd A
  ext := ext A
  bwd := bwd A
  next := next A

/-- **The simulating ordinary single-tape Turing machine.** -/
def toTM : TM := (prog A).toTM

/-! ### Generic index lemmas for transductions -/

section Scan
variable {D B : Type}

/-- Buffer before processing cell `k` in a forward scan. -/
def fbuf (f : B → D → D × B) (b : B) (l : List D) (k : ℕ) : B := (fscan f b (l.take k)).2

theorem fbuf_zero (f : B → D → D × B) (b : B) (l : List D) : fbuf f b l 0 = b := by
  simp [fbuf, fscan]

theorem fscan_append (f : B → D → D × B) :
    ∀ (b : B) (l l' : List D),
      fscan f b (l ++ l') = ((fscan f b l).1 ++ (fscan f (fscan f b l).2 l').1,
        (fscan f (fscan f b l).2 l').2)
  | b, [], l' => by simp [fscan]
  | b, a :: l, l' => by
    simp only [List.cons_append, fscan]
    rw [fscan_append f _ l l']

theorem fbuf_succ (f : B → D → D × B) (b : B) (l : List D) (k : ℕ) (hk : k < l.length) :
    fbuf f b l (k + 1) = (f (fbuf f b l k) l[k]).2 := by
  unfold fbuf
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, fscan_append]
  simp [fscan]

theorem fscan_snd (f : B → D → D × B) (b : B) (l : List D) :
    (fscan f b l).2 = fbuf f b l l.length := by
  simp [fbuf]

theorem fbuf_cons (f : B → D → D × B) (b : B) (a : D) (l : List D) (k : ℕ) :
    fbuf f b (a :: l) (k + 1) = fbuf f (f b a).2 l k := by
  simp [fbuf, fscan]

theorem fscan_getElem (f : B → D → D × B) :
    ∀ (b : B) (l : List D) (k : ℕ) (hk : k < l.length),
      (fscan f b l).1[k]'(by rw [fscan_length]; exact hk) = (f (fbuf f b l k) l[k]).1
  | _, [], _, hk => absurd hk (by simp)
  | b, a :: l, 0, _ => by simp [fscan, fbuf_zero]
  | b, a :: l, k + 1, hk => by
    have ih := fscan_getElem f (f b a).2 l k (by simpa using hk)
    simp only [fscan, List.getElem_cons_succ]
    rw [ih, fbuf_cons]

/-- Buffer before processing cell `k` in a backward scan (cells `k+1, …`
have been processed). -/
def bbuf (f : B → D → D × B) (b : B) (l : List D) (k : ℕ) : B := (bscan f b (l.drop (k + 1))).2

theorem bbuf_cons (f : B → D → D × B) (b : B) (a : D) (l : List D) (k : ℕ) :
    bbuf f b (a :: l) (k + 1) = bbuf f b l k := by
  simp [bbuf]

theorem bbuf_cons_zero (f : B → D → D × B) (b : B) (a : D) (l : List D) :
    bbuf f b (a :: l) 0 = (bscan f b l).2 := by
  simp [bbuf]

theorem bscan_getElem (f : B → D → D × B) :
    ∀ (b : B) (l : List D) (k : ℕ) (hk : k < l.length),
      (bscan f b l).1[k]'(by rw [bscan_length]; exact hk) = (f (bbuf f b l k) l[k]).1
  | _, [], _, hk => absurd hk (by simp)
  | b, a :: l, 0, _ => by simp [bscan, bbuf_cons_zero]
  | b, a :: l, k + 1, hk => by
    have ih := bscan_getElem f b l k (by simpa using hk)
    simp only [bscan, List.getElem_cons_succ]
    rw [ih, bbuf_cons]

theorem bbuf_last (f : B → D → D × B) (b : B) (l : List D) (k : ℕ) (hk : l.length ≤ k + 1) :
    bbuf f b l k = b := by
  simp [bbuf, List.drop_eq_nil_of_le hk, bscan]

theorem bbuf_pred (f : B → D → D × B) (b : B) (l : List D) (k : ℕ) (hk : k + 1 < l.length) :
    bbuf f b l k = (f (bbuf f b l (k + 1)) l[k + 1]).2 := by
  unfold bbuf
  rw [List.drop_eq_getElem_cons hk]
  simp [bscan]

theorem bscan_snd_cons (f : B → D → D × B) (b : B) (l : List D) (hl : 0 < l.length) :
    (bscan f b l).2 = (f (bbuf f b l 0) l[0]).2 := by
  cases l with
  | nil => simp at hl
  | cons a l => simp [bscan, bbuf_cons_zero]

theorem bscan_snd_nil (f : B → D → D × B) (b : B) : (bscan f b []).2 = b := rfl

end Scan

end PVNP.Discrete.WCCDSweep
