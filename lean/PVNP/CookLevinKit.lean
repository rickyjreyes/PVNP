import PVNP.CookLevinTableau
import PVNP.UniformSimLib

/-!
# CL-1, part 2a: a kit of marker round trips for the uniform Cook–Levin generator

The generator of `inst x` is one round-trip sweep program (`PVNP.Discrete.Sweep.Prog`), compiled
to an ordinary single-tape Turing machine by `Prog.toTM`.  Its data cells carry an input bit,
finitely many Boolean marker tracks (`Mk`), a column label and an output bit.  Every instruction
performs one of a few generic operations, each proved here once:

* `grow`: append one fresh cell;
* `shift m`: move every mark of track `m` one cell to the right (appending a cell if needed);
* `first m`: put the only mark of track `m` on cell `0`;
* `clear m`: erase track `m`;
* `setM m t v`, `setCl m c`, `setOut m b`: write on the cells marked by `m`;
* `read k`: leave the cells unchanged and report a finite summary (`RRes`).

Each lemma gives the effect cell by cell, so other tracks are visibly untouched.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim

/-! ## Cells -/

/-- Marker tracks. -/
inductive Mk where
  | ut | uq | sq | st | ca | cw | pb | rk | ck | rv | cv | op | pc | ci | cj | cq
  deriving DecidableEq, Fintype

/-- Column label of the tableau window. -/
structure CLab where
  first : Bool
  last : Bool
  inPre : Bool
  preBit : Bool
  origin : Bool
  wit : Bool
  deriving DecidableEq, Fintype

/-- A data cell. -/
structure Cell where
  inp : Option Bool
  m : Mk → Bool
  cl : Option CLab
  out : Option Bool

instance : DecidableEq Cell := fun a b =>
  decidable_of_iff (a.inp = b.inp ∧ a.m = b.m ∧ a.cl = b.cl ∧ a.out = b.out) (by
    cases a; cases b; simp)

instance : Fintype Cell :=
  Fintype.ofEquiv (Option Bool × (Mk → Bool) × Option CLab × Option Bool)
    ⟨fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩, fun c => (c.inp, c.m, c.cl, c.out),
      fun _ => rfl, fun _ => rfl⟩

/-- The fresh cell. -/
def dflt : Cell := ⟨none, fun _ => false, none, none⟩

/-- Lifted raw input bit. -/
def liftC (b : Bool) : Cell := ⟨some b, fun _ => false, none, none⟩

/-- Update one marker track of a cell. -/
def upd (c : Cell) (k : Mk) (v : Bool) : Cell := { c with m := Function.update c.m k v }

@[simp] theorem upd_m_self (c : Cell) (k : Mk) (v : Bool) : (upd c k v).m k = v := by simp [upd]
@[simp] theorem upd_m_ne (c : Cell) {k k' : Mk} (v : Bool) (h : k' ≠ k) :
    (upd c k v).m k' = c.m k' := by simp [upd, Function.update_of_ne h]
@[simp] theorem upd_inp (c : Cell) (k : Mk) (v : Bool) : (upd c k v).inp = c.inp := rfl
@[simp] theorem upd_cl (c : Cell) (k : Mk) (v : Bool) : (upd c k v).cl = c.cl := rfl
@[simp] theorem upd_out (c : Cell) (k : Mk) (v : Bool) : (upd c k v).out = c.out := rfl

/-! ## Read summaries -/

/-- Relative position of two marks. -/
inductive Rel3 where
  | same | plus | minus | other
  deriving DecidableEq, Fintype

/-- Read kinds. -/
inductive RKind where
  | mark (m t : Mk)      -- is track `t` set at the mark of `m`?
  | zero (m : Mk)        -- is the mark of `m` on cell `0`?
  | next (m t : Mk)      -- is track `t` set on the cell after the mark of `m`?
  | rel (m1 m2 : Mk)     -- position of the mark of `m2` relative to the mark of `m1`
  | lab (m : Mk)         -- column label at the mark of `m`
  | inp (m : Mk)         -- input bit at the mark of `m`
  deriving DecidableEq, Fintype

/-- Read results. -/
inductive RRes where
  | b (v : Bool)
  | r (v : Rel3)
  | l (v : Option CLab)
  | o (v : Option Bool)
  deriving DecidableEq, Fintype

/-- Read state: previous-cell marks, first-cell flag, and the answer once found. -/
structure RS where
  p1 : Bool
  p2 : Bool
  fst : Bool
  res : Option RRes
  deriving DecidableEq, Fintype

def RS.start : RS := ⟨false, false, true, none⟩

/-- One read step. -/
def rstep : RKind → RS → Cell → RS
  | .mark m t, s, a => if s.res = none ∧ a.m m then { s with res := some (.b (a.m t)), fst := false }
      else { s with fst := false }
  | .zero m, s, a => if s.res = none ∧ a.m m then { s with res := some (.b s.fst), fst := false }
      else { s with fst := false }
  | .next m t, s, a => if s.res = none ∧ s.p1 then
        { s with res := some (.b (a.m t)), p1 := a.m m, fst := false }
      else { s with p1 := a.m m, fst := false }
  | .rel m1 m2, s, a =>
      if s.res = none ∧ a.m m1 ∧ a.m m2 then { s with res := some (.r .same), fst := false }
      else if s.res = none ∧ a.m m2 ∧ s.p1 then
        { s with res := some (.r .plus), p1 := a.m m1, p2 := a.m m2, fst := false }
      else if s.res = none ∧ a.m m1 ∧ s.p2 then
        { s with res := some (.r .minus), p1 := a.m m1, p2 := a.m m2, fst := false }
      else { s with p1 := a.m m1, p2 := a.m m2, fst := false }
  | .lab m, s, a => if s.res = none ∧ a.m m then { s with res := some (.l a.cl), fst := false }
      else { s with fst := false }
  | .inp m, s, a => if s.res = none ∧ a.m m then { s with res := some (.o a.inp), fst := false }
      else { s with fst := false }

/-- The answer of a read, with defaults when nothing was found. -/
def answer : RKind → RS → RRes
  | .rel _ _, s => s.res.getD (.r .other)
  | .lab _, s => s.res.getD (.l none)
  | .inp _, s => s.res.getD (.o none)
  | _, s => s.res.getD (.b false)

/-! ## Operations -/

/-- One round trip of the generator. -/
inductive Op where
  | grow
  | shift (m : Mk)
  | first (m : Mk)
  | clear (m : Mk)
  | setM (m t : Mk) (v : Bool)
  | setCl (m : Mk) (c : CLab)
  | setOut (m : Mk) (b : Bool)
  | read (k : RKind)
  deriving DecidableEq

/-- Buffers: a carry bit and a read state. -/
abbrev Buf := Bool × RS

def Op.init : Op → Buf
  | .first _ => (true, RS.start)
  | _ => (false, RS.start)

def Op.fwd : Op → Buf → Cell → Cell × Buf
  | .grow, b, a => (a, b)
  | .shift m, b, a => (upd a m b.1, (a.m m, b.2))
  | .first m, b, a => (upd a m b.1, (false, b.2))
  | .clear m, b, a => (upd a m false, b)
  | .setM m t v, b, a => (if a.m m then upd a t v else a, b)
  | .setCl m c, b, a => (if a.m m then { a with cl := some c } else a, b)
  | .setOut m v, b, a => (if a.m m then { a with out := some v } else a, b)
  | .read k, b, a => (a, (b.1, rstep k b.2 a))

def Op.ext : Op → Buf → Option Cell
  | .grow, _ => some dflt
  | .shift m, b => if b.1 then some (upd dflt m true) else none
  | _, _ => none

/-! ## Scans with trivial cell output or a carry -/

section Scans

theorem fscan_id {B : Type} (st : B → Cell → B) :
    ∀ (b : B) (l : List Cell), fscan (fun b a => (a, st b a)) b l = (l, l.foldl st b)
  | _, [] => rfl
  | b, a :: l => by simp [fscan, fscan_id st _ l]

theorem bscan_id {B : Type} : ∀ (b : B) (l : List Cell), bscan (fun b a => (a, b)) b l = (l, b)
  | _, [] => rfl
  | b, a :: l => by simp [bscan, bscan_id b l]

/-- A cellwise map with a constant buffer. -/
theorem fscan_map {B : Type} (g : Cell → Cell) :
    ∀ (b : B) (l : List Cell), fscan (fun b a => (g a, b)) b l = (l.map g, b)
  | _, [] => rfl
  | b, a :: l => by simp [fscan, fscan_map g b l]

theorem fscan_shift_snd (k : Mk) (r : RS) :
    ∀ (c : Bool) (l : List Cell),
      (fscan (Op.fwd (.shift k)) (c, r) l).2 = ((l.getLast?.map (·.m k)).getD c, r)
  | c, [] => by simp [fscan]
  | c, a :: l => by
    simp only [fscan, Op.fwd]
    rw [fscan_shift_snd k r (a.m k) l]
    rcases l with _ | ⟨b, l⟩
    · simp
    · simp only [List.getLast?_cons, Option.getD_some, Option.map_some]

theorem fscan_shift_fst (k : Mk) (r : RS) :
    ∀ (c : Bool) (l : List Cell) (j : ℕ) (hj : j < l.length),
      (fscan (Op.fwd (.shift k)) (c, r) l).1[j]'(by rw [fscan_length]; exact hj) =
        upd l[j] k (if j = 0 then c else (l[j - 1]'(by omega)).m k)
  | c, a :: l, 0, _ => by simp [fscan, Op.fwd]
  | c, a :: l, j + 1, hj => by
    simp only [fscan, Op.fwd, List.getElem_cons_succ]
    rw [fscan_shift_fst k r (a.m k) l j (by simp at hj; omega)]
    rcases j with _ | j
    · simp
    · simp

end Scans

/-! ## List-level effects -/

/-- The data after one operation. -/
def Op.eff : Op → List Cell → List Cell
  | .grow, l => l ++ [dflt]
  | .shift m, l => (fscan (Op.fwd (.shift m)) (false, RS.start) l).1 ++
      (if (l.getLast?.map (·.m m)).getD false then [upd dflt m true] else [])
  | .first m, l => (fscan (Op.fwd (.first m)) (true, RS.start) l).1
  | .clear m, l => l.map fun a => upd a m false
  | .setM m t v, l => l.map fun a => if a.m m then upd a t v else a
  | .setCl m c, l => l.map fun a => if a.m m then { a with cl := some c } else a
  | .setOut m v, l => l.map fun a => if a.m m then { a with out := some v } else a
  | .read _, l => l

/-- The summary reported by one operation. -/
def Op.res : Op → List Cell → RRes
  | .read k, l => answer k (l.foldl (rstep k) RS.start)
  | _, _ => .b false

/-! ## Programs built from operations -/

/-- A generator program: control states, the operation of each state, and the continuation. -/
structure Ctrl where
  C : Type
  [finC : Fintype C]
  [decC : DecidableEq C]
  start : C
  op : C → Op
  nxt : C → RRes → C ⊕ Bool

attribute [instance] Ctrl.finC Ctrl.decC

namespace Ctrl

variable (G : Ctrl)

/-- The compiled sweep program. -/
def prog : Prog where
  D := Cell
  I := G.C
  B := Buf
  lift := liftC
  start := G.start
  init c := (G.op c).init
  fwd c := (G.op c).fwd
  ext c := (G.op c).ext
  bwd _ := fun b a => (a, b)
  next c b := G.nxt c (match G.op c with
    | .read k => answer k b.2
    | _ => .b false)

theorem fwd_first_snd (m : Mk) : ∀ (c : Bool) (r : RS) (l : List Cell),
    (fscan (Op.fwd (.first m)) (c, r) l).2.2 = r
  | _, _, [] => rfl
  | c, r, a :: l => by simp only [fscan, Op.fwd]; exact fwd_first_snd m false r l

theorem fwd_read_eq (k : RKind) : ∀ (c : Bool) (r : RS) (l : List Cell),
    fscan (Op.fwd (.read k)) (c, r) l = (l, (c, l.foldl (rstep k) r))
  | _, _, [] => rfl
  | c, r, a :: l => by simp [fscan, Op.fwd, fwd_read_eq k c (rstep k r a) l]

theorem fwd_map {g : Cell → Cell} {o : Op} (ho : ∀ b a, o.fwd b a = (g a, b)) :
    ∀ (b : Buf) (l : List Cell), fscan o.fwd b l = (l.map g, b)
  | _, [] => rfl
  | b, a :: l => by simp [fscan, ho, fwd_map ho b l]

theorem trip_unfold (c : G.C) (l : List Cell) :
    G.prog.trip c l = ((fscan (G.op c).fwd (G.op c).init l).1 ++
      ((G.op c).ext (fscan (G.op c).fwd (G.op c).init l).2).toList,
      (fscan (G.op c).fwd (G.op c).init l).2) := by
  simp only [Prog.trip, Prog.mid, Prog.fpass, prog]
  exact bscan_id _ _

/-- **One round trip** performs the operation of the control state. -/
theorem trip_fst (c : G.C) (l : List Cell) : (G.prog.trip c l).1 = (G.op c).eff l := by
  rw [trip_unfold]
  rcases G.op c with _ | m | m | m | ⟨m, t, v⟩ | ⟨m, cc⟩ | ⟨m, v⟩ | k
  · simp [Op.eff, Op.init, Op.ext, fwd_map (o := .grow) (g := id) (fun _ _ => rfl)]
  · simp only [Op.eff, Op.init, Op.ext, fscan_shift_snd]
    split_ifs <;> simp
  · simp [Op.eff, Op.init, Op.ext]
  · simp [Op.eff, Op.init, Op.ext, fwd_map (o := .clear m) (g := fun a => upd a m false)
      (fun _ _ => rfl)]
  · simp [Op.eff, Op.init, Op.ext, fwd_map (o := .setM m t v)
      (g := fun a => if a.m m then upd a t v else a) (fun _ _ => rfl)]
  · simp [Op.eff, Op.init, Op.ext, fwd_map (o := .setCl m cc)
      (g := fun a => if a.m m then { a with cl := some cc } else a) (fun _ _ => rfl)]
  · simp [Op.eff, Op.init, Op.ext, fwd_map (o := .setOut m v)
      (g := fun a => if a.m m then { a with out := some v } else a) (fun _ _ => rfl)]
  · simp [Op.eff, Op.init, Op.ext, fwd_read_eq]

theorem trip_snd_read (c : G.C) (l : List Cell) {k : RKind} (h : G.op c = .read k) :
    (G.prog.trip c l).2.2 = l.foldl (rstep k) RS.start := by
  rw [trip_unfold, h]
  simp [Op.init, fwd_read_eq]

/-- **One program step.** -/
theorem stepP_eq (c : G.C) (l : List Cell) :
    G.prog.stepP (c, l) = match G.nxt c ((G.op c).res l) with
      | .inl c' => .inl (c', (G.op c).eff l)
      | .inr a => .inr (a, (G.op c).eff l) := by
  have hn : G.prog.next c (G.prog.trip c l).2 = G.nxt c ((G.op c).res l) := by
    show G.nxt c (match G.op c with
      | .read k => answer k (G.prog.trip c l).2.2
      | _ => .b false) = _
    rcases hop : G.op c with _ | m | m | m | ⟨m, t, v⟩ | ⟨m, cc⟩ | ⟨m, v⟩ | k
    all_goals simp only [Op.res]
    rw [trip_snd_read G c l hop]
  simp only [Prog.stepP]
  rw [hn, trip_fst]
  cases G.nxt c ((G.op c).res l) <;> rfl

theorem step_of (c c' : G.C) (l : List Cell) (h : G.nxt c ((G.op c).res l) = .inl c') :
    RN G.prog (c, l) (c', (G.op c).eff l) 1 :=
  RN.single (by rw [stepP_eq, h])

end Ctrl

/-! ## Cellwise effects -/

section Effects

theorem eff_length_le (o : Op) (l : List Cell) : l.length ≤ (o.eff l).length := by
  cases o <;> simp [Op.eff, fscan_length] <;> split_ifs <;> simp

theorem eff_length_le_succ (o : Op) (l : List Cell) : (o.eff l).length ≤ l.length + 1 := by
  cases o <;> simp [Op.eff, fscan_length] <;> split_ifs <;> simp

theorem eff_shift_get (k : Mk) (l : List Cell) (j : ℕ) (hj : j < (Op.eff (.shift k) l).length) :
    (Op.eff (.shift k) l)[j] =
      upd (l.getD j dflt) k (if j = 0 then false else (l.getD (j - 1) dflt).m k) := by
  have hlen : (fscan (Op.fwd (.shift k)) (false, RS.start) l).1.length = l.length := fscan_length _ _ _
  by_cases hjl : j < l.length
  · simp only [Op.eff]
    rw [List.getElem_append_left (by rw [hlen]; exact hjl), fscan_shift_fst k RS.start
      false l j hjl, List.getD_eq_getElem _ _ hjl]
    split_ifs with h0
    · rfl
    · rw [List.getD_eq_getElem _ _ (by omega)]
  · by_cases hlast : (l.getLast?.map (·.m k)).getD false = true
    · have hj' : j = l.length := by
        simp only [Op.eff, if_pos hlast, List.length_append, hlen, List.length_singleton] at hj
        omega
      subst hj'
      simp only [Op.eff, if_pos hlast]
      rw [List.getElem_append_right (by rw [hlen])]
      simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
      have hne : l ≠ [] := by rintro rfl; simp at hlast
      have hl0 : l.length ≠ 0 := by simpa using hne
      rw [if_neg hl0, List.getD_eq_default _ _ le_rfl, List.getD_eq_getElem _ _ (by omega)]
      rw [List.getLast?_eq_getLast hne] at hlast
      simp only [Option.map_some, Option.getD_some] at hlast
      rw [List.getLast_eq_getElem] at hlast
      simp [hlast, upd, dflt]
    · simp only [Op.eff, if_neg hlast, List.append_nil, hlen] at hj
      omega

theorem eff_shift_length (k : Mk) (l : List Cell) :
    (Op.eff (.shift k) l).length =
      l.length + (if (l.getLast?.map (·.m k)).getD false then 1 else 0) := by
  simp only [Op.eff]; split_ifs <;> simp [fscan_length]

theorem fscan_first_fst (k : Mk) :
    ∀ (c : Bool) (r : RS) (l : List Cell) (j : ℕ) (hj : j < l.length),
      (fscan (Op.fwd (.first k)) (c, r) l).1[j]'(by rw [fscan_length]; exact hj) =
        upd l[j] k (if j = 0 then c else false)
  | c, r, a :: l, 0, _ => by simp [fscan, Op.fwd]
  | c, r, a :: l, j + 1, hj => by
    simp only [fscan, Op.fwd, List.getElem_cons_succ]
    rw [fscan_first_fst k false r l j (by simp at hj; omega)]
    simp

theorem eff_first_get (k : Mk) (l : List Cell) (j : ℕ) (hj : j < (Op.eff (.first k) l).length) :
    (Op.eff (.first k) l)[j] = upd (l[j]'(by simpa [Op.eff, fscan_length] using hj)) k
      (decide (j = 0)) := by
  simp only [Op.eff]
  rw [fscan_first_fst k true RS.start l j (by simpa [Op.eff, fscan_length] using hj)]
  by_cases h : j = 0 <;> simp [h]

theorem eff_first_length (k : Mk) (l : List Cell) : (Op.eff (.first k) l).length = l.length := by
  simp [Op.eff, fscan_length]

end Effects

/-! ## Unique marks and prefix runs -/

/-- The only mark of track `k` is on cell `p`. -/
def Uniq (l : List Cell) (k : Mk) (p : ℕ) : Prop :=
  p < l.length ∧ ∀ (j : ℕ) (hj : j < l.length), l[j].m k = decide (j = p)

/-- Track `k` is marked exactly on the cells `< r`, with `r ≤ |l|`. -/
def Run (l : List Cell) (k : Mk) (r : ℕ) : Prop :=
  r ≤ l.length ∧ ∀ (j : ℕ) (hj : j < l.length), l[j].m k = decide (j < r)

theorem getLast_mark {l : List Cell} {k : Mk} {p : ℕ} (h : Uniq l k p) :
    (l.getLast?.map (·.m k)).getD false = decide (p + 1 = l.length) := by
  have hne : l ≠ [] := by rintro rfl; simp [Uniq] at h
  rw [List.getLast?_eq_getLast hne]
  simp only [Option.map_some, Option.getD_some, List.getLast_eq_getElem]
  rw [h.2]
  have := h.1
  by_cases hp : p + 1 = l.length
  · simp [hp]; omega
  · simp [hp]; omega

theorem shift_uniq {l : List Cell} {k : Mk} {p : ℕ} (h : Uniq l k p) :
    Uniq (Op.eff (.shift k) l) k (p + 1) ∧
      (Op.eff (.shift k) l).length = max l.length (p + 2) := by
  have hlen := eff_shift_length k l
  rw [getLast_mark h] at hlen
  have hp := h.1
  have hlen' : (Op.eff (.shift k) l).length = max l.length (p + 2) := by
    rw [hlen]
    by_cases hp1 : p + 1 = l.length
    · simp only [hp1, decide_true, if_true]; omega
    · simp only [hp1, decide_false, Bool.false_eq_true, if_false]; omega
  refine ⟨⟨by rw [hlen']; omega, fun j hj => ?_⟩, hlen'⟩
  rw [eff_shift_get]
  simp only [upd_m_self]
  split_ifs with h0
  · subst h0; simp
  · have hjb : j < max l.length (p + 2) := by rw [← hlen']; exact hj
    by_cases hj1 : j - 1 < l.length
    · rw [List.getD_eq_getElem _ _ hj1, h.2]
      simp only [decide_eq_decide]; omega
    · exfalso; omega

theorem shift_other {l : List Cell} {k k' : Mk} (hk : k' ≠ k) (j : ℕ)
    (hj : j < (Op.eff (.shift k) l).length) :
    (Op.eff (.shift k) l)[j].m k' = (l.getD j dflt).m k' ∧
      (Op.eff (.shift k) l)[j].inp = (l.getD j dflt).inp ∧
      (Op.eff (.shift k) l)[j].cl = (l.getD j dflt).cl ∧
      (Op.eff (.shift k) l)[j].out = (l.getD j dflt).out := by
  rw [eff_shift_get]; simp [hk]

theorem first_uniq {l : List Cell} {k : Mk} (h : 0 < l.length) : Uniq (Op.eff (.first k) l) k 0 := by
  refine ⟨by rw [eff_first_length]; exact h, fun j hj => ?_⟩
  rw [eff_first_get]; simp

/-! ## Reads -/

section Reads

theorem rstep_res_stable (k : RKind) (s : RS) (a : Cell) (h : s.res ≠ none) :
    (rstep k s a).res = s.res := by
  cases k <;> simp only [rstep] <;> split_ifs <;> simp_all

theorem foldl_res_stable (k : RKind) : ∀ (l : List Cell) (s : RS), s.res ≠ none →
    (l.foldl (rstep k) s).res = s.res
  | [], _, _ => rfl
  | a :: l, s, h => by
    rw [List.foldl_cons, foldl_res_stable k l _ (by rw [rstep_res_stable k s a h]; exact h),
      rstep_res_stable k s a h]

/-- A read that fires at the unique mark of `m` (kinds `mark`, `zero`, `lab`, `inp`). -/
theorem foldl_hit {k : RKind} {m : Mk} (val : RS → Cell → RRes)
    (hstep : ∀ s a, rstep k s a = if s.res = none ∧ a.m m = true
      then { s with res := some (val s a), fst := false } else { s with fst := false }) :
    ∀ (l : List Cell) (s : RS) (p : ℕ) (hp : p < l.length), s.res = none →
      (∀ (j : ℕ) (hj : j < l.length), l[j].m m = decide (j = p)) →
      (l.foldl (rstep k) s).res = some (val (if p = 0 then s else { s with fst := false }) l[p])
  | a :: l, s, 0, _, hs, hm => by
    rw [List.foldl_cons, hstep]
    have : a.m m = true := by simpa using hm 0 (by simp)
    rw [if_pos ⟨hs, this⟩, foldl_res_stable k l _ (by simp)]
    simp
  | a :: l, s, p + 1, hp, hs, hm => by
    rw [List.foldl_cons, hstep]
    have : a.m m = false := by simpa using hm 0 (by simp)
    rw [if_neg (by simp [this])]
    rw [foldl_hit val hstep l _ p (by simp at hp; omega) (by simpa using hs)
      (fun j hj => by simpa using hm (j + 1) (by simp; omega))]
    simp only [List.getElem_cons_succ, if_neg (Nat.succ_ne_zero p)]
    split_ifs <;> rfl

theorem read_mark {l : List Cell} {m : Mk} {p : ℕ} (h : Uniq l m p) (t : Mk) :
    (Op.read (.mark m t)).res l = .b ((l[p]'h.1).m t) := by
  simp only [Op.res, answer]
  rw [foldl_hit (k := .mark m t) (m := m) (fun _ a => .b (a.m t)) (fun s a => rfl) l _ p h.1 rfl h.2]
  rfl

theorem read_zero {l : List Cell} {m : Mk} {p : ℕ} (h : Uniq l m p) :
    (Op.read (.zero m)).res l = .b (decide (p = 0)) := by
  simp only [Op.res, answer]
  rw [foldl_hit (k := .zero m) (m := m) (fun s _ => .b s.fst) (fun s a => rfl) l _ p h.1 rfl h.2]
  split_ifs with hp <;> simp [hp, RS.start]

theorem read_lab {l : List Cell} {m : Mk} {p : ℕ} (h : Uniq l m p) :
    (Op.read (.lab m)).res l = .l ((l[p]'h.1).cl) := by
  simp only [Op.res, answer]
  rw [foldl_hit (k := .lab m) (m := m) (fun _ a => .l a.cl) (fun s a => rfl) l _ p h.1 rfl h.2]
  rfl

theorem read_inp {l : List Cell} {m : Mk} {p : ℕ} (h : Uniq l m p) :
    (Op.read (.inp m)).res l = .o ((l[p]'h.1).inp) := by
  simp only [Op.res, answer]
  rw [foldl_hit (k := .inp m) (m := m) (fun _ a => .o a.inp) (fun s a => rfl) l _ p h.1 rfl h.2]
  rfl

end Reads

/-! ## The `next` read -/

theorem foldl_next_none (m t : Mk) : ∀ (l : List Cell) (s : RS), s.res = none → s.p1 = false →
    (∀ (j : ℕ) (hj : j < l.length), l[j].m m = false) →
    (l.foldl (rstep (.next m t)) s).res = none
  | [], _, h, _, _ => h
  | a :: l, s, h, hp, hm => by
    rw [List.foldl_cons]
    have ha : a.m m = false := hm 0 (by simp)
    apply foldl_next_none m t l
    · simp only [rstep]; rw [if_neg (by simp [hp])]; exact h
    · simp only [rstep]; rw [if_neg (by simp [hp])]; exact ha
    · intro j hj; exact hm (j + 1) (by simp; omega)

theorem foldl_next (m t : Mk) : ∀ (l : List Cell) (s : RS) (p : ℕ), p < l.length →
    s.res = none → s.p1 = false → (∀ (j : ℕ) (hj : j < l.length), l[j].m m = decide (j = p)) →
    answer (.next m t) (l.foldl (rstep (.next m t)) s) = .b ((l.getD (p + 1) dflt).m t)
  | a :: l, s, 0, _, h, hp, hm => by
    rw [List.foldl_cons]
    have ha : a.m m = true := by simpa using hm 0 (by simp)
    have s1 : rstep (.next m t) s a = { s with p1 := true, fst := false } := by
      simp only [rstep]; rw [if_neg (by simp [hp]), ha]
    rw [s1]
    rcases l with _ | ⟨b, l⟩
    · simp [answer, h, dflt]
    · rw [List.foldl_cons]
      have s2 : rstep (.next m t) { s with p1 := true, fst := false } b =
          { s with res := some (.b (b.m t)), p1 := b.m m, fst := false } := by
        simp only [rstep]; rw [if_pos (by simp [h])]
      rw [s2]
      simp only [answer]
      rw [foldl_res_stable _ _ _ (by simp)]
      simp
  | a :: l, s, p + 1, hpl, h, hp, hm => by
    rw [List.foldl_cons]
    have ha : a.m m = false := by simpa using hm 0 (by simp)
    have s1 : rstep (.next m t) s a = { s with p1 := false, fst := false } := by
      simp only [rstep]; rw [if_neg (by simp [hp]), ha]
    rw [s1, foldl_next m t l { s with p1 := false, fst := false } p (by simp at hpl; omega) h rfl
      (fun j hj => by simpa using hm (j + 1) (by simp; omega))]
    simp

theorem read_next {l : List Cell} {m : Mk} {p : ℕ} (h : Uniq l m p) (t : Mk) :
    (Op.read (.next m t)).res l = .b ((l.getD (p + 1) dflt).m t) :=
  foldl_next m t l RS.start p h.1 rfl rfl h.2

/-! ## Frames: what an operation leaves unchanged -/

/-- `b` agrees with `a` except possibly on marker track `k`. -/
def AgK (k : Mk) (a b : Cell) : Prop :=
  (∀ k', k' ≠ k → b.m k' = a.m k') ∧ b.inp = a.inp ∧ b.cl = a.cl ∧ b.out = a.out

/-- `l'` extends `l` cellwise by the relation `R` (fresh cells compared with `dflt`). -/
def Fr (R : Cell → Cell → Prop) (l l' : List Cell) : Prop :=
  l.length ≤ l'.length ∧ ∀ (j : ℕ) (hj : j < l'.length), R (l.getD j dflt) l'[j]

theorem AgK.refl (k : Mk) (a : Cell) : AgK k a a := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem fr_shift (k : Mk) (l : List Cell) : Fr (AgK k) l (Op.eff (.shift k) l) := by
  refine ⟨eff_length_le _ l, fun j hj => ?_⟩
  rw [eff_shift_get]
  exact ⟨fun k' hk' => by simp [hk'], rfl, rfl, rfl⟩

theorem fr_first (k : Mk) (l : List Cell) : Fr (AgK k) l (Op.eff (.first k) l) := by
  refine ⟨eff_length_le _ l, fun j hj => ?_⟩
  rw [eff_first_get, List.getD_eq_getElem _ _ (by simpa [eff_first_length] using hj)]
  exact ⟨fun k' hk' => by simp [hk'], rfl, rfl, rfl⟩

theorem eff_map_get {g : Cell → Cell} {o : Op} (ho : ∀ l, o.eff l = l.map g) (l : List Cell)
    (j : ℕ) (hj : j < (o.eff l).length) :
    (o.eff l)[j] = g (l[j]'(by rw [ho, List.length_map] at hj; exact hj)) := by
  simp only [ho, List.getElem_map]

theorem eff_clear (k : Mk) (l : List Cell) : Op.eff (.clear k) l = l.map fun a => upd a k false := rfl
theorem eff_setM (m t : Mk) (v : Bool) (l : List Cell) :
    Op.eff (.setM m t v) l = l.map fun a => if a.m m then upd a t v else a := rfl
theorem eff_setOut (m : Mk) (v : Bool) (l : List Cell) :
    Op.eff (.setOut m v) l = l.map fun a => if a.m m then { a with out := some v } else a := rfl
theorem eff_setCl (m : Mk) (c : CLab) (l : List Cell) :
    Op.eff (.setCl m c) l = l.map fun a => if a.m m then { a with cl := some c } else a := rfl
theorem eff_read (k : RKind) (l : List Cell) : Op.eff (.read k) l = l := rfl
theorem eff_grow (l : List Cell) : Op.eff .grow l = l ++ [dflt] := rfl

theorem fr_clear (k : Mk) (l : List Cell) : Fr (AgK k) l (Op.eff (.clear k) l) := by
  refine ⟨by simp [eff_clear], fun j hj => ?_⟩
  rw [eff_map_get (eff_clear k), List.getD_eq_getElem _ _ (by simpa [eff_clear] using hj)]
  exact ⟨fun k' hk' => by simp [hk'], rfl, rfl, rfl⟩

theorem fr_setM (m t : Mk) (v : Bool) (l : List Cell) : Fr (AgK t) l (Op.eff (.setM m t v) l) := by
  refine ⟨by simp [eff_setM], fun j hj => ?_⟩
  rw [eff_map_get (eff_setM m t v), List.getD_eq_getElem _ _ (by simpa [eff_setM] using hj)]
  split_ifs
  · exact ⟨fun k' hk' => by simp [hk'], rfl, rfl, rfl⟩
  · exact AgK.refl _ _

/-- Unique marks of an untouched track survive. -/
theorem Uniq.fr {k k' : Mk} {l l' : List Cell} {p : ℕ} (h : Uniq l k' p) (hf : Fr (AgK k) l l')
    (hk : k' ≠ k) : Uniq l' k' p := by
  refine ⟨by have := h.1; have := hf.1; omega, fun j hj => ?_⟩
  rw [(hf.2 j hj).1 k' hk]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.2]
  · rw [List.getD_eq_default _ _ (by omega)]; simp [dflt]; have := h.1; omega

/-- Prefix runs of an untouched track survive. -/
theorem Run.fr {k k' : Mk} {l l' : List Cell} {r : ℕ} (h : Run l k' r) (hf : Fr (AgK k) l l')
    (hk : k' ≠ k) : Run l' k' r := by
  refine ⟨by have := h.1; have := hf.1; omega, fun j hj => ?_⟩
  rw [(hf.2 j hj).1 k' hk]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.2]
  · rw [List.getD_eq_default _ _ (by omega)]; simp [dflt]; have := h.1; omega

/-! ## Frames over several tracks -/

/-- `b` agrees with `a` except possibly on the marker tracks in `S`. -/
def AgS (S : Mk → Bool) (a b : Cell) : Prop :=
  (∀ k, S k = false → b.m k = a.m k) ∧ b.inp = a.inp ∧ b.cl = a.cl ∧ b.out = a.out

theorem AgS.refl (S : Mk → Bool) (a : Cell) : AgS S a a := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem AgS.trans {S₁ S₂ : Mk → Bool} {a b c : Cell} (h₁ : AgS S₁ a b) (h₂ : AgS S₂ b c) :
    AgS (fun k => S₁ k || S₂ k) a c :=
  ⟨fun k hk => by
    simp only [Bool.or_eq_false_iff] at hk
    rw [h₂.1 k hk.2, h₁.1 k hk.1], by rw [h₂.2.1, h₁.2.1], by rw [h₂.2.2.1, h₁.2.2.1],
    by rw [h₂.2.2.2, h₁.2.2.2]⟩

theorem AgS.mono {S S' : Mk → Bool} (hS : ∀ k, S k = true → S' k = true) {a b : Cell}
    (h : AgS S a b) : AgS S' a b :=
  ⟨fun k hk => h.1 k (by cases h' : S k <;> simp_all [hS k]), h.2⟩

theorem AgK.agS {k : Mk} {S : Mk → Bool} (hk : S k = true) {a b : Cell} (h : AgK k a b) :
    AgS S a b :=
  ⟨fun k' hk' => h.1 k' (by rintro rfl; simp_all), h.2⟩

theorem AgS.dflt_self (S : Mk → Bool) : AgS S dflt dflt := AgS.refl _ _

theorem Fr.mono {R R' : Cell → Cell → Prop} (hR : ∀ a b, R a b → R' a b) {l l' : List Cell}
    (h : Fr R l l') : Fr R' l l' := ⟨h.1, fun j hj => hR _ _ (h.2 j hj)⟩

theorem Fr.refl_agS (S : Mk → Bool) (l : List Cell) : Fr (AgS S) l l :=
  ⟨le_rfl, fun j hj => by rw [List.getD_eq_getElem _ _ hj]; exact AgS.refl _ _⟩

theorem Fr.trans {S₁ S₂ : Mk → Bool} {l l' l'' : List Cell} (h₁ : Fr (AgS S₁) l l')
    (h₂ : Fr (AgS S₂) l' l'') : Fr (AgS fun k => S₁ k || S₂ k) l l'' := by
  refine ⟨le_trans h₁.1 h₂.1, fun j hj => ?_⟩
  have h2 := h₂.2 j hj
  by_cases hj' : j < l'.length
  · have h1 := h₁.2 j hj'
    rw [List.getD_eq_getElem _ _ hj'] at h2
    exact h1.trans h2
  · rw [List.getD_eq_default _ _ (by omega)] at h2
    rw [List.getD_eq_default _ _ (by have := h₁.1; omega)]
    exact (AgS.refl S₁ dflt).trans h2

/-- The input region: cells `< n` carry input bits, the others none. -/
def InpR (l : List Cell) (n : ℕ) : Prop :=
  n ≤ l.length ∧ ∀ (j : ℕ) (hj : j < l.length), (l[j].inp).isSome = decide (j < n)

theorem InpR.fr {S : Mk → Bool} {l l' : List Cell} {n : ℕ} (h : InpR l n) (hf : Fr (AgS S) l l') :
    InpR l' n := by
  refine ⟨le_trans h.1 hf.1, fun j hj => ?_⟩
  rw [(hf.2 j hj).2.1]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.2]
  · rw [List.getD_eq_default _ _ (by omega)]; simp [dflt]; have := h.1; omega

theorem Uniq.frS {S : Mk → Bool} {k : Mk} {l l' : List Cell} {p : ℕ} (h : Uniq l k p)
    (hf : Fr (AgS S) l l') (hk : S k = false) : Uniq l' k p := by
  refine ⟨by have := h.1; have := hf.1; omega, fun j hj => ?_⟩
  rw [(hf.2 j hj).1 k hk]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.2]
  · rw [List.getD_eq_default _ _ (by omega)]; simp [dflt]; have := h.1; omega

theorem Run.frS {S : Mk → Bool} {k : Mk} {l l' : List Cell} {r : ℕ} (h : Run l k r)
    (hf : Fr (AgS S) l l') (hk : S k = false) : Run l' k r := by
  refine ⟨by have := h.1; have := hf.1; omega, fun j hj => ?_⟩
  rw [(hf.2 j hj).1 k hk]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, h.2]
  · rw [List.getD_eq_default _ _ (by omega)]; simp [dflt]; have := h.1; omega

theorem Fr.agK_agS {k : Mk} {S : Mk → Bool} (hk : S k = true) {l l' : List Cell}
    (h : Fr (AgK k) l l') : Fr (AgS S) l l' := Fr.mono (fun _ _ h => AgK.agS hk h) h

/-- Setting track `t` on the cell marked by `m` extends a run of `t` by one. -/
theorem setM_run {l : List Cell} {m t : Mk} {r : ℕ} (hm : Uniq l m r) (ht : Run l t r) (hmt : m ≠ t) :
    Run (Op.eff (.setM m t true) l) t (r + 1) ∧ Uniq (Op.eff (.setM m t true) l) m r := by
  have hlen : (Op.eff (.setM m t true) l).length = l.length := by simp [eff_setM]
  refine ⟨⟨by rw [hlen]; exact hm.1, fun j hj => ?_⟩, ⟨by rw [hlen]; exact hm.1, fun j hj => ?_⟩⟩
  · rw [eff_map_get (eff_setM m t true)]
    have hjl : j < l.length := by rwa [hlen] at hj
    rw [hm.2 j hjl]
    by_cases hjr : j = r
    · subst hjr; simp
    · simp only [hjr, decide_false, Bool.false_eq_true, if_false]
      rw [ht.2 j hjl]; simp only [decide_eq_decide]; omega
  · rw [eff_map_get (eff_setM m t true)]
    have hjl : j < l.length := by rwa [hlen] at hj
    split_ifs
    · rw [upd_m_ne _ _ hmt, hm.2 j hjl]
    · exact hm.2 j hjl

/-! ## Sequential composition of programs -/

/-- Run `G₁`; when it halts, start `G₂`. -/
def seq (G₁ G₂ : Ctrl) : Ctrl where
  C := G₁.C ⊕ G₂.C
  start := .inl G₁.start
  op := Sum.elim G₁.op G₂.op
  nxt
    | .inl c, r => match G₁.nxt c r with
        | .inl c' => .inl (.inl c')
        | .inr _ => .inl (.inr G₂.start)
    | .inr c, r => match G₂.nxt c r with
        | .inl c' => .inl (.inr c')
        | .inr a => .inr a

theorem RN.cast_k {P : Prog} {s s' : P.I × List P.D} {k k' : ℕ} (h : RN P s s' k) (hk : k = k') :
    RN P s s' k' := hk ▸ h

section Seq

variable {G₁ G₂ : Ctrl}

theorem seq_op_inl (c : G₁.C) : (seq G₁ G₂).op (.inl c) = G₁.op c := rfl
theorem seq_op_inr (c : G₂.C) : (seq G₁ G₂).op (.inr c) = G₂.op c := rfl
theorem seq_nxt_inl (c : G₁.C) (r : RRes) : (seq G₁ G₂).nxt (.inl c) r =
    match G₁.nxt c r with
    | .inl c' => .inl (.inl c')
    | .inr _ => .inl (.inr G₂.start) := rfl
theorem seq_nxt_inr (c : G₂.C) (r : RRes) : (seq G₁ G₂).nxt (.inr c) r =
    match G₂.nxt c r with
    | .inl c' => .inl (.inr c')
    | .inr a => .inr a := rfl

theorem RN.seq_left : ∀ {s s' : G₁.prog.I × List G₁.prog.D} {k : ℕ}, RN G₁.prog s s' k →
    RN (seq G₁ G₂).prog (.inl s.1, s.2) (.inl s'.1, s'.2) k := by
  intro s s' k h
  induction h with
  | refl s => exact RN.refl _
  | @step s s₂ s₃ k hstep _ ih =>
    obtain ⟨c, l⟩ := s
    obtain ⟨c₂, l₂⟩ := s₂
    rw [Ctrl.stepP_eq] at hstep
    rcases hn : G₁.nxt c ((G₁.op c).res l) with c₁ | a
    · rw [hn] at hstep
      simp only [Sum.inl.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      refine RN.step ?_ ih
      rw [Ctrl.stepP_eq, seq_op_inl, seq_nxt_inl, hn]
    · rw [hn] at hstep; simp at hstep

theorem RN.seq_exit {c : G₁.C} {l : List Cell} {a : Bool}
    (h : G₁.nxt c ((G₁.op c).res l) = .inr a) :
    RN (seq G₁ G₂).prog (.inl c, l) (.inr G₂.start, (G₁.op c).eff l) 1 := by
  apply RN.single
  rw [Ctrl.stepP_eq, seq_op_inl, seq_nxt_inl, h]

theorem RN.seq_right : ∀ {s s' : G₂.prog.I × List G₂.prog.D} {k : ℕ}, RN G₂.prog s s' k →
    RN (seq G₁ G₂).prog (.inr s.1, s.2) (.inr s'.1, s'.2) k := by
  intro s s' k h
  induction h with
  | refl s => exact RN.refl _
  | @step s s₂ s₃ k hstep _ ih =>
    obtain ⟨c, l⟩ := s
    obtain ⟨c₂, l₂⟩ := s₂
    rw [Ctrl.stepP_eq] at hstep
    rcases hn : G₂.nxt c ((G₂.op c).res l) with c₁ | a
    · rw [hn] at hstep
      simp only [Sum.inl.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      refine RN.step ?_ ih
      rw [Ctrl.stepP_eq, seq_op_inr, seq_nxt_inr, hn]
    · rw [hn] at hstep; simp at hstep

theorem halt_seq_right {c : G₂.C} {l : List Cell} {a : Bool}
    (h : G₂.nxt c ((G₂.op c).res l) = .inr a) :
    (seq G₁ G₂).prog.stepP (.inr c, l) = .inr (a, (G₂.op c).eff l) := by
  rw [Ctrl.stepP_eq, seq_op_inr, seq_nxt_inr, h]

end Seq

end PVNP.CookLevin.Gen
