import PVNP.SweepTM

/-!
# Verified binary arithmetic in the repository's Turing-machine model

Numbers are little-endian bit lists on parallel tracks of one tape (`Cell`: operand tracks `a`,
`b` and a result track `r`). Each primitive below is one round trip of a sweep program. The
D-1a compiler `Prog.toTM` turns it into a single-tape Turing machine `Discrete.TM`, and
`Prog.reach_run` transfers correctness to the compiled machine together with the exact number
of transitions.

* **Addition.** `fscan_add` proves ripple-carry addition correct. `add_value` is the exact sum
  on the result track, including the overflow bit written by the one-cell extension.
  `add_tm`: from any tape representing the operands, the compiled TM reaches a tape
  representing the sum after exactly `2n + 2 + [carry] ≤ 2n + 3` transitions.
* **Subtraction.** `fscan_sub` proves borrow subtraction correct. `sub_value`: if
  `val b ≤ val a`, the result track holds `val a − val b` and no borrow remains. `sub_tm`
  transfers this to the TM, with `2n + 2` transitions.
* **Comparison.** `fscan_cmp` shows the comparison buffer ends at the order of `val a` and
  `val b`. `cmp_tm`: the compiled TM decides `val a < val b` in exactly `2n + 4` transitions.

Multiplication, division, rational and complex arithmetic are not built here.
-/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-- Little-endian value of a bit list. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * val l

theorem val_append (l m : List Bool) : val (l ++ m) = val l + 2 ^ l.length * val m := by
  induction l with
  | nil => simp [val]
  | cons b l ih => simp only [List.cons_append, val, ih, List.length_cons, pow_succ]; ring

theorem val_lt (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val]
  | cons b l ih =>
    simp only [val, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- A tape cell: two operand tracks and one result track. -/
structure Cell where
  a : Bool
  b : Bool
  r : Bool
  deriving DecidableEq, Fintype

theorem bscan_id {D B : Type} : ∀ (b : B) (l : List D), bscan (fun b a => (a, b)) b l = (l, b)
  | _, [] => rfl
  | b, a :: l => by simp [bscan, bscan_id b l]

/-! ### Addition -/

/-- The full adder. -/
def fadd (c : Bool) (x : Cell) : Cell × Bool :=
  (⟨x.a, x.b, xor (xor x.a x.b) c⟩, (x.a && x.b) || (c && xor x.a x.b))

theorem fadd_spec (c : Bool) (x : Cell) :
    (fadd c x).1.r.toNat + 2 * (fadd c x).2.toNat = x.a.toNat + x.b.toNat + c.toNat := by
  obtain ⟨a, b, r⟩ := x
  cases a <;> cases b <;> cases c <;> rfl

theorem fscan_add_ab : ∀ (c : Bool) (l : List Cell),
    (fscan fadd c l).1.map Cell.a = l.map Cell.a ∧ (fscan fadd c l).1.map Cell.b = l.map Cell.b
  | _, [] => ⟨rfl, rfl⟩
  | c, x :: l => by
    obtain ⟨h1, h2⟩ := fscan_add_ab (fadd c x).2 l
    simp only [fscan, List.map_cons, h1, h2]
    exact ⟨rfl, rfl⟩

/-- **Ripple-carry addition** as a left-to-right Mealy transduction. -/
theorem fscan_add : ∀ (c : Bool) (l : List Cell),
    val ((fscan fadd c l).1.map Cell.r) + 2 ^ l.length * (fscan fadd c l).2.toNat =
      val (l.map Cell.a) + val (l.map Cell.b) + c.toNat
  | c, [] => by simp [fscan, val]
  | c, x :: l => by
    have ih := fscan_add (fadd c x).2 l
    have hs := fadd_spec c x
    simp only [fscan, List.map_cons, val, List.length_cons, pow_succ]
    have e : (fadd c x).1.a = x.a ∧ (fadd c x).1.b = x.b := ⟨rfl, rfl⟩
    nlinarith [ih, hs]

inductive AddI | go | done
  deriving DecidableEq, Fintype

/-- The overflow cell appended by the extension. -/
def topCell : Cell := ⟨false, false, true⟩

/-- **The adder**: one round trip, then the program rests in `done`. -/
def addProg : Prog where
  D := Cell
  I := AddI
  B := Bool
  lift b := ⟨b, false, false⟩
  start := .go
  init _ := false
  fwd
    | .go => fadd
    | .done => fun c x => (x, c)
  ext
    | .go => fun c => if c then some topCell else none
    | .done => fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun _ => .inl .done

/-- The output tape of the adder. -/
def addOut (l : List Cell) : List Cell :=
  (fscan fadd false l).1 ++ (if (fscan fadd false l).2 then [topCell] else [])

/-- The exact cost of the adder. -/
def addCost (l : List Cell) : ℕ :=
  2 * l.length + 2 + (if (fscan fadd false l).2 then 1 else 0)

theorem add_reach (l : List Cell) :
    addProg.Reach (AddI.go, l) (AddI.done, addOut l) (addCost l) := by
  have hs : addProg.stepP (AddI.go, l) = .inl (AddI.done, addOut l) := by
    simp only [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, addProg, bscan_id, addOut]
    congr 2
    cases (fscan fadd false l).2 <;> rfl
  have hc : addProg.tripCost AddI.go l = addCost l := by
    simp only [Prog.tripCost, Prog.fpass, addProg, addCost]
    cases (fscan fadd false l).2 <;> rfl
  have h := Prog.Reach.step (P := addProg) hs (Prog.Reach.refl _)
  rwa [hc, add_zero] at h

/-- **The sum is exact**, including the overflow bit. -/
theorem add_value (l : List Cell) :
    val ((addOut l).map Cell.r) = val (l.map Cell.a) + val (l.map Cell.b) := by
  have h := fscan_add false l
  have hlen := fscan_length fadd false l
  simp only [Bool.toNat_false, add_zero] at h
  unfold addOut
  rw [List.map_append, val_append, List.length_map, hlen]
  cases hc : (fscan fadd false l).2
  · rw [hc] at h; simpa [val] using h
  · rw [hc] at h; simp [val, topCell] at h ⊢; omega

theorem addCost_le (l : List Cell) : addCost l ≤ 2 * l.length + 3 := by
  unfold addCost; split_ifs <;> omega

/-- **Addition on the compiled Turing machine.** From any tape representing the operand cells,
the single-tape TM `addProg.toTM` reaches, after exactly `addCost l ≤ 2n + 3` transitions, a
tape representing cells whose result track holds the binary sum. -/
theorem add_tm (l : List Cell) (T : ℤ → Sym Cell) (hT : addProg.Repr T l) :
    ∃ T', addProg.Repr T' (addOut l) ∧
      addProg.toTM.run ⟨.fwd AddI.go (addProg.init AddI.go), T, 0⟩ (addCost l) =
        ⟨.fwd AddI.done (addProg.init AddI.done), T', 0⟩ :=
  addProg.reach_run (add_reach l) T hT

/-! ### Subtraction -/

/-- The full subtractor: `r = a ⊕ b ⊕ w`, borrow out `(¬a ∧ b) ∨ (¬(a ⊕ b) ∧ w)`. -/
def fsub (w : Bool) (x : Cell) : Cell × Bool :=
  (⟨x.a, x.b, xor (xor x.a x.b) w⟩, (!x.a && x.b) || (!(xor x.a x.b) && w))

theorem fsub_spec (w : Bool) (x : Cell) :
    (fsub w x).1.r.toNat + x.b.toNat + w.toNat = x.a.toNat + 2 * (fsub w x).2.toNat := by
  obtain ⟨a, b, r⟩ := x
  cases a <;> cases b <;> cases w <;> rfl

theorem fscan_sub : ∀ (w : Bool) (l : List Cell),
    val ((fscan fsub w l).1.map Cell.r) + val (l.map Cell.b) + w.toNat =
      val (l.map Cell.a) + 2 ^ l.length * (fscan fsub w l).2.toNat
  | w, [] => by simp [fscan, val]
  | w, x :: l => by
    have ih := fscan_sub (fsub w x).2 l
    have hs := fsub_spec w x
    simp only [fscan, List.map_cons, val, List.length_cons, pow_succ]
    nlinarith [ih, hs]

def subProg : Prog where
  D := Cell
  I := AddI
  B := Bool
  lift b := ⟨b, false, false⟩
  start := .go
  init _ := false
  fwd
    | .go => fsub
    | .done => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun _ => .inl .done

theorem sub_reach (l : List Cell) :
    subProg.Reach (AddI.go, l) (AddI.done, (fscan fsub false l).1) (2 * l.length + 2) := by
  have hs : subProg.stepP (AddI.go, l) = .inl (AddI.done, (fscan fsub false l).1) := by
    simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, subProg, bscan_id]
  have h := Prog.Reach.step (P := subProg) hs (Prog.Reach.refl _)
  simpa [Prog.tripCost, subProg] using h

/-- **Exact difference** when no borrow is needed. -/
theorem sub_value (l : List Cell) (hle : val (l.map Cell.b) ≤ val (l.map Cell.a)) :
    val ((fscan fsub false l).1.map Cell.r) = val (l.map Cell.a) - val (l.map Cell.b) ∧
      (fscan fsub false l).2 = false := by
  have h := fscan_sub false l
  have hr := val_lt ((fscan fsub false l).1.map Cell.r)
  rw [List.length_map, fscan_length] at hr
  simp only [Bool.toNat_false, add_zero] at h
  cases hw : (fscan fsub false l).2
  · rw [hw] at h; simp only [Bool.toNat_false, mul_zero, add_zero] at h
    exact ⟨by omega, rfl⟩
  · rw [hw] at h; simp only [Bool.toNat_true, mul_one] at h
    omega

theorem sub_tm (l : List Cell) (T : ℤ → Sym Cell) (hT : subProg.Repr T l) :
    ∃ T', subProg.Repr T' (fscan fsub false l).1 ∧
      subProg.toTM.run ⟨.fwd AddI.go (subProg.init AddI.go), T, 0⟩ (2 * l.length + 2) =
        ⟨.fwd AddI.done (subProg.init AddI.done), T', 0⟩ :=
  subProg.reach_run (sub_reach l) T hT

/-! ### Comparison -/

inductive Cmp | lt | eq | gt
  deriving DecidableEq, Fintype

/-- The order of two numbers, with tie value `o`. -/
def cmpOf (x y : ℕ) (o : Cmp) : Cmp := if x < y then .lt else if y < x then .gt else o

/-- One comparison step: a differing bit overrides the less significant history. -/
def fcmp (o : Cmp) (x : Cell) : Cell × Cmp :=
  (x, if x.a = x.b then o else if x.b then .lt else .gt)

theorem cmpOf_step (a b : Bool) (X Y : ℕ) (o : Cmp) :
    cmpOf X Y (if a = b then o else if b = true then Cmp.lt else Cmp.gt) =
      cmpOf (a.toNat + 2 * X) (b.toNat + 2 * Y) o := by
  rcases lt_trichotomy X Y with h | h | h
  · have h1 : a.toNat + 2 * X < b.toNat + 2 * Y := by
      cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    simp only [cmpOf, if_pos h, if_pos h1]
  · subst h
    cases a <;> cases b <;> simp only [cmpOf, Bool.toNat_false, Bool.toNat_true, lt_irrefl,
      if_false, if_true, Bool.false_eq_true, Bool.true_eq_false] <;> split_ifs <;>
      first | rfl | omega
  · have h1 : ¬ (a.toNat + 2 * X < b.toNat + 2 * Y) := by
      cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have h2 : b.toNat + 2 * Y < a.toNat + 2 * X := by
      cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    simp only [cmpOf, if_neg (by omega : ¬ X < Y), if_pos h, if_neg h1, if_pos h2]

theorem fscan_cmp : ∀ (o : Cmp) (l : List Cell),
    (fscan fcmp o l).2 = cmpOf (val (l.map Cell.a)) (val (l.map Cell.b)) o
  | o, [] => by simp [fscan, cmpOf, val]
  | o, x :: l => by
    rw [show (fscan fcmp o (x :: l)).2 = (fscan fcmp (fcmp o x).2 l).2 from rfl,
      fscan_cmp (fcmp o x).2 l]
    simp only [List.map_cons, val]
    exact cmpOf_step x.a x.b _ _ o

/-- The comparator decides `val a < val b`. -/
def cmpProg : Prog where
  D := Cell
  I := Unit
  B := Cmp
  lift b := ⟨b, false, false⟩
  start := ()
  init _ := .eq
  fwd _ := fcmp
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun o => .inr (decide (o = .lt))

theorem cmp_halts (l : List Cell) :
    cmpProg.Halts ((), l) (decide (val (l.map Cell.a) < val (l.map Cell.b))) (2 * l.length + 2) := by
  have hs : cmpProg.stepP ((), l) =
      .inr (decide (val (l.map Cell.a) < val (l.map Cell.b)), (fscan fcmp .eq l).1) := by
    simp only [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, cmpProg, bscan_id]
    rw [fscan_cmp]
    simp only [List.append_nil, Option.toList_none]
    congr 2
    unfold cmpOf
    split_ifs with h1 h2 <;> simp [h1]
  have h := Prog.Halts.last (P := cmpProg) hs
  simpa [Prog.tripCost, cmpProg] using h

/-- **Comparison on the compiled Turing machine**: on the input word whose bits are lifted to
operand-`a` cells, the TM reaches its first answer `decide (val a < val b)` in exactly
`2n + 4` transitions. -/
theorem cmp_tm (x : List Bool) :
    FirstAnswer (cmpProg.toTM.out x) (2 * x.length + 4)
      (decide (val ((x.map cmpProg.lift).map Cell.a) < val ((x.map cmpProg.lift).map Cell.b))) := by
  have h := cmp_halts (x.map cmpProg.lift)
  rw [List.length_map] at h
  have := cmpProg.toTM_firstAnswer x h
  simpa [show 2 * x.length + 2 + 2 = 2 * x.length + 4 by ring] using this

end PVNP.Discrete.SweepArith
