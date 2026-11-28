import PVNP.SweepLayout

/-!
# Normalized fractions on the Turing machine: a verified Euclidean algorithm

The Euclidean algorithm runs as a loop of verified programs (`SweepLoop`) on the common alphabet
`GCell`. Every iteration is a four-stage composite:

1. a cellwise map loads `a` into the divider's dividend track, `b` into its divisor track, the
   saved marker `2^W` and the saved counter `W`;
2. the verified shift loop (`SweepLayout`) shifts the divisor track by `W` places;
3. the verified long-division machine (`SweepDiv`) leaves `a mod b` on the dividend track;
4. a cellwise map moves `b` to `a` and the remainder to `b`.

The loop test stops when `b = 0`. Normalization then divides the numerator and the denominator by
`a = gcd(P, Q)`, with the same shift-and-divide stages.

* `loop_iter`, `loop_stop`: one iteration and the stop of a loop, in first-arrival form.
* `mapProg`, `map_first`: a single-trip cellwise map.
* `euclidSteps`, `euclidSteps_le`: the number of Euclidean steps is at most `2k` when `b < 2^k`,
  because the remainder at least halves every two steps.
* `shdiv`: the shift-and-divide stages on `GCell`.
* `body_iter`: one iteration maps `(a, b)` to `(b, a mod b)` in exactly `(4W + 5)(4W + 2)`
  transitions.
* `gcd_loop`: the loop first-arrives at its stop exit with `a = gcd(A, B)`, in exactly
  `(s(4W + 6) + 1)(4W + 2)` transitions, where `s` is the number of Euclidean steps.
* `norm_layout`, `norm_tm`: **normalization of `P/Q` on the compiled TM**: the result tracks hold
  `P/g` and `Q/g` with `g = gcd(P, Q)`, a coprime pair with the same quotient, in at most
  `(2W(4W + 6) + 8W + 12)(4W + 2)` transitions.
-/

namespace PVNP.Discrete.Sweep.ProgOn

variable {D : Type} [Fintype D] [DecidableEq D] (T B : ProgOn D) (eT : T.I) (eB : B.I)

/-- **One iteration of a loop**: the test continues, the body first-arrives at its exit, and
the loop then first-arrives at the stop exit. -/
theorem loop_iter {eF : T.I} (hTF : T.start ≠ eF) {l m l₁ out : List D} {b c : ℕ}
    (ht : T.toProg.stepP (T.start, l) = .inl (eT, m))
    (hb : ReachFirst B.toProg eB (B.start, m) l₁ b)
    (hL : ReachFirst (loop T B eT eB).toProg (.inl eF) (.inl T.start, l₁) out c) :
    ReachFirst (loop T B eT eB).toProg (.inl eF) (.inl T.start, l) out
      (T.toProg.tripCost T.start l + (b + c)) := by
  have h1 := loop_body_then T B eT eB hTF hb hL
  have h2 := ReachFirst.step (P := (loop T B eT eB).toProg) (e := .inl eF)
    (loop_stepP_inl_exit T B eT eB ht) (fun h => Sum.inl_ne_inr h.symm) h1
  rwa [loop_tripCost_inl] at h2

/-- **The stop of a loop**: the test takes the stop exit. -/
theorem loop_stop {eF : T.I} (hFT : eF ≠ eT) {l out : List D}
    (ht : T.toProg.stepP (T.start, l) = .inl (eF, out)) :
    ReachFirst (loop T B eT eB).toProg (.inl eF) (.inl T.start, l) out
      (T.toProg.tripCost T.start l) := by
  have h1 := ReachFirst.last (P := (loop T B eT eB).toProg) (e := .inl eF)
    (loop_stepP_inl_ne T B eT eB ht hFT)
  rwa [loop_tripCost_inl] at h1

end PVNP.Discrete.Sweep.ProgOn

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-! ### A cellwise map -/

/-- **A cellwise map**: one trip that replaces every cell `x` by `f x`. -/
def mapProg (D : Type) [Fintype D] [DecidableEq D] (f : D → D) (lift : Bool → D) : Prog where
  D := D
  I := AddI
  B := Bool
  lift := lift
  start := .go
  init _ := false
  fwd
    | .go => fun c x => (f x, c)
    | .done => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun _ => .inl .done

theorem fscan_map {D : Type} (f : D → D) : ∀ (c : Bool) (l : List D),
    fscan (fun c x => (f x, c)) c l = (l.map f, c)
  | _, [] => rfl
  | c, x :: l => by simp only [fscan, fscan_map f c l, List.map_cons]

theorem map_first {D : Type} [Fintype D] [DecidableEq D] (f : D → D) (lift : Bool → D)
    (l : List D) :
    ReachFirst (mapProg D f lift) AddI.done (AddI.go, l) (l.map f) (2 * l.length + 2) := by
  have hs : (mapProg D f lift).stepP (AddI.go, l) = .inl (AddI.done, l.map f) := by
    simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, mapProg, fscan_map, bscan_id]
  have h := ReachFirst.last (P := mapProg D f lift) (e := AddI.done) hs
  simpa [Prog.tripCost, Prog.fpass, mapProg] using h

/-! ### Counting Euclidean steps -/

/-- The number of steps `(a, b) ↦ (b, a mod b)` until `b = 0`. -/
def euclidSteps (A B : ℕ) : ℕ :=
  if h : B = 0 then 0 else 1 + euclidSteps B (A % B)
termination_by B
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

theorem euclidSteps_zero (A : ℕ) : euclidSteps A 0 = 0 := by
  rw [euclidSteps, dif_pos rfl]

theorem euclidSteps_pos (A B : ℕ) (hB : B ≠ 0) :
    euclidSteps A B = 1 + euclidSteps B (A % B) := by
  rw [euclidSteps, dif_neg hB]

/-- Two Euclidean steps at least halve the second argument. -/
theorem two_mod_lt (A B : ℕ) (hB0 : 0 < B) (hB : 0 < A % B) : 2 * (B % (A % B)) < B := by
  have hr : A % B < B := Nat.mod_lt _ hB0
  set r := A % B with hr'
  have h1 : B % r < r := Nat.mod_lt _ hB
  by_cases h2 : 2 * r ≤ B
  · omega
  · have h3 : B % r = B - r := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The iteration bound**: at most `2k` Euclidean steps when `B < 2^k`. -/
theorem euclidSteps_le : ∀ (k A B : ℕ), B < 2 ^ k → euclidSteps A B ≤ 2 * k
  | 0, A, B, h => by
    have : B = 0 := by simpa using h
    rw [this, euclidSteps_zero]
  | k + 1, A, B, h => by
    by_cases hB : B = 0
    · rw [hB, euclidSteps_zero]; omega
    rw [euclidSteps_pos A B hB]
    by_cases hr : A % B = 0
    · rw [hr, euclidSteps_zero]; omega
    rw [euclidSteps_pos B (A % B) hr]
    have h2 := two_mod_lt A B (Nat.pos_of_ne_zero hB) (Nat.pos_of_ne_zero hr)
    have h3 : B % (A % B) < 2 ^ k := by
      rw [pow_succ] at h
      omega
    have ih := euclidSteps_le k (A % B) (B % (A % B)) h3
    omega

/-! ### The common alphabet -/

/-- Tracks that normalization carries along unchanged. `SweepRat` uses them for the operands, the
multiplier and the sign of a fraction. -/
structure XCell where
  x : Bool
  y : Bool
  acc : Bool
  fl : Bool
  z : Bool
  ia : Bool
  ib : Bool
  ic : Bool
  id : Bool
  deriving DecidableEq

instance : Fintype XCell :=
  Fintype.ofEquiv (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool)
    { toFun := fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩
      invFun := fun x => ⟨x.x, x.y, x.acc, x.fl, x.z, x.ia, x.ib, x.ic, x.id⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The all-zero carried block. -/
def xz : XCell := ⟨false, false, false, false, false, false, false, false, false⟩

/-- Cells for the Euclidean algorithm and normalization: the divider's tracks, the shift counter
`c`, the Euclidean pair `a, b`, the saved counter `c0 = W` and marker `m0 = 2^W`, the fraction
`p/qq`, the results `rp, rq`, and the carried block `xc`. -/
structure GCell where
  dv : DCell
  c : Bool
  a : Bool
  b : Bool
  c0 : Bool
  m0 : Bool
  p : Bool
  qq : Bool
  rp : Bool
  rq : Bool
  xc : XCell
  deriving DecidableEq

instance : Fintype GCell :=
  Fintype.ofEquiv (DCell × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × XCell)
    { toFun := fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩
      invFun := fun x => ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The value of one track. -/
def tv (f : GCell → Bool) (l : List GCell) : ℕ := val (l.map f)

theorem tv_congr {f : GCell → Bool} {l l' : List GCell} (h : l'.map f = l.map f) :
    tv f l' = tv f l := by
  unfold tv
  rw [h]

theorem val_false {α : Type} (l : List α) : val (l.map (fun _ => false)) = 0 := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp only [List.map_cons, val, Bool.toNat_false, ih]

/-- The divider's view. -/
def lensGd : TrackLens GCell DCell :=
  ⟨GCell.dv, fun x d => ⟨d, x.c, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩, fun _ _ => rfl⟩

/-- The shift loop's view: the divisor track and the counter. -/
def lensSh : TrackLens GCell SCell :=
  ⟨fun x => ⟨x.dv.d, x.c⟩,
    fun x s => ⟨⟨x.dv.n, s.x, x.dv.q, x.dv.m⟩, s.c, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩,
    fun _ _ => rfl⟩

/-- The tracks that the shift and divide stages never write. -/
def lensKeep : TrackLens GCell (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × XCell) :=
  ⟨fun x => (x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc),
    fun x k => ⟨x.dv, x.c, k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2.1, k.2.2.2.2.2.1,
      k.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2.2⟩,
    fun _ _ => rfl⟩

/-- The divider's tracks other than the divisor, which the shift stage never writes. -/
def lensNQM : TrackLens GCell (Bool × Bool × Bool) :=
  ⟨fun x => (x.dv.n, x.dv.q, x.dv.m),
    fun x k => ⟨⟨k.1, x.dv.d, k.2.1, k.2.2⟩, x.c, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩,
    fun _ _ => rfl⟩

/-- The fill cell. No stage extends the tape. -/
def gz : GCell := ⟨⟨false, false, false, false⟩, false, false, false, false, false, false, false,
  false, false, xz⟩

/-- Raw input bits enter the numerator track. -/
def gbit (b : Bool) : GCell := ⟨⟨false, false, false, false⟩, false, false, false, false, false, b,
  false, false, false, xz⟩

/-! ### The stages -/

/-- Load the divider: dividend `a`, divisor `b`, quotient `0`, marker `m0`, counter `c0`. -/
def setupF (x : GCell) : GCell :=
  ⟨⟨x.a, x.b, false, x.m0⟩, x.c0, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩

/-- Move `b` to `a` and the remainder to `b`. -/
def swapF (x : GCell) : GCell :=
  ⟨x.dv, x.c, x.b, x.dv.n, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩

/-- Load the Euclidean pair `(p, qq)`. -/
def initF (x : GCell) : GCell :=
  ⟨x.dv, x.c, x.p, x.qq, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩

/-- Load the divider with dividend `p` and divisor `a`. -/
def setPF (x : GCell) : GCell :=
  ⟨⟨x.p, x.a, false, x.m0⟩, x.c0, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩

/-- Load the divider with dividend `qq` and divisor `a`. -/
def setQF (x : GCell) : GCell :=
  ⟨⟨x.qq, x.a, false, x.m0⟩, x.c0, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩

/-- Save the quotient in `rp`. -/
def savePF (x : GCell) : GCell :=
  ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.dv.q, x.rq, x.xc⟩

/-- Save the quotient in `rq`. -/
def saveQF (x : GCell) : GCell :=
  ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.dv.q, x.xc⟩

def MAPG (f : GCell → GCell) : ProgOn GCell := ProgOn.ofProg (mapProg GCell f gbit)
def SHG : ProgOn GCell := shiftLoop.viaLens lensSh gz gbit
def DVG : ProgOn GCell := (ProgOn.ofProg divProg).viaLens lensGd gz gbit

/-- The zero test of `b`: the buffer records whether a set bit was seen. -/
def fnzB (nz : Bool) (x : GCell) : GCell × Bool := (x, nz || x.b)

/-- **The loop test**: continue while `b ≠ 0`. -/
def testB : Prog where
  D := GCell
  I := TstI
  B := Bool
  lift := gbit
  start := .test
  init _ := false
  fwd
    | .test => fnzB
    | _ => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next
    | .test => fun b => if b then .inl .yes else .inl .no
    | .yes => fun _ => .inl .yes
    | .no => fun _ => .inl .no

def TSG : ProgOn GCell := ProgOn.ofProg testB

def B1 : ProgOn GCell := ProgOn.seq (MAPG setupF) SHG AddI.done
def B2 : ProgOn GCell := ProgOn.seq B1 DVG (Sum.inr (Sum.inl TstI.no))

/-- **One Euclidean step**: load, shift, divide, move. -/
def BODYG : ProgOn GCell := ProgOn.seq B2 (MAPG swapF) (Sum.inr DivI.done)

/-- **The Euclidean loop.** -/
def gcdLoop : ProgOn GCell := ProgOn.loop TSG BODYG TstI.yes (Sum.inr AddI.done)

theorem shiftLoop_ext : ∀ i b, shiftLoop.ext i b = none := by
  intro i b
  rcases i with i | (i | i) <;> rcases b with b | (b | b) <;> rfl

theorem fscan_nzB : ∀ (b : Bool) (l : List GCell),
    (fscan fnzB b l).1 = l ∧ (fscan fnzB b l).2 = (b || decide (tv GCell.b l ≠ 0))
  | b, [] => by simp [fscan, tv, val]
  | b, ⟨dv, c, a, xb, c0, m0, p, qq, rp, rq, xc⟩ :: l => by
    obtain ⟨h1, h2⟩ := fscan_nzB (b || xb) l
    refine ⟨by simp only [fscan, fnzB, h1], ?_⟩
    simp only [fscan, fnzB, h2, tv, List.map_cons, val]
    cases b <;> cases xb <;> simp

theorem testB_step (l : List GCell) :
    TSG.toProg.stepP (TstI.test, l) =
      .inl (if tv GCell.b l ≠ 0 then TstI.yes else TstI.no, l) := by
  obtain ⟨h1, h2⟩ := fscan_nzB false l
  have ht : testB.trip TstI.test l = (l, decide (tv GCell.b l ≠ 0)) := by
    simp only [Prog.trip, Prog.mid, Prog.fpass, testB, bscan_id]
    rw [h1, h2]
    simp
  show testB.stepP (TstI.test, l) = _
  simp only [Prog.stepP, ht]
  by_cases h : tv GCell.b l ≠ 0
  · have hn : testB.next TstI.test (decide (tv GCell.b l ≠ 0)) = .inl TstI.yes := by
      simp [testB, h]
    rw [hn, if_pos h]
  · have hn : testB.next TstI.test (decide (tv GCell.b l ≠ 0)) = .inl TstI.no := by
      simp [testB, h]
    rw [hn, if_neg h]

theorem testB_cost (l : List GCell) : TSG.toProg.tripCost TSG.start l = 2 * l.length + 2 := by
  show testB.tripCost TstI.test l = _
  simp [Prog.tripCost, Prog.fpass, testB]

/-- A projection of the untouched tracks is untouched. -/
theorem keep_map {l l' : List GCell} (h : l'.map lensKeep.get = l.map lensKeep.get) {β : Type}
    (π : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × XCell → β) :
    l'.map (fun x => π (lensKeep.get x)) = l.map (fun x => π (lensKeep.get x)) := by
  have := congrArg (List.map π) h
  simpa [List.map_map, Function.comp_def] using this

/-! ### Shift and divide -/

/-- **Shift and divide on `GCell`.** From a tape whose divider tracks hold dividend `N`, divisor
`D`, quotient `0`, marker `2^W` and counter `W`, the shift stage puts `D·2^W` on the divisor track
and the divider leaves `N / D` on the quotient track and `N mod D` on the dividend track. The
tracks of `lensKeep` are unchanged. -/
theorem shdiv {W : ℕ} (l : List GCell) (hlen : l.length = 2 * W) {N D : ℕ}
    (hN : N < 2 ^ W) (hD0 : 0 < D) (hD : D < 2 ^ W)
    (hn : tv (fun x => x.dv.n) l = N) (hd : tv (fun x => x.dv.d) l = D)
    (hq : tv (fun x => x.dv.q) l = 0) (hm : tv (fun x => x.dv.m) l = 2 ^ W)
    (hc : tv GCell.c l = W) :
    ∃ l2 l3, ReachFirst SHG.toProg (Sum.inl TstI.no) (Sum.inl TstI.test, l) l2
        ((3 * W + 1) * (4 * W + 2)) ∧
      ReachFirst DVG.toProg DivI.done (DivI.prep, l2) l3 ((W + 2) * (4 * W + 2)) ∧
      l3.length = l.length ∧ tv (fun x => x.dv.q) l3 = N / D ∧
      tv (fun x => x.dv.n) l3 = N % D ∧ l3.map lensKeep.get = l.map lensKeep.get := by
  -- the shift stage
  obtain ⟨s', hs, hsx, _, _⟩ := shift_by_counter (l.map lensSh.get)
  have hvx : vSx (l.map lensSh.get) = D := by
    rw [← hd]
    unfold vSx tv
    rw [List.map_map]
    rfl
  have hvc : vSc (l.map lensSh.get) = W := by
    rw [← hc]
    unfold vSc tv
    rw [List.map_map]
    rfl
  rw [hvx, hvc, List.length_map, hlen] at hsx
  rw [hvc, List.length_map, hlen, show 2 * (2 * W) + 2 = 4 * W + 2 by ring] at hs
  obtain ⟨l2, r2, v2⟩ := ProgOn.reachFirst_lens shiftLoop lensSh gz gbit hs l rfl
  have k2 : l2.map lensKeep.get = l.map lensKeep.get :=
    ProgOn.reachFirst_lens_frame shiftLoop lensSh gz gbit shiftLoop_ext (fun _ _ => rfl) r2
  have q2 : l2.map lensNQM.get = l.map lensNQM.get :=
    ProgOn.reachFirst_lens_frame shiftLoop lensSh gz gbit shiftLoop_ext (fun _ _ => rfl) r2
  have hl2 : l2.length = l.length := by
    have := congrArg List.length k2
    simpa using this
  -- the divider's view after the shift
  have hpos : 0 < 2 ^ W := by positivity
  have hW2 : 2 ^ (2 * W) = 2 ^ W * 2 ^ W := by rw [two_mul, pow_add]
  have hDW : D * 2 ^ W < 2 ^ (2 * W) := by rw [hW2]; nlinarith
  have dv2 : vD (l2.map lensGd.get) = D * 2 ^ W := by
    have e : vD (l2.map lensGd.get) = vSx (l2.map lensSh.get) := by
      unfold vD vSx
      rw [List.map_map, List.map_map]
      rfl
    rw [e, v2, hsx, Nat.mod_eq_of_lt hDW]
  have mv2 : vM (l2.map lensGd.get) = 2 ^ W := by
    have e : vM (l2.map lensGd.get) = val ((l2.map lensNQM.get).map (fun k => k.2.2)) := by
      unfold vM
      rw [List.map_map, List.map_map]
      rfl
    rw [e, q2, ← hm]
    unfold tv
    rw [List.map_map]
    rfl
  have qv2 : vQ (l2.map lensGd.get) = 0 := by
    have e : vQ (l2.map lensGd.get) = val ((l2.map lensNQM.get).map (fun k => k.2.1)) := by
      unfold vQ
      rw [List.map_map, List.map_map]
      rfl
    rw [e, q2, ← hq]
    unfold tv
    rw [List.map_map]
    rfl
  have nv2 : vN (l2.map lensGd.get) = N := by
    have e : vN (l2.map lensGd.get) = val ((l2.map lensNQM.get).map (fun k => k.1)) := by
      unfold vN
      rw [List.map_map, List.map_map]
      rfl
    rw [e, q2, ← hn]
    unfold tv
    rw [List.map_map]
    rfl
  have hne : l2.map lensGd.get ≠ [] := by
    intro h
    rw [List.map_eq_nil_iff] at h
    rw [h, List.length_nil, hlen] at hl2
    have : 0 < 2 ^ W := hpos
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · rw [h0, pow_zero] at hD
      omega
    · omega
  have hlt : vN (l2.map lensGd.get) < 2 * (D * 2 ^ W) := by
    rw [nv2]
    nlinarith
  -- the divide stage
  obtain ⟨m', hr, hq', hn'⟩ := div_reach_first (l2.map lensGd.get) hne W D hD0 dv2 mv2 qv2 hlt
  rw [List.length_map, hl2, hlen, show 2 * (2 * W) + 2 = 4 * W + 2 by ring] at hr
  obtain ⟨l3, r3, v3⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg divProg) lensGd gz gbit hr l2 rfl
  have k3 : l3.map lensKeep.get = l2.map lensKeep.get :=
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg divProg) lensGd gz gbit (fun _ _ => rfl)
      (fun _ _ => rfl) r3
  refine ⟨l2, l3, r2, r3, ?_, ?_, ?_, by rw [k3, k2]⟩
  · have := congrArg List.length k3
    simp only [List.length_map] at this
    rw [this, hl2]
  · have e : tv (fun x => x.dv.q) l3 = vQ (l3.map lensGd.get) := by
      unfold tv vQ
      rw [List.map_map]
      rfl
    rw [e, v3, hq', nv2]
  · have e : tv (fun x => x.dv.n) l3 = vN (l3.map lensGd.get) := by
      unfold tv vN
      rw [List.map_map]
      rfl
    rw [e, v3, hn', nv2]

/-! ### One Euclidean step and the loop -/

/-- **One Euclidean step** maps `(a, b)` to `(b, a mod b)` in exactly `(4W + 5)(4W + 2)`
transitions. -/
theorem body_iter {W : ℕ} (l : List GCell) (hlen : l.length = 2 * W) {A B : ℕ}
    (hA : A < 2 ^ W) (hB0 : 0 < B) (hB : B < 2 ^ W)
    (ha : tv GCell.a l = A) (hb : tv GCell.b l = B) (hc0 : tv GCell.c0 l = W)
    (hm0 : tv GCell.m0 l = 2 ^ W) :
    ∃ l', ReachFirst BODYG.toProg (Sum.inr AddI.done) (BODYG.start, l) l'
        ((4 * W + 5) * (4 * W + 2)) ∧
      l'.length = l.length ∧ tv GCell.a l' = B ∧ tv GCell.b l' = A % B ∧
      l'.map (fun x => (x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc)) =
        l.map (fun x => (x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc)) := by
  have r1 := map_first setupF gbit l
  have hlen1 : (l.map setupF).length = 2 * W := by rw [List.length_map, hlen]
  have n1 : tv (fun x => x.dv.n) (l.map setupF) = A := by
    rw [← ha]; unfold tv; rw [List.map_map]; rfl
  have d1 : tv (fun x => x.dv.d) (l.map setupF) = B := by
    rw [← hb]; unfold tv; rw [List.map_map]; rfl
  have q1 : tv (fun x => x.dv.q) (l.map setupF) = 0 := by
    unfold tv; rw [List.map_map]; exact val_false l
  have m1 : tv (fun x => x.dv.m) (l.map setupF) = 2 ^ W := by
    rw [← hm0]; unfold tv; rw [List.map_map]; rfl
  have c1 : tv GCell.c (l.map setupF) = W := by
    rw [← hc0]; unfold tv; rw [List.map_map]; rfl
  obtain ⟨l2, l3, r2, r3, hlen3, q3, n3, k3⟩ := shdiv (l.map setupF) hlen1 hA hB0 hB n1 d1 q1 m1 c1
  have r4 := map_first swapF gbit l3
  have hc := ProgOn.seq_reachFirst B2 (MAPG swapF) (Sum.inr DivI.done)
    (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst B1 DVG (Sum.inr (Sum.inl TstI.no))
      (show DivI.prep ≠ DivI.done by decide)
      (ProgOn.seq_reachFirst (MAPG setupF) SHG AddI.done
        (show (Sum.inl TstI.test : TstI ⊕ (AddI ⊕ AddI)) ≠ Sum.inl TstI.no by decide) r1 r2)
      r3) r4
  rw [hlen3, hlen1, hlen] at hc
  refine ⟨l3.map swapF, ?_, ?_, ?_, ?_, ?_⟩
  · convert hc using 1
    ring
  · rw [List.length_map, hlen3, hlen1, hlen]
  · have e : tv GCell.a (l3.map swapF) = tv GCell.b l3 := by
      unfold tv; rw [List.map_map]; rfl
    rw [e, tv_congr (f := GCell.b) (keep_map k3 (fun k => k.2.1)), ← hb]
    unfold tv
    rw [List.map_map]
    rfl
  · have e : tv GCell.b (l3.map swapF) = tv (fun x => x.dv.n) l3 := by
      unfold tv; rw [List.map_map]; rfl
    rw [e, n3]
  · have h1 := keep_map k3 (fun k => (k.2.2.1, k.2.2.2.1, k.2.2.2.2.1, k.2.2.2.2.2.1,
      k.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2.2))
    rw [List.map_map]
    exact (h1.trans (by rw [List.map_map]; rfl))

/-- **The Euclidean loop.** From a tape with `a = A`, `b = B` (both below `2^W`), counter `W` and
marker `2^W`, the loop first-arrives at its stop exit with `a = gcd(A, B)`, in exactly
`(s(4W + 6) + 1)(4W + 2)` transitions, where `s` is the number of Euclidean steps. The tracks
`c0, m0, p, qq, rp, rq` are unchanged. -/
theorem gcd_loop {W : ℕ} : ∀ (B A : ℕ) (l : List GCell), l.length = 2 * W → A < 2 ^ W →
    B < 2 ^ W → tv GCell.a l = A → tv GCell.b l = B → tv GCell.c0 l = W →
    tv GCell.m0 l = 2 ^ W →
    ∃ l', ReachFirst gcdLoop.toProg (Sum.inl TstI.no) (Sum.inl TstI.test, l) l'
        ((euclidSteps A B * (4 * W + 6) + 1) * (4 * W + 2)) ∧
      l'.length = l.length ∧ tv GCell.a l' = Nat.gcd A B ∧
      l'.map (fun x => (x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc)) =
        l.map (fun x => (x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc)) := by
  intro B
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    intro A l hlen hA hB ha hb hc0 hm0
    have ht := testB_step l
    by_cases hB0 : B = 0
    · subst hB0
      rw [hb, if_neg (by simp)] at ht
      refine ⟨l, ?_, rfl, by rw [ha, Nat.gcd_zero_right], rfl⟩
      have h := ProgOn.loop_stop TSG BODYG TstI.yes (Sum.inr AddI.done) (eF := TstI.no)
        (show TstI.no ≠ TstI.yes by decide) ht
      rw [testB_cost, hlen] at h
      rw [euclidSteps_zero]
      convert h using 1
      ring
    · rw [hb, if_pos hB0] at ht
      have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      obtain ⟨l1, r1, hlen1, ha1, hb1, hk1⟩ := body_iter l hlen hA hBpos hB ha hb hc0 hm0
      have hmod : A % B < B := Nat.mod_lt _ hBpos
      have hc01 : tv GCell.c0 l1 = W := by
        rw [← hc0]
        exact tv_congr (by
          have := congrArg (List.map (fun k => k.1)) hk1
          simpa [List.map_map, Function.comp_def] using this)
      have hm01 : tv GCell.m0 l1 = 2 ^ W := by
        rw [← hm0]
        exact tv_congr (by
          have := congrArg (List.map (fun k => k.2.1)) hk1
          simpa [List.map_map, Function.comp_def] using this)
      obtain ⟨l2, r2, hlen2, ha2, hk2⟩ := ih (A % B) hmod B l1 (by rw [hlen1, hlen]) hB
        (lt_trans hmod hB) ha1 hb1 hc01 hm01
      refine ⟨l2, ?_, by rw [hlen2, hlen1], ?_, hk2.trans hk1⟩
      · have h := ProgOn.loop_iter TSG BODYG TstI.yes (Sum.inr AddI.done) (eF := TstI.no)
          (show TstI.test ≠ TstI.no by decide) ht r1 r2
        rw [testB_cost, hlen] at h
        rw [euclidSteps_pos A B hB0]
        convert h using 1
        ring
      · rw [ha2, Nat.gcd_comm A B, Nat.gcd_rec B A, Nat.gcd_comm (A % B) B]

/-! ### Normalization -/

def N1 : ProgOn GCell := ProgOn.seq (MAPG initF) gcdLoop AddI.done
def N2 : ProgOn GCell := ProgOn.seq N1 (MAPG setPF) (Sum.inr (Sum.inl TstI.no))
def N3 : ProgOn GCell := ProgOn.seq N2 SHG (Sum.inr AddI.done)
def N4 : ProgOn GCell := ProgOn.seq N3 DVG (Sum.inr (Sum.inl TstI.no))
def N5 : ProgOn GCell := ProgOn.seq N4 (MAPG savePF) (Sum.inr DivI.done)
def N6 : ProgOn GCell := ProgOn.seq N5 (MAPG setQF) (Sum.inr AddI.done)
def N7 : ProgOn GCell := ProgOn.seq N6 SHG (Sum.inr AddI.done)
def N8 : ProgOn GCell := ProgOn.seq N7 DVG (Sum.inr (Sum.inl TstI.no))

/-- **Normalization of a fraction**: load `(p, qq)` into the Euclidean pair, run the Euclidean
loop, then divide `p` and `qq` by `a = gcd(p, qq)` and save the quotients in `rp` and `rq`. -/
def normProg : ProgOn GCell := ProgOn.seq N8 (MAPG saveQF) (Sum.inr DivI.done)

/-- Single-track lenses for the layout. -/
def lensC0 : TrackLens GCell Bool :=
  ⟨GCell.c0, fun x b => ⟨x.dv, x.c, x.a, x.b, b, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩, fun _ _ => rfl⟩
def lensM0 : TrackLens GCell Bool :=
  ⟨GCell.m0, fun x b => ⟨x.dv, x.c, x.a, x.b, x.c0, b, x.p, x.qq, x.rp, x.rq, x.xc⟩, fun _ _ => rfl⟩
def lensP : TrackLens GCell Bool :=
  ⟨GCell.p, fun x b => ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, b, x.qq, x.rp, x.rq, x.xc⟩, fun _ _ => rfl⟩
def lensQQ : TrackLens GCell Bool :=
  ⟨GCell.qq, fun x b => ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.p, b, x.rp, x.rq, x.xc⟩, fun _ _ => rfl⟩

/-- The normalization layout on `2W` cells: numerator `P`, denominator `Q`, the word-length
counter `W` and the marker `2^W` in binary; every other track is zero. -/
def normInput (W P Q : ℕ) : List GCell :=
  List.zipWith lensQQ.put
    (List.zipWith lensP.put
      (List.zipWith lensM0.put
        (List.zipWith lensC0.put (List.replicate (2 * W) gz) (bitsOf (2 * W) W))
        (bitsOf (2 * W) (2 ^ W)))
      (bitsOf (2 * W) P))
    (bitsOf (2 * W) Q)

theorem normInput_spec (W P Q : ℕ) :
    (normInput W P Q).length = 2 * W ∧ tv GCell.c0 (normInput W P Q) = W % 2 ^ (2 * W) ∧
      tv GCell.m0 (normInput W P Q) = 2 ^ W % 2 ^ (2 * W) ∧
      tv GCell.p (normInput W P Q) = P % 2 ^ (2 * W) ∧
      tv GCell.qq (normInput W P Q) = Q % 2 ^ (2 * W) := by
  have b0 : (List.replicate (2 * W) gz).length = 2 * W := List.length_replicate
  have L1 := lensC0.length_zipWith (List.replicate (2 * W) gz) (bitsOf (2 * W) W)
    (by rw [bitsOf_length, b0])
  have L2 := lensM0.length_zipWith
    (List.zipWith lensC0.put (List.replicate (2 * W) gz) (bitsOf (2 * W) W))
    (bitsOf (2 * W) (2 ^ W)) (by rw [bitsOf_length, L1, b0])
  have L3 := lensP.length_zipWith
    (List.zipWith lensM0.put
      (List.zipWith lensC0.put (List.replicate (2 * W) gz) (bitsOf (2 * W) W))
      (bitsOf (2 * W) (2 ^ W))) (bitsOf (2 * W) P) (by rw [bitsOf_length, L2, L1, b0])
  have L4 := lensQQ.length_zipWith
    (List.zipWith lensP.put
      (List.zipWith lensM0.put
        (List.zipWith lensC0.put (List.replicate (2 * W) gz) (bitsOf (2 * W) W))
        (bitsOf (2 * W) (2 ^ W))) (bitsOf (2 * W) P)) (bitsOf (2 * W) Q)
    (by rw [bitsOf_length, L3, L2, L1, b0])
  refine ⟨by unfold normInput; rw [L4, L3, L2, L1, b0], ?_, ?_, ?_, ?_⟩
  · unfold normInput tv
    rw [show GCell.c0 = lensC0.get from rfl,
      lensQQ.frame_zipWith (ℓ₂ := lensC0) (fun _ _ => rfl) _ _ (by rw [bitsOf_length, L3, L2, L1, b0]),
      lensP.frame_zipWith (ℓ₂ := lensC0) (fun _ _ => rfl) _ _ (by rw [bitsOf_length, L2, L1, b0]),
      lensM0.frame_zipWith (ℓ₂ := lensC0) (fun _ _ => rfl) _ _ (by rw [bitsOf_length, L1, b0]),
      lensC0.map_get_zipWith _ _ (by rw [bitsOf_length, b0]), val_bitsOf]
  · unfold normInput tv
    rw [show GCell.m0 = lensM0.get from rfl,
      lensQQ.frame_zipWith (ℓ₂ := lensM0) (fun _ _ => rfl) _ _ (by rw [bitsOf_length, L3, L2, L1, b0]),
      lensP.frame_zipWith (ℓ₂ := lensM0) (fun _ _ => rfl) _ _ (by rw [bitsOf_length, L2, L1, b0]),
      lensM0.map_get_zipWith _ _ (by rw [bitsOf_length, L1, b0]), val_bitsOf]
  · unfold normInput tv
    rw [show GCell.p = lensP.get from rfl,
      lensQQ.frame_zipWith (ℓ₂ := lensP) (fun _ _ => rfl) _ _ (by rw [bitsOf_length, L3, L2, L1, b0]),
      lensP.map_get_zipWith _ _ (by rw [bitsOf_length, L2, L1, b0]), val_bitsOf]
  · unfold normInput tv
    rw [show GCell.qq = lensQQ.get from rfl,
      lensQQ.map_get_zipWith _ _ (by rw [bitsOf_length, L3, L2, L1, b0]), val_bitsOf]

theorem tv_map (f : GCell → Bool) (g : GCell → GCell) (l : List GCell) :
    tv f (l.map g) = tv (fun x => f (g x)) l := by
  unfold tv
  rw [List.map_map]
  rfl

/-- A projection of the six persistent tracks is unchanged. -/
theorem six_map {l l' : List GCell}
    (h : l'.map (fun x => (x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc)) =
      l.map (fun x => (x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc))) {β : Type}
    (π : Bool × Bool × Bool × Bool × Bool × Bool × XCell → β) :
    l'.map (fun x => π (x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc)) =
      l.map (fun x => π (x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc)) := by
  have := congrArg (List.map π) h
  simpa [List.map_map, Function.comp_def] using this

/-- **Normalization on any tape.** Suppose the tape has length `2W`, numerator track `P < 2^W`,
denominator track `0 < Q < 2^W`, counter `W` and marker `2^W`. Then the normalization machine
first-arrives at its exit in exactly `(s(4W + 6) + 8W + 12)(4W + 2)` transitions, where `s` is the
number of Euclidean steps of `(P, Q)`. The result tracks hold `P / gcd(P, Q)` and
`Q / gcd(P, Q)`, and the carried block `xc` is unchanged. -/
theorem norm_run {W : ℕ} (l : List GCell) (len0 : l.length = 2 * W) {P Q : ℕ}
    (hP : P < 2 ^ W) (hQ0 : 0 < Q) (hQ : Q < 2 ^ W) (p0 : tv GCell.p l = P)
    (q0 : tv GCell.qq l = Q) (c00 : tv GCell.c0 l = W) (m00 : tv GCell.m0 l = 2 ^ W) :
    ∃ l', ReachFirst normProg.toProg (Sum.inr AddI.done) (normProg.start, l) l'
        ((euclidSteps P Q * (4 * W + 6) + 8 * W + 12) * (4 * W + 2)) ∧
      l'.length = l.length ∧ tv GCell.rp l' = P / Nat.gcd P Q ∧
      tv GCell.rq l' = Q / Nat.gcd P Q ∧ l'.map GCell.xc = l.map GCell.xc := by
  -- load the Euclidean pair
  have r1 := map_first initF gbit l
  have len1 : (l.map initF).length = 2 * W := by rw [List.length_map, len0]
  have a1 : tv GCell.a (l.map initF) = P := by rw [tv_map]; exact p0
  have b1 : tv GCell.b (l.map initF) = Q := by rw [tv_map]; exact q0
  have c01 : tv GCell.c0 (l.map initF) = W := by rw [tv_map]; exact c00
  have m01 : tv GCell.m0 (l.map initF) = 2 ^ W := by rw [tv_map]; exact m00
  -- the Euclidean loop
  obtain ⟨l2, r2, len2, a2, k2⟩ := gcd_loop Q P _ len1 hP hQ a1 b1 c01 m01
  rw [len1] at len2
  have hg0 : 0 < Nat.gcd P Q := Nat.gcd_pos_of_pos_right _ hQ0
  have hgW : Nat.gcd P Q < 2 ^ W :=
    lt_of_le_of_lt (Nat.le_of_dvd hQ0 (Nat.gcd_dvd_right P Q)) hQ
  have c02 : tv GCell.c0 l2 = W := by
    rw [← c01]; exact tv_congr (f := GCell.c0) (six_map k2 (fun k => k.1))
  have m02 : tv GCell.m0 l2 = 2 ^ W := by
    rw [← m01]; exact tv_congr (f := GCell.m0) (six_map k2 (fun k => k.2.1))
  have p2 : tv GCell.p l2 = P := by
    rw [← p0, tv_congr (f := GCell.p) (six_map k2 (fun k => k.2.2.1)), tv_map]; rfl
  have qq2 : tv GCell.qq l2 = Q := by
    rw [← q0, tv_congr (f := GCell.qq) (six_map k2 (fun k => k.2.2.2.1)), tv_map]; rfl
  -- divide the numerator
  have r3 := map_first setPF gbit l2
  have len3 : (l2.map setPF).length = 2 * W := by rw [List.length_map, len2]
  obtain ⟨l4, l5, r4, r5, len5, q5, _, k5⟩ := shdiv (l2.map setPF) len3 hP hg0 hgW
    (by rw [tv_map, ← p2]; rfl) (by rw [tv_map, ← a2]; rfl)
    (by rw [tv_map]; exact val_false l2) (by rw [tv_map, ← m02]; rfl) (by rw [tv_map, ← c02]; rfl)
  have r6 := map_first savePF gbit l5
  -- divide the denominator
  have r7 := map_first setQF gbit (l5.map savePF)
  have len7 : ((l5.map savePF).map setQF).length = 2 * W := by
    rw [List.length_map, List.length_map, len5, len3]
  have a5 : tv GCell.a l5 = Nat.gcd P Q := by
    rw [tv_congr (f := GCell.a) (keep_map k5 (fun k => k.1)), tv_map, ← a2]; rfl
  have qq5 : tv GCell.qq l5 = Q := by
    rw [tv_congr (f := GCell.qq) (keep_map k5 (fun k => k.2.2.2.2.2.1)), tv_map, ← qq2]; rfl
  have m05 : tv GCell.m0 l5 = 2 ^ W := by
    rw [tv_congr (f := GCell.m0) (keep_map k5 (fun k => k.2.2.2.1)), tv_map, ← m02]; rfl
  have c05 : tv GCell.c0 l5 = W := by
    rw [tv_congr (f := GCell.c0) (keep_map k5 (fun k => k.2.2.1)), tv_map, ← c02]; rfl
  obtain ⟨l8, l9, r8, r9, len9, q9, _, k9⟩ := shdiv ((l5.map savePF).map setQF) len7 hQ hg0 hgW
    (by rw [tv_map, tv_map, ← qq5]; rfl) (by rw [tv_map, tv_map, ← a5]; rfl)
    (by rw [tv_map]; exact val_false _) (by rw [tv_map, tv_map, ← m05]; rfl)
    (by rw [tv_map, tv_map, ← c05]; rfl)
  have r10 := map_first saveQF gbit l9
  -- the composite
  have hc := ProgOn.seq_reachFirst N8 (MAPG saveQF) (Sum.inr DivI.done)
    (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst N7 DVG (Sum.inr (Sum.inl TstI.no))
      (show DivI.prep ≠ DivI.done by decide)
      (ProgOn.seq_reachFirst N6 SHG (Sum.inr AddI.done)
        (show (Sum.inl TstI.test : TstI ⊕ (AddI ⊕ AddI)) ≠ Sum.inl TstI.no by decide)
        (ProgOn.seq_reachFirst N5 (MAPG setQF) (Sum.inr AddI.done)
          (show AddI.go ≠ AddI.done by decide)
          (ProgOn.seq_reachFirst N4 (MAPG savePF) (Sum.inr DivI.done)
            (show AddI.go ≠ AddI.done by decide)
            (ProgOn.seq_reachFirst N3 DVG (Sum.inr (Sum.inl TstI.no))
              (show DivI.prep ≠ DivI.done by decide)
              (ProgOn.seq_reachFirst N2 SHG (Sum.inr AddI.done)
                (show (Sum.inl TstI.test : TstI ⊕ (AddI ⊕ AddI)) ≠ Sum.inl TstI.no by decide)
                (ProgOn.seq_reachFirst N1 (MAPG setPF) (Sum.inr (Sum.inl TstI.no))
                  (show AddI.go ≠ AddI.done by decide)
                  (ProgOn.seq_reachFirst (MAPG initF) gcdLoop AddI.done
                    (Sum.inl_injective.ne (show TstI.test ≠ TstI.no by decide)) r1 r2)
                  r3) r4) r5) r6) r7) r8) r9) r10
  rw [len0, len2, List.length_map, len5, len3, len9, len7] at hc
  refine ⟨(l9.map saveQF), ?_, ?_, ?_, ?_, ?_⟩
  · convert hc using 1
    ring
  · rw [List.length_map, len9, len7, len0]
  · rw [tv_map, show tv (fun x => (saveQF x).rp) l9 = tv GCell.rp l9 from rfl,
      tv_congr (f := GCell.rp) (keep_map k9 (fun k => k.2.2.2.2.2.2.1)), tv_map, tv_map]
    exact q5
  · rw [tv_map]
    exact q9
  · have e1 : (l9.map saveQF).map GCell.xc = l9.map GCell.xc := by rw [List.map_map]; rfl
    have e2 : l9.map GCell.xc = ((l5.map savePF).map setQF).map GCell.xc :=
      keep_map k9 (fun k => k.2.2.2.2.2.2.2.2)
    have e3 : ((l5.map savePF).map setQF).map GCell.xc = l5.map GCell.xc := by
      rw [List.map_map, List.map_map]; rfl
    have e4 : l5.map GCell.xc = (l2.map setPF).map GCell.xc :=
      keep_map k5 (fun k => k.2.2.2.2.2.2.2.2)
    have e5 : (l2.map setPF).map GCell.xc = l2.map GCell.xc := by rw [List.map_map]; rfl
    have e6 : l2.map GCell.xc = (l.map initF).map GCell.xc := six_map k2 (fun k => k.2.2.2.2.2.2)
    have e7 : (l.map initF).map GCell.xc = l.map GCell.xc := by rw [List.map_map]; rfl
    rw [e1, e2, e3, e4, e5, e6, e7]

/-- **Normalization on the layout.** For `P < 2^W` and `0 < Q < 2^W`, the normalization machine
first-arrives at its exit in exactly `(s(4W + 6) + 8W + 12)(4W + 2)` transitions, where `s` is the
number of Euclidean steps of `(P, Q)`. The result tracks hold `P / gcd(P, Q)` and
`Q / gcd(P, Q)`. -/
theorem norm_layout {W : ℕ} (hW : 0 < W) {P Q : ℕ} (hP : P < 2 ^ W) (hQ0 : 0 < Q)
    (hQ : Q < 2 ^ W) :
    ∃ l', ReachFirst normProg.toProg (Sum.inr AddI.done) (normProg.start, normInput W P Q) l'
        ((euclidSteps P Q * (4 * W + 6) + 8 * W + 12) * (4 * W + 2)) ∧
      tv GCell.rp l' = P / Nat.gcd P Q ∧ tv GCell.rq l' = Q / Nat.gcd P Q := by
  obtain ⟨len0, c00, m00, p0, q0⟩ := normInput_spec W P Q
  have hWW : 2 ^ W < 2 ^ (2 * W) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hW2 : W < 2 ^ (2 * W) := lt_trans Nat.lt_two_pow_self hWW
  rw [Nat.mod_eq_of_lt hW2] at c00
  rw [Nat.mod_eq_of_lt hWW] at m00
  rw [Nat.mod_eq_of_lt (lt_trans hP hWW)] at p0
  rw [Nat.mod_eq_of_lt (lt_trans hQ hWW)] at q0
  obtain ⟨l', hr, _, hp, hq, _⟩ := norm_run _ len0 hP hQ0 hQ p0 q0 c00 m00
  exact ⟨l', hr, hp, hq⟩


/-- **Normalization of a fraction on the compiled Turing machine.** For `P < 2^W` and
`0 < Q < 2^W`, from the layout `normInput W P Q` the compiled single-tape TM computes the
normalized fraction: the result tracks hold a coprime pair `(P', Q')` with `0 < Q'` and
`P'/Q' = P/Q`. It takes exactly `(s(4W + 6) + 8W + 12)(4W + 2)` transitions, where `s ≤ 2W` is
the number of Euclidean steps. -/
theorem norm_tm {W : ℕ} (hW : 0 < W) {P Q : ℕ} (hP : P < 2 ^ W) (hQ0 : 0 < Q) (hQ : Q < 2 ^ W)
    (T : ℤ → Sym GCell) (hT : normProg.toProg.Repr T (normInput W P Q)) :
    ∃ l' T', normProg.toProg.Repr T' l' ∧
      tv GCell.rp l' = P / Nat.gcd P Q ∧ tv GCell.rq l' = Q / Nat.gcd P Q ∧
      Nat.Coprime (tv GCell.rp l') (tv GCell.rq l') ∧ 0 < tv GCell.rq l' ∧
      ((tv GCell.rp l' : ℚ) / tv GCell.rq l' = (P : ℚ) / Q) ∧
      euclidSteps P Q ≤ 2 * W ∧
      normProg.toProg.toTM.run
          ⟨.fwd normProg.start (normProg.toProg.init normProg.start), T, 0⟩
          ((euclidSteps P Q * (4 * W + 6) + 8 * W + 12) * (4 * W + 2)) =
        ⟨.fwd (Sum.inr AddI.done) (normProg.toProg.init (Sum.inr AddI.done)), T', 0⟩ := by
  obtain ⟨l', hr, hp, hq⟩ := norm_layout hW hP hQ0 hQ
  obtain ⟨T', hT', hrun⟩ := normProg.toProg.reach_run hr.reach T hT
  have hg0 : 0 < Nat.gcd P Q := Nat.gcd_pos_of_pos_right _ hQ0
  have hdP := Nat.div_mul_cancel (Nat.gcd_dvd_left P Q)
  have hdQ := Nat.div_mul_cancel (Nat.gcd_dvd_right P Q)
  have hQ' : 0 < Q / Nat.gcd P Q := Nat.div_pos (Nat.le_of_dvd hQ0 (Nat.gcd_dvd_right P Q)) hg0
  refine ⟨l', T', hT', hp, hq, ?_, by rw [hq]; exact hQ', ?_, euclidSteps_le W P Q hQ, hrun⟩
  · rw [hp, hq]
    exact Nat.coprime_div_gcd_div_gcd hg0
  · rw [hp, hq]
    have hg : (Nat.gcd P Q : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
    have hq0 : ((Q / Nat.gcd P Q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hQ'.ne'
    have hQq : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ0.ne'
    have eP : (P : ℚ) = ((P / Nat.gcd P Q : ℕ) : ℚ) * Nat.gcd P Q := by exact_mod_cast hdP.symm
    have eQ : (Q : ℚ) = ((Q / Nat.gcd P Q : ℕ) : ℚ) * Nat.gcd P Q := by exact_mod_cast hdQ.symm
    rw [div_eq_div_iff hq0 hQq, eQ, eP]
    ring

end PVNP.Discrete.SweepArith
