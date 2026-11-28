import PVNP.SweepAccess
import PVNP.SweepComplex

/-!
# Polynomial evaluation on the Turing machine: a Horner loop with indexed coefficient access

A polynomial `p(x) = Σ_{k<K} c_k x^k` with signed coefficients is evaluated at a signed point by
one machine, uniform in the degree. The coefficients are stored as `L`-bit words in excess
`s = 2^{L−1}` (`d_k = c_k + s`), packed on one track. The machine is a loop of verified programs
(`SweepLoop`) on the common alphabet `HCell`. Each iteration, for the coefficient index `j − 1`:

1. a cellwise map loads the offset `(j − 1)L` into the access counter;
2. the access machine (`SweepAccess`) reads `d_{j−1}`;
3. a cellwise map loads the multiplier: accumulator `d_{j−1}`, multiplicand `res`, multiplier `x`;
4. the verified multiplier (`SweepMul`) leaves `d_{j−1} + res·x` modulo `2ⁿ`;
5. the verified subtractor removes the excess `s`, writing `res·x + c_{j−1}` to `res`;
6. the subtractor steps the offset down by `L`, and a cellwise map stores it;
7. the counter decrements.

The loop test continues while the counter is nonzero. In two's complement every step is an exact
code modulo `2ⁿ` (`tc_mul`, `tc_add`, `sub_tc_value`), so only the final value must lie in range.

* `seq_ext_none`, `loop_ext_none`, `viaLens_ext_none`: composites never extend the tape.
* `hornerFrom`, `hornerFrom_eq`: Horner's scheme from the top, `R ↦ R xʲ + Σ_{k<j} c_k x^k`.
* `body_poly`: one iteration maps `res = tc(R)` to `tc(R x + c_{j−1})`.
* `poly_loop`: the loop first-arrives at its stop exit with `res = tc(hornerFrom R j)`.
* `poly_tm`: **polynomial evaluation on the compiled TM**: the result track, read in `n`-bit two's
  complement, is `Σ_{k<K} c_k x^k`, with exact and polynomial cost.
-/

namespace PVNP.Discrete.Sweep.ProgOn

variable {D : Type} [Fintype D] [DecidableEq D]

/-- A sequential composite of programs that never extend the tape never extends it. -/
theorem seq_ext_none (A B : ProgOn D) (e : A.I) (hA : ∀ i b, A.ext i b = none)
    (hB : ∀ i b, B.ext i b = none) : ∀ i b, (seq A B e).ext i b = none := by
  intro i b
  rcases i with i | j <;> rcases b with a | c
  · exact hA i a
  · rfl
  · rfl
  · exact hB j c

/-- A loop of programs that never extend the tape never extends it. -/
theorem loop_ext_none (T B : ProgOn D) (eT : T.I) (eB : B.I) (hT : ∀ i b, T.ext i b = none)
    (hB : ∀ i b, B.ext i b = none) : ∀ i b, (loop T B eT eB).ext i b = none :=
  seq_ext_none T B eT hT hB

/-- A lifted program that never extends the tape never extends it. -/
theorem viaLens_ext_none {E : Type} [Fintype E] [DecidableEq E] (A : ProgOn D)
    (ℓ : TrackLens E D) (z : E) (lift' : Bool → E) (hA : ∀ i b, A.ext i b = none) :
    ∀ i b, (A.viaLens ℓ z lift').ext i b = none := by
  intro i b
  show (A.ext i b).map (ℓ.put z) = none
  rw [hA]
  rfl

end PVNP.Discrete.Sweep.ProgOn

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

theorem fscan_sub_ab : ∀ (w : Bool) (l : List Cell),
    (fscan fsub w l).1.map Cell.a = l.map Cell.a ∧ (fscan fsub w l).1.map Cell.b = l.map Cell.b
  | _, [] => ⟨rfl, rfl⟩
  | w, x :: l => by
    obtain ⟨h1, h2⟩ := fscan_sub_ab (fsub w x).2 l
    simp only [fscan, List.map_cons, h1, h2]
    exact ⟨rfl, rfl⟩

theorem accessProg_ext : ∀ i b, accessProg.ext i b = none :=
  ProgOn.seq_ext_none _ _ _
    (ProgOn.seq_ext_none _ _ _ (fun _ _ => rfl)
      (ProgOn.viaLens_ext_none _ _ _ _ shrLoop_ext))
    (fun _ _ => rfl)

/-! ### Horner's scheme -/

/-- Horner's scheme from the top `j` coefficients down. -/
def hornerFrom (cs : List ℤ) (x : ℤ) : ℤ → ℕ → ℤ
  | R, 0 => R
  | R, j + 1 => hornerFrom cs x (R * x + cs.getD j 0) j

theorem hornerFrom_eq (cs : List ℤ) (x : ℤ) : ∀ (j : ℕ) (R : ℤ),
    hornerFrom cs x R j = R * x ^ j + ∑ k ∈ Finset.range j, cs.getD k 0 * x ^ k
  | 0, R => by simp [hornerFrom]
  | j + 1, R => by
    rw [hornerFrom, hornerFrom_eq cs x j, Finset.sum_range_succ]
    ring

/-! ### The common alphabet -/

/-- Cells for polynomial evaluation: the access cells (work, access counter, packed coefficients,
mask), the multiplier, the offset `off`, the constants `lL = L` and `sT = 2^{L−1}`, the counter
`cnt`, the point `px`, the result `res`, and two scratch tracks. -/
structure HCell where
  ac : ACell
  m : MCell
  off : Bool
  lL : Bool
  sT : Bool
  cnt : Bool
  px : Bool
  res : Bool
  tmp : Bool
  zt : Bool
  deriving DecidableEq

instance : Fintype HCell :=
  Fintype.ofEquiv (ACell × MCell × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool)
    { toFun := fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩
      invFun := fun x => ⟨x.ac, x.m, x.off, x.lL, x.sT, x.cnt, x.px, x.res, x.tmp, x.zt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The value of one track. -/
def pv (f : HCell → Bool) (l : List HCell) : ℕ := val (l.map f)

def lensPa : TrackLens HCell ACell :=
  ⟨HCell.ac, fun x a => ⟨a, x.m, x.off, x.lL, x.sT, x.cnt, x.px, x.res, x.tmp, x.zt⟩,
    fun _ _ => rfl⟩
def lensPm : TrackLens HCell MCell :=
  ⟨HCell.m, fun x m => ⟨x.ac, m, x.off, x.lL, x.sT, x.cnt, x.px, x.res, x.tmp, x.zt⟩,
    fun _ _ => rfl⟩
/-- The excess correction: `res := acc − s`. -/
def lensPs : TrackLens HCell Cell :=
  ⟨fun x => ⟨x.m.acc, x.sT, x.res⟩,
    fun x c => ⟨x.ac, ⟨x.m.x, x.m.y, c.a⟩, x.off, x.lL, c.b, x.cnt, x.px, c.r, x.tmp, x.zt⟩,
    fun _ _ => rfl⟩
/-- The offset step: `tmp := off − L`. -/
def lensPo : TrackLens HCell Cell :=
  ⟨fun x => ⟨x.off, x.lL, x.tmp⟩,
    fun x c => ⟨x.ac, x.m, c.a, c.b, x.sT, x.cnt, x.px, x.res, c.r, x.zt⟩,
    fun _ _ => rfl⟩
/-- The counter step: `cnt := cnt − 1` (the scratch track `zt` rides along). -/
def lensPc : TrackLens HCell SCell :=
  ⟨fun x => ⟨x.zt, x.cnt⟩,
    fun x s => ⟨x.ac, x.m, x.off, x.lL, x.sT, s.c, x.px, x.res, x.tmp, s.x⟩,
    fun _ _ => rfl⟩

def hz0 : HCell := ⟨az, ⟨false, false, false⟩, false, false, false, false, false, false, false, false⟩
def hbit (b : Bool) : HCell :=
  ⟨abit b, ⟨false, false, false⟩, false, false, false, false, false, false, false, false⟩

/-- Load the access counter with the offset. -/
def setcF (x : HCell) : HCell :=
  ⟨⟨⟨x.ac.s.x, x.off⟩, x.ac.v, x.ac.mask⟩, x.m, x.off, x.lL, x.sT, x.cnt, x.px, x.res, x.tmp, x.zt⟩
/-- Load the multiplier: accumulator = the word read, multiplicand = `res`, multiplier = `px`. -/
def ldmF (x : HCell) : HCell :=
  ⟨x.ac, ⟨x.res, x.px, x.ac.s.x⟩, x.off, x.lL, x.sT, x.cnt, x.px, x.res, x.tmp, x.zt⟩
/-- Store the stepped offset. -/
def movoF (x : HCell) : HCell :=
  ⟨x.ac, x.m, x.tmp, x.lL, x.sT, x.cnt, x.px, x.res, x.tmp, x.zt⟩

def MAPP (f : HCell → HCell) : ProgOn HCell := ProgOn.ofProg (mapProg HCell f hbit)
def ACCP : ProgOn HCell := accessProg.viaLens lensPa hz0 hbit
def MULP : ProgOn HCell := (ProgOn.ofProg mulProg).viaLens lensPm hz0 hbit
def SUBS : ProgOn HCell := (ProgOn.ofProg subProg).viaLens lensPs hz0 hbit
def SUBO : ProgOn HCell := (ProgOn.ofProg subProg).viaLens lensPo hz0 hbit
def DECC : ProgOn HCell := (ProgOn.ofProg decProg).viaLens lensPc hz0 hbit

def H1 : ProgOn HCell := ProgOn.seq (MAPP setcF) ACCP AddI.done
def H2 : ProgOn HCell := ProgOn.seq H1 (MAPP ldmF) (Sum.inr (Sum.inr AddI.done))
def H3 : ProgOn HCell := ProgOn.seq H2 MULP (Sum.inr AddI.done)
def H4 : ProgOn HCell := ProgOn.seq H3 SUBS (Sum.inr MulI.done)
def H5 : ProgOn HCell := ProgOn.seq H4 SUBO (Sum.inr AddI.done)
def H6 : ProgOn HCell := ProgOn.seq H5 (MAPP movoF) (Sum.inr AddI.done)

/-- **One Horner step**: read the coefficient, multiply-add, correct the excess, step the
offset, decrement the counter. -/
def BODYP : ProgOn HCell := ProgOn.seq H6 DECC (Sum.inr AddI.done)

/-- The zero test of the counter. -/
def fnzP (nz : Bool) (x : HCell) : HCell × Bool := (x, nz || x.cnt)

def testP : Prog where
  D := HCell
  I := TstI
  B := Bool
  lift := hbit
  start := .test
  init _ := false
  fwd
    | .test => fnzP
    | _ => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next
    | .test => fun b => if b then .inl .yes else .inl .no
    | .yes => fun _ => .inl .yes
    | .no => fun _ => .inl .no

def TSTP : ProgOn HCell := ProgOn.ofProg testP

/-- **The Horner loop.** -/
def hornerLoop : ProgOn HCell := ProgOn.loop TSTP BODYP TstI.yes (Sum.inr AddI.done)

theorem fscan_nzP : ∀ (b : Bool) (l : List HCell),
    (fscan fnzP b l).1 = l ∧ (fscan fnzP b l).2 = (b || decide (pv HCell.cnt l ≠ 0))
  | b, [] => by simp [fscan, pv, val]
  | b, ⟨ac, m, off, lL, sT, xc, px, res, tmp, zt⟩ :: l => by
    obtain ⟨h1, h2⟩ := fscan_nzP (b || xc) l
    refine ⟨by simp only [fscan, fnzP, h1], ?_⟩
    simp only [fscan, fnzP, h2, pv, List.map_cons, val]
    cases b <;> cases xc <;> simp

theorem testP_step (l : List HCell) :
    TSTP.toProg.stepP (TstI.test, l) =
      .inl (if pv HCell.cnt l ≠ 0 then TstI.yes else TstI.no, l) := by
  obtain ⟨h1, h2⟩ := fscan_nzP false l
  have ht : testP.trip TstI.test l = (l, decide (pv HCell.cnt l ≠ 0)) := by
    simp only [Prog.trip, Prog.mid, Prog.fpass, testP, bscan_id]
    rw [h1, h2]
    simp
  show testP.stepP (TstI.test, l) = _
  simp only [Prog.stepP, ht]
  by_cases h : pv HCell.cnt l ≠ 0
  · have hn : testP.next TstI.test (decide (pv HCell.cnt l ≠ 0)) = .inl TstI.yes := by
      simp [testP, h]
    rw [hn, if_pos h]
  · have hn : testP.next TstI.test (decide (pv HCell.cnt l ≠ 0)) = .inl TstI.no := by
      simp [testP, h]
    rw [hn, if_neg h]

theorem testP_cost (l : List HCell) : TSTP.toProg.tripCost TSTP.start l = 2 * l.length + 2 := by
  show testP.tripCost TstI.test l = _
  simp [Prog.tripCost, Prog.fpass, testP]

/-! ### One stage on `HCell` -/

/-- **The access stage**, with its frame. -/
theorem st_acc (l : List HCell) (L : ℕ)
    (hm : l.map (fun x => x.ac.mask) = bitsOf l.length (2 ^ L - 1)) :
    ∃ l', ReachFirst ACCP.toProg (Sum.inr AddI.done) (accessProg.start, l) l'
        ((3 * pv (fun x => x.ac.s.c) l + 3) * (2 * l.length + 2)) ∧
      pv (fun x => x.ac.s.x) l' = pv (fun x => x.ac.v) l / 2 ^ pv (fun x => x.ac.s.c) l % 2 ^ L ∧
      l'.map (fun x => x.ac.v) = l.map (fun x => x.ac.v) ∧
      l'.map (fun x => x.ac.mask) = l.map (fun x => x.ac.mask) ∧ l'.length = l.length ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens HCell D₂), lensPa.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hm' : (l.map lensPa.get).map ACell.mask = bitsOf (l.map lensPa.get).length (2 ^ L - 1) := by
    rw [List.map_map, List.length_map]; exact hm
  obtain ⟨a', hr, hx, hv, hk, hlen⟩ := access_run (l.map lensPa.get) L hm'
  have ec : val ((l.map lensPa.get).map (fun z => z.s.c)) = pv (fun x => x.ac.s.c) l := by
    rw [List.map_map]; rfl
  have ev : val ((l.map lensPa.get).map ACell.v) = pv (fun x => x.ac.v) l := by
    rw [List.map_map]; rfl
  rw [ec, List.length_map] at hr
  rw [ec, ev] at hx
  obtain ⟨l', hr', hv'⟩ := ProgOn.reachFirst_lens accessProg lensPa hz0 hbit hr l rfl
  have hfr : ∀ {D₂ : Type} (ℓ₂ : TrackLens HCell D₂), lensPa.Indep ℓ₂ →
      l'.map ℓ₂.get = l.map ℓ₂.get := fun ℓ₂ hi =>
    ProgOn.reachFirst_lens_frame accessProg lensPa hz0 hbit accessProg_ext hi hr'
  refine ⟨l', hr', ?_, ?_, ?_, ?_, hfr⟩
  · have e : pv (fun x => x.ac.s.x) l' = val (a'.map (fun z => z.s.x)) := by
      rw [← hv']; unfold pv; rw [List.map_map]; rfl
    rw [e, hx]
  · have e : l'.map (fun x => x.ac.v) = a'.map ACell.v := by rw [← hv', List.map_map]; rfl
    exact e.trans (by rw [hv, List.map_map]; rfl)
  · have e : l'.map (fun x => x.ac.mask) = a'.map ACell.mask := by rw [← hv', List.map_map]; rfl
    exact e.trans (by rw [hk, List.map_map]; rfl)
  · have := congrArg List.length hv'
    rw [List.length_map, hlen, List.length_map] at this
    exact this

/-- **The multiplier stage**, with its frame. -/
theorem st_mul (l : List HCell) (hl : l ≠ []) :
    ∃ l', ReachFirst MULP.toProg MulI.done (MulI.prep, l) l'
        ((trips (pv (fun x => x.m.y) l) + 1) * (2 * l.length + 2)) ∧
      pv (fun x => x.m.acc) l' =
        (pv (fun x => x.m.acc) l + pv (fun x => x.m.x) l * pv (fun x => x.m.y) l) % 2 ^ l.length ∧
      l'.length = l.length ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens HCell D₂), lensPm.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  obtain ⟨m, hr, hlen, _, hv⟩ := mul_first (l.map lensPm.get) (by simpa using hl)
  have ey : vY (l.map lensPm.get) = pv (fun x => x.m.y) l := by
    unfold vY pv; rw [List.map_map]; rfl
  have ex : vX (l.map lensPm.get) = pv (fun x => x.m.x) l := by
    unfold vX pv; rw [List.map_map]; rfl
  have ea : vA (l.map lensPm.get) = pv (fun x => x.m.acc) l := by
    unfold vA pv; rw [List.map_map]; rfl
  rw [ey, List.length_map] at hr
  rw [List.length_map] at hv hlen
  obtain ⟨l', hr', hv'⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg mulProg) lensPm hz0 hbit hr l rfl
  have hfr : ∀ {D₂ : Type} (ℓ₂ : TrackLens HCell D₂), lensPm.Indep ℓ₂ →
      l'.map ℓ₂.get = l.map ℓ₂.get := fun ℓ₂ hi =>
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg mulProg) lensPm hz0 hbit (fun _ _ => rfl) hi hr'
  have hl' : l'.length = l.length := by
    have := congrArg List.length hv'
    rw [List.length_map, hlen] at this
    exact this
  refine ⟨l', hr', ?_, hl', hfr⟩
  have hlt : vA m < 2 ^ l.length := by
    have := val_lt (m.map MCell.acc)
    rw [List.length_map, hlen] at this
    exact this
  have e : pv (fun x => x.m.acc) l' = vA m := by
    rw [← hv']; unfold pv vA; rw [List.map_map]; rfl
  rw [e, ← Nat.mod_eq_of_lt hlt, hv, ea, ex, ey]

/-- **A subtractor stage** along a lens, with its frame. -/
theorem st_sub (ℓ : TrackLens HCell Cell) (l : List HCell) :
    ∃ l', ReachFirst ((ProgOn.ofProg subProg).viaLens ℓ hz0 hbit).toProg AddI.done (AddI.go, l) l'
        (2 * l.length + 2) ∧
      l'.map ℓ.get = (fscan fsub false (l.map ℓ.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens HCell D₂), ℓ.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := sub_first (l.map ℓ.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg subProg) ℓ hz0 hbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg subProg) ℓ hz0 hbit (fun _ _ => rfl) hi hr'

/-- **The counter stage**, with its frame. -/
theorem st_dec (l : List HCell) :
    ∃ l', ReachFirst DECC.toProg AddI.done (AddI.go, l) l' (2 * l.length + 2) ∧
      l'.map lensPc.get = (fscan fdec true (l.map lensPc.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens HCell D₂), lensPc.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := dec_first (l.map lensPc.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg decProg) lensPc hz0 hbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg decProg) lensPc hz0 hbit (fun _ _ => rfl) hi hr'

/-! ### Frames on `HCell` -/

def lensRA : TrackLens HCell (MCell × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.m, x.off, x.lL, x.sT, x.cnt, x.px, x.res, x.tmp, x.zt),
    fun x k => ⟨x.ac, k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2.1, k.2.2.2.2.2.1, k.2.2.2.2.2.2.1,
      k.2.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2.2⟩, fun _ _ => rfl⟩
def lensRM : TrackLens HCell (ACell × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.ac, x.off, x.lL, x.sT, x.cnt, x.px, x.res, x.tmp, x.zt),
    fun x k => ⟨k.1, x.m, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2.1, k.2.2.2.2.2.1, k.2.2.2.2.2.2.1,
      k.2.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2.2⟩, fun _ _ => rfl⟩
def lensRS : TrackLens HCell (ACell × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.ac, x.m.x, x.m.y, x.off, x.lL, x.cnt, x.px, x.tmp, x.zt),
    fun x k => ⟨k.1, ⟨k.2.1, k.2.2.1, x.m.acc⟩, k.2.2.2.1, k.2.2.2.2.1, x.sT, k.2.2.2.2.2.1,
      k.2.2.2.2.2.2.1, x.res, k.2.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2.2⟩, fun _ _ => rfl⟩
def lensRO : TrackLens HCell (ACell × MCell × Bool × Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.ac, x.m, x.sT, x.cnt, x.px, x.res, x.zt),
    fun x k => ⟨k.1, k.2.1, x.off, x.lL, k.2.2.1, k.2.2.2.1, k.2.2.2.2.1, k.2.2.2.2.2.1, x.tmp,
      k.2.2.2.2.2.2⟩, fun _ _ => rfl⟩
def lensRC : TrackLens HCell (ACell × MCell × Bool × Bool × Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.ac, x.m, x.off, x.lL, x.sT, x.px, x.res, x.tmp),
    fun x k => ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2.1, x.cnt, k.2.2.2.2.2.1,
      k.2.2.2.2.2.2.1, k.2.2.2.2.2.2.2, x.zt⟩, fun _ _ => rfl⟩

/-- A projection of an unchanged view is unchanged. -/
theorem map_proj {α β γ : Type} {l l' : List α} {g : α → β} (h : l'.map g = l.map g)
    (π : β → γ) : l'.map (fun x => π (g x)) = l.map (fun x => π (g x)) := by
  have := congrArg (List.map π) h
  simpa [List.map_map, Function.comp_def] using this

theorem pv_congr {f : HCell → Bool} {l l' : List HCell} (h : l'.map f = l.map f) :
    pv f l' = pv f l := by
  unfold pv; rw [h]

/-- The invariant tracks of the Horner loop. -/
structure HInv (N L V s X : ℕ) (l : List HCell) : Prop where
  len : l.length = N
  mask : l.map (fun x => x.ac.mask) = bitsOf N (2 ^ L - 1)
  v : pv (fun x => x.ac.v) l = V
  lL : pv HCell.lL l = L
  sT : pv HCell.sT l = s
  px : pv HCell.px l = X

/-! ### One Horner step -/

/-- **One Horner step.** From a tape with counter `j > 0`, offset `(j − 1)L` and result
`tc(R)`, the body first-arrives at its exit in exactly `(3(j − 1)L + trips X + 10)(2N + 2)`
transitions. The result becomes `tc(R x + (w − s))`, where `w` is the word at offset
`(j − 1)L`; the counter becomes `j − 1` and the offset `(j − 2)L`. -/
theorem body_poly {N L V s X : ℕ} {l : List HCell} (hI : HInv N L V s X l) (hN : 0 < N)
    {j : ℕ} (hj : 0 < j) (hcnt : pv HCell.cnt l = j) (hoff : pv HCell.off l = (j - 1) * L)
    (hoffN : (j - 1) * L < 2 ^ N) (hLN : L < 2 ^ N) (hsN : s < 2 ^ N) {x R : ℤ}
    (hX : X = tc N x) (hres : pv HCell.res l = tc N R) :
    ∃ l', ReachFirst BODYP.toProg (Sum.inr AddI.done) (BODYP.start, l) l'
        ((3 * ((j - 1) * L) + trips X + 10) * (2 * N + 2)) ∧
      HInv N L V s X l' ∧ pv HCell.cnt l' = j - 1 ∧
      pv HCell.res l' = tc N (R * x + (((V / 2 ^ ((j - 1) * L) % 2 ^ L : ℕ) : ℤ) - s)) ∧
      (1 < j → pv HCell.off l' = (j - 2) * L) := by
  obtain ⟨len0, mask0, v0, lL0, sT0, px0⟩ := hI
  have hne : ∀ l : List HCell, l.length = N → l ≠ [] := by
    intro l h e; rw [e, List.length_nil] at h; omega
  -- stage 1: load the access counter
  have r1 := map_first setcF hbit l
  have len1 : (l.map setcF).length = N := by rw [List.length_map, len0]
  have mask1 : (l.map setcF).map (fun x => x.ac.mask) =
      bitsOf (l.map setcF).length (2 ^ L - 1) := by
    rw [len1, List.map_map, ← mask0]; rfl
  -- stage 2: read the coefficient word
  obtain ⟨l2, r2, x2, v2, k2, len2, f2⟩ := st_acc (l.map setcF) L mask1
  have c1 : pv (fun x => x.ac.s.c) (l.map setcF) = (j - 1) * L := by
    rw [← hoff]; unfold pv; rw [List.map_map]; rfl
  have vv1 : pv (fun x => x.ac.v) (l.map setcF) = V := by
    rw [← v0]; unfold pv; rw [List.map_map]; rfl
  rw [c1, len1] at r2
  rw [vv1, c1] at x2
  have len2' : l2.length = N := by rw [len2, len1]
  have g2 : l2.map lensRA.get = (l.map setcF).map lensRA.get := f2 lensRA (fun _ _ => rfl)
  -- stage 3: load the multiplier
  have r3 := map_first ldmF hbit l2
  have len3 : (l2.map ldmF).length = N := by rw [List.length_map, len2']
  -- stage 4: multiply and add
  obtain ⟨l4, r4, acc4, len4, f4⟩ := st_mul (l2.map ldmF) (hne _ len3)
  have pxl2 : l2.map HCell.px = l.map HCell.px := by
    have h : l2.map HCell.px = (l.map setcF).map HCell.px := map_proj g2 (fun k => k.2.2.2.2.2.1)
    exact h.trans (by rw [List.map_map]; rfl)
  have resl2 : l2.map HCell.res = l.map HCell.res := by
    have h : l2.map HCell.res = (l.map setcF).map HCell.res :=
      map_proj g2 (fun k => k.2.2.2.2.2.2.1)
    exact h.trans (by rw [List.map_map]; rfl)
  have y3 : pv (fun x => x.m.y) (l2.map ldmF) = X := by
    unfold pv; rw [List.map_map]
    exact (congrArg val pxl2).trans px0
  have x3 : pv (fun x => x.m.x) (l2.map ldmF) = tc N R := by
    unfold pv; rw [List.map_map]
    exact (congrArg val resl2).trans hres
  have a3 : pv (fun x => x.m.acc) (l2.map ldmF) = V / 2 ^ ((j - 1) * L) % 2 ^ L := by
    unfold pv; rw [List.map_map]
    exact x2
  rw [y3, len3] at r4
  rw [a3, x3, y3, len3] at acc4
  have len4' : l4.length = N := by rw [len4, len3]
  have g4 : l4.map lensRM.get = (l2.map ldmF).map lensRM.get := f4 lensRM (fun _ _ => rfl)
  -- the accumulator as a code
  have hVN : V < 2 ^ N := by
    have := val_lt (l.map (fun x => x.ac.v))
    rw [List.length_map, len0] at this
    unfold pv at v0
    rw [← v0]; exact this
  have hwN : V / 2 ^ ((j - 1) * L) % 2 ^ L < 2 ^ N :=
    lt_of_le_of_lt (le_trans (Nat.mod_le _ _) (Nat.div_le_self _ _)) hVN
  have hacc4 : pv (fun x => x.m.acc) l4 =
      tc N (((V / 2 ^ ((j - 1) * L) % 2 ^ L : ℕ) : ℤ) + R * x) := by
    rw [acc4, hX, ← Nat.add_mod_mod, tc_mul, ← tc_natCast hwN, tc_add, tc_natCast hwN]
  -- stage 5: remove the excess
  obtain ⟨l5, r5, v5, f5⟩ := st_sub lensPs l4
  have sTl4 : l4.map HCell.sT = l.map HCell.sT := by
    have h4 : l4.map HCell.sT = (l2.map ldmF).map HCell.sT := map_proj g4 (fun k => k.2.2.2.1)
    have h2 : l2.map HCell.sT = (l.map setcF).map HCell.sT := map_proj g2 (fun k => k.2.2.2.1)
    exact h4.trans (by rw [List.map_map]; exact h2.trans (by rw [List.map_map]; rfl))
  have ha5 : val ((l4.map lensPs.get).map Cell.a) =
      tc N (((V / 2 ^ ((j - 1) * L) % 2 ^ L : ℕ) : ℤ) + R * x) := by
    rw [List.map_map]; exact hacc4
  have hb5 : val ((l4.map lensPs.get).map Cell.b) = tc N (s : ℤ) := by
    rw [List.map_map, tc_natCast hsN]
    exact (congrArg val sTl4).trans sT0
  have hsub5 := sub_tc_value (l4.map lensPs.get) N (by rw [List.length_map, len4']) _ _ ha5 hb5
  obtain ⟨-, hbb5⟩ := fscan_sub_ab false (l4.map lensPs.get)
  have len5 : l5.length = N := by
    have := congrArg List.length v5
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, len4']
  have g5 : l5.map lensRS.get = l4.map lensRS.get := f5 lensRS (fun _ _ => rfl)
  -- stage 6: step the offset
  obtain ⟨l6, r6, v6, f6⟩ := st_sub lensPo l5
  have offl5 : l5.map HCell.off = l.map HCell.off := by
    have h5 : l5.map HCell.off = l4.map HCell.off := map_proj g5 (fun k => k.2.2.2.1)
    have h4 : l4.map HCell.off = (l2.map ldmF).map HCell.off := map_proj g4 (fun k => k.2.1)
    have h2 : l2.map HCell.off = (l.map setcF).map HCell.off := map_proj g2 (fun k => k.2.1)
    exact h5.trans (h4.trans (by rw [List.map_map]; exact h2.trans (by rw [List.map_map]; rfl)))
  have lLl5 : l5.map HCell.lL = l.map HCell.lL := by
    have h5 : l5.map HCell.lL = l4.map HCell.lL := map_proj g5 (fun k => k.2.2.2.2.1)
    have h4 : l4.map HCell.lL = (l2.map ldmF).map HCell.lL := map_proj g4 (fun k => k.2.2.1)
    have h2 : l2.map HCell.lL = (l.map setcF).map HCell.lL := map_proj g2 (fun k => k.2.2.1)
    exact h5.trans (h4.trans (by rw [List.map_map]; exact h2.trans (by rw [List.map_map]; rfl)))
  have ha6 : val ((l5.map lensPo.get).map Cell.a) = tc N (((j - 1) * L : ℕ) : ℤ) := by
    rw [List.map_map, tc_natCast hoffN]
    exact (congrArg val offl5).trans hoff
  have hb6 : val ((l5.map lensPo.get).map Cell.b) = tc N (L : ℤ) := by
    rw [List.map_map, tc_natCast hLN]
    exact (congrArg val lLl5).trans lL0
  have hsub6 := sub_tc_value (l5.map lensPo.get) N (by rw [List.length_map, len5]) _ _ ha6 hb6
  obtain ⟨-, hbb6⟩ := fscan_sub_ab false (l5.map lensPo.get)
  have len6 : l6.length = N := by
    have := congrArg List.length v6
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, len5]
  have g6 : l6.map lensRO.get = l5.map lensRO.get := f6 lensRO (fun _ _ => rfl)
  -- stage 7: store the offset
  have r7 := map_first movoF hbit l6
  have len7 : (l6.map movoF).length = N := by rw [List.length_map, len6]
  -- stage 8: decrement the counter
  obtain ⟨l8, r8, v8, f8⟩ := st_dec (l6.map movoF)
  have cntl6 : l6.map HCell.cnt = l.map HCell.cnt := by
    have h6 : l6.map HCell.cnt = l5.map HCell.cnt := map_proj g6 (fun k => k.2.2.2.1)
    have h5 : l5.map HCell.cnt = l4.map HCell.cnt := map_proj g5 (fun k => k.2.2.2.2.2.1)
    have h4 : l4.map HCell.cnt = (l2.map ldmF).map HCell.cnt := map_proj g4 (fun k => k.2.2.2.2.1)
    have h2 : l2.map HCell.cnt = (l.map setcF).map HCell.cnt := map_proj g2 (fun k => k.2.2.2.2.1)
    exact h6.trans (h5.trans (h4.trans (by
      rw [List.map_map]; exact h2.trans (by rw [List.map_map]; rfl))))
  have hc7 : vSc ((l6.map movoF).map lensPc.get) = j := by
    unfold vSc; rw [List.map_map, List.map_map]
    exact (congrArg val cntl6).trans hcnt
  have len8 : l8.length = N := by
    have := congrArg List.length v8
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, len7]
  have g8 : l8.map lensRC.get = (l6.map movoF).map lensRC.get := f8 lensRC (fun _ _ => rfl)
  -- the composite
  have hc := ProgOn.seq_reachFirst H6 DECC (Sum.inr AddI.done) (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst H5 (MAPP movoF) (Sum.inr AddI.done) (show AddI.go ≠ AddI.done by decide)
      (ProgOn.seq_reachFirst H4 SUBO (Sum.inr AddI.done) (show AddI.go ≠ AddI.done by decide)
        (ProgOn.seq_reachFirst H3 SUBS (Sum.inr MulI.done) (show AddI.go ≠ AddI.done by decide)
          (ProgOn.seq_reachFirst H2 MULP (Sum.inr AddI.done) (show MulI.prep ≠ MulI.done by decide)
            (ProgOn.seq_reachFirst H1 (MAPP ldmF) (Sum.inr (Sum.inr AddI.done))
              (show AddI.go ≠ AddI.done by decide)
              (ProgOn.seq_reachFirst (MAPP setcF) ACCP AddI.done Sum.inl_ne_inr r1 r2) r3)
            r4) r5) r6) r7) r8
  rw [len0, len2', len4', len5, len6, List.length_map, len6] at hc
  refine ⟨l8, ?_, ⟨len8, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · convert hc using 1
    ring
  · -- the mask
    have h8 : l8.map (fun x => x.ac.mask) = (l6.map movoF).map (fun x => x.ac.mask) :=
      map_proj g8 (fun k => k.1.mask)
    have h6 : l6.map (fun x => x.ac.mask) = l5.map (fun x => x.ac.mask) := map_proj g6 (fun k => k.1.mask)
    have h5 : l5.map (fun x => x.ac.mask) = l4.map (fun x => x.ac.mask) := map_proj g5 (fun k => k.1.mask)
    have h4 : l4.map (fun x => x.ac.mask) = (l2.map ldmF).map (fun x => x.ac.mask) :=
      map_proj g4 (fun k => k.1.mask)
    refine h8.trans ?_
    rw [List.map_map]
    refine (h6.trans (h5.trans (h4.trans ?_)))
    rw [List.map_map]
    refine k2.trans ?_
    rw [List.map_map]
    exact mask0
  · -- the coefficients
    have h8 : l8.map (fun x => x.ac.v) = (l6.map movoF).map (fun x => x.ac.v) :=
      map_proj g8 (fun k => k.1.v)
    have h6 : l6.map (fun x => x.ac.v) = l5.map (fun x => x.ac.v) := map_proj g6 (fun k => k.1.v)
    have h5 : l5.map (fun x => x.ac.v) = l4.map (fun x => x.ac.v) := map_proj g5 (fun k => k.1.v)
    have h4 : l4.map (fun x => x.ac.v) = (l2.map ldmF).map (fun x => x.ac.v) :=
      map_proj g4 (fun k => k.1.v)
    have e1 : (l6.map movoF).map (fun x => x.ac.v) = l6.map (fun x => x.ac.v) := by
      rw [List.map_map]; rfl
    have e2 : (l2.map ldmF).map (fun x => x.ac.v) = l2.map (fun x => x.ac.v) := by
      rw [List.map_map]; rfl
    have e3 : (l.map setcF).map (fun x => x.ac.v) = l.map (fun x => x.ac.v) := by
      rw [List.map_map]; rfl
    have chain : l8.map (fun x => x.ac.v) = l.map (fun x => x.ac.v) :=
      h8.trans (e1.trans (h6.trans (h5.trans (h4.trans (e2.trans (v2.trans e3))))))
    unfold pv
    exact (congrArg val chain).trans v0
  · -- the constant L
    have h8 : l8.map HCell.lL = (l6.map movoF).map HCell.lL := map_proj g8 (fun k => k.2.2.2.1)
    have e6 : l6.map HCell.lL = l5.map HCell.lL := by
      have := congrArg (List.map Cell.b) v6
      rw [List.map_map, hbb6, List.map_map] at this
      exact this
    unfold pv
    rw [h8, List.map_map]
    exact (congrArg val (e6.trans lLl5)).trans lL0
  · -- the excess
    have h8 : l8.map HCell.sT = (l6.map movoF).map HCell.sT := map_proj g8 (fun k => k.2.2.2.2.1)
    have h6 : l6.map HCell.sT = l5.map HCell.sT := map_proj g6 (fun k => k.2.2.1)
    have e5 : l5.map HCell.sT = l4.map HCell.sT := by
      have := congrArg (List.map Cell.b) v5
      rw [List.map_map, hbb5, List.map_map] at this
      exact this
    unfold pv
    rw [h8, List.map_map]
    exact (congrArg val (h6.trans (e5.trans sTl4))).trans sT0
  · -- the point
    have h8 : l8.map HCell.px = (l6.map movoF).map HCell.px := map_proj g8 (fun k => k.2.2.2.2.2.1)
    have h6 : l6.map HCell.px = l5.map HCell.px := map_proj g6 (fun k => k.2.2.2.2.1)
    have h5 : l5.map HCell.px = l4.map HCell.px := map_proj g5 (fun k => k.2.2.2.2.2.2.1)
    have h4 : l4.map HCell.px = (l2.map ldmF).map HCell.px := map_proj g4 (fun k => k.2.2.2.2.2.1)
    unfold pv
    rw [h8, List.map_map]
    refine (congrArg val (h6.trans (h5.trans (h4.trans ?_)))).trans px0
    rw [List.map_map]
    exact pxl2
  · -- the counter
    have hdec := fscan_dec true ((l6.map movoF).map lensPc.get)
    have hlt := val_lt ((fscan fdec true ((l6.map movoF).map lensPc.get)).1.map SCell.c)
    rw [List.length_map, fscan_length, List.length_map, len7] at hlt
    rw [hc7, List.length_map, len7, Bool.toNat_true] at hdec
    have hjN : j < 2 ^ N := by
      have := val_lt (l.map HCell.cnt)
      rw [List.length_map, len0] at this
      unfold pv at hcnt
      rw [← hcnt]; exact this
    have e : pv HCell.cnt l8 = val ((fscan fdec true ((l6.map movoF).map lensPc.get)).1.map SCell.c) := by
      unfold pv
      rw [← v8, List.map_map]
      rfl
    rw [e]
    cases hb : (fscan fdec true ((l6.map movoF).map lensPc.get)).2
    · rw [hb, Bool.toNat_false, mul_zero, add_zero] at hdec
      omega
    · rw [hb, Bool.toNat_true, mul_one] at hdec
      omega
  · -- the result
    have h8 : l8.map HCell.res = (l6.map movoF).map HCell.res := map_proj g8 (fun k => k.2.2.2.2.2.2.1)
    have h6 : l6.map HCell.res = l5.map HCell.res := map_proj g6 (fun k => k.2.2.2.2.2.1)
    have e5 : pv HCell.res l5 = tc N (((V / 2 ^ ((j - 1) * L) % 2 ^ L : ℕ) : ℤ) + R * x - s) := by
      unfold pv
      have := congrArg (List.map Cell.r) v5
      rw [List.map_map] at this
      exact (congrArg val this).trans hsub5
    unfold pv
    rw [h8, List.map_map]
    refine (congrArg val h6).trans ?_
    unfold pv at e5
    rw [e5]
    congr 1
    ring
  · -- the offset
    intro hj1
    have h8 : l8.map HCell.off = (l6.map movoF).map HCell.off := map_proj g8 (fun k => k.2.2.1)
    have e6 : pv HCell.tmp l6 = tc N ((((j - 1) * L : ℕ) : ℤ) - L) := by
      unfold pv
      have := congrArg (List.map Cell.r) v6
      rw [List.map_map] at this
      exact (congrArg val this).trans hsub6
    have hj2 : ((((j - 1) * L : ℕ) : ℤ) - L) = (((j - 2) * L : ℕ) : ℤ) := by
      have : j - 1 = (j - 2) + 1 := by omega
      rw [this]
      push_cast
      ring
    have hlt2 : (j - 2) * L < 2 ^ N := lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hoffN
    unfold pv
    rw [h8, List.map_map]
    show val (l6.map HCell.tmp) = _
    unfold pv at e6
    rw [e6, hj2, tc_natCast hlt2]

/-! ### The loop -/

/-- Horner's scheme on the packed words, with excess `s`: from the counter value `j`, the word at
offset `(j − 1)L` is read first. -/
def hornerW (V L s : ℕ) (x : ℤ) : ℤ → ℕ → ℤ
  | R, 0 => R
  | R, j + 1 => hornerW V L s x (R * x + (((V / 2 ^ (j * L) % 2 ^ L : ℕ) : ℤ) - s)) j

/-- The number of trips of the Horner loop from the counter value `j`. -/
def hornerTrips (L t : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => 1 + (3 * (j * L) + t + 10) + hornerTrips L t j

theorem hornerTrips_le (L t : ℕ) : ∀ j, hornerTrips L t j ≤ 1 + j * (3 * j * L + t + 11)
  | 0 => by simp [hornerTrips]
  | j + 1 => by
    have ih := hornerTrips_le L t j
    rw [hornerTrips]
    have h1 : j * (3 * j * L + t + 11) ≤ j * (3 * (j + 1) * L + t + 11) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith

/-- **The Horner loop.** From a tape with counter `j`, offset `(j − 1)L` and result `tc(R)`, the
loop first-arrives at its stop exit with result `tc(hornerW R j)`, in exactly
`hornerTrips L (trips X) j · (2N + 2)` transitions. -/
theorem poly_loop {N L V s X : ℕ} (hN : 0 < N) (hLN : L < 2 ^ N) (hsN : s < 2 ^ N) {x : ℤ}
    (hX : X = tc N x) :
    ∀ (j : ℕ) (R : ℤ) (l : List HCell), HInv N L V s X l → pv HCell.cnt l = j →
      (0 < j → pv HCell.off l = (j - 1) * L) → (j - 1) * L < 2 ^ N →
      pv HCell.res l = tc N R →
      ∃ l', ReachFirst hornerLoop.toProg (Sum.inl TstI.no) (Sum.inl TstI.test, l) l'
          (hornerTrips L (trips X) j * (2 * N + 2)) ∧
        pv HCell.res l' = tc N (hornerW V L s x R j) := by
  intro j
  induction j with
  | zero =>
    intro R l hI hcnt _ _ hres
    have ht := testP_step l
    rw [hcnt, if_neg (by simp)] at ht
    refine ⟨l, ?_, hres⟩
    have h := ProgOn.loop_stop TSTP BODYP TstI.yes (Sum.inr AddI.done) (eF := TstI.no)
      (show TstI.no ≠ TstI.yes by decide) ht
    rw [testP_cost, hI.len] at h
    convert h using 1
    simp [hornerTrips]
  | succ j ih =>
    intro R l hI hcnt hoff hoffN hres
    have ht := testP_step l
    rw [hcnt, if_pos (by omega)] at ht
    have hoff' : pv HCell.off l = (j + 1 - 1) * L := hoff (by omega)
    obtain ⟨l1, r1, hI1, hcnt1, hres1, hoff1⟩ :=
      body_poly hI hN (by omega) hcnt hoff' hoffN hLN hsN hX hres
    have hoffN' : (j - 1) * L < 2 ^ N :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hoffN
    obtain ⟨l2, r2, hres2⟩ := ih _ l1 hI1 (by rw [hcnt1]; rfl)
      (fun hj => by rw [hoff1 (by omega)]; congr 1) hoffN' hres1
    refine ⟨l2, ?_, ?_⟩
    · have h := ProgOn.loop_iter TSTP BODYP TstI.yes (Sum.inr AddI.done) (eF := TstI.no)
        (show TstI.test ≠ TstI.no by decide) ht r1 r2
      rw [testP_cost, hI.len] at h
      convert h using 1
      simp only [hornerTrips, Nat.add_sub_cancel]
      ring
    · rw [hres2]
      simp only [hornerW, Nat.add_sub_cancel]

/-- Horner's scheme on the packed words is Horner's scheme on the coefficients. -/
theorem hornerW_eq (V L s : ℕ) (x : ℤ) (cs : List ℤ)
    (hc : ∀ k < cs.length, (((V / 2 ^ (k * L) % 2 ^ L : ℕ) : ℤ) - s) = cs.getD k 0) :
    ∀ j ≤ cs.length, ∀ R, hornerW V L s x R j = hornerFrom cs x R j := by
  intro j
  induction j with
  | zero => intro _ R; rfl
  | succ j ih =>
    intro hj R
    rw [hornerW, hornerFrom, hc j (by omega), ih (by omega)]

/-! ### The layout and the compiled machine -/

/-- Seven tracks zipped into Horner cells; every other track is zero. -/
def mkH : List Bool → List Bool → List Bool → List Bool → List Bool → List Bool → List Bool →
    List HCell
  | v :: vs, m :: ms, a :: as, b :: bs, p :: ps, c :: cs, o :: os =>
      ⟨⟨⟨false, false⟩, v, m⟩, ⟨false, false, false⟩, o, a, b, c, p, false, false, false⟩ ::
        mkH vs ms as bs ps cs os
  | _, _, _, _, _, _, _ => []

theorem mkH_spec : ∀ (vs ms as bs ps cs os : List Bool), ms.length = vs.length →
    as.length = vs.length → bs.length = vs.length → ps.length = vs.length →
    cs.length = vs.length → os.length = vs.length →
    (mkH vs ms as bs ps cs os).map (fun x => x.ac.v) = vs ∧
      (mkH vs ms as bs ps cs os).map (fun x => x.ac.mask) = ms ∧
      (mkH vs ms as bs ps cs os).map HCell.lL = as ∧
      (mkH vs ms as bs ps cs os).map HCell.sT = bs ∧
      (mkH vs ms as bs ps cs os).map HCell.px = ps ∧
      (mkH vs ms as bs ps cs os).map HCell.cnt = cs ∧
      (mkH vs ms as bs ps cs os).map HCell.off = os ∧
      (mkH vs ms as bs ps cs os).map HCell.res = vs.map (fun _ => false) ∧
      (mkH vs ms as bs ps cs os).length = vs.length
  | [], ms, as, bs, ps, cs, os, h1, h2, h3, h4, h5, h6 => by
    rw [List.length_nil, List.length_eq_zero_iff] at h1 h2 h3 h4 h5 h6
    subst h1 h2 h3 h4 h5 h6
    simp [mkH]
  | v :: vs, m :: ms, a :: as, b :: bs, p :: ps, c :: cs, o :: os, h1, h2, h3, h4, h5, h6 => by
    simp only [List.length_cons, add_left_inj] at h1 h2 h3 h4 h5 h6
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := mkH_spec vs ms as bs ps cs os h1 h2 h3 h4 h5 h6
    simp [mkH, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  | _ :: _, [], _, _, _, _, _, h1, _, _, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, _, _, _, h2, _, _, _, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, h3, _, _, _ => by simp at h3
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, h4, _, _ => by simp at h4
  | _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, h5, _ => by simp at h5
  | _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, h6 => by simp at h6

/-- The excess codes of the coefficients. -/
def excessCodes (L : ℕ) (cs : List ℤ) : List ℕ := cs.map (fun c => (c + 2 ^ (L - 1)).toNat)

/-- The polynomial layout on `N` cells: the packed excess codes, the mask `2^L − 1`, the
constants `L` and `2^{L−1}`, the point `x`, the counter `K` and the offset `(K − 1)L`. -/
def polyInput (N L : ℕ) (cs : List ℤ) (x : ℤ) : List HCell :=
  mkH (bitsOf N (pack L (excessCodes L cs))) (bitsOf N (2 ^ L - 1)) (bitsOf N L)
    (bitsOf N (2 ^ (L - 1))) (bitsOf N (tc N x)) (bitsOf N cs.length)
    (bitsOf N ((cs.length - 1) * L))

/-- **Polynomial evaluation on the compiled Turing machine.** Let `p(x) = Σ_{k<K} c_k x^k` with
coefficients in the `L`-bit range, `0 < L ≤ N`, `KL < 2^N`, and the packed excess codes below
`2^N`. If `p(x)` lies in the `N`-bit range, then from the layout `polyInput N L cs x` the compiled
single-tape TM runs exactly `hornerTrips L (trips (tc_N x)) K · (2N + 2)` transitions, and its
result track, read in `N`-bit two's complement, is `p(x)`. The number of trips is at most
`1 + K(3KL + N + 11)`, uniformly in the degree. -/
theorem poly_tm {N L : ℕ} (hL : 0 < L) (hLN : L ≤ N) {cs : List ℤ} {x : ℤ}
    (hcs : ∀ c ∈ cs, -(2 : ℤ) ^ (L - 1) ≤ c ∧ c < 2 ^ (L - 1))
    (hpack : pack L (excessCodes L cs) < 2 ^ N) (hKL : cs.length * L < 2 ^ N)
    (hv1 : -(2 : ℤ) ^ (N - 1) ≤ ∑ k ∈ Finset.range cs.length, cs.getD k 0 * x ^ k)
    (hv2 : ∑ k ∈ Finset.range cs.length, cs.getD k 0 * x ^ k < 2 ^ (N - 1))
    (T : ℤ → Sym HCell) (hT : hornerLoop.toProg.Repr T (polyInput N L cs x)) :
    ∃ l' T', hornerLoop.toProg.Repr T' l' ∧
      sval N (pv HCell.res l') = ∑ k ∈ Finset.range cs.length, cs.getD k 0 * x ^ k ∧
      hornerTrips L (trips (tc N x)) cs.length ≤
        1 + cs.length * (3 * cs.length * L + N + 11) ∧
      hornerLoop.toProg.toTM.run
          ⟨.fwd hornerLoop.start (hornerLoop.toProg.init hornerLoop.start), T, 0⟩
          (hornerTrips L (trips (tc N x)) cs.length * (2 * N + 2)) =
        ⟨.fwd (Sum.inl TstI.no) (hornerLoop.toProg.init (Sum.inl TstI.no)), T', 0⟩ := by
  have hN : 0 < N := by omega
  have hLN2 : L < 2 ^ N := lt_of_le_of_lt hLN Nat.lt_two_pow_self
  have hsN : 2 ^ (L - 1) < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hKN : cs.length < 2 ^ N := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hL) hKL
  have hoffN : (cs.length - 1) * L < 2 ^ N :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) hKL
  have hmaskN : 2 ^ L - 1 < 2 ^ (N + 1) := by
    have : 2 ^ L ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hLN
    have : 2 ^ N < 2 ^ (N + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := mkH_spec (bitsOf N (pack L (excessCodes L cs)))
    (bitsOf N (2 ^ L - 1)) (bitsOf N L) (bitsOf N (2 ^ (L - 1))) (bitsOf N (tc N x))
    (bitsOf N cs.length) (bitsOf N ((cs.length - 1) * L))
    (by simp [bitsOf_length]) (by simp [bitsOf_length]) (by simp [bitsOf_length])
    (by simp [bitsOf_length]) (by simp [bitsOf_length]) (by simp [bitsOf_length])
  rw [bitsOf_length] at e9
  have hI : HInv N L (pack L (excessCodes L cs)) (2 ^ (L - 1)) (tc N x) (polyInput N L cs x) := by
    refine ⟨e9, e2, ?_, ?_, ?_, ?_⟩
    · unfold pv polyInput; rw [e1, val_bitsOf, Nat.mod_eq_of_lt hpack]
    · unfold pv polyInput; rw [e3, val_bitsOf, Nat.mod_eq_of_lt hLN2]
    · unfold pv polyInput; rw [e4, val_bitsOf, Nat.mod_eq_of_lt hsN]
    · unfold pv polyInput; rw [e5, val_bitsOf, Nat.mod_eq_of_lt (tc_lt _ _)]
  have hcnt : pv HCell.cnt (polyInput N L cs x) = cs.length := by
    unfold pv polyInput; rw [e6, val_bitsOf, Nat.mod_eq_of_lt hKN]
  have hoff : pv HCell.off (polyInput N L cs x) = (cs.length - 1) * L := by
    unfold pv polyInput; rw [e7, val_bitsOf, Nat.mod_eq_of_lt hoffN]
  have hres : pv HCell.res (polyInput N L cs x) = tc N 0 := by
    unfold pv polyInput; rw [e8]
    show val ((bitsOf N (pack L (excessCodes L cs))).map (fun _ => false)) = tc N 0
    rw [val_false]
    rfl
  obtain ⟨l', hr, hres'⟩ := poly_loop hN hLN2 hsN rfl cs.length 0 _ hI hcnt (fun _ => hoff)
    hoffN hres
  obtain ⟨T', hT', hrun⟩ := hornerLoop.toProg.reach_run hr.reach T hT
  -- the words are the coefficients
  have hw : ∀ k < cs.length, ((((pack L (excessCodes L cs)) / 2 ^ (k * L) % 2 ^ L : ℕ) : ℤ) -
      ((2 ^ (L - 1) : ℕ) : ℤ)) = cs.getD k 0 := by
    intro k hk
    have hk' : k < (excessCodes L cs).length := by simp [excessCodes, hk]
    have hbound : ∀ w ∈ excessCodes L cs, w < 2 ^ L := by
      intro w hw
      simp only [excessCodes, List.mem_map] at hw
      obtain ⟨c, hc, rfl⟩ := hw
      obtain ⟨h1, h2⟩ := hcs c hc
      have e : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h3 : ((c + 2 ^ (L - 1)).toNat : ℤ) < ((2 ^ L : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by linarith)]; push_cast; linarith
      exact_mod_cast h3
    rw [pack_word L _ k hk' hbound]
    simp only [excessCodes, List.getElem_map]
    obtain ⟨h1, _⟩ := hcs cs[k] (List.getElem_mem hk)
    rw [Int.toNat_of_nonneg (by linarith), List.getD_eq_getElem _ _ hk]
    push_cast
    ring
  have hval := hornerW_eq (pack L (excessCodes L cs)) L (2 ^ (L - 1)) x cs hw cs.length le_rfl 0
  rw [hornerFrom_eq, zero_mul, zero_add] at hval
  rw [hval] at hres'
  refine ⟨l', T', hT', ?_, ?_, hrun⟩
  · rw [hres', sval_tc N hN _ hv1 hv2]
  · have ht := trips_le N (tc N x) (tc_lt _ _)
    have h := hornerTrips_le L (trips (tc N x)) cs.length
    have h2 : cs.length * (3 * cs.length * L + trips (tc N x) + 11) ≤
        cs.length * (3 * cs.length * L + N + 11) := Nat.mul_le_mul_left _ (by omega)
    omega

end PVNP.Discrete.SweepArith
