import PVNP.SweepLens

/-!
# Certified fixed-point multiplication, composed from verified programs

This module is the first instantiation of the composition framework (`SweepCompose`,
`SweepLens`) on the repository's verified primitives.

* **Multiplication in first-arrival form** (`mul_loop_first`, `mul_first`). The shift-and-add
  multiplier first-arrives at `done` after exactly `(trips Y + 1)(2n + 2)` transitions. The
  accumulator holds `(A₀ + X·Y) mod 2ⁿ` and the multiplier track is cleared.
* **First arrivals compose** (`ProgOn.reachFirst_lift_inr`, `ProgOn.seq_reachFirst`). If `B`'s
  start is not its exit, two composed first arrivals form a first arrival of the composite, with
  cost exactly `c₁ + c₂`. Composites can therefore be composed again.
* **A common alphabet** `FCell = MCell × DCell` with three lenses:
  - `lensM`: the multiplier's tracks;
  - `lensD`: the divider's tracks, whose dividend track is the multiplier's accumulator;
  - `lensS`: the divider's own tracks.

  The multiplier's lens is independent of `lensS` (`indep_MS`).
* **Multiply, then divide by `2^p`** (`fmulProg = seq mulOn divOn done`). `fmul_first`: under
  the stated track conditions, the composite first-arrives at the divider's `done` after exactly
  `(trips Y + 1)(2n + 2) + (K + 2)(2n + 2)` transitions. The quotient track holds
  `⌊(X·Y mod 2ⁿ) / 2^p⌋` and the remainder track `(X·Y mod 2ⁿ) mod 2^p`. No copying program is
  used: the divider reads the product where the multiplier left it.
* **Unsigned fixed point** (`fmulInput`, `fmul_layout`, `fmul_exact`, `fixmul_certified`,
  `fixmul_tm`). Take `p < L` and `X, Y, X·Y < 2^L` on the explicit `L`-cell layout. The
  compiled TM returns `q = ⌊XY/2^p⌋` with `q/2^p ≤ (X/2^p)(Y/2^p) < (q + 1)/2^p`. It takes
  exactly `(trips Y + 1)(2L + 2) + (L + 1 − p)(2L + 2) ≤ (2L + 2)²` transitions.
* **Signed fixed point in two's complement** (`tc`, `sval`, `sval_tc`, `tc_mul`, `tc_shift`,
  `sfixmul_certified`, `sfixmul_tm`). Encode integers `x` and `y` as `x mod 2^L` and
  `y mod 2^L`. The same machine returns an `(L − p)`-bit word whose two's-complement reading is
  `⌊xy/2^p⌋`, whenever that value lies in the `(L − p)`-bit range. The same rounding certificate
  holds, with the same exact cost.
-/

namespace PVNP.Discrete.Sweep

namespace ProgOn

variable {D : Type} [Fintype D] [DecidableEq D] (A B : ProgOn D) (e : A.I)

/-- First arrivals of `B` lift into the composite. -/
theorem reachFirst_lift_inr {eB : B.I} {s : B.toProg.I × List B.toProg.D} {l : List D}
    {c : ℕ} (h : ReachFirst B.toProg eB s l c) :
    ReachFirst (seq A B e).toProg (.inr eB) (.inr s.1, s.2) l c := by
  induction h with
  | @last s l hs =>
    have h1 := ReachFirst.last (P := (seq A B e).toProg) (e := .inr eB) (stepP_inr A B e hs)
    rwa [tripCost_inr] at h1
  | @step s i l₁ l c hs hne _ ih =>
    have h1 := ReachFirst.step (P := (seq A B e).toProg) (e := .inr eB) (stepP_inr A B e hs)
      (fun h => hne (Sum.inr.inj h)) ih
    rwa [tripCost_inr] at h1

/-- **Composition of first arrivals.** Suppose `A` first-arrives at `e` with output `l₁` and
cost `c₁`. Suppose `B` first-arrives at `e_B` from its start on `l₁` with cost `c₂`, and
`B.start ≠ e_B`. Then the composite first-arrives at `inr e_B`, with cost exactly `c₁ + c₂`. -/
theorem seq_reachFirst {eB : B.I} (hst : B.start ≠ eB) {s : A.toProg.I × List A.toProg.D}
    {l₁ l₂ : List D} {c₁ c₂ : ℕ} (hA : ReachFirst A.toProg e s l₁ c₁)
    (hB : ReachFirst B.toProg eB (B.start, l₁) l₂ c₂) :
    ReachFirst (seq A B e).toProg (.inr eB) (.inl s.1, s.2) l₂ (c₁ + c₂) := by
  revert hB
  induction hA with
  | @last s l hs =>
    intro hB
    have h1 := ReachFirst.step (P := (seq A B e).toProg) (e := .inr eB)
      (stepP_inl_exit A B e hs) (fun h => hst (Sum.inr.inj h)) (reachFirst_lift_inr A B e hB)
    rwa [tripCost_inl] at h1
  | @step s i l₁ l c hs hne _ ih =>
    intro hB
    have h1 := ReachFirst.step (P := (seq A B e).toProg) (e := .inr eB)
      (stepP_inl_ne A B e hs hne) Sum.inl_ne_inr (ih hB)
    rw [tripCost_inl, ← Nat.add_assoc] at h1
    exact h1

end ProgOn

end PVNP.Discrete.Sweep

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-! ### Multiplication in first-arrival form -/

theorem instrOf_ne_done {y : ℕ} (hy : y ≠ 0) : instrOf y ≠ MulI.done := by
  unfold instrOf
  rw [if_neg hy]
  split_ifs <;> decide

/-- One add/skip trip preserves `acc + x·y mod 2ⁿ`. -/
theorem mul_step_inv (l l₁ : List MCell) (hy1 : vY l₁ = vY l / 2)
    (hx1 : vX l₁ = 2 * vX l % 2 ^ l.length)
    (ha1 : vA l₁ = (vA l + if vY l % 2 = 1 then vX l else 0) % 2 ^ l.length) :
    (vA l₁ + vX l₁ * vY l₁) % 2 ^ l.length = (vA l + vX l * vY l) % 2 ^ l.length := by
  rw [hy1, hx1, ha1, mod_add_mul]
  congr 1
  have hq := Nat.div_add_mod (vY l) 2
  split_ifs with ho
  · rw [ho] at hq
    calc vA l + vX l + 2 * vX l * (vY l / 2) = vA l + vX l * (2 * (vY l / 2) + 1) := by ring
      _ = vA l + vX l * vY l := by rw [hq]
  · have h0' : vY l % 2 = 0 := by omega
    rw [h0', add_zero] at hq
    calc vA l + 0 + 2 * vX l * (vY l / 2) = vA l + vX l * (2 * (vY l / 2)) := by ring
      _ = vA l + vX l * vY l := by rw [hq]

/-- **The multiplication loop, with first arrival at `done`.** -/
theorem mul_loop_first (n : ℕ) : ∀ (y : ℕ), y ≠ 0 → ∀ (l : List MCell), l.length = n →
    vY l = y →
    ∃ l', ReachFirst mulProg MulI.done (instrOf y, l) l' (trips y * (2 * n + 2)) ∧
      l'.length = n ∧ vY l' = 0 ∧ vA l' % 2 ^ n = (vA l + vX l * vY l) % 2 ^ n := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy0 l hl hy
    subst hy
    have hne : l ≠ [] := by
      intro h
      apply hy0
      rw [h]
      rfl
    obtain ⟨l₁, hs, hlen, hy1, hx1, ha1⟩ := step_trip l hne hy0
    have hinv1 := mul_step_inv l l₁ hy1 hx1 ha1
    rw [hl] at hinv1
    by_cases h1 : vY l₁ = 0
    · have hs' : mulProg.stepP (instrOf (vY l), l) = .inl (MulI.done, l₁) := by
        rw [hs, h1]
        rfl
      have h := ReachFirst.last (P := mulProg) (e := MulI.done) hs'
      rw [tripCost_mul, hl] at h
      have ht : trips (vY l) = 1 := by
        rw [trips_pos hy0, ← hy1, h1, trips_zero]
      refine ⟨l₁, ?_, by rw [hlen, hl], h1, ?_⟩
      · rw [ht, one_mul]
        exact h
      · rw [← hinv1, h1, mul_zero, add_zero]
    · have hlt : vY l₁ < vY l := by rw [hy1]; omega
      obtain ⟨l', hr, hl', hy', hinv⟩ := ih (vY l₁) hlt h1 l₁ (by rw [hlen, hl]) rfl
      refine ⟨l', ?_, hl', hy', by rw [hinv, hinv1]⟩
      have h := ReachFirst.step (P := mulProg) (e := MulI.done) hs (instrOf_ne_done h1) hr
      rw [tripCost_mul, hl] at h
      rw [trips_pos hy0, ← hy1]
      convert h using 1
      ring

/-- **Multiplication from `prep`, with first arrival at `done`.** -/
theorem mul_first (l : List MCell) (hl : l ≠ []) :
    ∃ l', ReachFirst mulProg MulI.done (MulI.prep, l) l'
        ((trips (vY l) + 1) * (2 * l.length + 2)) ∧
      l'.length = l.length ∧ vY l' = 0 ∧
      vA l' % 2 ^ l.length = (vA l + vX l * vY l) % 2 ^ l.length := by
  have hfr : (fscan fP (mulProg.init MulI.prep) l).2.fr = true :=
    fscan_fr fP (fun _ _ => rfl) _ l hl
  have hF : (fscan fP (mulProg.init MulI.prep) l).1 = l := fscan_fP _ l
  obtain ⟨p1, _, p3, p4⟩ := bscan_bP _ hfr l hl
  have hs : mulProg.stepP (MulI.prep, l) = .inl (instrOf (vY l), l) := by
    have ht := trip_eq MulI.prep fP bP rfl rfl l
    rw [hF] at ht
    simp only [Prog.stepP, ht, p1]
    rw [show mulProg.next MulI.prep = mnext from rfl, mnext_eq _ _ (vY l) p3 p4 _ ⟨rfl, rfl⟩]
  by_cases h0 : vY l = 0
  · have hs' : mulProg.stepP (MulI.prep, l) = .inl (MulI.done, l) := by
      rw [hs, h0]
      rfl
    have h := ReachFirst.last (P := mulProg) (e := MulI.done) hs'
    rw [tripCost_mul] at h
    refine ⟨l, ?_, rfl, h0, by rw [h0, mul_zero, add_zero]⟩
    rw [h0, trips_zero, zero_add, one_mul]
    exact h
  · obtain ⟨l', hr, hl', hy', hinv⟩ := mul_loop_first l.length (vY l) h0 l rfl rfl
    refine ⟨l', ?_, hl', hy', hinv⟩
    have h := ReachFirst.step (P := mulProg) (e := MulI.done) hs (instrOf_ne_done h0) hr
    rw [tripCost_mul] at h
    convert h using 1
    ring

/-! ### A common track alphabet for multiply-then-divide -/

/-- Cells of the common alphabet: the multiplier's three tracks and the divider's four. -/
abbrev FCell := MCell × DCell

/-- The multiplier's view: its three tracks. -/
def lensM : TrackLens FCell MCell where
  get := Prod.fst
  put x c := (c, x.2)
  get_put _ _ := rfl

/-- The divider's view. Its dividend track is the multiplier's accumulator. -/
def lensD : TrackLens FCell DCell where
  get x := ⟨x.1.acc, x.2.d, x.2.q, x.2.m⟩
  put x c := (⟨x.1.x, x.1.y, c.n⟩, ⟨x.2.n, c.d, c.q, c.m⟩)
  get_put _ _ := rfl

/-- The divider's own four tracks. -/
def lensS : TrackLens FCell DCell where
  get := Prod.snd
  put x c := (x.1, c)
  get_put _ _ := rfl

/-- The multiplier does not write the divider's own tracks. -/
theorem indep_MS : lensM.Indep lensS := fun _ _ => rfl

theorem lensD_n (l : List FCell) :
    (l.map lensD.get).map DCell.n = (l.map lensM.get).map MCell.acc := by
  rw [List.map_map, List.map_map]
  rfl

theorem lensD_d (l : List FCell) :
    (l.map lensD.get).map DCell.d = (l.map lensS.get).map DCell.d := by
  rw [List.map_map, List.map_map]
  rfl

theorem lensD_q (l : List FCell) :
    (l.map lensD.get).map DCell.q = (l.map lensS.get).map DCell.q := by
  rw [List.map_map, List.map_map]
  rfl

theorem lensD_m (l : List FCell) :
    (l.map lensD.get).map DCell.m = (l.map lensS.get).map DCell.m := by
  rw [List.map_map, List.map_map]
  rfl

/-- The fill cell. Neither component extends the tape. -/
def fz : FCell := (⟨false, false, false⟩, ⟨false, false, false, false⟩)

/-- Raw input bits enter the multiplicand track. -/
def fbit (b : Bool) : FCell := (⟨b, false, false⟩, ⟨false, false, false, false⟩)

/-- The multiplier on the common alphabet. -/
def mulOn : ProgOn FCell := (ProgOn.ofProg mulProg).viaLens lensM fz fbit

/-- The divider on the common alphabet. -/
def divOn : ProgOn FCell := (ProgOn.ofProg divProg).viaLens lensD fz fbit

/-- **Fixed-point multiplication**: multiply, then divide by the divisor `2^p` that is laid out
on the divider's tracks. -/
def fmulProg : ProgOn FCell := ProgOn.seq mulOn divOn MulI.done

/-- **Multiply, then divide by `2^p`, in first-arrival form.** Suppose:
- the accumulator is zero;
- the divider's tracks hold the divisor `2^p·2^K`, the marker `2^K` and a zero quotient;
- `2ⁿ ≤ 2·2^p·2^K`.

Then the composite first-arrives at the divider's `done` with cost exactly
`(trips Y + 1)(2n + 2) + (K + 2)(2n + 2)`. The quotient track holds `⌊(XY mod 2ⁿ)/2^p⌋` and the
remainder track `(XY mod 2ⁿ) mod 2^p`. -/
theorem fmul_first (l : List FCell) (hl : l ≠ []) (p K : ℕ)
    (ha : vA (l.map lensM.get) = 0) (hd : vD (l.map lensS.get) = 2 ^ p * 2 ^ K)
    (hm : vM (l.map lensS.get) = 2 ^ K) (hq : vQ (l.map lensS.get) = 0)
    (hK : 2 ^ l.length ≤ 2 * (2 ^ p * 2 ^ K)) :
    ∃ l', ReachFirst fmulProg.toProg (Sum.inr DivI.done) (Sum.inl MulI.prep, l) l'
        ((trips (vY (l.map lensM.get)) + 1) * (2 * l.length + 2) +
          (K + 2) * (2 * l.length + 2)) ∧
      vQ (l'.map lensD.get) =
        vX (l.map lensM.get) * vY (l.map lensM.get) % 2 ^ l.length / 2 ^ p ∧
      vN (l'.map lensD.get) =
        vX (l.map lensM.get) * vY (l.map lensM.get) % 2 ^ l.length % 2 ^ p := by
  have hlenM : (l.map lensM.get).length = l.length := by simp
  have hneM : l.map lensM.get ≠ [] := fun h => hl (List.map_eq_nil_iff.mp h)
  obtain ⟨lM', hr1, hlen1, _, hinv⟩ := mul_first (l.map lensM.get) hneM
  rw [hlenM, ha, zero_add] at hinv
  have hprod : vA lM' = vX (l.map lensM.get) * vY (l.map lensM.get) % 2 ^ l.length := by
    have hlt : vA lM' < 2 ^ l.length := by
      have := val_lt (lM'.map MCell.acc)
      rwa [List.length_map, hlen1, hlenM] at this
    rw [← hinv, Nat.mod_eq_of_lt hlt]
  obtain ⟨l₁, hr1', hv1⟩ :=
    ProgOn.reachFirst_lens (ProgOn.ofProg mulProg) lensM fz fbit hr1 l rfl
  have hframe : l₁.map lensS.get = l.map lensS.get :=
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg mulProg) lensM fz fbit (fun _ _ => rfl)
      indep_MS hr1'
  have hlen₁ : l₁.length = l.length := by
    have := congrArg List.length hv1
    rwa [List.length_map, hlen1, hlenM] at this
  have hnD : vN (l₁.map lensD.get) =
      vX (l.map lensM.get) * vY (l.map lensM.get) % 2 ^ l.length := by
    unfold vN
    rw [lensD_n, hv1]
    exact hprod
  have hdD : vD (l₁.map lensD.get) = 2 ^ p * 2 ^ K := by
    unfold vD
    rw [lensD_d, hframe]
    exact hd
  have hmD : vM (l₁.map lensD.get) = 2 ^ K := by
    unfold vM
    rw [lensD_m, hframe]
    exact hm
  have hqD : vQ (l₁.map lensD.get) = 0 := by
    unfold vQ
    rw [lensD_q, hframe]
    exact hq
  have hlenD : (l₁.map lensD.get).length = l.length := by rw [List.length_map, hlen₁]
  have hneD : l₁.map lensD.get ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlenD
    exact hl (List.length_eq_zero_iff.mp hlenD.symm)
  have hltD : vN (l₁.map lensD.get) < 2 * (2 ^ p * 2 ^ K) := by
    rw [hnD]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hK
  obtain ⟨lD', hr2, hq2, hn2⟩ :=
    div_reach_first (l₁.map lensD.get) hneD K (2 ^ p) (by positivity) hdD hmD hqD hltD
  obtain ⟨l₂, hr2', hv2⟩ :=
    ProgOn.reachFirst_lens (ProgOn.ofProg divProg) lensD fz fbit hr2 l₁ rfl
  have hcomp := ProgOn.seq_reachFirst mulOn divOn MulI.done
    (show DivI.prep ≠ DivI.done by decide) hr1' hr2'
  rw [hlenD, hlenM] at hcomp
  refine ⟨l₂, hcomp, ?_, ?_⟩
  · rw [hv2, hq2, hnD]
  · rw [hv2, hn2, hnD]

/-! ### Explicit layout and unsigned fixed point -/

/-- Three tracks zipped into multiplier cells. -/
def mkMCells : List Bool → List Bool → List Bool → List MCell
  | a :: as, b :: bs, c :: cs => ⟨a, b, c⟩ :: mkMCells as bs cs
  | _, _, _ => []

theorem mkMCells_spec (as bs cs : List Bool) (hb : bs.length = as.length)
    (hc : cs.length = as.length) :
    (mkMCells as bs cs).map MCell.x = as ∧ (mkMCells as bs cs).map MCell.y = bs ∧
      (mkMCells as bs cs).map MCell.acc = cs ∧ (mkMCells as bs cs).length = as.length := by
  induction as generalizing bs cs with
  | nil =>
    rw [List.length_nil, List.length_eq_zero_iff] at hb hc
    subst hb hc
    exact ⟨rfl, rfl, rfl, rfl⟩
  | cons a as ih =>
    cases bs with
    | nil => simp at hb
    | cons b bs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        simp only [List.length_cons, add_left_inj] at hb hc
        obtain ⟨h1, h2, h3, h4⟩ := ih bs cs hb hc
        simp [mkMCells, h1, h2, h3, h4]

/-- Layout for fixed-point multiplication on `L` cells with `p < L` fractional bits.
- The multiplier's tracks hold the multiplicand `X`, the multiplier `Y` and a zero accumulator.
- The divider's tracks hold the divisor `2^p` shifted by `K = L − 1 − p` places (that is,
  `2^(L−1)`), a zero quotient and the marker `2^K`.
- The divider's own dividend track is not read and is zero.

The divisor and marker are fixed, data-independent words. -/
def fmulInput (L p X Y : ℕ) : List FCell :=
  (mkMCells (bitsOf L X) (bitsOf L Y) (bitsOf L 0)).zip
    (mkCells (bitsOf L 0) (bitsOf L (2 ^ (L - 1))) (bitsOf L 0) (bitsOf L (2 ^ (L - 1 - p))))

theorem fmulInput_views (L p X Y : ℕ) :
    vX ((fmulInput L p X Y).map lensM.get) = X % 2 ^ L ∧
    vY ((fmulInput L p X Y).map lensM.get) = Y % 2 ^ L ∧
    vA ((fmulInput L p X Y).map lensM.get) = 0 ∧
    vD ((fmulInput L p X Y).map lensS.get) = 2 ^ (L - 1) % 2 ^ L ∧
    vQ ((fmulInput L p X Y).map lensS.get) = 0 ∧
    vM ((fmulInput L p X Y).map lensS.get) = 2 ^ (L - 1 - p) % 2 ^ L ∧
    (fmulInput L p X Y).length = L := by
  obtain ⟨m1, m2, m3, m4⟩ := mkMCells_spec (bitsOf L X) (bitsOf L Y) (bitsOf L 0)
    (by simp [bitsOf_length]) (by simp [bitsOf_length])
  obtain ⟨d1, d2, d3, d4, d5⟩ := mkCells_spec (bitsOf L 0) (bitsOf L (2 ^ (L - 1)))
    (bitsOf L 0) (bitsOf L (2 ^ (L - 1 - p))) (by simp [bitsOf_length])
    (by simp [bitsOf_length]) (by simp [bitsOf_length])
  rw [bitsOf_length] at m4 d5
  have hM : (fmulInput L p X Y).map lensM.get =
      mkMCells (bitsOf L X) (bitsOf L Y) (bitsOf L 0) :=
    List.map_fst_zip (le_of_eq (by rw [m4, d5]))
  have hS : (fmulInput L p X Y).map lensS.get =
      mkCells (bitsOf L 0) (bitsOf L (2 ^ (L - 1))) (bitsOf L 0) (bitsOf L (2 ^ (L - 1 - p))) :=
    List.map_snd_zip (le_of_eq (by rw [m4, d5]))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold vX; rw [hM, m1, val_bitsOf]
  · unfold vY; rw [hM, m2, val_bitsOf]
  · unfold vA; rw [hM, m3, val_bitsOf, Nat.zero_mod]
  · unfold vD; rw [hS, d2, val_bitsOf]
  · unfold vQ; rw [hS, d3, val_bitsOf, Nat.zero_mod]
  · unfold vM; rw [hS, d4, val_bitsOf]
  · unfold fmulInput; rw [List.length_zip, m4, d5, min_self]

/-- **Multiply-then-shift on the explicit layout.** For `p < L` and `X, Y < 2^L`, the composite
first-arrives at the divider's `done` after exactly
`(trips Y + 1)(2L + 2) + (L − 1 − p + 2)(2L + 2)` transitions. The quotient track holds
`⌊(XY mod 2^L)/2^p⌋` and the remainder track `(XY mod 2^L) mod 2^p`. -/
theorem fmul_layout (L p X Y : ℕ) (hp : p < L) (hX : X < 2 ^ L) (hY : Y < 2 ^ L) :
    ∃ l', ReachFirst fmulProg.toProg (Sum.inr DivI.done)
        (Sum.inl MulI.prep, fmulInput L p X Y) l'
        ((trips Y + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2)) ∧
      vQ (l'.map lensD.get) = X * Y % 2 ^ L / 2 ^ p ∧
      vN (l'.map lensD.get) = X * Y % 2 ^ L % 2 ^ p := by
  obtain ⟨hx, hy, ha, hd, hq, hm, hlen⟩ := fmulInput_views L p X Y
  have hL1 : 2 ^ (L - 1) < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hLK : 2 ^ (L - 1 - p) < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [Nat.mod_eq_of_lt hX] at hx
  rw [Nat.mod_eq_of_lt hY] at hy
  rw [Nat.mod_eq_of_lt hL1] at hd
  rw [Nat.mod_eq_of_lt hLK] at hm
  have hpK : 2 ^ p * 2 ^ (L - 1 - p) = 2 ^ (L - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hne : fmulInput L p X Y ≠ [] := by
    intro h
    rw [h, List.length_nil] at hlen
    omega
  have hK : 2 ^ (fmulInput L p X Y).length ≤ 2 * (2 ^ p * 2 ^ (L - 1 - p)) := by
    rw [hlen, hpK, ← pow_succ']
    exact le_of_eq (by congr 1; omega)
  obtain ⟨l', hr, hq', hn'⟩ := fmul_first (fmulInput L p X Y) hne p (L - 1 - p) ha
    (by rw [hd, hpK]) hm hq hK
  rw [hx, hy, hlen] at hq' hn'
  rw [hy, hlen] at hr
  exact ⟨l', hr, hq', hn'⟩

/-- **Unsigned fixed-point multiplication, end to end.** With moreover `XY < 2^L`, the quotient
track holds `⌊XY/2^p⌋` and the remainder track `XY mod 2^p`. -/
theorem fmul_exact (L p X Y : ℕ) (hp : p < L) (hX : X < 2 ^ L) (hY : Y < 2 ^ L)
    (hXY : X * Y < 2 ^ L) :
    ∃ l', ReachFirst fmulProg.toProg (Sum.inr DivI.done)
        (Sum.inl MulI.prep, fmulInput L p X Y) l'
        ((trips Y + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2)) ∧
      vQ (l'.map lensD.get) = X * Y / 2 ^ p ∧ vN (l'.map lensD.get) = X * Y % 2 ^ p := by
  obtain ⟨l', hr, hq, hn⟩ := fmul_layout L p X Y hp hX hY
  rw [Nat.mod_eq_of_lt hXY] at hq hn
  exact ⟨l', hr, hq, hn⟩

/-- **Rounding certificate for unsigned fixed-point multiplication.** `q = ⌊XY / 2^p⌋` is the
dyadic rounding of `(X/2^p)(Y/2^p)` downwards: `q/2^p ≤ (X/2^p)(Y/2^p) < (q + 1)/2^p`. -/
theorem fixmul_certified (X Y p : ℕ) :
    ((X * Y / 2 ^ p : ℕ) : ℚ) / 2 ^ p ≤ ((X : ℚ) / 2 ^ p) * ((Y : ℚ) / 2 ^ p) ∧
      ((X : ℚ) / 2 ^ p) * ((Y : ℚ) / 2 ^ p) < (((X * Y / 2 ^ p : ℕ) : ℚ) + 1) / 2 ^ p := by
  have hP : (0 : ℚ) < 2 ^ p := by positivity
  have h1 : X * Y / 2 ^ p * 2 ^ p ≤ X * Y := Nat.div_mul_le_self _ _
  have h2 : X * Y < X * Y / 2 ^ p * 2 ^ p + 2 ^ p := Nat.lt_div_mul_add (by positivity)
  have h1' : ((X * Y / 2 ^ p : ℕ) : ℚ) * 2 ^ p ≤ (X : ℚ) * Y := by exact_mod_cast h1
  have h2' : (X : ℚ) * Y < (((X * Y / 2 ^ p : ℕ) : ℚ) + 1) * 2 ^ p := by
    have : ((X * Y : ℕ) : ℚ) < ((X * Y / 2 ^ p * 2 ^ p + 2 ^ p : ℕ) : ℚ) := by exact_mod_cast h2
    push_cast at this
    linarith
  have e : ((X : ℚ) / 2 ^ p) * ((Y : ℚ) / 2 ^ p) = ((X : ℚ) * Y / 2 ^ p) / 2 ^ p := by ring
  rw [e]
  exact ⟨div_le_div_of_nonneg_right ((le_div_iff₀ hP).mpr h1') hP.le,
    div_lt_div_of_pos_right ((div_lt_iff₀ hP).mpr h2') hP⟩

/-- The exact cost of the composite on the `L`-cell layout is at most `(2L + 2)²`. -/
theorem fmul_cost_le (L p Y : ℕ) (hp : p < L) (hY : Y < 2 ^ L) :
    (trips Y + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2) ≤ (2 * L + 2) ^ 2 := by
  have ht := trips_le L Y hY
  have e : (trips Y + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2) =
      (trips Y + 1 + (L - 1 - p + 2)) * (2 * L + 2) := by ring
  rw [e, sq]
  exact Nat.mul_le_mul_right _ (by omega)

/-- **Certified unsigned fixed-point multiplication on the compiled Turing machine.** From any
tape representing the layout, the single-tape TM of `fmulProg` reaches the divider's `done`
after exactly the stated number of transitions, at most `(2L + 2)²`. Its quotient track `q`
satisfies `q = ⌊XY/2^p⌋` and `q/2^p ≤ (X/2^p)(Y/2^p) < (q + 1)/2^p`. -/
theorem fixmul_tm (L p X Y : ℕ) (hp : p < L) (hX : X < 2 ^ L) (hY : Y < 2 ^ L)
    (hXY : X * Y < 2 ^ L) (T : ℤ → Sym FCell)
    (hT : fmulProg.toProg.Repr T (fmulInput L p X Y)) :
    ∃ l' T', fmulProg.toProg.Repr T' l' ∧ vQ (l'.map lensD.get) = X * Y / 2 ^ p ∧
      (vQ (l'.map lensD.get) : ℚ) / 2 ^ p ≤ ((X : ℚ) / 2 ^ p) * ((Y : ℚ) / 2 ^ p) ∧
      ((X : ℚ) / 2 ^ p) * ((Y : ℚ) / 2 ^ p) < ((vQ (l'.map lensD.get) : ℚ) + 1) / 2 ^ p ∧
      fmulProg.toProg.toTM.run
          ⟨.fwd (Sum.inl MulI.prep) (fmulProg.toProg.init (Sum.inl MulI.prep)), T, 0⟩
          ((trips Y + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2)) =
        ⟨.fwd (Sum.inr DivI.done) (fmulProg.toProg.init (Sum.inr DivI.done)), T', 0⟩ ∧
      (trips Y + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2) ≤ (2 * L + 2) ^ 2 := by
  obtain ⟨l', hr, hq, _⟩ := fmul_exact L p X Y hp hX hY hXY
  obtain ⟨T', hT', hrun⟩ := fmulProg.toProg.reach_run hr.reach T hT
  obtain ⟨c1, c2⟩ := fixmul_certified X Y p
  rw [← hq] at c1 c2
  exact ⟨l', T', hT', hq, c1, c2, hrun, fmul_cost_le L p Y hp hY⟩

/-! ### Signed fixed point in two's complement -/

/-- The `L`-bit two's-complement code of an integer: its residue modulo `2^L`. -/
def tc (L : ℕ) (x : ℤ) : ℕ := (x % 2 ^ L).toNat

/-- The two's-complement reading of an `n`-bit word. -/
def sval (n N : ℕ) : ℤ := if N < 2 ^ (n - 1) then (N : ℤ) else (N : ℤ) - 2 ^ n

theorem tc_cast (L : ℕ) (x : ℤ) : ((tc L x : ℕ) : ℤ) = x % 2 ^ L :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))

theorem tc_lt (L : ℕ) (x : ℤ) : tc L x < 2 ^ L := by
  have h : ((tc L x : ℕ) : ℤ) < ((2 ^ L : ℕ) : ℤ) := by
    rw [tc_cast]
    push_cast
    exact Int.emod_lt_of_pos _ (by positivity)
  exact_mod_cast h

/-- The code of a product is the product of the codes, modulo `2^L`. -/
theorem tc_mul (L : ℕ) (x y : ℤ) : tc L x * tc L y % 2 ^ L = tc L (x * y) := by
  have h : ((tc L x * tc L y % 2 ^ L : ℕ) : ℤ) = ((tc L (x * y) : ℕ) : ℤ) := by
    push_cast
    rw [tc_cast, tc_cast, tc_cast, ← Int.mul_emod]
  exact_mod_cast h

/-- A logical right shift of an `L`-bit code by `p ≤ L` places is the `(L − p)`-bit code of
the floor quotient. -/
theorem tc_shift (L p : ℕ) (hp : p ≤ L) (z : ℤ) : tc L z / 2 ^ p = tc (L - p) (z / 2 ^ p) := by
  have hNc := tc_cast L z
  have hNlt := tc_lt L z
  generalize tc L z = N at hNc hNlt ⊢
  have hq : N / 2 ^ p < 2 ^ (L - p) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hp]
    exact hNlt
  have hL : (2 : ℤ) ^ L = 2 ^ (L - p) * 2 ^ p := by rw [← pow_add, Nat.sub_add_cancel hp]
  obtain ⟨k, hk⟩ : ∃ k, k = z / 2 ^ L := ⟨_, rfl⟩
  have h := Int.emod_add_ediv z (2 ^ L)
  rw [← hk, ← hNc, hL] at h
  have hdiv : z / 2 ^ p = ((N / 2 ^ p : ℕ) : ℤ) + 2 ^ (L - p) * k := by
    have hz : z = (N : ℤ) + (2 ^ (L - p) * k) * 2 ^ p := by rw [← h]; ring
    rw [hz, Int.add_mul_ediv_right _ _ (by positivity : (2 : ℤ) ^ p ≠ 0)]
    push_cast
    rfl
  unfold tc
  rw [hdiv, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hq), Int.toNat_natCast]

/-- An integer in the `n`-bit range is read back from its code. -/
theorem sval_tc (n : ℕ) (hn : 0 < n) (x : ℤ) (h1 : -(2 : ℤ) ^ (n - 1) ≤ x)
    (h2 : x < 2 ^ (n - 1)) : sval n (tc n x) = x := by
  have hc := tc_cast n x
  have hpos : (0 : ℤ) < 2 ^ (n - 1) := by positivity
  have hn' : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  unfold sval
  rcases le_or_gt 0 x with hx | hx
  · have hmod : x % 2 ^ n = x := Int.emod_eq_of_lt hx (by rw [hn']; linarith)
    rw [hmod] at hc
    have hlt : tc n x < 2 ^ (n - 1) := by
      have : ((tc n x : ℕ) : ℤ) < ((2 ^ (n - 1) : ℕ) : ℤ) := by
        rw [hc]
        push_cast
        exact h2
      exact_mod_cast this
    rw [if_pos hlt, hc]
  · have hmod : x % 2 ^ n = x + 2 ^ n := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by linarith) (by linarith)]
    rw [hmod] at hc
    have hge : ¬ tc n x < 2 ^ (n - 1) := by
      intro h
      have : ((tc n x : ℕ) : ℤ) < ((2 ^ (n - 1) : ℕ) : ℤ) := by exact_mod_cast h
      rw [hc] at this
      push_cast at this
      linarith
    rw [if_neg hge, hc]
    ring

/-- The machine's quotient word, read in two's complement, is `⌊xy / 2^p⌋` whenever that value
lies in the `(L − p)`-bit range. -/
theorem sfix_word (L p : ℕ) (hp : p < L) (x y : ℤ)
    (h1 : -(2 : ℤ) ^ (L - p - 1) ≤ x * y / 2 ^ p) (h2 : x * y / 2 ^ p < 2 ^ (L - p - 1)) :
    sval (L - p) (tc L x * tc L y % 2 ^ L / 2 ^ p) = x * y / 2 ^ p := by
  rw [tc_mul, tc_shift L p hp.le, sval_tc (L - p) (by omega) _ h1 h2]

/-- **Rounding certificate for signed fixed-point multiplication.** `q = ⌊xy / 2^p⌋` satisfies
`q/2^p ≤ (x/2^p)(y/2^p) < (q + 1)/2^p`. -/
theorem sfixmul_certified (x y : ℤ) (p : ℕ) :
    ((x * y / 2 ^ p : ℤ) : ℚ) / 2 ^ p ≤ ((x : ℚ) / 2 ^ p) * ((y : ℚ) / 2 ^ p) ∧
      ((x : ℚ) / 2 ^ p) * ((y : ℚ) / 2 ^ p) < (((x * y / 2 ^ p : ℤ) : ℚ) + 1) / 2 ^ p := by
  have hP : (0 : ℚ) < 2 ^ p := by positivity
  have hPz : (0 : ℤ) < 2 ^ p := by positivity
  have h1 : x * y / 2 ^ p * 2 ^ p ≤ x * y := Int.ediv_mul_le _ hPz.ne'
  have h2 : x * y < (x * y / 2 ^ p + 1) * 2 ^ p := Int.lt_ediv_add_one_mul_self _ hPz
  have h1' : ((x * y / 2 ^ p : ℤ) : ℚ) * 2 ^ p ≤ (x : ℚ) * y := by exact_mod_cast h1
  have h2' : (x : ℚ) * y < (((x * y / 2 ^ p : ℤ) : ℚ) + 1) * 2 ^ p := by exact_mod_cast h2
  have e : ((x : ℚ) / 2 ^ p) * ((y : ℚ) / 2 ^ p) = ((x : ℚ) * y / 2 ^ p) / 2 ^ p := by ring
  rw [e]
  exact ⟨div_le_div_of_nonneg_right ((le_div_iff₀ hP).mpr h1') hP.le,
    div_lt_div_of_pos_right ((div_lt_iff₀ hP).mpr h2') hP⟩

/-- **Certified signed fixed-point multiplication on the compiled Turing machine (two's
complement).** Lay out the `L`-bit codes of integers `x` and `y`. Suppose `⌊xy/2^p⌋` lies in
the `(L − p)`-bit two's-complement range. Then the same machine `fmulProg` reaches the divider's
`done` after exactly the stated number of transitions, at most `(2L + 2)²`. The two's-complement
reading `s` of its quotient word satisfies `s = ⌊xy/2^p⌋` and
`s/2^p ≤ (x/2^p)(y/2^p) < (s + 1)/2^p`. -/
theorem sfixmul_tm (L p : ℕ) (hp : p < L) (x y : ℤ)
    (h1 : -(2 : ℤ) ^ (L - p - 1) ≤ x * y / 2 ^ p) (h2 : x * y / 2 ^ p < 2 ^ (L - p - 1))
    (T : ℤ → Sym FCell) (hT : fmulProg.toProg.Repr T (fmulInput L p (tc L x) (tc L y))) :
    ∃ l' T', fmulProg.toProg.Repr T' l' ∧
      sval (L - p) (vQ (l'.map lensD.get)) = x * y / 2 ^ p ∧
      (sval (L - p) (vQ (l'.map lensD.get)) : ℚ) / 2 ^ p ≤
        ((x : ℚ) / 2 ^ p) * ((y : ℚ) / 2 ^ p) ∧
      ((x : ℚ) / 2 ^ p) * ((y : ℚ) / 2 ^ p) <
        ((sval (L - p) (vQ (l'.map lensD.get)) : ℚ) + 1) / 2 ^ p ∧
      fmulProg.toProg.toTM.run
          ⟨.fwd (Sum.inl MulI.prep) (fmulProg.toProg.init (Sum.inl MulI.prep)), T, 0⟩
          ((trips (tc L y) + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2)) =
        ⟨.fwd (Sum.inr DivI.done) (fmulProg.toProg.init (Sum.inr DivI.done)), T', 0⟩ ∧
      (trips (tc L y) + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2) ≤
        (2 * L + 2) ^ 2 := by
  obtain ⟨l', hr, hq, _⟩ := fmul_layout L p (tc L x) (tc L y) hp (tc_lt L x) (tc_lt L y)
  obtain ⟨T', hT', hrun⟩ := fmulProg.toProg.reach_run hr.reach T hT
  have hw : sval (L - p) (vQ (l'.map lensD.get)) = x * y / 2 ^ p := by
    rw [hq]
    exact sfix_word L p hp x y h1 h2
  obtain ⟨c1, c2⟩ := sfixmul_certified x y p
  rw [← hw] at c1 c2
  exact ⟨l', T', hT', hw, c1, c2, hrun, fmul_cost_le L p (tc L y) hp (tc_lt L y)⟩

/-! ### Signed addition, subtraction and comparison in two's complement -/

/-- The code of a sum is the sum of the codes, modulo `2ⁿ`. -/
theorem tc_add (n : ℕ) (x y : ℤ) : (tc n x + tc n y) % 2 ^ n = tc n (x + y) := by
  have h : (((tc n x + tc n y) % 2 ^ n : ℕ) : ℤ) = ((tc n (x + y) : ℕ) : ℤ) := by
    push_cast
    rw [tc_cast, tc_cast, tc_cast, ← Int.add_emod]
  exact_mod_cast h

/-- The adder's result word, read modulo `2ⁿ` (its low `n` cells), is the code of `x + y`. -/
theorem add_tc_value (l : List Cell) (n : ℕ) (x y : ℤ) (ha : val (l.map Cell.a) = tc n x)
    (hb : val (l.map Cell.b) = tc n y) :
    val ((addOut l).map Cell.r) % 2 ^ n = tc n (x + y) := by
  rw [add_value, ha, hb, tc_add]

/-- The subtractor's result word is the code of `x − y`, whatever the final borrow. -/
theorem sub_tc_value (l : List Cell) (n : ℕ) (hl : l.length = n) (x y : ℤ)
    (ha : val (l.map Cell.a) = tc n x) (hb : val (l.map Cell.b) = tc n y) :
    val ((fscan fsub false l).1.map Cell.r) = tc n (x - y) := by
  have h := fscan_sub false l
  have hr := val_lt ((fscan fsub false l).1.map Cell.r)
  rw [List.length_map, fscan_length, hl] at hr
  rw [hl, ha, hb, Bool.toNat_false, add_zero] at h
  generalize val ((fscan fsub false l).1.map Cell.r) = r at h hr ⊢
  generalize ((fscan fsub false l).2.toNat) = w at h
  have key : (r : ℤ) = (x - y) % 2 ^ n := by
    have hc : (r : ℤ) + (tc n y : ℤ) = (tc n x : ℤ) + 2 ^ n * (w : ℤ) := by exact_mod_cast h
    rw [tc_cast, tc_cast] at hc
    have hr' : (r : ℤ) = (x % 2 ^ n - y % 2 ^ n) + 2 ^ n * (w : ℤ) := by linarith
    have hr0 : (r : ℤ) < 2 ^ n := by exact_mod_cast hr
    rw [Int.sub_emod, ← Int.add_mul_emod_self_left (x % 2 ^ n - y % 2 ^ n) (2 ^ n) (w : ℤ),
      ← hr', Int.emod_eq_of_lt (by positivity) hr0]
  have := key.trans (tc_cast n (x - y)).symm
  exact_mod_cast this

/-- **Signed addition on the compiled Turing machine.** The operand tracks hold the `n`-bit codes
of `x` and `y`, and `x + y` lies in the `n`-bit range. Then the adder's TM reaches `done` after
exactly `addCost l ≤ 2n + 3` transitions, and the low `n` bits of its result track read back
`x + y` in two's complement. -/
theorem sadd_tm (l : List Cell) (n : ℕ) (hl : l.length = n) (hn : 0 < n) (x y : ℤ)
    (ha : val (l.map Cell.a) = tc n x) (hb : val (l.map Cell.b) = tc n y)
    (h1 : -(2 : ℤ) ^ (n - 1) ≤ x + y) (h2 : x + y < 2 ^ (n - 1))
    (T : ℤ → Sym Cell) (hT : addProg.Repr T l) :
    ∃ T', addProg.Repr T' (addOut l) ∧
      sval n (val ((addOut l).map Cell.r) % 2 ^ n) = x + y ∧
      addProg.toTM.run ⟨.fwd AddI.go (addProg.init AddI.go), T, 0⟩ (addCost l) =
        ⟨.fwd AddI.done (addProg.init AddI.done), T', 0⟩ ∧ addCost l ≤ 2 * n + 3 := by
  obtain ⟨T', hT', hrun⟩ := add_tm l T hT
  refine ⟨T', hT', ?_, hrun, by rw [← hl]; exact addCost_le l⟩
  rw [add_tc_value l n x y ha hb, sval_tc n hn _ h1 h2]

/-- **Signed subtraction on the compiled Turing machine.** The operand tracks hold the `n`-bit
codes of `x` and `y`, and `x − y` lies in the `n`-bit range. Then the subtractor's TM reaches
`done` after exactly `2n + 2` transitions, and its result track reads back `x − y` in two's
complement. With `x = 0` this is negation. -/
theorem ssub_tm (l : List Cell) (n : ℕ) (hl : l.length = n) (hn : 0 < n) (x y : ℤ)
    (ha : val (l.map Cell.a) = tc n x) (hb : val (l.map Cell.b) = tc n y)
    (h1 : -(2 : ℤ) ^ (n - 1) ≤ x - y) (h2 : x - y < 2 ^ (n - 1))
    (T : ℤ → Sym Cell) (hT : subProg.Repr T l) :
    ∃ T', subProg.Repr T' (fscan fsub false l).1 ∧
      sval n (val ((fscan fsub false l).1.map Cell.r)) = x - y ∧
      subProg.toTM.run ⟨.fwd AddI.go (subProg.init AddI.go), T, 0⟩ (2 * n + 2) =
        ⟨.fwd AddI.done (subProg.init AddI.done), T', 0⟩ := by
  obtain ⟨T', hT', hrun⟩ := sub_tm l T hT
  refine ⟨T', hT', ?_, by rw [← hl]; exact hrun⟩
  rw [sub_tc_value l n hl x y ha hb, sval_tc n hn _ h1 h2]

/-- The two's-complement reading of an `n`-bit word is negative exactly when its top bit is
set. -/
theorem sval_neg_iff (n N : ℕ) (hN : N < 2 ^ n) : sval n N < 0 ↔ 2 ^ (n - 1) ≤ N := by
  unfold sval
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    rw [if_pos hlt] at h
    have : (0 : ℤ) ≤ N := by positivity
    linarith
  · intro h
    rw [if_neg (not_lt.mpr h)]
    have : (N : ℤ) < 2 ^ n := by exact_mod_cast hN
    linarith

/-- **Signed comparison on the compiled Turing machine.** Suppose `x − y` lies in the `n`-bit
range. Then `x < y` exactly when the subtractor's result word has its top bit set. -/
theorem slt_iff (l : List Cell) (n : ℕ) (hl : l.length = n) (hn : 0 < n) (x y : ℤ)
    (ha : val (l.map Cell.a) = tc n x) (hb : val (l.map Cell.b) = tc n y)
    (h1 : -(2 : ℤ) ^ (n - 1) ≤ x - y) (h2 : x - y < 2 ^ (n - 1)) :
    x < y ↔ 2 ^ (n - 1) ≤ val ((fscan fsub false l).1.map Cell.r) := by
  have hv := sub_tc_value l n hl x y ha hb
  have hlt : val ((fscan fsub false l).1.map Cell.r) < 2 ^ n := by
    rw [hv]
    exact tc_lt n (x - y)
  rw [← sval_neg_iff n _ hlt, hv, sval_tc n hn _ h1 h2]
  constructor <;> intro h <;> linarith

end PVNP.Discrete.SweepArith
