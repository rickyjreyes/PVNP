import PVNP.SweepArith

/-!
# Verified shift-and-add multiplication on the repository's Turing-machine model

A tape cell carries three little-endian tracks: the multiplicand `x`, the multiplier `y` and
the accumulator `acc`. The sweep program `mulProg` runs as follows.

* **prep**: one trip that leaves the tape unchanged. Its backward pass reports whether `y = 0`
  and the low bit of `y`.
* **add / skip**: the forward pass shifts `x` one cell left (`x ↦ 2x mod 2ⁿ`) and, in `add`,
  simultaneously adds the old `x` into `acc` with a ripple carry. The backward pass shifts `y` one
  cell right (`y ↦ ⌊y/2⌋`) and reports the zero test and low bit of the new `y`, which select the
  next instruction.
* **done**: rest.

The invariant is `acc + x·y ≡ A₀ + X·Y (mod 2ⁿ)`.

* `mul_reach`: from `prep`, the program reaches `done` after exactly
  `(trips Y + 1)(2n + 2)` TM transitions. Here `trips Y` is the bit length of `Y`, and the
  accumulator holds `(A₀ + X·Y) mod 2ⁿ`.
* `mul_exact`: with `A₀ = 0` and `X·Y < 2ⁿ`, the accumulator is exactly `X·Y`, using at most
  `(n + 1)(2n + 2)` transitions.
* `mul_tm`: the same on the compiled single-tape Turing machine, via `Prog.reach_run`.
-/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-- Multiplier cell: multiplicand `x`, multiplier `y`, accumulator `acc`. -/
structure MCell where
  x : Bool
  y : Bool
  acc : Bool
  deriving DecidableEq, Fintype

/-- The sweep buffer, shared by the forward and backward passes. -/
structure MBuf where
  c : Bool
  px : Bool
  fr : Bool
  py : Bool
  nz : Bool
  w : Bool
  deriving DecidableEq, Fintype

def vX (l : List MCell) : ℕ := val (l.map MCell.x)
def vY (l : List MCell) : ℕ := val (l.map MCell.y)
def vA (l : List MCell) : ℕ := val (l.map MCell.acc)

/-- Forward pass of `add`: shift `x` left and add the old `x` into `acc`. -/
def fA (b : MBuf) (z : MCell) : MCell × MBuf :=
  (⟨b.px, z.y, xor (xor z.acc z.x) b.c⟩,
   ⟨(z.acc && z.x) || (b.c && xor z.acc z.x), z.x, true, b.py, b.nz, b.w⟩)

/-- Forward pass of `skip`: shift `x` left. -/
def fS (b : MBuf) (z : MCell) : MCell × MBuf :=
  (⟨b.px, z.y, z.acc⟩, ⟨b.c, z.x, true, b.py, b.nz, b.w⟩)

/-- Forward pass of `prep`: identity. -/
def fP (b : MBuf) (z : MCell) : MCell × MBuf :=
  (z, ⟨b.c, b.px, true, b.py, b.nz, b.w⟩)

/-- Backward pass of `add`/`skip`: shift `y` right and record the zero test and low bit. -/
def bR (b : MBuf) (z : MCell) : MCell × MBuf :=
  (⟨z.x, !b.fr && b.py, z.acc⟩,
   ⟨b.c, b.px, false, z.y, (!b.fr && b.nz) || (!b.fr && b.py), !b.fr && b.py⟩)

/-- Backward pass of `prep`: record the zero test and low bit of `y`. -/
def bP (b : MBuf) (z : MCell) : MCell × MBuf :=
  (z, ⟨b.c, b.px, false, b.py, (!b.fr && b.nz) || z.y, z.y⟩)

/-! ### Forward passes -/

theorem fscan_shift_x (f : MBuf → MCell → MCell × MBuf)
    (hx : ∀ b z, (f b z).1.x = b.px) (hpx : ∀ b z, (f b z).2.px = z.x) :
    ∀ (b : MBuf) (l : List MCell),
      val ((fscan f b l).1.map MCell.x) + 2 ^ l.length * (fscan f b l).2.px.toNat =
        2 * vX l + b.px.toNat
  | b, [] => by simp [fscan, val, vX]
  | b, z :: l => by
    have ih := fscan_shift_x f hx hpx (f b z).2 l
    simp only [fscan, List.map_cons, val, List.length_cons, pow_succ, vX] at ih ⊢
    rw [hpx] at ih
    rw [hx]
    linarith [ih]

theorem fscan_keep_y (f : MBuf → MCell → MCell × MBuf) (hy : ∀ b z, (f b z).1.y = z.y) :
    ∀ (b : MBuf) (l : List MCell), (fscan f b l).1.map MCell.y = l.map MCell.y
  | _, [] => rfl
  | b, z :: l => by
    simp only [fscan, List.map_cons, hy, fscan_keep_y f hy (f b z).2 l]

theorem fscan_fr (f : MBuf → MCell → MCell × MBuf) (hfr : ∀ b z, (f b z).2.fr = true) :
    ∀ (b : MBuf) (l : List MCell), l ≠ [] → (fscan f b l).2.fr = true
  | _, [], h => absurd rfl h
  | b, [z], _ => by simp [fscan, hfr]
  | b, z :: z' :: l, _ => by
    simp only [fscan]
    exact fscan_fr f hfr (f b z).2 (z' :: l) (List.cons_ne_nil _ _)

theorem fscan_fA_acc : ∀ (b : MBuf) (l : List MCell),
    val ((fscan fA b l).1.map MCell.acc) + 2 ^ l.length * (fscan fA b l).2.c.toNat =
      vA l + vX l + b.c.toNat
  | b, [] => by simp [fscan, val, vA, vX]
  | b, z :: l => by
    have ih := fscan_fA_acc (fA b z).2 l
    have hs : (fA b z).1.acc.toNat + 2 * (fA b z).2.c.toNat =
        z.acc.toNat + z.x.toNat + b.c.toNat := by
      obtain ⟨x, y, a⟩ := z
      obtain ⟨c, px, fr, py, nz, w⟩ := b
      cases x <;> cases a <;> cases c <;> rfl
    simp only [fscan, List.map_cons, val, List.length_cons, pow_succ, vA, vX] at ih ⊢
    linarith [ih, hs]

theorem fscan_fS_acc : ∀ (b : MBuf) (l : List MCell),
    (fscan fS b l).1.map MCell.acc = l.map MCell.acc
  | _, [] => rfl
  | b, z :: l => by simp only [fscan, List.map_cons, fS, fscan_fS_acc _ l]

theorem fscan_fP : ∀ (b : MBuf) (l : List MCell), (fscan fP b l).1 = l
  | _, [] => rfl
  | b, z :: l => by simp only [fscan, fP, fscan_fP _ l]

/-! ### Backward passes -/

theorem decide_ne_zero (a : Bool) (V : ℕ) :
    decide (a.toNat + 2 * V ≠ 0) = (a || decide (V ≠ 0)) := by
  cases a <;> by_cases h : V = 0 <;> simp [h]

theorem decide_odd (a : Bool) (V : ℕ) : decide ((a.toNat + 2 * V) % 2 = 1) = a := by
  cases a <;> simp [Nat.add_mul_mod_self_left]

/-- The preparation backward pass. -/
theorem bscan_bP (b : MBuf) (hb : b.fr = true) : ∀ l : List MCell, l ≠ [] →
    (bscan bP b l).1 = l ∧ (bscan bP b l).2.fr = false ∧
      (bscan bP b l).2.nz = decide (vY l ≠ 0) ∧ (bscan bP b l).2.w = decide (vY l % 2 = 1)
  | [], h => absurd rfl h
  | [z], _ => by
    obtain ⟨x, y, a⟩ := z
    have hv : vY [⟨x, y, a⟩] = y.toNat := by simp [vY, val]
    rw [hv]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · show ((!b.fr && b.nz) || y) = _
      rw [hb]; cases y <;> rfl
    · show y = _
      cases y <;> rfl
  | z :: z' :: l, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := bscan_bP b hb (z' :: l) (List.cons_ne_nil _ _)
    have e : bscan bP b (z :: z' :: l) =
        ((bP (bscan bP b (z' :: l)).2 z).1 :: (bscan bP b (z' :: l)).1,
          (bP (bscan bP b (z' :: l)).2 z).2) := rfl
    have hv : vY (z :: z' :: l) = z.y.toNat + 2 * vY (z' :: l) := rfl
    rw [e, hv]
    refine ⟨?_, rfl, ?_, ?_⟩
    · show z :: (bscan bP b (z' :: l)).1 = z :: z' :: l
      rw [h1]
    · show ((!(bscan bP b (z' :: l)).2.fr && (bscan bP b (z' :: l)).2.nz) || z.y) = _
      rw [h2, h3, decide_ne_zero]
      cases z.y <;> simp
    · show z.y = _
      rw [decide_odd]

/-- The shifting backward pass: `y` moves one cell towards the low end, with a zero fill. -/
theorem bscan_bR (b : MBuf) (hb : b.fr = true) : ∀ l : List MCell, l ≠ [] →
    (bscan bR b l).1.map MCell.x = l.map MCell.x ∧
      (bscan bR b l).1.map MCell.acc = l.map MCell.acc ∧
      (bscan bR b l).1.map MCell.y = (l.map MCell.y).tail ++ [false] ∧
      (bscan bR b l).2.fr = false ∧
      (bscan bR b l).2.py = (l.headD ⟨false, false, false⟩).y ∧
      (bscan bR b l).2.nz = decide (val ((l.map MCell.y).tail ++ [false]) ≠ 0) ∧
      (bscan bR b l).2.w = decide (val ((l.map MCell.y).tail ++ [false]) % 2 = 1)
  | [], h => absurd rfl h
  | [z], _ => by
    refine ⟨rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
    · show [!b.fr && b.py] = _
      rw [hb]; rfl
    · show ((!b.fr && b.nz) || (!b.fr && b.py)) = _
      rw [hb]; simp [val]
    · show (!b.fr && b.py) = _
      rw [hb]; simp [val]
  | z :: z' :: l, _ => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := bscan_bR b hb (z' :: l) (List.cons_ne_nil _ _)
    have e : bscan bR b (z :: z' :: l) =
        ((bR (bscan bR b (z' :: l)).2 z).1 :: (bscan bR b (z' :: l)).1,
          (bR (bscan bR b (z' :: l)).2 z).2) := rfl
    have hpy : (bscan bR b (z' :: l)).2.py = z'.y := h5
    rw [e]
    refine ⟨?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
    · show z.x :: (bscan bR b (z' :: l)).1.map MCell.x = _
      rw [h1]; rfl
    · show z.acc :: (bscan bR b (z' :: l)).1.map MCell.acc = _
      rw [h2]; rfl
    · show (!(bscan bR b (z' :: l)).2.fr && (bscan bR b (z' :: l)).2.py) ::
          (bscan bR b (z' :: l)).1.map MCell.y = _
      rw [h3, h4, hpy]; simp
    · show ((!(bscan bR b (z' :: l)).2.fr && (bscan bR b (z' :: l)).2.nz) ||
          (!(bscan bR b (z' :: l)).2.fr && (bscan bR b (z' :: l)).2.py)) = _
      rw [h4, h6, hpy]
      have ev : val ((List.map MCell.y (z :: z' :: l)).tail ++ [false]) =
          z'.y.toNat + 2 * val ((List.map MCell.y (z' :: l)).tail ++ [false]) := by
        simp [val]
      rw [ev, decide_ne_zero]
      cases z'.y <;> simp
    · show (!(bscan bR b (z' :: l)).2.fr && (bscan bR b (z' :: l)).2.py) = _
      rw [h4, hpy]
      have ev : val ((List.map MCell.y (z :: z' :: l)).tail ++ [false]) =
          z'.y.toNat + 2 * val ((List.map MCell.y (z' :: l)).tail ++ [false]) := by
        simp [val]
      rw [ev, decide_odd]; simp

theorem val_tail_append_false (ys : List Bool) :
    val (ys.tail ++ [false]) = val ys / 2 := by
  cases ys with
  | nil => simp [val]
  | cons y ys =>
    simp only [List.tail_cons, val_append, val, Bool.toNat_false, mul_zero, add_zero]
    cases y <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-! ### The program -/

inductive MulI | prep | add | skip | done
  deriving DecidableEq, Fintype

def mnext (b : MBuf) : MulI ⊕ Bool :=
  if !b.nz then .inl .done else if b.w then .inl .add else .inl .skip

def mulProg : Prog where
  D := MCell
  I := MulI
  B := MBuf
  lift b := ⟨b, false, false⟩
  start := .prep
  init _ := ⟨false, false, false, false, false, false⟩
  fwd
    | .prep => fP
    | .add => fA
    | .skip => fS
    | .done => fun b z => (z, b)
  ext _ := fun _ => none
  bwd
    | .prep => bP
    | .add => bR
    | .skip => bR
    | .done => fun b z => (z, b)
  next
    | .done => fun _ => .inl .done
    | _ => mnext

/-- The instruction selected by the current multiplier value. -/
def instrOf (y : ℕ) : MulI := if y = 0 then .done else if y % 2 = 1 then .add else .skip

theorem mnext_eq (nz w : Bool) (y : ℕ) (hnz : nz = decide (y ≠ 0))
    (hw : w = decide (y % 2 = 1)) (b : MBuf) (hb : b.nz = nz ∧ b.w = w) :
    mnext b = .inl (instrOf y) := by
  obtain ⟨h1, h2⟩ := hb
  unfold mnext instrOf
  rw [h1, h2, hnz, hw]
  by_cases hy : y = 0
  · simp [hy]
  · by_cases ho : y % 2 = 1 <;> simp [hy, ho]

/-- Bit length: the number of add/skip trips needed from `y`. -/
def trips (y : ℕ) : ℕ := if y = 0 then 0 else 1 + trips (y / 2)
termination_by y
decreasing_by omega

theorem trips_zero : trips 0 = 0 := by rw [trips]; simp

theorem trips_pos {y : ℕ} (h : y ≠ 0) : trips y = 1 + trips (y / 2) := by
  rw [trips, if_neg h]

theorem trips_le : ∀ (n y : ℕ), y < 2 ^ n → trips y ≤ n := by
  intro n
  induction n with
  | zero => intro y hy; simp at hy; subst hy; rw [trips_zero]
  | succ n ih =>
    intro y hy
    by_cases h : y = 0
    · subst h; rw [trips_zero]; omega
    · rw [trips_pos h]
      have := ih (y / 2) (by rw [pow_succ] at hy; omega)
      omega

theorem trip_eq (i : MulI) (f g : MBuf → MCell → MCell × MBuf) (hf : mulProg.fwd i = f)
    (hg : mulProg.bwd i = g) (l : List MCell) :
    mulProg.trip i l = bscan g (fscan f (mulProg.init i) l).2 (fscan f (mulProg.init i) l).1 := by
  have hext : mulProg.ext i (fscan f (mulProg.init i) l).2 = none := rfl
  simp only [Prog.trip, Prog.mid, Prog.fpass, hf, hg, hext, Option.toList_none, List.append_nil]

/-- The common part of an add/skip trip. -/
theorem step_core (i : MulI) (f : MBuf → MCell → MCell × MBuf) (hf : mulProg.fwd i = f)
    (hb : mulProg.bwd i = bR) (hnext : mulProg.next i = mnext)
    (hx : ∀ b z, (f b z).1.x = b.px) (hpx : ∀ b z, (f b z).2.px = z.x)
    (hy : ∀ b z, (f b z).1.y = z.y) (hfr : ∀ b z, (f b z).2.fr = true)
    (hinit : (mulProg.init i).px = false) (l : List MCell) (hl : l ≠ []) :
    ∃ l₁, mulProg.stepP (i, l) = .inl (instrOf (vY l₁), l₁) ∧ l₁.length = l.length ∧
      vY l₁ = vY l / 2 ∧ vX l₁ = 2 * vX l % 2 ^ l.length ∧
      l₁.map MCell.acc = (fscan f (mulProg.init i) l).1.map MCell.acc := by
  have hFlen : (fscan f (mulProg.init i) l).1.length = l.length := fscan_length f _ l
  have hFne : (fscan f (mulProg.init i) l).1 ≠ [] := by
    intro h
    rw [h, List.length_nil] at hFlen
    exact hl (List.length_eq_zero_iff.mp hFlen.symm)
  have hfr' : (fscan f (mulProg.init i) l).2.fr = true := fscan_fr f hfr _ l hl
  obtain ⟨b1, b2, b3, _, _, b6, b7⟩ := bscan_bR _ hfr' _ hFne
  have hFy := fscan_keep_y f hy (mulProg.init i) l
  have hFx := fscan_shift_x f hx hpx (mulProg.init i) l
  set l₁ := (bscan bR (fscan f (mulProg.init i) l).2 (fscan f (mulProg.init i) l).1).1 with hl₁
  have hvy : vY l₁ = val ((((fscan f (mulProg.init i) l).1).map MCell.y).tail ++ [false]) := by
    unfold vY; rw [b3]
  refine ⟨l₁, ?_, ?_, ?_, ?_, b2⟩
  · have ht := trip_eq i f bR hf hb l
    simp only [Prog.stepP, ht, hnext]
    rw [mnext_eq _ _ (vY l₁) (by rw [hvy]; exact b6) (by rw [hvy]; exact b7) _ ⟨rfl, rfl⟩]
  · rw [hl₁, bscan_length, hFlen]
  · rw [hvy, hFy, val_tail_append_false]; rfl
  · unfold vX; rw [b1]
    have hlt := val_lt (((fscan f (mulProg.init i) l).1).map MCell.x)
    rw [List.length_map, hFlen] at hlt
    unfold vX at hFx
    rw [hinit, Bool.toNat_false, add_zero] at hFx
    rw [← hFx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- One add/skip trip. -/
theorem step_trip (l : List MCell) (hl : l ≠ []) (hy : vY l ≠ 0) :
    ∃ l₁, mulProg.stepP (instrOf (vY l), l) = .inl (instrOf (vY l₁), l₁) ∧
      l₁.length = l.length ∧ vY l₁ = vY l / 2 ∧
      vX l₁ = 2 * vX l % 2 ^ l.length ∧
      vA l₁ = (vA l + if vY l % 2 = 1 then vX l else 0) % 2 ^ l.length := by
  by_cases ho : vY l % 2 = 1
  · have hi : instrOf (vY l) = MulI.add := by unfold instrOf; simp [hy, ho]
    obtain ⟨l₁, hs, hlen, hy1, hx1, ha1⟩ := step_core MulI.add fA rfl rfl rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl l hl
    refine ⟨l₁, by rw [hi]; exact hs, hlen, hy1, hx1, ?_⟩
    have hFa := fscan_fA_acc (mulProg.init MulI.add) l
    have hlt := val_lt (((fscan fA (mulProg.init MulI.add) l).1).map MCell.acc)
    rw [List.length_map, fscan_length] at hlt
    rw [show (mulProg.init MulI.add).c = false from rfl, Bool.toNat_false, add_zero] at hFa
    unfold vA at hFa ⊢
    rw [ha1, if_pos ho, ← hFa, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · have hi : instrOf (vY l) = MulI.skip := by unfold instrOf; simp [hy, ho]
    obtain ⟨l₁, hs, hlen, hy1, hx1, ha1⟩ := step_core MulI.skip fS rfl rfl rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl l hl
    refine ⟨l₁, by rw [hi]; exact hs, hlen, hy1, hx1, ?_⟩
    have hlt := val_lt (l.map MCell.acc)
    rw [List.length_map] at hlt
    unfold vA; rw [ha1, fscan_fS_acc, if_neg ho, add_zero, Nat.mod_eq_of_lt hlt]

theorem tripCost_mul (i : MulI) (l : List MCell) : mulProg.tripCost i l = 2 * l.length + 2 := by
  cases i <;> rfl

theorem mod_add_mul (a b q M : ℕ) : (a % M + b % M * q) % M = (a + b * q) % M :=
  (Nat.mod_modEq a M).add ((Nat.mod_modEq b M).mul_right q)

/-- **The multiplication loop.** -/
theorem mul_loop (n : ℕ) : ∀ (y : ℕ) (l : List MCell), l.length = n → vY l = y →
    ∃ l', mulProg.Reach (instrOf y, l) (.done, l') (trips y * (2 * n + 2)) ∧
      l'.length = n ∧ vA l' % 2 ^ n = (vA l + vX l * vY l) % 2 ^ n := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro l hl hy
    subst hy
    by_cases h0 : vY l = 0
    · refine ⟨l, ?_, hl, by rw [h0, mul_zero, add_zero]⟩
      rw [h0, trips_zero, zero_mul, show instrOf 0 = MulI.done from rfl]
      exact Prog.Reach.refl _
    · have hne : l ≠ [] := by
        intro h
        apply h0
        rw [h]; rfl
      obtain ⟨l₁, hs, hlen, hy1, hx1, ha1⟩ := step_trip l hne h0
      have hlt : vY l₁ < vY l := by rw [hy1]; omega
      obtain ⟨l', hr, hl', hinv⟩ := ih (vY l₁) hlt l₁ (by rw [hlen, hl]) rfl
      refine ⟨l', ?_, hl', ?_⟩
      · have h := Prog.Reach.step (P := mulProg) hs hr
        rw [tripCost_mul, hl, hy1] at h
        rw [trips_pos h0]
        convert h using 1
        ring
      · rw [hinv, hy1, hx1, ha1, hl, mod_add_mul]
        congr 1
        have hq := Nat.div_add_mod (vY l) 2
        split_ifs with ho
        · rw [ho] at hq
          calc vA l + vX l + 2 * vX l * (vY l / 2) = vA l + vX l * (2 * (vY l / 2) + 1) := by
                ring
            _ = vA l + vX l * vY l := by rw [hq]
        · have h0' : vY l % 2 = 0 := by omega
          rw [h0', add_zero] at hq
          calc vA l + 0 + 2 * vX l * (vY l / 2) = vA l + vX l * (2 * (vY l / 2)) := by ring
            _ = vA l + vX l * vY l := by rw [hq]

/-- **Multiplication.** From `prep`, the program reaches `done` after exactly
`(trips Y + 1)(2n + 2)` transitions, with the accumulator holding `(A₀ + X·Y) mod 2ⁿ`. -/
theorem mul_reach (l : List MCell) (hl : l ≠ []) :
    ∃ l', mulProg.Reach (MulI.prep, l) (.done, l')
        ((trips (vY l) + 1) * (2 * l.length + 2)) ∧
      l'.length = l.length ∧ vA l' % 2 ^ l.length = (vA l + vX l * vY l) % 2 ^ l.length := by
  have hfr : (fscan fP (mulProg.init MulI.prep) l).2.fr = true :=
    fscan_fr fP (fun _ _ => rfl) _ l hl
  have hF : (fscan fP (mulProg.init MulI.prep) l).1 = l := fscan_fP _ l
  obtain ⟨p1, _, p3, p4⟩ := bscan_bP _ hfr l hl
  have hs : mulProg.stepP (MulI.prep, l) = .inl (instrOf (vY l), l) := by
    have ht := trip_eq MulI.prep fP bP rfl rfl l
    rw [hF] at ht
    simp only [Prog.stepP, ht, p1]
    rw [show mulProg.next MulI.prep = mnext from rfl, mnext_eq _ _ (vY l) p3 p4 _ ⟨rfl, rfl⟩]
  obtain ⟨l', hr, hl', hinv⟩ := mul_loop l.length (vY l) l rfl rfl
  refine ⟨l', ?_, hl', hinv⟩
  have h := Prog.Reach.step (P := mulProg) hs hr
  rw [tripCost_mul] at h
  convert h using 1
  ring

/-- **Exact product.** With a zero accumulator and `X·Y < 2ⁿ`, the accumulator holds `X·Y`, in at
most `(n + 1)(2n + 2)` transitions. -/
theorem mul_exact (l : List MCell) (hl : l ≠ []) (ha : vA l = 0)
    (hxy : vX l * vY l < 2 ^ l.length) :
    ∃ l', mulProg.Reach (MulI.prep, l) (.done, l')
        ((trips (vY l) + 1) * (2 * l.length + 2)) ∧
      vA l' = vX l * vY l ∧ (trips (vY l) + 1) * (2 * l.length + 2) ≤
        (l.length + 1) * (2 * l.length + 2) := by
  obtain ⟨l', hr, hl', hinv⟩ := mul_reach l hl
  refine ⟨l', hr, ?_, ?_⟩
  · have hlt := val_lt (l'.map MCell.acc)
    rw [List.length_map, hl'] at hlt
    unfold vA at hinv ⊢
    rw [show val (l.map MCell.acc) = 0 from ha, zero_add, Nat.mod_eq_of_lt hxy,
      Nat.mod_eq_of_lt hlt] at hinv
    exact hinv
  · have hy : vY l < 2 ^ l.length := by
      have := val_lt (l.map MCell.y); rwa [List.length_map] at this
    have := trips_le l.length (vY l) hy
    exact Nat.mul_le_mul_right _ (by omega)

/-- **Multiplication on the compiled Turing machine.** -/
theorem mul_tm (l : List MCell) (hl : l ≠ []) (T : ℤ → Sym MCell) (hT : mulProg.Repr T l) :
    ∃ l' T', mulProg.Repr T' l' ∧
      vA l' % 2 ^ l.length = (vA l + vX l * vY l) % 2 ^ l.length ∧
      mulProg.toTM.run ⟨.fwd MulI.prep (mulProg.init MulI.prep), T, 0⟩
          ((trips (vY l) + 1) * (2 * l.length + 2)) =
        ⟨.fwd MulI.done (mulProg.init MulI.done), T', 0⟩ := by
  obtain ⟨l', hr, _, hinv⟩ := mul_reach l hl
  obtain ⟨T', hT', hrun⟩ := mulProg.reach_run hr T hT
  exact ⟨l', T', hT', hinv, hrun⟩

end PVNP.Discrete.SweepArith
