import PVNP.SweepFixMul
import PVNP.SweepLoop

/-!
# Data-dependent layout conversion: shifting a track by a binary counter

This is the first application of the loop combinator (`SweepLoop`). Some layouts are placed by
convention in the verified primitives, for example the divider's divisor `D·2^W`. A machine can
produce such a placement when the shift amount is given in binary on a counter track.

* Single-trip in-place programs on `SCell` (tracks `x` and `c`):
  - `shlProg` doubles `x` modulo `2ⁿ`;
  - `decProg` decrements the counter;
  - `testProg` branches on `c ≠ 0`.

  Their value lemmas are `fscan_shl`, `fscan_dec` and `fscan_nz`.
* The body `shl` then `dec` is a two-stage `seq` (`body_first`).
* `shift_by_counter`: the loop `loop test body` first-arrives at the test's `no` exit.
  - *Input:* a tape with counter value `W` (`W < 2ⁿ`).
  - *Output:* `x = X·2^W mod 2ⁿ` and a zero counter.
  - *Cost:* exactly `(3W + 1)(2n + 2)` transitions.
* `shift_by_counter_tm`: the same on the compiled single-tape TM.
-/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-- Cells for shifting: the shifted track `x` and the counter `c`. -/
structure SCell where
  x : Bool
  c : Bool
  deriving DecidableEq, Fintype

def vSx (l : List SCell) : ℕ := val (l.map SCell.x)
def vSc (l : List SCell) : ℕ := val (l.map SCell.c)

/-- Doubling the `x` track in place. -/
def fshl (carry : Bool) (z : SCell) : SCell × Bool := (⟨carry, z.c⟩, z.x)

/-- Decrementing the counter in place (borrow ripple; the initial borrow is `1`). -/
def fdec (b : Bool) (z : SCell) : SCell × Bool := (⟨z.x, xor z.c b⟩, b && !z.c)

/-- The zero test of the counter: the buffer records whether a set bit was seen. -/
def fnz (nz : Bool) (z : SCell) : SCell × Bool := (z, nz || z.c)

theorem fscan_shl : ∀ (b : Bool) (l : List SCell),
    val ((fscan fshl b l).1.map SCell.x) + 2 ^ l.length * (fscan fshl b l).2.toNat =
      2 * vSx l + b.toNat
  | b, [] => by simp [fscan, val, vSx]
  | b, z :: l => by
    have ih := fscan_shl z.x l
    simp only [fscan, List.map_cons, val, List.length_cons, pow_succ, vSx, fshl] at ih ⊢
    linarith [ih]

theorem fscan_shl_c : ∀ (b : Bool) (l : List SCell),
    (fscan fshl b l).1.map SCell.c = l.map SCell.c
  | _, [] => rfl
  | b, z :: l => by simp only [fscan, List.map_cons, fshl, fscan_shl_c z.x l]

theorem fdec_spec (b : Bool) (z : SCell) :
    (fdec b z).1.c.toNat + b.toNat = z.c.toNat + 2 * (fdec b z).2.toNat := by
  obtain ⟨x, c⟩ := z
  cases b <;> cases c <;> rfl

theorem fscan_dec : ∀ (b : Bool) (l : List SCell),
    val ((fscan fdec b l).1.map SCell.c) + b.toNat =
      vSc l + 2 ^ l.length * (fscan fdec b l).2.toNat
  | b, [] => by simp [fscan, val, vSc]
  | b, z :: l => by
    have ih := fscan_dec (fdec b z).2 l
    have hs := fdec_spec b z
    simp only [fscan, List.map_cons, val, List.length_cons, pow_succ, vSc] at ih ⊢
    nlinarith [ih, hs]

theorem fscan_dec_x : ∀ (b : Bool) (l : List SCell),
    (fscan fdec b l).1.map SCell.x = l.map SCell.x
  | _, [] => rfl
  | b, z :: l => by
    simp only [fscan, List.map_cons, fdec]
    rw [fscan_dec_x]

theorem fscan_nz : ∀ (b : Bool) (l : List SCell),
    (fscan fnz b l).1 = l ∧ (fscan fnz b l).2 = (b || decide (vSc l ≠ 0))
  | b, [] => by simp [fscan, vSc, val]
  | b, ⟨x, c⟩ :: l => by
    obtain ⟨h1, h2⟩ := fscan_nz (b || c) l
    refine ⟨by simp only [fscan, fnz, h1], ?_⟩
    simp only [fscan, fnz, h2, vSc, List.map_cons, val]
    cases b <;> cases c <;> simp

/-! ### The three single-trip programs -/

def shlProg : Prog where
  D := SCell
  I := AddI
  B := Bool
  lift b := ⟨b, false⟩
  start := .go
  init _ := false
  fwd
    | .go => fshl
    | .done => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun _ => .inl .done

def decProg : Prog where
  D := SCell
  I := AddI
  B := Bool
  lift b := ⟨b, false⟩
  start := .go
  init _ := true
  fwd
    | .go => fdec
    | .done => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun _ => .inl .done

inductive TstI | test | yes | no
  deriving DecidableEq, Fintype

def testProg : Prog where
  D := SCell
  I := TstI
  B := Bool
  lift b := ⟨b, false⟩
  start := .test
  init _ := false
  fwd
    | .test => fnz
    | _ => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next
    | .test => fun b => if b then .inl .yes else .inl .no
    | .yes => fun _ => .inl .yes
    | .no => fun _ => .inl .no

theorem shl_first (l : List SCell) :
    ReachFirst shlProg AddI.done (AddI.go, l) (fscan fshl false l).1 (2 * l.length + 2) := by
  have hs : shlProg.stepP (AddI.go, l) = .inl (AddI.done, (fscan fshl false l).1) := by
    simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, shlProg, bscan_id]
  have h := ReachFirst.last (P := shlProg) (e := AddI.done) hs
  simpa [Prog.tripCost, Prog.fpass, shlProg] using h

theorem dec_first (l : List SCell) :
    ReachFirst decProg AddI.done (AddI.go, l) (fscan fdec true l).1 (2 * l.length + 2) := by
  have hs : decProg.stepP (AddI.go, l) = .inl (AddI.done, (fscan fdec true l).1) := by
    simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, decProg, bscan_id]
  have h := ReachFirst.last (P := decProg) (e := AddI.done) hs
  simpa [Prog.tripCost, Prog.fpass, decProg] using h

theorem test_step (l : List SCell) :
    testProg.stepP (TstI.test, l) =
      .inl (if vSc l ≠ 0 then TstI.yes else TstI.no, l) := by
  obtain ⟨h1, h2⟩ := fscan_nz false l
  have ht : testProg.trip TstI.test l = (l, decide (vSc l ≠ 0)) := by
    simp only [Prog.trip, Prog.mid, Prog.fpass, testProg, bscan_id]
    rw [h1, h2]
    simp
  simp only [Prog.stepP, ht]
  by_cases h : vSc l ≠ 0
  · have hn : testProg.next TstI.test (decide (vSc l ≠ 0)) = .inl TstI.yes := by
      simp [testProg, h]
    rw [hn, if_pos h]
  · have hn : testProg.next TstI.test (decide (vSc l ≠ 0)) = .inl TstI.no := by
      simp [testProg, h]
    rw [hn, if_neg h]

theorem test_cost (l : List SCell) : testProg.tripCost TstI.test l = 2 * l.length + 2 := by
  simp [Prog.tripCost, Prog.fpass, testProg]

/-! ### The body and the loop -/

/-- The body: double `x`, then decrement the counter. -/
def bodyOn : ProgOn SCell := ProgOn.seq (ProgOn.ofProg shlProg) (ProgOn.ofProg decProg) AddI.done

/-- One body step on the tape. -/
def bodyStep (l : List SCell) : List SCell := (fscan fdec true (fscan fshl false l).1).1

theorem body_first (l : List SCell) :
    ReachFirst bodyOn.toProg (Sum.inr AddI.done) (bodyOn.start, l) (bodyStep l)
      ((2 * l.length + 2) + (2 * l.length + 2)) := by
  have h1 := shl_first l
  have h2 := dec_first (fscan fshl false l).1
  rw [fscan_length] at h2
  exact ProgOn.seq_reachFirst (ProgOn.ofProg shlProg) (ProgOn.ofProg decProg) AddI.done
    (show AddI.go ≠ AddI.done by decide) h1 h2

theorem bodyStep_length (l : List SCell) : (bodyStep l).length = l.length := by
  unfold bodyStep
  rw [fscan_length, fscan_length]

theorem bodyStep_x (l : List SCell) : vSx (bodyStep l) = 2 * vSx l % 2 ^ l.length := by
  have h := fscan_shl false l
  have hlt := val_lt ((fscan fshl false l).1.map SCell.x)
  rw [List.length_map, fscan_length] at hlt
  simp only [Bool.toNat_false, add_zero] at h
  have e : vSx (bodyStep l) = val ((fscan fshl false l).1.map SCell.x) := by
    unfold vSx bodyStep
    rw [fscan_dec_x]
  rw [e, ← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem bodyStep_c (l : List SCell) (hc : 0 < vSc l) : vSc (bodyStep l) = vSc l - 1 := by
  have h := fscan_dec true (fscan fshl false l).1
  have hlt := val_lt ((fscan fdec true (fscan fshl false l).1).1.map SCell.c)
  rw [List.length_map, fscan_length, fscan_length] at hlt
  have hc' : vSc (fscan fshl false l).1 = vSc l := by unfold vSc; rw [fscan_shl_c]
  rw [hc', fscan_length, Bool.toNat_true] at h
  unfold bodyStep
  show val ((fscan fdec true (fscan fshl false l).1).1.map SCell.c) = vSc l - 1
  cases hb : (fscan fdec true (fscan fshl false l).1).2
  · rw [hb, Bool.toNat_false, mul_zero, add_zero] at h
    omega
  · rw [hb, Bool.toNat_true, mul_one] at h
    omega

/-- **The shift loop**: test the counter; while it is nonzero, double `x` and decrement. -/
def shiftLoop : ProgOn SCell :=
  ProgOn.loop (ProgOn.ofProg testProg) bodyOn TstI.yes (Sum.inr AddI.done)

theorem iter_spec (l : List SCell) (W : ℕ) (hW : vSc l = W) :
    ∀ k ≤ W, (bodyStep^[k] l).length = l.length ∧ vSc (bodyStep^[k] l) = W - k ∧
      vSx (bodyStep^[k] l) = vSx l * 2 ^ k % 2 ^ l.length := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, by simp [hW], ?_⟩
    simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
    unfold vSx
    have := val_lt (l.map SCell.x)
    rw [List.length_map] at this
    rw [Nat.mod_eq_of_lt this]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    refine ⟨by rw [bodyStep_length, h1], ?_, ?_⟩
    · rw [bodyStep_c _ (by rw [h2]; omega), h2]
      omega
    · rw [bodyStep_x, h1, h3, Nat.mul_mod_mod, pow_succ,
        show 2 * (vSx l * 2 ^ k) = vSx l * (2 ^ k * 2) by ring]

/-- **Shift by a binary counter.** From a tape of length `n` with counter value `W`, the shift loop
first-arrives at the test's `no` exit. Then `x = X·2^W mod 2ⁿ` and the counter is zero. The cost is
exactly `(3W + 1)(2n + 2)` transitions. -/
theorem shift_by_counter (l : List SCell) :
    ∃ l', ReachFirst shiftLoop.toProg (Sum.inl TstI.no) (Sum.inl TstI.test, l) l'
        ((3 * vSc l + 1) * (2 * l.length + 2)) ∧
      vSx l' = vSx l * 2 ^ vSc l % 2 ^ l.length ∧ vSc l' = 0 ∧ l'.length = l.length := by
  set W := vSc l with hW
  obtain ⟨hlen, hc, hx⟩ := iter_spec l W rfl W le_rfl
  refine ⟨bodyStep^[W] l, ?_, hx, by rw [hc]; simp, hlen⟩
  have hr := ProgOn.loop_reachFirst (ProgOn.ofProg testProg) bodyOn TstI.yes (Sum.inr AddI.done)
    (eF := TstI.no) (show TstI.test ≠ TstI.no by decide) (show TstI.no ≠ TstI.yes by decide) W
    (fun k => bodyStep^[k] l) (fun k => bodyStep^[k] l)
    (fun _ => (2 * l.length + 2) + (2 * l.length + 2)) (bodyStep^[W] l)
    (fun k hk => by
      obtain ⟨_, hck, _⟩ := iter_spec l W rfl k hk.le
      show testProg.stepP (TstI.test, bodyStep^[k] l) = _
      rw [test_step, if_pos (by rw [hck]; omega)])
    (fun k hk => by
      obtain ⟨hlk, _, _⟩ := iter_spec l W rfl k hk.le
      have hb := body_first (bodyStep^[k] l)
      rw [hlk, ← Function.iterate_succ_apply' bodyStep k l] at hb
      exact hb)
    (by
      show testProg.stepP (TstI.test, bodyStep^[W] l) = _
      rw [test_step, if_neg (by rw [hc]; simp)])
  have hcost : ∑ k ∈ Finset.range W, ((ProgOn.ofProg testProg).toProg.tripCost
        (ProgOn.ofProg testProg).start (bodyStep^[k] l) +
          ((2 * l.length + 2) + (2 * l.length + 2))) +
        (ProgOn.ofProg testProg).toProg.tripCost (ProgOn.ofProg testProg).start
          (bodyStep^[W] l) = (3 * W + 1) * (2 * l.length + 2) := by
    have hk : ∀ k ∈ Finset.range W, (ProgOn.ofProg testProg).toProg.tripCost
          (ProgOn.ofProg testProg).start (bodyStep^[k] l) +
            ((2 * l.length + 2) + (2 * l.length + 2)) = 3 * (2 * l.length + 2) := by
      intro k hk
      obtain ⟨hlk, _, _⟩ := iter_spec l W rfl k (Finset.mem_range.mp hk).le
      show testProg.tripCost TstI.test (bodyStep^[k] l) + _ = _
      rw [test_cost, hlk]
      ring
    rw [Finset.sum_congr rfl hk, Finset.sum_const, Finset.card_range, smul_eq_mul]
    show _ + testProg.tripCost TstI.test (bodyStep^[W] l) = _
    rw [test_cost, hlen]
    ring
  rw [hcost] at hr
  exact hr

/-- **Shift by a binary counter on the compiled Turing machine.** -/
theorem shift_by_counter_tm (l : List SCell) (T : ℤ → Sym SCell)
    (hT : shiftLoop.toProg.Repr T l) :
    ∃ l' T', shiftLoop.toProg.Repr T' l' ∧
      vSx l' = vSx l * 2 ^ vSc l % 2 ^ l.length ∧ vSc l' = 0 ∧
      shiftLoop.toProg.toTM.run
          ⟨.fwd (Sum.inl TstI.test) (shiftLoop.toProg.init (Sum.inl TstI.test)), T, 0⟩
          ((3 * vSc l + 1) * (2 * l.length + 2)) =
        ⟨.fwd (Sum.inl TstI.no) (shiftLoop.toProg.init (Sum.inl TstI.no)), T', 0⟩ := by
  obtain ⟨l', hr, hx, hc, _⟩ := shift_by_counter l
  obtain ⟨T', hT', hrun⟩ := shiftLoop.toProg.reach_run hr.reach T hT
  exact ⟨l', T', hT', hx, hc, hrun⟩

end PVNP.Discrete.SweepArith
