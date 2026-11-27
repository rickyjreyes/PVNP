import PVNP.SweepMul

/-!
# Verified binary long division on the repository's Turing-machine model

Cells carry four little-endian tracks: the remainder `n`, the shifted divisor `d = D·2^k`, the
quotient `q` and a marker `m = 2^k`. The sweep program `divProg` runs restoring division.

* `prep`: compare `n` with `d` (most significant bit first) and test `m ≠ 0`.
* `sub` / `nosub`:
  - the forward pass (in `sub`) subtracts `d` from `n` and shifts `q` left, inserting the new
    quotient bit;
  - the backward pass shifts `d` and `m` right, compares the new `n` with the new `d`, and tests
    the new marker. These select the next instruction.
* `done`: rest.

The invariant is `N₀ = Q·(2·D·2^k) + n` with `n < 2·D·2^k`.

* `div_loop`: from `divI n d` with marker `2^k`, the program reaches `done` after exactly
  `(k + 1)(2W + 2)` transitions, with `q = (N₀ / D) mod 2^W` and `n = N₀ mod D`.
* `div_reach`: from `prep` with `d = D·2^K`, `m = 2^K`, `q = 0` and `N₀ < 2·D·2^K`, after exactly
  `(K + 2)(2W + 2)` transitions the quotient track is `N₀ / D` and the remainder track is
  `N₀ mod D` (no reduction mod `2^W` is needed, since `N₀ < 2^W`).
* `div_exact`, `div_exact_tm`: for `W`-bit operands `N < 2^W` and `0 < D < 2^W` on the explicit
  `2W`-cell layout `divInput W N D` (dividend, divisor shifted by `W` places, zero quotient,
  marker `2^W`), the compiled single-tape TM computes `N / D` and `N mod D` in exactly
  `(W + 2)(4W + 2)` transitions.
* `fixdiv_certified`, `fixdiv_tm`: with `p` fractional bits the machine returns the dyadic
  rounding `q` of `N / D`, certified by `q / 2^p ≤ N / D < (q + 1) / 2^p`.

The layout's shift by `W` places is a fixed, data-independent placement of the divisor. The
alignment search of schoolbook division is not needed because the marker runs over all `W + 1`
positions.
-/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

structure DCell where
  n : Bool
  d : Bool
  q : Bool
  m : Bool
  deriving DecidableEq, Fintype

structure DBuf where
  w : Bool
  pq : Bool
  fr : Bool
  pd : Bool
  pm : Bool
  c : Cmp
  nz : Bool
  deriving DecidableEq

instance : Fintype DBuf :=
  Fintype.ofEquiv (Bool × Bool × Bool × Bool × Bool × Cmp × Bool)
    { toFun := fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩
      invFun := fun x => ⟨x.w, x.pq, x.fr, x.pd, x.pm, x.c, x.nz⟩
      left_inv := fun ⟨_, _, _, _, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _, _, _, _⟩ => rfl }

def vN (l : List DCell) : ℕ := val (l.map DCell.n)
def vD (l : List DCell) : ℕ := val (l.map DCell.d)
def vQ (l : List DCell) : ℕ := val (l.map DCell.q)
def vM (l : List DCell) : ℕ := val (l.map DCell.m)

/-- Bit comparison of `a` against `b`. -/
def bitcmp (a b : Bool) : Cmp := if a = b then .eq else if b = true then .lt else .gt

/-- Forward pass of `sub`: `n := n − d` (borrow ripple) and `q := 2q + inserted bit`. -/
def gS (b : DBuf) (z : DCell) : DCell × DBuf :=
  (⟨xor (xor z.n z.d) b.w, z.d, b.pq, z.m⟩,
   ⟨(!z.n && z.d) || (!(xor z.n z.d) && b.w), z.q, true, b.pd, b.pm, b.c, b.nz⟩)

/-- Forward pass of `nosub`: `q := 2q + inserted bit`. -/
def gN (b : DBuf) (z : DCell) : DCell × DBuf :=
  (⟨z.n, z.d, b.pq, z.m⟩, ⟨b.w, z.q, true, b.pd, b.pm, b.c, b.nz⟩)

/-- Forward pass of `prep`: identity. -/
def gP (b : DBuf) (z : DCell) : DCell × DBuf :=
  (z, ⟨b.w, b.pq, true, b.pd, b.pm, b.c, b.nz⟩)

/-- Backward pass of `sub`/`nosub`: shift `d` and `m` right, compare, test the marker. -/
def hR (b : DBuf) (z : DCell) : DCell × DBuf :=
  (⟨z.n, !b.fr && b.pd, z.q, !b.fr && b.pm⟩,
   ⟨b.w, b.pq, false, z.d, z.m,
    if (if b.fr then Cmp.eq else b.c) = Cmp.eq then bitcmp z.n (!b.fr && b.pd)
      else (if b.fr then Cmp.eq else b.c),
    (!b.fr && b.nz) || (!b.fr && b.pm)⟩)

/-- Backward pass of `prep`: compare `n` with `d`, test the marker. -/
def hP (b : DBuf) (z : DCell) : DCell × DBuf :=
  (z, ⟨b.w, b.pq, false, b.pd, b.pm,
    if (if b.fr then Cmp.eq else b.c) = Cmp.eq then bitcmp z.n z.d
      else (if b.fr then Cmp.eq else b.c),
    (!b.fr && b.nz) || z.m⟩)

/-! ### Comparison, most significant bit first -/

theorem cmpOf_msb (a b : Bool) (X Y : ℕ) :
    cmpOf (a.toNat + 2 * X) (b.toNat + 2 * Y) .eq =
      if cmpOf X Y .eq = .eq then bitcmp a b else cmpOf X Y .eq := by
  rw [← cmpOf_step a b X Y .eq]
  unfold cmpOf bitcmp
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all

/-! ### Forward passes -/

theorem gscan_q (f : DBuf → DCell → DCell × DBuf)
    (hq : ∀ b z, (f b z).1.q = b.pq) (hpq : ∀ b z, (f b z).2.pq = z.q) :
    ∀ (b : DBuf) (l : List DCell),
      val ((fscan f b l).1.map DCell.q) + 2 ^ l.length * (fscan f b l).2.pq.toNat =
        2 * vQ l + b.pq.toNat
  | b, [] => by simp [fscan, val, vQ]
  | b, z :: l => by
    have ih := gscan_q f hq hpq (f b z).2 l
    simp only [fscan, List.map_cons, val, List.length_cons, pow_succ, vQ] at ih ⊢
    rw [hpq] at ih
    rw [hq]
    linarith [ih]

theorem gscan_keep (f : DBuf → DCell → DCell × DBuf) (p : DCell → Bool)
    (hp : ∀ b z, p (f b z).1 = p z) :
    ∀ (b : DBuf) (l : List DCell), (fscan f b l).1.map p = l.map p
  | _, [] => rfl
  | b, z :: l => by simp only [fscan, List.map_cons, hp, gscan_keep f p hp (f b z).2 l]

theorem gscan_fr (f : DBuf → DCell → DCell × DBuf) (hfr : ∀ b z, (f b z).2.fr = true) :
    ∀ (b : DBuf) (l : List DCell), l ≠ [] → (fscan f b l).2.fr = true
  | _, [], h => absurd rfl h
  | b, [z], _ => by simp [fscan, hfr]
  | b, z :: z' :: l, _ => by
    simp only [fscan]
    exact gscan_fr f hfr (f b z).2 (z' :: l) (List.cons_ne_nil _ _)

theorem gscan_sub : ∀ (b : DBuf) (l : List DCell),
    val ((fscan gS b l).1.map DCell.n) + vD l + b.w.toNat =
      vN l + 2 ^ l.length * (fscan gS b l).2.w.toNat
  | b, [] => by simp [fscan, val, vD, vN]
  | b, z :: l => by
    have ih := gscan_sub (gS b z).2 l
    have hs : (gS b z).1.n.toNat + z.d.toNat + b.w.toNat = z.n.toNat + 2 * (gS b z).2.w.toNat := by
      obtain ⟨n, d, q, m⟩ := z
      obtain ⟨w, pq, fr, pd, pm, c, nz⟩ := b
      cases n <;> cases d <;> cases w <;> rfl
    simp only [fscan, List.map_cons, val, List.length_cons, pow_succ, vD, vN] at ih ⊢
    linarith [ih, hs]

theorem gscan_gP : ∀ (b : DBuf) (l : List DCell), (fscan gP b l).1 = l
  | _, [] => rfl
  | b, z :: l => by simp only [fscan, gP, gscan_gP _ l]

/-! ### Backward passes -/

theorem hscan_hP (b : DBuf) (hb : b.fr = true) : ∀ l : List DCell, l ≠ [] →
    (bscan hP b l).1 = l ∧ (bscan hP b l).2.fr = false ∧
      (bscan hP b l).2.c = cmpOf (vN l) (vD l) .eq ∧ (bscan hP b l).2.nz = decide (vM l ≠ 0)
  | [], h => absurd rfl h
  | [z], _ => by
    obtain ⟨n, d, q, m⟩ := z
    obtain ⟨w, pq, fr, pd, pm, c, nz⟩ := b
    simp only at hb
    subst hb
    refine ⟨rfl, rfl, ?_, ?_⟩
    · cases n <;> cases d <;> rfl
    · cases m <;> rfl
  | z :: z' :: l, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := hscan_hP b hb (z' :: l) (List.cons_ne_nil _ _)
    have e : bscan hP b (z :: z' :: l) =
        ((hP (bscan hP b (z' :: l)).2 z).1 :: (bscan hP b (z' :: l)).1,
          (hP (bscan hP b (z' :: l)).2 z).2) := rfl
    have hvn : vN (z :: z' :: l) = z.n.toNat + 2 * vN (z' :: l) := rfl
    have hvd : vD (z :: z' :: l) = z.d.toNat + 2 * vD (z' :: l) := rfl
    have hvm : vM (z :: z' :: l) = z.m.toNat + 2 * vM (z' :: l) := rfl
    rw [e]
    refine ⟨?_, rfl, ?_, ?_⟩
    · show z :: (bscan hP b (z' :: l)).1 = z :: z' :: l
      rw [h1]
    · show (if (if (bscan hP b (z' :: l)).2.fr then Cmp.eq else (bscan hP b (z' :: l)).2.c) =
          Cmp.eq then bitcmp z.n z.d
          else (if (bscan hP b (z' :: l)).2.fr then Cmp.eq else (bscan hP b (z' :: l)).2.c)) = _
      rw [h2, h3, hvn, hvd, cmpOf_msb]
      simp only [Bool.false_eq_true, if_false]
    · show ((!(bscan hP b (z' :: l)).2.fr && (bscan hP b (z' :: l)).2.nz) || z.m) = _
      rw [h2, h4, hvm, decide_ne_zero]
      cases z.m <;> simp

theorem hscan_hR (b : DBuf) (hb : b.fr = true) : ∀ l : List DCell, l ≠ [] →
    (bscan hR b l).1.map DCell.n = l.map DCell.n ∧
      (bscan hR b l).1.map DCell.q = l.map DCell.q ∧
      (bscan hR b l).1.map DCell.d = (l.map DCell.d).tail ++ [false] ∧
      (bscan hR b l).1.map DCell.m = (l.map DCell.m).tail ++ [false] ∧
      (bscan hR b l).2.fr = false ∧
      (bscan hR b l).2.pd = (l.headD ⟨false, false, false, false⟩).d ∧
      (bscan hR b l).2.pm = (l.headD ⟨false, false, false, false⟩).m ∧
      (bscan hR b l).2.c = cmpOf (vN l) (val ((l.map DCell.d).tail ++ [false])) .eq ∧
      (bscan hR b l).2.nz = decide (val ((l.map DCell.m).tail ++ [false]) ≠ 0)
  | [], h => absurd rfl h
  | [z], _ => by
    obtain ⟨n, d, q, m⟩ := z
    obtain ⟨w, pq, fr, pd, pm, c, nz⟩ := b
    simp only at hb
    subst hb
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    cases n <;> rfl
  | z :: z' :: l, _ => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hscan_hR b hb (z' :: l) (List.cons_ne_nil _ _)
    have e : bscan hR b (z :: z' :: l) =
        ((hR (bscan hR b (z' :: l)).2 z).1 :: (bscan hR b (z' :: l)).1,
          (hR (bscan hR b (z' :: l)).2 z).2) := rfl
    have hpd : (bscan hR b (z' :: l)).2.pd = z'.d := h6
    have hpm : (bscan hR b (z' :: l)).2.pm = z'.m := h7
    have hvn : vN (z :: z' :: l) = z.n.toNat + 2 * vN (z' :: l) := rfl
    have hvd : val ((List.map DCell.d (z :: z' :: l)).tail ++ [false]) =
        z'.d.toNat + 2 * val ((List.map DCell.d (z' :: l)).tail ++ [false]) := by simp [val]
    have hvm : val ((List.map DCell.m (z :: z' :: l)).tail ++ [false]) =
        z'.m.toNat + 2 * val ((List.map DCell.m (z' :: l)).tail ++ [false]) := by simp [val]
    rw [e]
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · show z.n :: (bscan hR b (z' :: l)).1.map DCell.n = _
      rw [h1]; rfl
    · show z.q :: (bscan hR b (z' :: l)).1.map DCell.q = _
      rw [h2]; rfl
    · show (!(bscan hR b (z' :: l)).2.fr && (bscan hR b (z' :: l)).2.pd) ::
          (bscan hR b (z' :: l)).1.map DCell.d = _
      rw [h3, h5, hpd]; simp
    · show (!(bscan hR b (z' :: l)).2.fr && (bscan hR b (z' :: l)).2.pm) ::
          (bscan hR b (z' :: l)).1.map DCell.m = _
      rw [h4, h5, hpm]; simp
    · show (if (if (bscan hR b (z' :: l)).2.fr then Cmp.eq else (bscan hR b (z' :: l)).2.c) =
          Cmp.eq then bitcmp z.n (!(bscan hR b (z' :: l)).2.fr && (bscan hR b (z' :: l)).2.pd)
          else (if (bscan hR b (z' :: l)).2.fr then Cmp.eq else (bscan hR b (z' :: l)).2.c)) = _
      rw [h5, h8, hpd, hvn, hvd, cmpOf_msb]
      simp only [Bool.false_eq_true, if_false, Bool.not_false, Bool.true_and]
    · show ((!(bscan hR b (z' :: l)).2.fr && (bscan hR b (z' :: l)).2.nz) ||
          (!(bscan hR b (z' :: l)).2.fr && (bscan hR b (z' :: l)).2.pm)) = _
      rw [h5, h9, hpm, hvm, decide_ne_zero]
      cases z'.m <;> simp

/-! ### The program -/

inductive DivI | prep | sub | nosub | done
  deriving DecidableEq, Fintype

def dnext (b : DBuf) : DivI ⊕ Bool :=
  if !b.nz then .inl .done else if b.c = Cmp.lt then .inl .nosub else .inl .sub

def divProg : Prog where
  D := DCell
  I := DivI
  B := DBuf
  lift b := ⟨b, false, false, false⟩
  start := .prep
  init
    | .sub => ⟨false, true, false, false, false, .eq, false⟩
    | _ => ⟨false, false, false, false, false, .eq, false⟩
  fwd
    | .prep => gP
    | .sub => gS
    | .nosub => gN
    | .done => fun b z => (z, b)
  ext _ := fun _ => none
  bwd
    | .prep => hP
    | .sub => hR
    | .nosub => hR
    | .done => fun b z => (z, b)
  next
    | .done => fun _ => .inl .done
    | _ => dnext

/-- The instruction chosen by the comparison of remainder and shifted divisor. -/
def divI (N Dsh : ℕ) : DivI := if Dsh ≤ N then .sub else .nosub

theorem cmpOf_lt_iff (X Y : ℕ) : cmpOf X Y .eq = .lt ↔ X < Y := by
  unfold cmpOf; split_ifs with h1 h2 <;> simp_all

theorem dnext_eq (b : DBuf) (N Dsh M : ℕ) (hc : b.c = cmpOf N Dsh .eq)
    (hnz : b.nz = decide (M ≠ 0)) :
    dnext b = .inl (if M = 0 then .done else divI N Dsh) := by
  unfold dnext divI
  rw [hc, hnz]
  by_cases hM : M = 0
  · simp [hM]
  · have h1 : (!decide (M ≠ 0)) = false := by simp [hM]
    rw [h1, if_neg hM]
    simp only [Bool.false_eq_true, if_false]
    by_cases hl : N < Dsh
    · rw [if_pos ((cmpOf_lt_iff N Dsh).2 hl), if_neg (show ¬ Dsh ≤ N by omega)]
    · rw [if_neg (fun h => hl ((cmpOf_lt_iff N Dsh).1 h)), if_pos (show Dsh ≤ N by omega)]

theorem trip_eq_div (i : DivI) (f g : DBuf → DCell → DCell × DBuf) (hf : divProg.fwd i = f)
    (hg : divProg.bwd i = g) (l : List DCell) :
    divProg.trip i l = bscan g (fscan f (divProg.init i) l).2 (fscan f (divProg.init i) l).1 := by
  have hext : divProg.ext i (fscan f (divProg.init i) l).2 = none := rfl
  simp only [Prog.trip, Prog.mid, Prog.fpass, hf, hg, hext, Option.toList_none, List.append_nil]

theorem tripCost_div (i : DivI) (l : List DCell) : divProg.tripCost i l = 2 * l.length + 2 := by
  cases i <;> rfl

/-- The common part of a `sub`/`nosub` trip. -/
theorem dstep_core (i : DivI) (f : DBuf → DCell → DCell × DBuf) (hf : divProg.fwd i = f)
    (hb : divProg.bwd i = hR) (hnext : divProg.next i = dnext)
    (hq : ∀ b z, (f b z).1.q = b.pq) (hpq : ∀ b z, (f b z).2.pq = z.q)
    (hd : ∀ b z, (f b z).1.d = z.d) (hm : ∀ b z, (f b z).1.m = z.m)
    (hfr : ∀ b z, (f b z).2.fr = true) (l : List DCell) (hl : l ≠ []) :
    ∃ l₁, divProg.stepP (i, l) =
        .inl (if vM l₁ = 0 then .done else divI (vN l₁) (vD l₁), l₁) ∧
      l₁.length = l.length ∧ vD l₁ = vD l / 2 ∧ vM l₁ = vM l / 2 ∧
      vQ l₁ = (2 * vQ l + (divProg.init i).pq.toNat) % 2 ^ l.length ∧
      l₁.map DCell.n = (fscan f (divProg.init i) l).1.map DCell.n := by
  have hFlen : (fscan f (divProg.init i) l).1.length = l.length := fscan_length f _ l
  have hFne : (fscan f (divProg.init i) l).1 ≠ [] := by
    intro h
    rw [h, List.length_nil] at hFlen
    exact hl (List.length_eq_zero_iff.mp hFlen.symm)
  have hfr' : (fscan f (divProg.init i) l).2.fr = true := gscan_fr f hfr _ l hl
  obtain ⟨b1, b2, b3, b4, _, _, _, b8, b9⟩ := hscan_hR _ hfr' _ hFne
  set l₁ := (bscan hR (fscan f (divProg.init i) l).2 (fscan f (divProg.init i) l).1).1 with hl₁
  have hFd := gscan_keep f DCell.d hd (divProg.init i) l
  have hFm := gscan_keep f DCell.m hm (divProg.init i) l
  have hFq := gscan_q f hq hpq (divProg.init i) l
  have hvd : vD l₁ = val (((fscan f (divProg.init i) l).1.map DCell.d).tail ++ [false]) := by
    unfold vD; rw [b3]
  have hvm : vM l₁ = val (((fscan f (divProg.init i) l).1.map DCell.m).tail ++ [false]) := by
    unfold vM; rw [b4]
  have hvn : vN l₁ = vN (fscan f (divProg.init i) l).1 := by unfold vN; rw [b1]
  refine ⟨l₁, ?_, ?_, ?_, ?_, ?_, b1⟩
  · have ht := trip_eq_div i f hR hf hb l
    simp only [Prog.stepP, ht, hnext]
    rw [dnext_eq _ (vN l₁) (vD l₁) (vM l₁) (by rw [hvn, hvd]; exact b8) (by rw [hvm]; exact b9)]
  · rw [hl₁, bscan_length, hFlen]
  · rw [hvd, hFd, val_tail_append_false]; rfl
  · rw [hvm, hFm, val_tail_append_false]; rfl
  · have hq1 : vQ l₁ = val ((fscan f (divProg.init i) l).1.map DCell.q) := by
      unfold vQ; rw [b2]
    rw [hq1]
    have hlt := val_lt ((fscan f (divProg.init i) l).1.map DCell.q)
    rw [List.length_map, hFlen] at hlt
    rw [← hFq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- One `sub`/`nosub` trip, with its arithmetic effect. -/
theorem dstep (l : List DCell) (hl : l ≠ []) :
    ∃ l₁, divProg.stepP (divI (vN l) (vD l), l) =
        .inl (if vM l₁ = 0 then .done else divI (vN l₁) (vD l₁), l₁) ∧
      l₁.length = l.length ∧ vD l₁ = vD l / 2 ∧ vM l₁ = vM l / 2 ∧
      vQ l₁ = (2 * vQ l + if vD l ≤ vN l then 1 else 0) % 2 ^ l.length ∧
      vN l₁ = if vD l ≤ vN l then vN l - vD l else vN l := by
  by_cases hs : vD l ≤ vN l
  · have hi : divI (vN l) (vD l) = DivI.sub := by unfold divI; rw [if_pos hs]
    obtain ⟨l₁, h1, h2, h3, h4, h5, h6⟩ := dstep_core DivI.sub gS rfl rfl rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) l hl
    refine ⟨l₁, by rw [hi]; exact h1, h2, h3, h4, by rw [h5, if_pos hs]; rfl, ?_⟩
    rw [if_pos hs]
    have hsub := gscan_sub (divProg.init DivI.sub) l
    have hlt := val_lt ((fscan gS (divProg.init DivI.sub) l).1.map DCell.n)
    rw [List.length_map, fscan_length] at hlt
    have hw0 : (divProg.init DivI.sub).w = false := rfl
    rw [hw0, Bool.toNat_false, add_zero] at hsub
    have hvn : vN l₁ = val ((fscan gS (divProg.init DivI.sub) l).1.map DCell.n) := by
      unfold vN; rw [h6]
    rw [hvn]
    cases hbw : (fscan gS (divProg.init DivI.sub) l).2.w
    · rw [hbw, Bool.toNat_false, mul_zero, add_zero] at hsub; omega
    · rw [hbw, Bool.toNat_true, mul_one] at hsub
      have := val_lt (l.map DCell.n); rw [List.length_map] at this; omega
  · have hi : divI (vN l) (vD l) = DivI.nosub := by unfold divI; rw [if_neg hs]
    obtain ⟨l₁, h1, h2, h3, h4, h5, h6⟩ := dstep_core DivI.nosub gN rfl rfl rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) l hl
    refine ⟨l₁, by rw [hi]; exact h1, h2, h3, h4, by rw [h5, if_neg hs]; rfl, ?_⟩
    rw [if_neg hs]
    unfold vN; rw [h6, gscan_keep gN DCell.n (fun _ _ => rfl)]

/-- The arithmetic of one restoring step. -/
theorem div_arith (N₀ Qt n Dk : ℕ) (hinv : N₀ = Qt * (2 * Dk) + n) (hlt : n < 2 * Dk) :
    N₀ = (2 * Qt + if Dk ≤ n then 1 else 0) * Dk + (if Dk ≤ n then n - Dk else n) ∧
      (if Dk ≤ n then n - Dk else n) < Dk := by
  have e1 : Qt * (2 * Dk) = 2 * (Qt * Dk) := by ring
  rw [e1] at hinv
  split_ifs with hc
  · have e2 : (2 * Qt + 1) * Dk = 2 * (Qt * Dk) + Dk := by ring
    rw [e2]
    clear e1 e2
    generalize Qt * Dk = P at *
    omega
  · have e3 : (2 * Qt + 0) * Dk = 2 * (Qt * Dk) := by ring
    rw [e3]
    clear e1 e3
    generalize Qt * Dk = P at *
    omega

/-- Shifting a reduced quotient. -/
theorem mod_shift (Q b M : ℕ) : (2 * (Q % M) + b) % M = (2 * Q + b) % M :=
  ((Nat.mod_modEq Q M).mul_left 2).add_right b

/-- **The division loop.** -/
theorem div_loop (W D N₀ : ℕ) (hD : 0 < D) : ∀ (k : ℕ) (l : List DCell) (Qt : ℕ),
    l.length = W → vM l = 2 ^ k → vD l = D * 2 ^ k →
    N₀ = Qt * (2 * (D * 2 ^ k)) + vN l → vN l < 2 * (D * 2 ^ k) → vQ l = Qt % 2 ^ W →
    ∃ l', divProg.Reach (divI (vN l) (vD l), l) (.done, l') ((k + 1) * (2 * W + 2)) ∧
      vQ l' = (N₀ / D) % 2 ^ W ∧ vN l' = N₀ % D := by
  intro k
  induction k with
  | zero =>
    intro l Qt hlen hm hd hinv hlt hq
    have hne : l ≠ [] := by
      rintro rfl
      have h0 : (2 : ℕ) ^ 0 ≠ 0 := by positivity
      exact h0 hm.symm
    obtain ⟨l₁, hs, _, _, hm1, hq1, hn1⟩ := dstep l hne
    have hm0 : vM l₁ = 0 := by rw [hm1, hm]; rfl
    rw [if_pos hm0] at hs
    have hinv2 : N₀ = Qt * (2 * vD l) + vN l := by rw [hd]; exact hinv
    have hlt2 : vN l < 2 * vD l := by rw [hd]; exact hlt
    obtain ⟨k1, k2⟩ := div_arith N₀ Qt (vN l) (vD l) hinv2 hlt2
    rw [← hn1] at k1 k2
    rw [hq, hlen, mod_shift] at hq1
    obtain ⟨Qt', hQt'⟩ : ∃ Qt', Qt' = 2 * Qt + (if vD l ≤ vN l then 1 else 0) := ⟨_, rfl⟩
    rw [← hQt'] at k1 hq1
    have hd0 : vD l = D := by rw [hd, pow_zero, mul_one]
    rw [hd0] at k1 k2
    have hdiv : N₀ / D = Qt' := by
      rw [k1, Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt k2, zero_add]
    have hmod : N₀ % D = vN l₁ := by
      rw [k1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k2]
    refine ⟨l₁, ?_, by rw [hq1, hdiv], hmod.symm⟩
    have h := Prog.Reach.step (P := divProg) hs (Prog.Reach.refl _)
    rw [tripCost_div, hlen] at h
    simpa using h
  | succ k ih =>
    intro l Qt hlen hm hd hinv hlt hq
    have hne : l ≠ [] := by
      rintro rfl
      have h0 : (2 : ℕ) ^ (k + 1) ≠ 0 := by positivity
      exact h0 hm.symm
    obtain ⟨l₁, hs, hlen1, hd1, hm1, hq1, hn1⟩ := dstep l hne
    have hm1' : vM l₁ = 2 ^ k := by rw [hm1, hm, pow_succ]; omega
    have hd1' : vD l₁ = D * 2 ^ k := by
      rw [hd1, hd, pow_succ, ← mul_assoc]; omega
    have hm0 : vM l₁ ≠ 0 := by rw [hm1']; positivity
    rw [if_neg hm0] at hs
    have hpk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hinv2 : N₀ = Qt * (2 * vD l) + vN l := by rw [hd]; exact hinv
    have hlt2 : vN l < 2 * vD l := by rw [hd]; exact hlt
    obtain ⟨k1, k2⟩ := div_arith N₀ Qt (vN l) (vD l) hinv2 hlt2
    rw [← hn1] at k1 k2
    rw [hq, hlen, mod_shift] at hq1
    obtain ⟨Qt', hQt'⟩ : ∃ Qt', Qt' = 2 * Qt + (if vD l ≤ vN l then 1 else 0) := ⟨_, rfl⟩
    rw [← hQt'] at k1 hq1
    have hvd2 : vD l = 2 * (D * 2 ^ k) := by rw [hd, hpk]; ring
    rw [hvd2] at k1 k2
    obtain ⟨l', hr, hq'', hn''⟩ := ih l₁ Qt' (by rw [hlen1, hlen]) hm1' hd1' k1 k2 hq1
    refine ⟨l', ?_, hq'', hn''⟩
    have h := Prog.Reach.step (P := divProg) hs hr
    rw [tripCost_div, hlen] at h
    convert h using 1
    ring

/-- **Long division.** Suppose the tape has `d = D·2^K`, `m = 2^K`, `q = 0` and dividend
`N₀ = val n < 2·D·2^K`. Then from `prep` the program reaches `done` after exactly
`(K + 2)(2W + 2)` transitions, with quotient track `N₀ / D` and remainder track `N₀ mod D`. -/
theorem div_reach (l : List DCell) (hl : l ≠ []) (K D : ℕ) (hD : 0 < D)
    (hd : vD l = D * 2 ^ K) (hm : vM l = 2 ^ K) (hq : vQ l = 0)
    (hlt : vN l < 2 * (D * 2 ^ K)) :
    ∃ l', divProg.Reach (DivI.prep, l) (.done, l') ((K + 2) * (2 * l.length + 2)) ∧
      vQ l' = vN l / D ∧ vN l' = vN l % D := by
  have hfr : (fscan gP (divProg.init DivI.prep) l).2.fr = true :=
    gscan_fr gP (fun _ _ => rfl) _ l hl
  have hF : (fscan gP (divProg.init DivI.prep) l).1 = l := gscan_gP _ l
  obtain ⟨p1, _, p3, p4⟩ := hscan_hP _ hfr l hl
  have hm0 : vM l ≠ 0 := by rw [hm]; positivity
  have hs : divProg.stepP (DivI.prep, l) = .inl (divI (vN l) (vD l), l) := by
    have ht := trip_eq_div DivI.prep gP hP rfl rfl l
    rw [hF] at ht
    simp only [Prog.stepP, ht, p1]
    rw [show divProg.next DivI.prep = dnext from rfl, dnext_eq _ (vN l) (vD l) (vM l) p3 p4,
      if_neg hm0]
  obtain ⟨l', hr, hq', hn'⟩ := div_loop l.length D (vN l) hD K l 0 rfl hm hd
    (by ring) hlt (by rw [hq]; simp)
  refine ⟨l', ?_, ?_, hn'⟩
  · have h := Prog.Reach.step (P := divProg) hs hr
    rw [tripCost_div] at h
    convert h using 1
    ring
  · have hN := val_lt (l.map DCell.n)
    rw [List.length_map] at hN
    rw [hq', Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self (vN l) D) hN)]

/-- **Long division on the compiled Turing machine.** -/
theorem div_tm (l : List DCell) (hl : l ≠ []) (K D : ℕ) (hD : 0 < D)
    (hd : vD l = D * 2 ^ K) (hm : vM l = 2 ^ K) (hq : vQ l = 0)
    (hlt : vN l < 2 * (D * 2 ^ K)) (T : ℤ → Sym DCell) (hT : divProg.Repr T l) :
    ∃ l' T', divProg.Repr T' l' ∧ vQ l' = vN l / D ∧ vN l' = vN l % D ∧
      divProg.toTM.run ⟨.fwd DivI.prep (divProg.init DivI.prep), T, 0⟩
          ((K + 2) * (2 * l.length + 2)) =
        ⟨.fwd DivI.done (divProg.init DivI.done), T', 0⟩ := by
  obtain ⟨l', hr, hq', hn'⟩ := div_reach l hl K D hD hd hm hq hlt
  obtain ⟨T', hT', hrun⟩ := divProg.reach_run hr T hT
  exact ⟨l', T', hT', hq', hn', hrun⟩

/-! ### Explicit input layout for `W`-bit operands -/

/-- The `W`-bit little-endian encoding of `N mod 2^W`. -/
def bitsOf : ℕ → ℕ → List Bool
  | 0, _ => []
  | W + 1, N => decide (N % 2 = 1) :: bitsOf W (N / 2)

theorem bitsOf_length : ∀ W N, (bitsOf W N).length = W
  | 0, _ => rfl
  | W + 1, N => by simp [bitsOf, bitsOf_length W (N / 2)]

theorem val_bitsOf : ∀ W N, val (bitsOf W N) = N % 2 ^ W
  | 0, N => by simp [bitsOf, val, Nat.mod_one]
  | W + 1, N => by
    have h2 : (decide (N % 2 = 1)).toNat = N % 2 := by
      rcases Nat.mod_two_eq_zero_or_one N with h | h <;> simp [h]
    show (decide (N % 2 = 1)).toNat + 2 * val (bitsOf W (N / 2)) = _
    rw [val_bitsOf W (N / 2), h2, pow_succ, mul_comm (2 ^ W) 2, Nat.mod_mul]

/-- Four tracks zipped into cells. -/
def mkCells : List Bool → List Bool → List Bool → List Bool → List DCell
  | a :: as, b :: bs, c :: cs, d :: ds => ⟨a, b, c, d⟩ :: mkCells as bs cs ds
  | _, _, _, _ => []

theorem mkCells_spec (as bs cs ds : List Bool) (hb : bs.length = as.length)
    (hc : cs.length = as.length) (hd : ds.length = as.length) :
    (mkCells as bs cs ds).map DCell.n = as ∧ (mkCells as bs cs ds).map DCell.d = bs ∧
      (mkCells as bs cs ds).map DCell.q = cs ∧ (mkCells as bs cs ds).map DCell.m = ds ∧
      (mkCells as bs cs ds).length = as.length := by
  induction as generalizing bs cs ds with
  | nil =>
    rw [List.length_nil, List.length_eq_zero_iff] at hb hc hd
    subst hb hc hd
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons a as ih =>
    cases bs with
    | nil => simp at hb
    | cons b bs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        cases ds with
        | nil => simp at hd
        | cons d ds =>
          simp only [List.length_cons, add_left_inj] at hb hc hd
          obtain ⟨h1, h2, h3, h4, h5⟩ := ih bs cs ds hb hc hd
          simp [mkCells, h1, h2, h3, h4, h5]

/-- Layout for `W`-bit division on `2W` cells: dividend `N`, divisor `D` shifted by `W` places,
quotient `0` and marker `2^W`. The shift is a fixed, data-independent placement. -/
def divInput (W N D : ℕ) : List DCell :=
  mkCells (bitsOf (2 * W) N) (bitsOf (2 * W) (D * 2 ^ W)) (bitsOf (2 * W) 0)
    (bitsOf (2 * W) (2 ^ W))

theorem divInput_spec (W N D : ℕ) :
    vN (divInput W N D) = N % 2 ^ (2 * W) ∧ vD (divInput W N D) = D * 2 ^ W % 2 ^ (2 * W) ∧
      vQ (divInput W N D) = 0 ∧ vM (divInput W N D) = 2 ^ W % 2 ^ (2 * W) ∧
      (divInput W N D).length = 2 * W := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkCells_spec (bitsOf (2 * W) N) (bitsOf (2 * W) (D * 2 ^ W))
    (bitsOf (2 * W) 0) (bitsOf (2 * W) (2 ^ W)) (by simp [bitsOf_length])
    (by simp [bitsOf_length]) (by simp [bitsOf_length])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold vN divInput; rw [h1, val_bitsOf]
  · unfold vD divInput; rw [h2, val_bitsOf]
  · unfold vQ divInput; rw [h3, val_bitsOf, Nat.zero_mod]
  · unfold vM divInput; rw [h4, val_bitsOf]
  · unfold divInput; rw [h5, bitsOf_length]

/-- **`W`-bit long division, end to end.** For `N < 2^W` and `0 < D < 2^W`, from the layout
`divInput W N D` the program reaches `done` after exactly `(W + 2)(4W + 2)` transitions, with
quotient track `N / D` and remainder track `N mod D`. -/
theorem div_exact (W N D : ℕ) (hN : N < 2 ^ W) (hD : 0 < D) (hDW : D < 2 ^ W) :
    ∃ l', divProg.Reach (DivI.prep, divInput W N D) (.done, l') ((W + 2) * (4 * W + 2)) ∧
      vQ l' = N / D ∧ vN l' = N % D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := divInput_spec W N D
  have hW2 : 2 ^ (2 * W) = 2 ^ W * 2 ^ W := by rw [two_mul, pow_add]
  have hpos : 0 < 2 ^ W := by positivity
  have hW0 : W ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hDW
    omega
  have hN2 : N < 2 ^ (2 * W) := by rw [hW2]; nlinarith
  have hD2 : D * 2 ^ W < 2 ^ (2 * W) := by rw [hW2]; nlinarith
  have hM2 : 2 ^ W < 2 ^ (2 * W) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [Nat.mod_eq_of_lt hN2] at h1
  rw [Nat.mod_eq_of_lt hD2] at h2
  rw [Nat.mod_eq_of_lt hM2] at h4
  have hne : divInput W N D ≠ [] := by
    intro h; rw [h, List.length_nil] at h5; omega
  have hlt : vN (divInput W N D) < 2 * (D * 2 ^ W) := by rw [h1]; nlinarith
  obtain ⟨l', hr, hq, hn⟩ := div_reach (divInput W N D) hne W D hD h2 h4 h3 hlt
  refine ⟨l', ?_, by rw [hq, h1], by rw [hn, h1]⟩
  rw [h5] at hr
  convert hr using 1
  ring

/-- **`W`-bit long division on the compiled Turing machine.** -/
theorem div_exact_tm (W N D : ℕ) (hN : N < 2 ^ W) (hD : 0 < D) (hDW : D < 2 ^ W)
    (T : ℤ → Sym DCell) (hT : divProg.Repr T (divInput W N D)) :
    ∃ l' T', divProg.Repr T' l' ∧ vQ l' = N / D ∧ vN l' = N % D ∧
      divProg.toTM.run ⟨.fwd DivI.prep (divProg.init DivI.prep), T, 0⟩ ((W + 2) * (4 * W + 2)) =
        ⟨.fwd DivI.done (divProg.init DivI.done), T', 0⟩ := by
  obtain ⟨l', hr, hq, hn⟩ := div_exact W N D hN hD hDW
  obtain ⟨T', hT', hrun⟩ := divProg.reach_run hr T hT
  exact ⟨l', T', hT', hq, hn, hrun⟩

/-! ### Certified fixed-point rounding -/

/-- **Correct rounding of a quotient.** `q = ⌊N·2^p / D⌋` is the dyadic rounding of `N / D`
downwards: `q / 2^p ≤ N / D < (q + 1) / 2^p`. -/
theorem fixdiv_certified (N D p : ℕ) (hD : 0 < D) :
    ((N * 2 ^ p / D : ℕ) : ℚ) / 2 ^ p ≤ (N : ℚ) / D ∧
      (N : ℚ) / D < (((N * 2 ^ p / D : ℕ) : ℚ) + 1) / 2 ^ p := by
  have h1 : N * 2 ^ p / D * D ≤ N * 2 ^ p := Nat.div_mul_le_self _ _
  have h2 : N * 2 ^ p < N * 2 ^ p / D * D + D := Nat.lt_div_mul_add hD
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hP : (0 : ℚ) < 2 ^ p := by positivity
  have h1' : ((N * 2 ^ p / D : ℕ) : ℚ) * D ≤ (N : ℚ) * 2 ^ p := by exact_mod_cast h1
  have h2' : (N : ℚ) * 2 ^ p < (((N * 2 ^ p / D : ℕ) : ℚ) + 1) * D := by
    have : ((N * 2 ^ p : ℕ) : ℚ) < ((N * 2 ^ p / D * D + D : ℕ) : ℚ) := by exact_mod_cast h2
    push_cast at this
    linarith
  constructor
  · rw [div_le_div_iff₀ hP hDq]; linarith
  · rw [div_lt_div_iff₀ hDq hP]; linarith

/-- **Fixed-point division on the compiled Turing machine.** With `p` fractional bits and
`N·2^p < 2^W`, `0 < D < 2^W`, the machine computes the dyadic rounding `q` of `N / D`, with
`q / 2^p ≤ N / D < (q + 1) / 2^p`, in exactly `(W + 2)(4W + 2)` transitions. -/
theorem fixdiv_tm (W N D p : ℕ) (hN : N * 2 ^ p < 2 ^ W) (hD : 0 < D) (hDW : D < 2 ^ W)
    (T : ℤ → Sym DCell) (hT : divProg.Repr T (divInput W (N * 2 ^ p) D)) :
    ∃ l' T', divProg.Repr T' l' ∧
      (vQ l' : ℚ) / 2 ^ p ≤ (N : ℚ) / D ∧ (N : ℚ) / D < ((vQ l' : ℚ) + 1) / 2 ^ p ∧
      divProg.toTM.run ⟨.fwd DivI.prep (divProg.init DivI.prep), T, 0⟩ ((W + 2) * (4 * W + 2)) =
        ⟨.fwd DivI.done (divProg.init DivI.done), T', 0⟩ := by
  obtain ⟨l', T', hT', hq, _, hrun⟩ := div_exact_tm W (N * 2 ^ p) D hN hD hDW T hT
  obtain ⟨c1, c2⟩ := fixdiv_certified N D p hD
  rw [← hq] at c1 c2
  exact ⟨l', T', hT', c1, c2, hrun⟩

end PVNP.Discrete.SweepArith
