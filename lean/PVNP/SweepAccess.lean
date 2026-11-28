import PVNP.SweepGcd

/-!
# Uniform access to packed words on the Turing machine

An input vector of `L`-bit words `w₀, …, w_{M−1}` is stored on one track as the packed number
`pack L [w₀, …, w_{M−1}] = w₀ + 2^L w₁ + ⋯`. A machine reads the word `w_k` for an index given on
the tape: the offset `kL` in binary on a counter track. The machine runs three stages, composed
by `ProgOn.seq_reachFirst`:

1. a cellwise map copies the vector track into the work track;
2. a loop of verified programs shifts the work track right by the counter (`shrLoop`): each
   iteration halves the work track and decrements the counter;
3. a cellwise map masks the work track with the mask track, which holds `2^L − 1`.

* `bscan_shr`, `shr_first`: the single-trip right shift, `x ↦ ⌊x/2⌋`.
* `shift_right_by_counter`: the loop first-arrives at its stop exit with `x = ⌊X/2^s⌋` and a zero
  counter, in exactly `(3s + 1)(2n + 2)` transitions, where `s` is the counter value.
* `val_mask`: masking with `2^L − 1` keeps the residue modulo `2^L`.
* `pack_word`: `⌊pack L ws / 2^{kL}⌋ mod 2^L = ws[k]` for words below `2^L`.
* `access_layout`, `access_tm`: **the machine returns `w_k`** on the compiled single-tape TM, in
  exactly `(3kL + 3)(2n + 2)` transitions, uniformly in the index `k`.
-/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-! ### The right shift -/

/-- The backward pass of the right shift: each cell takes the bit of the cell above it. -/
def fshr (b : Bool) (z : SCell) : SCell × Bool := (⟨b, z.c⟩, z.x)

theorem fscan_idS : ∀ (b : Bool) (l : List SCell), fscan (fun b x => (x, b)) b l = (l, b)
  | _, [] => rfl
  | b, x :: l => by simp only [fscan, fscan_idS b l]

theorem bscan_shr : ∀ (b : Bool) (l : List SCell),
    2 * val ((bscan fshr b l).1.map SCell.x) + (bscan fshr b l).2.toNat =
      vSx l + 2 ^ l.length * b.toNat
  | b, [] => by simp [bscan, val, vSx]
  | b, z :: l => by
    have ih := bscan_shr b l
    simp only [bscan, List.map_cons, val, List.length_cons, pow_succ, vSx, fshr] at ih ⊢
    linarith

theorem bscan_shr_c : ∀ (b : Bool) (l : List SCell),
    (bscan fshr b l).1.map SCell.c = l.map SCell.c
  | _, [] => rfl
  | b, z :: l => by simp only [bscan, List.map_cons, fshr, bscan_shr_c b l]

/-- **The single-trip right shift**: `x ↦ ⌊x/2⌋`, counter unchanged. -/
def shrProg : Prog where
  D := SCell
  I := AddI
  B := Bool
  lift b := ⟨b, false⟩
  start := .go
  init _ := false
  fwd _ := fun b x => (x, b)
  ext _ := fun _ => none
  bwd
    | .go => fshr
    | .done => fun b x => (x, b)
  next _ := fun _ => .inl .done

theorem shr_first (l : List SCell) :
    ReachFirst shrProg AddI.done (AddI.go, l) (bscan fshr false l).1 (2 * l.length + 2) := by
  have hs : shrProg.stepP (AddI.go, l) = .inl (AddI.done, (bscan fshr false l).1) := by
    simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, shrProg, fscan_idS]
  have h := ReachFirst.last (P := shrProg) (e := AddI.done) hs
  simpa [Prog.tripCost, Prog.fpass, shrProg] using h

theorem shr_value (l : List SCell) : vSx (bscan fshr false l).1 = vSx l / 2 := by
  have h := bscan_shr false l
  simp only [Bool.toNat_false, mul_zero, add_zero] at h
  unfold vSx at h ⊢
  have hb : (bscan fshr false l).2.toNat ≤ 1 := by cases (bscan fshr false l).2 <;> decide
  omega

/-! ### The right-shift loop -/

/-- The body: halve `x`, then decrement the counter. -/
def bodyR : ProgOn SCell := ProgOn.seq (ProgOn.ofProg shrProg) (ProgOn.ofProg decProg) AddI.done

/-- One body step on the tape. -/
def bodyRStep (l : List SCell) : List SCell := (fscan fdec true (bscan fshr false l).1).1

theorem bodyR_first (l : List SCell) :
    ReachFirst bodyR.toProg (Sum.inr AddI.done) (bodyR.start, l) (bodyRStep l)
      ((2 * l.length + 2) + (2 * l.length + 2)) := by
  have h1 := shr_first l
  have h2 := dec_first (bscan fshr false l).1
  rw [bscan_length] at h2
  exact ProgOn.seq_reachFirst (ProgOn.ofProg shrProg) (ProgOn.ofProg decProg) AddI.done
    (show AddI.go ≠ AddI.done by decide) h1 h2

theorem bodyRStep_length (l : List SCell) : (bodyRStep l).length = l.length := by
  unfold bodyRStep
  rw [fscan_length, bscan_length]

theorem bodyRStep_x (l : List SCell) : vSx (bodyRStep l) = vSx l / 2 := by
  have e : vSx (bodyRStep l) = vSx (bscan fshr false l).1 := by
    unfold vSx bodyRStep
    rw [fscan_dec_x]
  rw [e, shr_value]

theorem bodyRStep_c (l : List SCell) (hc : 0 < vSc l) : vSc (bodyRStep l) = vSc l - 1 := by
  have h := fscan_dec true (bscan fshr false l).1
  have hlt := val_lt ((fscan fdec true (bscan fshr false l).1).1.map SCell.c)
  rw [List.length_map, fscan_length, bscan_length] at hlt
  have hc' : vSc (bscan fshr false l).1 = vSc l := by unfold vSc; rw [bscan_shr_c]
  rw [hc', bscan_length, Bool.toNat_true] at h
  unfold bodyRStep
  show val ((fscan fdec true (bscan fshr false l).1).1.map SCell.c) = vSc l - 1
  cases hb : (fscan fdec true (bscan fshr false l).1).2
  · rw [hb, Bool.toNat_false, mul_zero, add_zero] at h
    omega
  · rw [hb, Bool.toNat_true, mul_one] at h
    omega

/-- **The right-shift loop**: test the counter; while it is nonzero, halve `x` and decrement. -/
def shrLoop : ProgOn SCell :=
  ProgOn.loop (ProgOn.ofProg testProg) bodyR TstI.yes (Sum.inr AddI.done)

theorem iterR_spec (l : List SCell) (W : ℕ) (hW : vSc l = W) :
    ∀ k ≤ W, (bodyRStep^[k] l).length = l.length ∧ vSc (bodyRStep^[k] l) = W - k ∧
      vSx (bodyRStep^[k] l) = vSx l / 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨rfl, by simp [hW], by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    refine ⟨by rw [bodyRStep_length, h1], ?_, ?_⟩
    · rw [bodyRStep_c _ (by rw [h2]; omega), h2]
      omega
    · rw [bodyRStep_x, h3, Nat.div_div_eq_div_mul, pow_succ]

/-- **Shift right by a binary counter.** From a tape of length `n` with counter value `s`, the
loop first-arrives at the test's `no` exit with `x = ⌊X/2^s⌋` and a zero counter, in exactly
`(3s + 1)(2n + 2)` transitions. -/
theorem shift_right_by_counter (l : List SCell) :
    ∃ l', ReachFirst shrLoop.toProg (Sum.inl TstI.no) (Sum.inl TstI.test, l) l'
        ((3 * vSc l + 1) * (2 * l.length + 2)) ∧
      vSx l' = vSx l / 2 ^ vSc l ∧ vSc l' = 0 ∧ l'.length = l.length := by
  set W := vSc l with hW
  obtain ⟨hlen, hc, hx⟩ := iterR_spec l W rfl W le_rfl
  refine ⟨bodyRStep^[W] l, ?_, hx, by rw [hc]; simp, hlen⟩
  have hr := ProgOn.loop_reachFirst (ProgOn.ofProg testProg) bodyR TstI.yes (Sum.inr AddI.done)
    (eF := TstI.no) (show TstI.test ≠ TstI.no by decide) (show TstI.no ≠ TstI.yes by decide) W
    (fun k => bodyRStep^[k] l) (fun k => bodyRStep^[k] l)
    (fun _ => (2 * l.length + 2) + (2 * l.length + 2)) (bodyRStep^[W] l)
    (fun k hk => by
      obtain ⟨_, hck, _⟩ := iterR_spec l W rfl k hk.le
      show testProg.stepP (TstI.test, bodyRStep^[k] l) = _
      rw [test_step, if_pos (by rw [hck]; omega)])
    (fun k hk => by
      obtain ⟨hlk, _, _⟩ := iterR_spec l W rfl k hk.le
      have hb := bodyR_first (bodyRStep^[k] l)
      rw [hlk, ← Function.iterate_succ_apply' bodyRStep k l] at hb
      exact hb)
    (by
      show testProg.stepP (TstI.test, bodyRStep^[W] l) = _
      rw [test_step, if_neg (by rw [hc]; simp)])
  have hcost : ∑ k ∈ Finset.range W, ((ProgOn.ofProg testProg).toProg.tripCost
        (ProgOn.ofProg testProg).start (bodyRStep^[k] l) +
          ((2 * l.length + 2) + (2 * l.length + 2))) +
        (ProgOn.ofProg testProg).toProg.tripCost (ProgOn.ofProg testProg).start
          (bodyRStep^[W] l) = (3 * W + 1) * (2 * l.length + 2) := by
    have hk : ∀ k ∈ Finset.range W, (ProgOn.ofProg testProg).toProg.tripCost
          (ProgOn.ofProg testProg).start (bodyRStep^[k] l) +
            ((2 * l.length + 2) + (2 * l.length + 2)) = 3 * (2 * l.length + 2) := by
      intro k hk
      obtain ⟨hlk, _, _⟩ := iterR_spec l W rfl k (Finset.mem_range.mp hk).le
      show testProg.tripCost TstI.test (bodyRStep^[k] l) + _ = _
      rw [test_cost, hlk]
      ring
    rw [Finset.sum_congr rfl hk, Finset.sum_const, Finset.card_range, smul_eq_mul]
    show _ + testProg.tripCost TstI.test (bodyRStep^[W] l) = _
    rw [test_cost, hlen]
    ring
  rw [hcost] at hr
  exact hr

/-! ### Masks and packed words -/

/-- **Masking with `2^L − 1`** keeps the residue modulo `2^L`. -/
theorem val_and_mask : ∀ (L : ℕ) (xs ms : List Bool), ms = bitsOf xs.length (2 ^ L - 1) →
    val (List.zipWith (· && ·) xs ms) = val xs % 2 ^ L
  | L, [], ms, hm => by
    rw [hm]
    simp [bitsOf, val]
  | L, x :: xs, ms, hm => by
    rw [hm, List.length_cons]
    rcases L with _ | L
    · have ih := val_and_mask 0 xs _ rfl
      have h0 : (2 : ℕ) ^ 0 - 1 = 0 := rfl
      rw [h0] at ih ⊢
      rw [pow_zero, Nat.mod_one] at ih ⊢
      simp only [bitsOf, Nat.zero_mod, Nat.zero_div, List.zipWith_cons_cons, val, ih]
      cases x <;> rfl
    · have ht : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have e1 : (2 ^ (L + 1) - 1) % 2 = 1 := by rw [pow_succ]; omega
      have e2 : (2 ^ (L + 1) - 1) / 2 = 2 ^ L - 1 := by rw [pow_succ]; omega
      have ih := val_and_mask L xs _ rfl
      simp only [bitsOf, e1, e2, List.zipWith_cons_cons, val, decide_true, Bool.and_true]
      rw [ih]
      have hx : x.toNat ≤ 1 := by cases x <;> decide
      have hdm := Nat.div_add_mod (val xs) (2 ^ L)
      have hr : val xs % 2 ^ L < 2 ^ L := Nat.mod_lt _ (by positivity)
      have e3 : x.toNat + 2 * val xs =
          (x.toNat + 2 * (val xs % 2 ^ L)) + 2 ^ (L + 1) * (val xs / 2 ^ L) := by
        rw [pow_succ]
        nlinarith
      have hlt : x.toNat + 2 * (val xs % 2 ^ L) < 2 ^ (L + 1) := by rw [pow_succ]; omega
      rw [e3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- A list of words packed into one number, `L` bits per word. -/
def pack (L : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: ws => w + 2 ^ L * pack L ws

/-- **Reading a packed word**: `⌊pack L ws / 2^{kL}⌋ mod 2^L = ws[k]` for words below `2^L`. -/
theorem pack_word (L : ℕ) : ∀ (ws : List ℕ) (k : ℕ) (hk : k < ws.length),
    (∀ w ∈ ws, w < 2 ^ L) → pack L ws / 2 ^ (k * L) % 2 ^ L = ws[k]
  | [], k, hk, _ => absurd hk (by simp)
  | w :: ws, 0, _, h => by
    have hw : w < 2 ^ L := h w (by simp)
    simp only [pack, zero_mul, pow_zero, Nat.div_one, List.getElem_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]
  | w :: ws, k + 1, hk, h => by
    have hw : w < 2 ^ L := h w (by simp)
    have ih := pack_word L ws k (by simpa using hk) (fun v hv => h v (by simp [hv]))
    have e : 2 ^ ((k + 1) * L) = 2 ^ L * 2 ^ (k * L) := by
      rw [← pow_add]; congr 1; ring
    simp only [pack, List.getElem_cons_succ]
    rw [e, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt hw, zero_add]
    exact ih

/-! ### The access machine -/

/-- Cells for word access: the shift tracks (work `x`, counter `c`), the vector `v` and the
mask `mk`. -/
structure ACell where
  s : SCell
  v : Bool
  mask : Bool
  deriving DecidableEq, Fintype

def lensAs : TrackLens ACell SCell := ⟨ACell.s, fun x s => ⟨s, x.v, x.mask⟩, fun _ _ => rfl⟩

/-- The fill cell, and raw input bits on the vector track. -/
def az : ACell := ⟨⟨false, false⟩, false, false⟩
def abit (b : Bool) : ACell := ⟨⟨false, false⟩, b, false⟩

/-- Copy the vector into the work track. -/
def copyF (x : ACell) : ACell := ⟨⟨x.v, x.s.c⟩, x.v, x.mask⟩

/-- Mask the work track. -/
def maskF (x : ACell) : ACell := ⟨⟨x.s.x && x.mask, x.s.c⟩, x.v, x.mask⟩

theorem shrLoop_ext : ∀ i b, shrLoop.ext i b = none := by
  intro i b
  rcases i with i | (i | i) <;> rcases b with b | (b | b) <;> rfl

def ACC1 : ProgOn ACell :=
  ProgOn.seq (ProgOn.ofProg (mapProg ACell copyF abit)) (shrLoop.viaLens lensAs az abit) AddI.done

/-- **The access machine**: copy, shift right by the counter, mask. -/
def accessProg : ProgOn ACell :=
  ProgOn.seq ACC1 (ProgOn.ofProg (mapProg ACell maskF abit)) (Sum.inr (Sum.inl TstI.no))

/-- **Word access on any tape.** On a tape of length `n` with vector value `V`, counter value
`s` and mask track `2^L − 1`, the machine first-arrives at its exit in exactly
`(3s + 3)(2n + 2)` transitions with work track `⌊V/2^s⌋ mod 2^L`. -/
theorem access_run (l : List ACell) (L : ℕ) (hm : l.map ACell.mask = bitsOf l.length (2 ^ L - 1)) :
    ∃ l', ReachFirst accessProg.toProg (Sum.inr AddI.done) (accessProg.start, l) l'
        ((3 * val (l.map (fun z => z.s.c)) + 3) * (2 * l.length + 2)) ∧
      val (l'.map (fun z => z.s.x)) = val (l.map ACell.v) / 2 ^ val (l.map (fun z => z.s.c)) % 2 ^ L ∧
      l'.map ACell.v = l.map ACell.v ∧ l'.map ACell.mask = l.map ACell.mask ∧
      l'.length = l.length := by
  -- copy
  have r1 := map_first copyF abit l
  -- shift right
  obtain ⟨s', hs, hsx, _, hslen⟩ := shift_right_by_counter ((l.map copyF).map lensAs.get)
  have hvx : vSx ((l.map copyF).map lensAs.get) = val (l.map ACell.v) := by
    unfold vSx; rw [List.map_map, List.map_map]; rfl
  have hvc : vSc ((l.map copyF).map lensAs.get) = val (l.map (fun z => z.s.c)) := by
    unfold vSc; rw [List.map_map, List.map_map]; rfl
  rw [hvx, hvc] at hsx
  rw [hvc, List.length_map, List.length_map] at hs
  obtain ⟨l2, r2, v2⟩ := ProgOn.reachFirst_lens shrLoop lensAs az abit hs (l.map copyF) rfl
  have k2 : l2.map (fun z => z.mask) = (l.map copyF).map (fun z => z.mask) :=
    ProgOn.reachFirst_lens_frame shrLoop lensAs az abit shrLoop_ext
      (ℓ₂ := ⟨ACell.mask, fun x b => ⟨x.s, x.v, b⟩, fun _ _ => rfl⟩) (fun _ _ => rfl) r2
  have kv : l2.map (fun z => z.v) = (l.map copyF).map (fun z => z.v) :=
    ProgOn.reachFirst_lens_frame shrLoop lensAs az abit shrLoop_ext
      (ℓ₂ := ⟨ACell.v, fun x b => ⟨x.s, b, x.mask⟩, fun _ _ => rfl⟩) (fun _ _ => rfl) r2
  have hl2 : l2.length = l.length := by
    have := congrArg List.length k2
    simpa using this
  -- mask
  have r3 := map_first maskF abit l2
  have hc := ProgOn.seq_reachFirst ACC1 (ProgOn.ofProg (mapProg ACell maskF abit))
    (Sum.inr (Sum.inl TstI.no)) (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst (ProgOn.ofProg (mapProg ACell copyF abit)) (shrLoop.viaLens lensAs az abit)
      AddI.done (show (Sum.inl TstI.test : TstI ⊕ (AddI ⊕ AddI)) ≠ Sum.inl TstI.no by decide) r1 r2)
    r3
  rw [hl2] at hc
  refine ⟨l2.map maskF, ?_, ?_, ?_, ?_, by rw [List.length_map, hl2]⟩
  · convert hc using 1
    ring
  · have e1 : (l2.map maskF).map (fun z => z.s.x) =
        List.zipWith (· && ·) (l2.map (fun z => z.s.x)) (l2.map (fun z => z.mask)) := by
      clear r2 v2 k2 kv hl2 hc r3
      induction l2 with
      | nil => rfl
      | cons z l ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]; rfl
    have e2 : l2.map (fun z => z.s.x) = s'.map SCell.x := by
      rw [← v2, List.map_map]; rfl
    have e3 : l2.map (fun z => z.mask) = bitsOf (l2.map (fun z => z.s.x)).length (2 ^ L - 1) := by
      rw [k2, List.map_map, List.length_map, hl2]
      exact hm
    have key : val ((l2.map maskF).map (fun z => z.s.x)) =
        val (l.map ACell.v) / 2 ^ val (l.map (fun z => z.s.c)) % 2 ^ L := by
      rw [e1, val_and_mask L _ _ e3, e2]
      show vSx s' % 2 ^ L = _
      rw [hsx]
    exact key
  · have e : (l2.map maskF).map ACell.v = l2.map (fun z => z.v) := by rw [List.map_map]; rfl
    rw [e, kv, List.map_map]
    rfl
  · have e : (l2.map maskF).map ACell.mask = l2.map (fun z => z.mask) := by
      rw [List.map_map]; rfl
    rw [e, k2, List.map_map]
    rfl

/-! ### The layout and the compiled machine -/

/-- Three tracks zipped into access cells, with a zero work track. -/
def mkA : List Bool → List Bool → List Bool → List ACell
  | v :: vs, c :: cs, m :: ms => ⟨⟨false, c⟩, v, m⟩ :: mkA vs cs ms
  | _, _, _ => []

theorem mkA_spec : ∀ (vs cs ms : List Bool), cs.length = vs.length → ms.length = vs.length →
    (mkA vs cs ms).map ACell.v = vs ∧ (mkA vs cs ms).map (fun z => z.s.c) = cs ∧
      (mkA vs cs ms).map ACell.mask = ms ∧ (mkA vs cs ms).length = vs.length
  | [], [], [], _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | [], _ :: _, _, h, _ => by simp at h
  | [], [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | v :: vs, c :: cs, m :: ms, hc, hm => by
    obtain ⟨h1, h2, h3, h4⟩ := mkA_spec vs cs ms (by simpa using hc) (by simpa using hm)
    simp [mkA, h1, h2, h3, h4]

/-- The access layout on `n` cells: the packed vector, the offset `kL` and the mask `2^L − 1`,
in binary. -/
def accessInput (n L : ℕ) (ws : List ℕ) (k : ℕ) : List ACell :=
  mkA (bitsOf n (pack L ws)) (bitsOf n (k * L)) (bitsOf n (2 ^ L - 1))

/-- **Uniform access to a packed word on the compiled Turing machine.** For words `ws` below
`2^L`, an index `k < |ws|`, and a tape of `n` cells that holds the packed vector and the offset
`kL`, the compiled single-tape TM returns the word `ws[k]` on its work track. It takes exactly
`(3kL + 3)(2n + 2)` transitions. -/
theorem access_tm {n L k : ℕ} {ws : List ℕ} (hk : k < ws.length) (hw : ∀ w ∈ ws, w < 2 ^ L)
    (hpack : pack L ws < 2 ^ n) (hkL : k * L < 2 ^ n) (T : ℤ → Sym ACell)
    (hT : accessProg.toProg.Repr T (accessInput n L ws k)) :
    ∃ l' T', accessProg.toProg.Repr T' l' ∧ val (l'.map (fun z => z.s.x)) = ws[k] ∧
      accessProg.toProg.toTM.run
          ⟨.fwd accessProg.start (accessProg.toProg.init accessProg.start), T, 0⟩
          ((3 * (k * L) + 3) * (2 * n + 2)) =
        ⟨.fwd (Sum.inr AddI.done) (accessProg.toProg.init (Sum.inr AddI.done)), T', 0⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := mkA_spec (bitsOf n (pack L ws)) (bitsOf n (k * L))
    (bitsOf n (2 ^ L - 1)) (by simp [bitsOf_length]) (by simp [bitsOf_length])
  rw [bitsOf_length] at h4
  have hv : val ((accessInput n L ws k).map ACell.v) = pack L ws := by
    unfold accessInput; rw [h1, val_bitsOf, Nat.mod_eq_of_lt hpack]
  have hc : val ((accessInput n L ws k).map (fun z => z.s.c)) = k * L := by
    unfold accessInput; rw [h2, val_bitsOf, Nat.mod_eq_of_lt hkL]
  have hm : (accessInput n L ws k).map ACell.mask =
      bitsOf (accessInput n L ws k).length (2 ^ L - 1) := by
    unfold accessInput; rw [h3, h4]
  obtain ⟨l', hr, hx, -, -, -⟩ := access_run (accessInput n L ws k) L hm
  have hlen : (accessInput n L ws k).length = n := by unfold accessInput; exact h4
  rw [hc, hlen] at hr
  rw [hv, hc, pack_word L ws k hk hw] at hx
  obtain ⟨T', hT', hrun⟩ := accessProg.toProg.reach_run hr.reach T hT
  exact ⟨l', T', hT', hx, hrun⟩

end PVNP.Discrete.SweepArith
