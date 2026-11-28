import PVNP.SweepComplex

/-!
# Signed fixed-point division with certified rounding

Signed division runs as one Turing machine, a four-stage composite of verified programs on the
common alphabet `SDCell`. That alphabet is the divider's four tracks plus two sign flags.

1. `NEGN`: record the sign of the dividend on the flag `fn` of every cell, then negate the
   dividend where `fn` is set. The dividend track then holds `|N|·2^p`.
2. `NEGD`: the same for the divisor and the flag `fd`. The divisor track then holds `|D|·2^W`.
3. `DIVS`: the verified long-division machine on the four division tracks. The quotient track
   holds `|N|·2^p / |D|` and the remainder track holds `|N|·2^p mod |D|`.
4. `FIXQ`: negate the quotient where `fn ≠ fd`.

Stages 1, 2 and 4 are instances of one conditional-negation transducer (`fnegBy`), seen through
three track lenses. The stages are chained by `ProgOn.seq_reachFirst`, and frame preservation
along independent lenses keeps the other tracks unchanged.

* `cneg_first`, `cneg_spec`: the sign-and-negate program first-arrives in two trips. On a word
  read in two's complement it leaves the absolute value and writes the sign bit on every cell.
* `fix_first`, `fix_spec`: the single-trip sign correction.
* `tc_neg`, `cneg_abs`, `tc_mul_pow`: two's-complement negation, absolute values from codes, and
  the placement of a code shifted by `p` places.
* `tdiv_cases`, `sdiv_certified`: truncated division `Int.tdiv` by signs and magnitudes, and the
  certificate `|tdiv(N·2^p, D)/2^p − N/D| < 2^{−p}`.
* `sdiv_layout`: on the explicit layout `sdivInput`, the composite first-arrives at its exit in
  exactly `(W + 7)(4W + 2)` transitions. The quotient track, read in `2W`-bit two's complement,
  is `tdiv(N·2^p, D)`. The remainder track is `|tmod(N·2^p, D)|`.
* `sdiv_tm`: **signed fixed-point division with certified rounding on the compiled TM**.
-/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-! ### Conditional two's-complement negation -/

/-- A word track `w` and two flag tracks `f`, `g`. -/
structure NCell where
  w : Bool
  f : Bool
  g : Bool
  deriving DecidableEq, Fintype

def vW (l : List NCell) : ℕ := val (l.map NCell.w)

/-- One cell of negation, enabled where `p` holds: invert the bit and add the carry. -/
def fnegBy (p : NCell → Bool) (c : Bool) (z : NCell) : NCell × Bool :=
  if p z then (⟨xor (!z.w) c, z.f, z.g⟩, (!z.w) && c) else (z, c)

theorem fnegBy_w (p : NCell → Bool) (c : Bool) (z : NCell) (hz : p z = true) :
    (fnegBy p c z).1.w.toNat + 2 * (fnegBy p c z).2.toNat + z.w.toNat = 1 + c.toNat := by
  simp only [fnegBy, hz, if_true]
  cases z.w <;> cases c <;> rfl

theorem fscan_negBy_on (p : NCell → Bool) : ∀ (c : Bool) (l : List NCell),
    (∀ z ∈ l, p z = true) →
      vW (fscan (fnegBy p) c l).1 + 2 ^ l.length * (fscan (fnegBy p) c l).2.toNat + vW l + 1 =
        2 ^ l.length + c.toNat
  | c, [], _ => by simp [fscan, vW, val]; omega
  | c, z :: l, h => by
    have hz : p z = true := h z (by simp)
    have ih := fscan_negBy_on p (fnegBy p c z).2 l (fun y hy => h y (by simp [hy]))
    have hw := fnegBy_w p c z hz
    simp only [fscan, vW, List.map_cons, val, List.length_cons, pow_succ] at ih ⊢
    linarith

theorem fscan_negBy_off (p : NCell → Bool) : ∀ (c : Bool) (l : List NCell),
    (∀ z ∈ l, p z = false) → fscan (fnegBy p) c l = (l, c)
  | _, [], _ => rfl
  | c, z :: l, h => by
    have hz : p z = false := h z (by simp)
    have ih := fscan_negBy_off p c l (fun y hy => h y (by simp [hy]))
    have e : fnegBy p c z = (z, c) := by simp [fnegBy, hz]
    simp only [fscan, e, ih]

theorem fscan_negBy_f (p : NCell → Bool) : ∀ (c : Bool) (l : List NCell),
    (fscan (fnegBy p) c l).1.map NCell.f = l.map NCell.f
  | _, [] => rfl
  | c, z :: l => by
    have ih := fscan_negBy_f p (fnegBy p c z).2 l
    have e : (fnegBy p c z).1.f = z.f := by unfold fnegBy; split <;> rfl
    simp only [fscan, List.map_cons, ih, e]

theorem fscan_negBy_g (p : NCell → Bool) : ∀ (c : Bool) (l : List NCell),
    (fscan (fnegBy p) c l).1.map NCell.g = l.map NCell.g
  | _, [] => rfl
  | c, z :: l => by
    have ih := fscan_negBy_g p (fnegBy p c z).2 l
    have e : (fnegBy p c z).1.g = z.g := by unfold fnegBy; split <;> rfl
    simp only [fscan, List.map_cons, ih, e]

/-- **Negation of an enabled word**: with carry-in `1`, the word becomes `(2ⁿ − w) mod 2ⁿ`. -/
theorem negBy_value (p : NCell → Bool) (l : List NCell) (h : ∀ z ∈ l, p z = true) :
    vW (fscan (fnegBy p) true l).1 = (2 ^ l.length - vW l) % 2 ^ l.length := by
  have e := fscan_negBy_on p true l h
  have hlt : vW (fscan (fnegBy p) true l).1 < 2 ^ l.length := by
    have := val_lt ((fscan (fnegBy p) true l).1.map NCell.w)
    rwa [List.length_map, fscan_length] at this
  simp only [Bool.toNat_true] at e
  have e' : 2 ^ l.length - vW l =
      vW (fscan (fnegBy p) true l).1 + 2 ^ l.length * (fscan (fnegBy p) true l).2.toNat := by
    omega
  rw [e', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ### The sign-and-negate program -/

inductive NegI | sgn | neg | done
  deriving DecidableEq, Fintype

/-- The forward pass of `sgn`: carry the last bit seen. -/
def fsgn (_ : Bool) (z : NCell) : NCell × Bool := (z, z.w)

/-- The backward pass of `sgn`: write the recorded bit on the flag `f`. -/
def bset (s : Bool) (z : NCell) : NCell × Bool := (⟨z.w, s, z.g⟩, s)

/-- Set the flag `f` of every cell to `s`. -/
def setF (s : Bool) (l : List NCell) : List NCell := l.map (fun z => ⟨z.w, s, z.g⟩)

/-- The top bit of a word (`b` for the empty word). -/
def lastW : Bool → List NCell → Bool
  | b, [] => b
  | _, z :: l => lastW z.w l

/-- **Sign and negate**: record the top bit of `w` on `f` in one trip, then negate `w` where `f`
is set. -/
def cnegProg : Prog where
  D := NCell
  I := NegI
  B := Bool
  lift b := ⟨b, false, false⟩
  start := .sgn
  init
    | .neg => true
    | _ => false
  fwd
    | .sgn => fsgn
    | .neg => fnegBy NCell.f
    | .done => fun c z => (z, c)
  ext _ := fun _ => none
  bwd
    | .sgn => bset
    | _ => fun b z => (z, b)
  next
    | .sgn => fun _ => .inl .neg
    | _ => fun _ => .inl .done

theorem fscan_sgn : ∀ (b : Bool) (l : List NCell), fscan fsgn b l = (l, lastW b l)
  | _, [] => rfl
  | b, z :: l => by simp only [fscan, fsgn, fscan_sgn z.w l, lastW]

theorem bscan_set : ∀ (s : Bool) (l : List NCell), bscan bset s l = (setF s l, s)
  | _, [] => rfl
  | s, z :: l => by simp only [bscan, bscan_set s l, bset, setF, List.map_cons]

theorem setF_length (s : Bool) (l : List NCell) : (setF s l).length = l.length := by
  simp [setF]

theorem vW_setF (s : Bool) (l : List NCell) : vW (setF s l) = vW l := by
  simp [vW, setF, List.map_map, Function.comp_def]

/-- The top bit of a nonempty word is set exactly when its value is at least `2^{n−1}`. -/
theorem lastW_eq : ∀ (b : Bool) (l : List NCell), l ≠ [] →
    lastW b l = decide (2 ^ (l.length - 1) ≤ vW l)
  | _, [], h => absurd rfl h
  | b, [z], _ => by
    show z.w = decide (2 ^ 0 ≤ z.w.toNat + 2 * 0)
    cases z.w <;> rfl
  | b, z :: y :: l, _ => by
    have ih := lastW_eq z.w (y :: l) (List.cons_ne_nil _ _)
    show lastW z.w (y :: l) = _
    rw [ih]
    have hx : z.w.toNat ≤ 1 := by cases z.w <;> decide
    have e1 : (y :: l).length - 1 = l.length := by simp
    have e2 : (z :: y :: l).length - 1 = l.length + 1 := by simp
    have e3 : vW (z :: y :: l) = z.w.toNat + 2 * vW (y :: l) := rfl
    rw [e1, e2, e3, pow_succ]
    apply decide_eq_decide.mpr
    omega

theorem cneg_step1 (l : List NCell) :
    cnegProg.stepP (NegI.sgn, l) = .inl (NegI.neg, setF (lastW false l) l) := by
  simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, cnegProg, fscan_sgn, bscan_set]

theorem cneg_step2 (l : List NCell) :
    cnegProg.stepP (NegI.neg, l) = .inl (NegI.done, (fscan (fnegBy NCell.f) true l).1) := by
  simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, cnegProg, bscan_id]

/-- The sign-and-negate program first-arrives at `done` in two trips. -/
theorem cneg_first (l : List NCell) :
    ReachFirst cnegProg NegI.done (NegI.sgn, l)
      (fscan (fnegBy NCell.f) true (setF (lastW false l) l)).1
      ((2 * l.length + 2) + (2 * l.length + 2)) := by
  have h2 := ReachFirst.last (P := cnegProg) (e := NegI.done)
    (cneg_step2 (setF (lastW false l) l))
  have h1 := ReachFirst.step (P := cnegProg) (e := NegI.done) (cneg_step1 l) (by intro h; cases h) h2
  have c1 : cnegProg.tripCost NegI.sgn l = 2 * l.length + 2 := by
    simp [Prog.tripCost, cnegProg]
  have c2 : cnegProg.tripCost NegI.neg (setF (lastW false l) l) = 2 * l.length + 2 := by
    simp [Prog.tripCost, cnegProg, setF_length]
  have e : cnegProg.tripCost (NegI.sgn, l).1 (NegI.sgn, l).2 +
      cnegProg.tripCost (NegI.neg, setF (lastW false l) l).1
        (NegI.neg, setF (lastW false l) l).2 = (2 * l.length + 2) + (2 * l.length + 2) := by
    simp only [c1, c2]
  rw [e] at h1
  exact h1

/-- **What sign-and-negate computes.** With `s` the top bit of `w`: the word becomes
`(2ⁿ − w) mod 2ⁿ` if `s` is set and is unchanged otherwise; every flag `f` becomes `s`; the
flags `g` are unchanged. -/
theorem cneg_spec (l : List NCell) (hl : l ≠ []) :
    vW (fscan (fnegBy NCell.f) true (setF (lastW false l) l)).1 =
        (if 2 ^ (l.length - 1) ≤ vW l then (2 ^ l.length - vW l) % 2 ^ l.length else vW l) ∧
      (fscan (fnegBy NCell.f) true (setF (lastW false l) l)).1.map NCell.f =
        l.map (fun _ => decide (2 ^ (l.length - 1) ≤ vW l)) ∧
      (fscan (fnegBy NCell.f) true (setF (lastW false l) l)).1.map NCell.g = l.map NCell.g ∧
      (fscan (fnegBy NCell.f) true (setF (lastW false l) l)).1.length = l.length := by
  rw [lastW_eq false l hl]
  set s := decide (2 ^ (l.length - 1) ≤ vW l) with hs
  have hf : (setF s l).map NCell.f = l.map (fun _ => s) := by
    simp [setF, List.map_map, Function.comp_def]
  have hg : (setF s l).map NCell.g = l.map NCell.g := by
    simp [setF, List.map_map, Function.comp_def]
  refine ⟨?_, by rw [fscan_negBy_f, hf], by rw [fscan_negBy_g, hg],
    by rw [fscan_length, setF_length]⟩
  by_cases h : 2 ^ (l.length - 1) ≤ vW l
  · have hs1 : s = true := by rw [hs]; exact decide_eq_true h
    rw [if_pos h, hs1, negBy_value NCell.f (setF true l) (by simp [setF]), vW_setF, setF_length]
  · have hs0 : s = false := by rw [hs]; exact decide_eq_false h
    rw [if_neg h, hs0, fscan_negBy_off NCell.f true (setF false l) (by simp [setF]), vW_setF]

/-! ### The sign correction -/

/-- **Sign correction**: negate `w` where the flags differ, in one trip. -/
def fixProg : Prog where
  D := NCell
  I := AddI
  B := Bool
  lift b := ⟨b, false, false⟩
  start := .go
  init _ := true
  fwd
    | .go => fnegBy (fun z => xor z.f z.g)
    | .done => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun _ => .inl .done

theorem fix_first (l : List NCell) :
    ReachFirst fixProg AddI.done (AddI.go, l) (fscan (fnegBy (fun z => xor z.f z.g)) true l).1
      (2 * l.length + 2) := by
  have hs : fixProg.stepP (AddI.go, l) =
      .inl (AddI.done, (fscan (fnegBy (fun z => xor z.f z.g)) true l).1) := by
    simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, fixProg, bscan_id]
  have h := ReachFirst.last (P := fixProg) (e := AddI.done) hs
  simpa [Prog.tripCost, Prog.fpass, fixProg] using h

/-- **What the sign correction computes**, for uniform flags `f = a` and `g = b`. -/
theorem fix_spec (l : List NCell) (a b : Bool) (ha : ∀ z ∈ l, z.f = a) (hb : ∀ z ∈ l, z.g = b) :
    vW (fscan (fnegBy (fun z => xor z.f z.g)) true l).1 =
      if xor a b then (2 ^ l.length - vW l) % 2 ^ l.length else vW l := by
  by_cases hx : xor a b = true
  · rw [if_pos hx, negBy_value _ l (fun z hz => by rw [ha z hz, hb z hz]; exact hx)]
  · rw [if_neg hx, fscan_negBy_off _ true l (fun z hz => by
      rw [ha z hz, hb z hz]; simpa using hx)]

/-! ### Two's complement: negation, absolute values and placement -/

/-- **Two's-complement negation of a code.** -/
theorem tc_neg (n : ℕ) (x : ℤ) : (2 ^ n - tc n x) % 2 ^ n = tc n (-x) := by
  have hA := tc_cast n x
  have hlt := tc_lt n x
  have h : (((2 ^ n - tc n x) % 2 ^ n : ℕ) : ℤ) = ((tc n (-x) : ℕ) : ℤ) := by
    rw [tc_cast]
    push_cast [Nat.cast_sub hlt.le]
    rw [hA, Int.emod_def x (2 ^ n)]
    have e : (2 : ℤ) ^ n - (x - 2 ^ n * (x / 2 ^ n)) = -x + 2 ^ n * (1 + x / 2 ^ n) := by ring
    rw [e, Int.add_mul_emod_self_left]
  exact_mod_cast h

/-- **Sign and negate on a code returns the absolute value.** For `x` in the `n`-bit range, the
top bit of its code is set exactly when `x < 0`, and negating the code in that case gives
`|x|`. -/
theorem cneg_abs (n : ℕ) (hn : 0 < n) (x : ℤ) (h1 : -(2 : ℤ) ^ (n - 1) ≤ x)
    (h2 : x < 2 ^ (n - 1)) :
    (if 2 ^ (n - 1) ≤ tc n x then (2 ^ n - tc n x) % 2 ^ n else tc n x) = x.natAbs ∧
      (2 ^ (n - 1) ≤ tc n x ↔ x < 0) := by
  have hsv := sval_tc n hn x h1 h2
  have hneg : 2 ^ (n - 1) ≤ tc n x ↔ x < 0 := by
    rw [← sval_neg_iff n _ (tc_lt n x), hsv]
  refine ⟨?_, hneg⟩
  have hn' : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : (0 : ℤ) < 2 ^ (n - 1) := by positivity
  by_cases hx : x < 0
  · rw [if_pos (hneg.mpr hx), tc_neg]
    have hm : (-x) % 2 ^ n = -x := Int.emod_eq_of_lt (by linarith) (by rw [hn']; linarith)
    have h3 : ((tc n (-x) : ℕ) : ℤ) = ((x.natAbs : ℕ) : ℤ) := by
      rw [tc_cast, hm]
      omega
    exact_mod_cast h3
  · rw [if_neg (fun h => hx (hneg.mp h))]
    push_neg at hx
    have hm : x % 2 ^ n = x := Int.emod_eq_of_lt hx (by rw [hn']; linarith)
    have h3 : ((tc n x : ℕ) : ℤ) = ((x.natAbs : ℕ) : ℤ) := by
      rw [tc_cast, hm]
      omega
    exact_mod_cast h3

/-- **Placement**: the code of `x·2^p` is the `(n − p)`-bit code of `x` shifted by `p` places.
The signed-division layout is therefore a placement of codes, as in the unsigned layout. -/
theorem tc_mul_pow (n p : ℕ) (hp : p ≤ n) (x : ℤ) :
    tc n (x * 2 ^ p) = tc (n - p) x * 2 ^ p := by
  have h : ((tc n (x * 2 ^ p) : ℕ) : ℤ) = ((tc (n - p) x * 2 ^ p : ℕ) : ℤ) := by
    push_cast
    rw [tc_cast, tc_cast]
    have hn : (2 : ℤ) ^ n = 2 ^ p * 2 ^ (n - p) := by rw [← pow_add, Nat.add_sub_cancel' hp]
    rw [hn, mul_comm x, Int.mul_emod_mul_of_pos _ _ (by positivity), mul_comm]
  exact_mod_cast h

/-! ### Truncated division -/

/-- **Truncated division by signs and magnitudes.** -/
theorem tdiv_cases (x d : ℤ) :
    Int.tdiv x d = if xor (decide (x < 0)) (decide (d < 0)) then
      -((x.natAbs / d.natAbs : ℕ) : ℤ) else ((x.natAbs / d.natAbs : ℕ) : ℤ) := by
  rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 d with hd | hd
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [decide_eq_false (by omega : ¬((a : ℤ) < 0)), decide_eq_false (by omega : ¬((b : ℤ) < 0))]
    rw [if_neg (by decide), Int.natAbs_natCast, Int.natAbs_natCast, Int.ofNat_tdiv]
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    obtain ⟨b, rfl⟩ := Int.exists_eq_neg_ofNat hd.le
    rw [decide_eq_false (by omega : ¬((a : ℤ) < 0)), decide_eq_true hd]
    rw [if_pos (by decide), Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast,
      Int.tdiv_neg, Int.ofNat_tdiv]
  · obtain ⟨a, rfl⟩ := Int.exists_eq_neg_ofNat hx.le
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [decide_eq_true hx, decide_eq_false (by omega : ¬((b : ℤ) < 0))]
    rw [if_pos (by decide), Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_natCast,
      Int.neg_tdiv, Int.ofNat_tdiv]
  · obtain ⟨a, rfl⟩ := Int.exists_eq_neg_ofNat hx.le
    obtain ⟨b, rfl⟩ := Int.exists_eq_neg_ofNat hd.le
    rw [decide_eq_true hx, decide_eq_true hd]
    rw [if_neg (by decide), Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_natCast,
      Int.natAbs_natCast, Int.neg_tdiv_neg, Int.ofNat_tdiv]

/-- **The certificate.** Truncated division is within one unit in the last place:
`|tdiv(N·2^p, D)/2^p − N/D| < 2^{−p}`. -/
theorem sdiv_certified (N D : ℤ) (p : ℕ) (hD : D ≠ 0) :
    |((Int.tdiv (N * 2 ^ p) D : ℤ) : ℚ) / 2 ^ p - (N : ℚ) / D| < 1 / 2 ^ p := by
  have hqr := Int.tdiv_add_tmod (N * 2 ^ p) D
  have hr : (Int.tmod (N * 2 ^ p) D).natAbs < D.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_lt _ (Int.natAbs_pos.mpr hD)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hP : (0 : ℚ) < 2 ^ p := by positivity
  have hqr' : (D : ℚ) * (Int.tdiv (N * 2 ^ p) D : ℚ) + (Int.tmod (N * 2 ^ p) D : ℚ) =
      (N : ℚ) * 2 ^ p := by exact_mod_cast hqr
  have e : ((Int.tdiv (N * 2 ^ p) D : ℤ) : ℚ) / 2 ^ p - (N : ℚ) / D =
      -((Int.tmod (N * 2 ^ p) D : ℤ) : ℚ) / (2 ^ p * D) := by
    rw [div_sub_div _ _ (ne_of_gt hP) hDq]
    congr 1
    linarith
  have hrD : |((Int.tmod (N * 2 ^ p) D : ℤ) : ℚ)| < |(D : ℚ)| := by
    have h1 : |Int.tmod (N * 2 ^ p) D| < |D| := by
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
      exact_mod_cast hr
    exact_mod_cast h1
  rw [e, abs_div, abs_neg, abs_mul, abs_of_pos hP, div_lt_div_iff₀ (by positivity) hP]
  nlinarith

/-! ### The common alphabet for signed division -/

/-- Cells for signed division: the divider's four tracks and the two sign flags. -/
structure SDCell where
  c : DCell
  fn : Bool
  fd : Bool
  deriving DecidableEq, Fintype

/-- The divider's view. -/
def lensDv : TrackLens SDCell DCell := ⟨SDCell.c, fun x c => { x with c := c }, fun _ _ => rfl⟩

/-- Sign and negate the dividend: word `n`, flag `fn`, other flag `fd`. -/
def lensNn : TrackLens SDCell NCell where
  get x := ⟨x.c.n, x.fn, x.fd⟩
  put x y := ⟨⟨y.w, x.c.d, x.c.q, x.c.m⟩, y.f, y.g⟩
  get_put _ _ := rfl

/-- Sign and negate the divisor: word `d`, flag `fd`, other flag `fn`. -/
def lensNd : TrackLens SDCell NCell where
  get x := ⟨x.c.d, x.fd, x.fn⟩
  put x y := ⟨⟨x.c.n, y.w, x.c.q, x.c.m⟩, y.g, y.f⟩
  get_put _ _ := rfl

/-- Correct the sign of the quotient: word `q`, flags `fn` and `fd`. -/
def lensNq : TrackLens SDCell NCell where
  get x := ⟨x.c.q, x.fn, x.fd⟩
  put x y := ⟨⟨x.c.n, x.c.d, y.w, x.c.m⟩, y.f, y.g⟩
  get_put _ _ := rfl

/-- Single tracks and the flag pair, for frames. -/
def lensTn : TrackLens SDCell Bool :=
  ⟨fun x => x.c.n, fun x b => ⟨⟨b, x.c.d, x.c.q, x.c.m⟩, x.fn, x.fd⟩, fun _ _ => rfl⟩
def lensTd : TrackLens SDCell Bool :=
  ⟨fun x => x.c.d, fun x b => ⟨⟨x.c.n, b, x.c.q, x.c.m⟩, x.fn, x.fd⟩, fun _ _ => rfl⟩
def lensTq : TrackLens SDCell Bool :=
  ⟨fun x => x.c.q, fun x b => ⟨⟨x.c.n, x.c.d, b, x.c.m⟩, x.fn, x.fd⟩, fun _ _ => rfl⟩
def lensTm : TrackLens SDCell Bool :=
  ⟨fun x => x.c.m, fun x b => ⟨⟨x.c.n, x.c.d, x.c.q, b⟩, x.fn, x.fd⟩, fun _ _ => rfl⟩
def lensFl : TrackLens SDCell (Bool × Bool) :=
  ⟨fun x => (x.fn, x.fd), fun x b => ⟨x.c, b.1, b.2⟩, fun _ _ => rfl⟩

/-- The fill cell. No stage extends the tape. -/
def zS : SDCell := ⟨⟨false, false, false, false⟩, false, false⟩

/-- Raw input bits enter the dividend track. -/
def sbit (b : Bool) : SDCell := ⟨⟨b, false, false, false⟩, false, false⟩

def NEGN : ProgOn SDCell := (ProgOn.ofProg cnegProg).viaLens lensNn zS sbit
def NEGD : ProgOn SDCell := (ProgOn.ofProg cnegProg).viaLens lensNd zS sbit
def DIVS : ProgOn SDCell := (ProgOn.ofProg divProg).viaLens lensDv zS sbit
def FIXQ : ProgOn SDCell := (ProgOn.ofProg fixProg).viaLens lensNq zS sbit

/-- The first two stages. -/
def NN : ProgOn SDCell := ProgOn.seq NEGN NEGD NegI.done

/-- The first three stages. -/
def NND : ProgOn SDCell := ProgOn.seq NN DIVS (Sum.inr NegI.done)

/-- **The signed divider**: sign and negate the dividend, then the divisor; divide; correct the
sign of the quotient. -/
def sdivProg : ProgOn SDCell := ProgOn.seq NND FIXQ (Sum.inr DivI.done)

/-! ### One stage on the common alphabet -/

/-- **A sign-and-negate stage** along a lens, with its frame. -/
theorem stage_cneg (ℓ : TrackLens SDCell NCell) (l : List SDCell) :
    ∃ l', ReachFirst ((ProgOn.ofProg cnegProg).viaLens ℓ zS sbit).toProg NegI.done
        (NegI.sgn, l) l' ((2 * l.length + 2) + (2 * l.length + 2)) ∧
      l'.map ℓ.get =
        (fscan (fnegBy NCell.f) true (setF (lastW false (l.map ℓ.get)) (l.map ℓ.get))).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens SDCell D₂), ℓ.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := cneg_first (l.map ℓ.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg cnegProg) ℓ zS sbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg cnegProg) ℓ zS sbit (fun _ _ => rfl) hi hr'

/-- **The division stage**, with its frame. -/
theorem stage_div (l : List SDCell) (hl : l ≠ []) (K D : ℕ) (hD : 0 < D)
    (hd : vD (l.map lensDv.get) = D * 2 ^ K) (hm : vM (l.map lensDv.get) = 2 ^ K)
    (hq : vQ (l.map lensDv.get) = 0) (hlt : vN (l.map lensDv.get) < 2 * (D * 2 ^ K)) :
    ∃ l', ReachFirst DIVS.toProg DivI.done (DivI.prep, l) l' ((K + 2) * (2 * l.length + 2)) ∧
      vQ (l'.map lensDv.get) = vN (l.map lensDv.get) / D ∧
      vN (l'.map lensDv.get) = vN (l.map lensDv.get) % D ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens SDCell D₂), lensDv.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  obtain ⟨m, hr, hq', hn'⟩ :=
    div_reach_first (l.map lensDv.get) (by simpa using hl) K D hD hd hm hq hlt
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg divProg) lensDv zS sbit hr l rfl
  refine ⟨l', hr', by rw [hv]; exact hq', by rw [hv]; exact hn', fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg divProg) lensDv zS sbit (fun _ _ => rfl) hi hr'

/-- **The sign-correction stage**, with its frame. -/
theorem stage_fix (l : List SDCell) :
    ∃ l', ReachFirst FIXQ.toProg AddI.done (AddI.go, l) l' (2 * l.length + 2) ∧
      l'.map lensNq.get = (fscan (fnegBy (fun z => xor z.f z.g)) true (l.map lensNq.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens SDCell D₂), lensNq.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := fix_first (l.map lensNq.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg fixProg) lensNq zS sbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg fixProg) lensNq zS sbit (fun _ _ => rfl) hi hr'

/-! ### The layout -/

/-- The signed-division layout on `2W` cells: the `2W`-bit codes of `N·2^p` (dividend) and `D·2^W`
(divisor), quotient `0`, marker `2^W`, clear sign flags. By `tc_mul_pow` the two codes are the
codes of `N` and `D` placed at offsets `p` and `W`. -/
def sdivInput (W p : ℕ) (N D : ℤ) : List SDCell :=
  (mkCells (bitsOf (2 * W) (tc (2 * W) (N * 2 ^ p))) (bitsOf (2 * W) (tc (2 * W) (D * 2 ^ W)))
    (bitsOf (2 * W) 0) (bitsOf (2 * W) (2 ^ W))).map (fun c => ⟨c, false, false⟩)

theorem sdivInput_spec (W p : ℕ) (N D : ℤ) :
    val ((sdivInput W p N D).map lensTn.get) = tc (2 * W) (N * 2 ^ p) ∧
      val ((sdivInput W p N D).map lensTd.get) = tc (2 * W) (D * 2 ^ W) ∧
      val ((sdivInput W p N D).map lensTq.get) = 0 ∧
      val ((sdivInput W p N D).map lensTm.get) = 2 ^ W % 2 ^ (2 * W) ∧
      (sdivInput W p N D).map (fun x => x.fn) = (sdivInput W p N D).map (fun _ => false) ∧
      (sdivInput W p N D).map (fun x => x.fd) = (sdivInput W p N D).map (fun _ => false) ∧
      (sdivInput W p N D).length = 2 * W := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkCells_spec (bitsOf (2 * W) (tc (2 * W) (N * 2 ^ p)))
    (bitsOf (2 * W) (tc (2 * W) (D * 2 ^ W))) (bitsOf (2 * W) 0) (bitsOf (2 * W) (2 ^ W))
    (by simp [bitsOf_length]) (by simp [bitsOf_length]) (by simp [bitsOf_length])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (sdivInput W p N D).map lensTn.get = (mkCells (bitsOf (2 * W) (tc (2 * W) (N * 2 ^ p)))
        (bitsOf (2 * W) (tc (2 * W) (D * 2 ^ W))) (bitsOf (2 * W) 0)
        (bitsOf (2 * W) (2 ^ W))).map DCell.n := by
      unfold sdivInput; rw [List.map_map]; rfl
    rw [e, h1, val_bitsOf, Nat.mod_eq_of_lt (tc_lt _ _)]
  · have e : (sdivInput W p N D).map lensTd.get = (mkCells (bitsOf (2 * W) (tc (2 * W) (N * 2 ^ p)))
        (bitsOf (2 * W) (tc (2 * W) (D * 2 ^ W))) (bitsOf (2 * W) 0)
        (bitsOf (2 * W) (2 ^ W))).map DCell.d := by
      unfold sdivInput; rw [List.map_map]; rfl
    rw [e, h2, val_bitsOf, Nat.mod_eq_of_lt (tc_lt _ _)]
  · have e : (sdivInput W p N D).map lensTq.get = (mkCells (bitsOf (2 * W) (tc (2 * W) (N * 2 ^ p)))
        (bitsOf (2 * W) (tc (2 * W) (D * 2 ^ W))) (bitsOf (2 * W) 0)
        (bitsOf (2 * W) (2 ^ W))).map DCell.q := by
      unfold sdivInput; rw [List.map_map]; rfl
    rw [e, h3, val_bitsOf, Nat.zero_mod]
  · have e : (sdivInput W p N D).map lensTm.get = (mkCells (bitsOf (2 * W) (tc (2 * W) (N * 2 ^ p)))
        (bitsOf (2 * W) (tc (2 * W) (D * 2 ^ W))) (bitsOf (2 * W) 0)
        (bitsOf (2 * W) (2 ^ W))).map DCell.m := by
      unfold sdivInput; rw [List.map_map]; rfl
    rw [e, h4, val_bitsOf]
  · unfold sdivInput; rw [List.map_map, List.map_map]; rfl
  · unfold sdivInput; rw [List.map_map, List.map_map]; rfl
  · unfold sdivInput; rw [List.length_map, h5, bitsOf_length]

/-! ### Signed division, end to end -/

/-- A list whose image under `f` is constant. -/
theorem all_eq_of_map {α β : Type} {l : List α} {k : List β} {f : α → Bool} {s : Bool}
    (h : l.map f = k.map (fun _ => s)) : ∀ z ∈ l, f z = s := by
  intro z hz
  have hm : f z ∈ l.map f := List.mem_map_of_mem hz
  rw [h] at hm
  obtain ⟨_, _, e⟩ := List.mem_map.mp hm
  exact e.symm

/-- **Signed division on the layout.** For `D ≠ 0` with `−2^W ≤ 2D < 2^W` and `|N|·2^p < 2^W`,
the composite first-arrives at its exit in exactly `(W + 7)(4W + 2)` transitions. The quotient
track, read in `2W`-bit two's complement, is the truncated quotient `tdiv(N·2^p, D)`. The
remainder track holds `|tmod(N·2^p, D)|`. -/
theorem sdiv_layout {W p : ℕ} {N D : ℤ} (hD : D ≠ 0) (hDl : -(2 : ℤ) ^ W ≤ 2 * D)
    (hDu : 2 * D < 2 ^ W) (hN : |N| * 2 ^ p < 2 ^ W) :
    ∃ l', ReachFirst sdivProg.toProg (Sum.inr AddI.done) (sdivProg.start, sdivInput W p N D) l'
        ((W + 7) * (4 * W + 2)) ∧
      sval (2 * W) (val (l'.map lensTq.get)) = Int.tdiv (N * 2 ^ p) D ∧
      val (l'.map lensTn.get) = (Int.tmod (N * 2 ^ p) D).natAbs := by
  obtain ⟨v1, v2, v3, v4, v5, v6, vlen⟩ := sdivInput_spec W p N D
  set l0 := sdivInput W p N D with hl0
  -- ranges
  have hW : 0 < W := by
    rcases Nat.eq_zero_or_pos W with h | h
    · subst h
      norm_num at hDl hDu
      omega
    · exact h
  have hn0 : 0 < 2 * W := by omega
  have hPp : (0 : ℤ) < 2 ^ p := by positivity
  have hPW : (0 : ℤ) < 2 ^ W := by positivity
  have hW1 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hn1 : (2 : ℤ) ^ (2 * W - 1) = 2 ^ (W - 1) * 2 ^ W := by
    rw [← pow_add]
    congr 1
    omega
  have h1W : (1 : ℤ) ≤ 2 ^ (W - 1) := one_le_pow₀ (by norm_num)
  have hx : |N * 2 ^ p| < 2 ^ (2 * W - 1) := by
    rw [abs_mul, abs_of_pos hPp, hn1]
    exact lt_of_lt_of_le hN (le_mul_of_one_le_left hPW.le h1W)
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  have hD1 : -(2 : ℤ) ^ (W - 1) ≤ D := by linarith
  have hD2 : D < 2 ^ (W - 1) := by linarith
  have hy1 : -(2 : ℤ) ^ (2 * W - 1) ≤ D * 2 ^ W := by
    rw [hn1]
    have := mul_le_mul_of_nonneg_right hD1 hPW.le
    linarith
  have hy2 : D * 2 ^ W < 2 ^ (2 * W - 1) := by
    rw [hn1]
    exact mul_lt_mul_of_pos_right hD2 hPW
  have hl0ne : l0 ≠ [] := by
    intro h
    rw [h, List.length_nil] at vlen
    omega
  -- stage 1: sign and negate the dividend
  obtain ⟨l1, r1, e1, f1⟩ := stage_cneg lensNn l0
  have hu0 : l0.map lensNn.get ≠ [] := by simpa using hl0ne
  obtain ⟨s1w, s1f, s1g, -⟩ := cneg_spec (l0.map lensNn.get) hu0
  have hu0len : (l0.map lensNn.get).length = 2 * W := by rw [List.length_map, vlen]
  have hu0w : vW (l0.map lensNn.get) = tc (2 * W) (N * 2 ^ p) := by
    rw [← v1]
    unfold vW
    rw [List.map_map]
    rfl
  obtain ⟨absx, sgnx⟩ := cneg_abs (2 * W) hn0 (N * 2 ^ p) hx1.le hx2
  rw [hu0len, hu0w, absx] at s1w
  rw [hu0len, hu0w] at s1f
  rw [← e1] at s1w s1f s1g
  set sN := decide (2 ^ (2 * W - 1) ≤ tc (2 * W) (N * 2 ^ p)) with hsN
  have t1 : val (l1.map lensTn.get) = (N * 2 ^ p).natAbs := by
    rw [← s1w]
    unfold vW
    rw [List.map_map]
    rfl
  have g1 : l1.map (fun x => x.fn) = l0.map (fun _ => sN) := by
    have h := s1f
    rw [List.map_map, List.map_map] at h
    exact h
  have hl1 : l1.length = 2 * W := by
    have h := congrArg List.length (f1 lensTd fun _ _ => rfl)
    rw [List.length_map, List.length_map] at h
    rw [h, vlen]
  -- stage 2: sign and negate the divisor
  obtain ⟨l2, r2, e2, f2⟩ := stage_cneg lensNd l1
  have hu1 : l1.map lensNd.get ≠ [] := by
    intro h
    rw [List.map_eq_nil_iff] at h
    rw [h, List.length_nil] at hl1
    omega
  obtain ⟨s2w, s2f, s2g, -⟩ := cneg_spec (l1.map lensNd.get) hu1
  have hu1len : (l1.map lensNd.get).length = 2 * W := by rw [List.length_map, hl1]
  have hu1w : vW (l1.map lensNd.get) = tc (2 * W) (D * 2 ^ W) := by
    rw [← v2, ← f1 lensTd fun _ _ => rfl]
    unfold vW
    rw [List.map_map]
    rfl
  obtain ⟨absy, sgny⟩ := cneg_abs (2 * W) hn0 (D * 2 ^ W) hy1 hy2
  rw [hu1len, hu1w, absy] at s2w
  rw [hu1len, hu1w] at s2f
  rw [← e2] at s2w s2f s2g
  set sD := decide (2 ^ (2 * W - 1) ≤ tc (2 * W) (D * 2 ^ W)) with hsD
  have t2 : val (l2.map lensTd.get) = (D * 2 ^ W).natAbs := by
    rw [← s2w]
    unfold vW
    rw [List.map_map]
    rfl
  have g2d : l2.map (fun x => x.fd) = l1.map (fun _ => sD) := by
    have h := s2f
    rw [List.map_map, List.map_map] at h
    exact h
  have g2n : l2.map (fun x => x.fn) = l1.map (fun x => x.fn) := by
    have h := s2g
    rw [List.map_map, List.map_map] at h
    exact h
  have hl2 : l2.length = 2 * W := by
    have h := congrArg List.length (f2 lensTn fun _ _ => rfl)
    rw [List.length_map, List.length_map] at h
    rw [h, hl1]
  -- stage 3: divide the magnitudes
  have hl2ne : l2 ≠ [] := by
    intro h
    rw [h, List.length_nil] at hl2
    omega
  have hD0 : 0 < D.natAbs := Int.natAbs_pos.mpr hD
  have q2 : vQ (l2.map lensDv.get) = 0 := by
    have e : vQ (l2.map lensDv.get) = val (l2.map lensTq.get) := by
      unfold vQ
      rw [List.map_map]
      rfl
    rw [e, f2 lensTq fun _ _ => rfl, f1 lensTq fun _ _ => rfl, v3]
  have m2 : vM (l2.map lensDv.get) = 2 ^ W := by
    have e : vM (l2.map lensDv.get) = val (l2.map lensTm.get) := by
      unfold vM
      rw [List.map_map]
      rfl
    rw [e, f2 lensTm fun _ _ => rfl, f1 lensTm fun _ _ => rfl, v4,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
  have d2 : vD (l2.map lensDv.get) = D.natAbs * 2 ^ W := by
    have e : vD (l2.map lensDv.get) = val (l2.map lensTd.get) := by
      unfold vD
      rw [List.map_map]
      rfl
    rw [e, t2, Int.natAbs_mul, Int.natAbs_pow]
    rfl
  have n2 : vN (l2.map lensDv.get) = (N * 2 ^ p).natAbs := by
    have e : vN (l2.map lensDv.get) = val (l2.map lensTn.get) := by
      unfold vN
      rw [List.map_map]
      rfl
    rw [e, f2 lensTn fun _ _ => rfl, t1]
  have hxW : (N * 2 ^ p).natAbs < 2 ^ W := by
    have h : (((N * 2 ^ p).natAbs : ℕ) : ℤ) < ((2 ^ W : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_mul, abs_of_pos hPp]
      push_cast
      exact hN
    exact_mod_cast h
  have hlt : vN (l2.map lensDv.get) < 2 * (D.natAbs * 2 ^ W) := by
    rw [n2]
    have h1 : 2 ^ W ≤ D.natAbs * 2 ^ W := Nat.le_mul_of_pos_left _ hD0
    omega
  obtain ⟨l3, r3, q3, n3, f3⟩ := stage_div l2 hl2ne W D.natAbs hD0 d2 m2 q2 hlt
  rw [n2] at q3 n3
  have fl3 : l3.map lensFl.get = l2.map lensFl.get := f3 lensFl fun _ _ => rfl
  have hl3 : l3.length = 2 * W := by
    have h := congrArg List.length fl3
    rw [List.length_map, List.length_map] at h
    rw [h, hl2]
  -- stage 4: correct the sign of the quotient
  obtain ⟨l4, r4, e4, f4⟩ := stage_fix l3
  have a3 : ∀ z ∈ l3.map lensNq.get, z.f = sN := by
    apply all_eq_of_map (k := l0)
    have h1 : (l3.map lensNq.get).map NCell.f = (l3.map lensFl.get).map Prod.fst := by
      rw [List.map_map, List.map_map]
      rfl
    have h2 : (l2.map lensFl.get).map Prod.fst = l2.map (fun x => x.fn) := by
      rw [List.map_map]
      rfl
    rw [h1, fl3, h2, g2n, g1]
  have b3 : ∀ z ∈ l3.map lensNq.get, z.g = sD := by
    apply all_eq_of_map (k := l1)
    have h1 : (l3.map lensNq.get).map NCell.g = (l3.map lensFl.get).map Prod.snd := by
      rw [List.map_map, List.map_map]
      rfl
    have h2 : (l2.map lensFl.get).map Prod.snd = l2.map (fun x => x.fd) := by
      rw [List.map_map]
      rfl
    rw [h1, fl3, h2, g2d]
  have s4 := fix_spec (l3.map lensNq.get) sN sD a3 b3
  rw [← e4] at s4
  have hu3len : (l3.map lensNq.get).length = 2 * W := by rw [List.length_map, hl3]
  have hu3w : vW (l3.map lensNq.get) = (N * 2 ^ p).natAbs / D.natAbs := by
    rw [← q3]
    unfold vW vQ
    rw [List.map_map, List.map_map]
    rfl
  rw [hu3len, hu3w] at s4
  -- the composite
  have hc := ProgOn.seq_reachFirst NND FIXQ (Sum.inr DivI.done)
    (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst NN DIVS (Sum.inr NegI.done) (show DivI.prep ≠ DivI.done by decide)
      (ProgOn.seq_reachFirst NEGN NEGD NegI.done (show NegI.sgn ≠ NegI.done by decide) r1 r2)
      r3) r4
  rw [vlen, hl1, hl2, hl3] at hc
  refine ⟨l4, ?_, ?_, ?_⟩
  · convert hc using 1
    ring
  · -- the quotient
    have eq4 : val (l4.map lensTq.get) = vW (l4.map lensNq.get) := by
      unfold vW
      rw [List.map_map]
      rfl
    have hq0 : (N * 2 ^ p).natAbs / D.natAbs < 2 ^ W :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hxW
    have hq0n : (N * 2 ^ p).natAbs / D.natAbs < 2 ^ (2 * W) :=
      lt_of_lt_of_le hq0 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hq0z : (((N * 2 ^ p).natAbs / D.natAbs : ℕ) : ℤ) < 2 ^ (2 * W - 1) := by
      rw [hn1]
      have : (((N * 2 ^ p).natAbs / D.natAbs : ℕ) : ℤ) < 2 ^ W := by exact_mod_cast hq0
      exact lt_of_lt_of_le this (le_mul_of_one_le_left hPW.le h1W)
    have hsN' : sN = decide (N * 2 ^ p < 0) := by rw [hsN]; exact decide_eq_decide.mpr sgnx
    have hsD' : sD = decide (D < 0) := by
      rw [hsD]
      apply decide_eq_decide.mpr
      rw [sgny]
      constructor
      · intro h
        by_contra h'
        push_neg at h'
        have := mul_nonneg h' hPW.le
        linarith
      · intro h
        exact mul_neg_of_neg_of_pos h hPW
    rw [eq4, s4, tdiv_cases, hsN', hsD']
    split_ifs
    · conv_lhs => rw [← tc_natCast hq0n]
      rw [tc_neg, sval_tc (2 * W) hn0 _ (by
        have : (0 : ℤ) ≤ (((N * 2 ^ p).natAbs / D.natAbs : ℕ) : ℤ) := by positivity
        linarith) (by
        have : (0 : ℤ) ≤ (((N * 2 ^ p).natAbs / D.natAbs : ℕ) : ℤ) := by positivity
        have : (0 : ℤ) < 2 ^ (2 * W - 1) := by positivity
        linarith)]
    · conv_lhs => rw [← tc_natCast hq0n]
      rw [sval_tc (2 * W) hn0 _ (by
        have : (0 : ℤ) ≤ (((N * 2 ^ p).natAbs / D.natAbs : ℕ) : ℤ) := by positivity
        have : (0 : ℤ) < 2 ^ (2 * W - 1) := by positivity
        linarith) hq0z]
  · -- the remainder
    have e : val (l4.map lensTn.get) = vN (l3.map lensDv.get) := by
      rw [f4 lensTn fun _ _ => rfl]
      unfold vN
      rw [List.map_map]
      rfl
    rw [e, n3, Int.natAbs_tmod]

/-- **Signed fixed-point division with certified rounding on the compiled Turing machine.**
For `D ≠ 0` with `−2^W ≤ 2D < 2^W` and `|N|·2^p < 2^W`, from the layout `sdivInput W p N D` the
compiled single-tape TM runs exactly `(W + 7)(4W + 2)` transitions. Its quotient track, read in
`2W`-bit two's complement, is `q = tdiv(N·2^p, D)`, with `|q/2^p − N/D| < 2^{−p}`. -/
theorem sdiv_tm {W p : ℕ} {N D : ℤ} (hD : D ≠ 0) (hDl : -(2 : ℤ) ^ W ≤ 2 * D)
    (hDu : 2 * D < 2 ^ W) (hN : |N| * 2 ^ p < 2 ^ W) (T : ℤ → Sym SDCell)
    (hT : sdivProg.toProg.Repr T (sdivInput W p N D)) :
    ∃ l' T', sdivProg.toProg.Repr T' l' ∧
      sval (2 * W) (val (l'.map lensTq.get)) = Int.tdiv (N * 2 ^ p) D ∧
      |((sval (2 * W) (val (l'.map lensTq.get)) : ℤ) : ℚ) / 2 ^ p - (N : ℚ) / D| < 1 / 2 ^ p ∧
      val (l'.map lensTn.get) = (Int.tmod (N * 2 ^ p) D).natAbs ∧
      sdivProg.toProg.toTM.run
          ⟨.fwd sdivProg.start (sdivProg.toProg.init sdivProg.start), T, 0⟩
          ((W + 7) * (4 * W + 2)) =
        ⟨.fwd (Sum.inr AddI.done) (sdivProg.toProg.init (Sum.inr AddI.done)), T', 0⟩ := by
  obtain ⟨l', hr, hq, hn⟩ := sdiv_layout hD hDl hDu hN
  obtain ⟨T', hT', hrun⟩ := sdivProg.toProg.reach_run hr.reach T hT
  refine ⟨l', T', hT', hq, ?_, hn, hrun⟩
  rw [hq]
  exact sdiv_certified N D p hD

end PVNP.Discrete.SweepArith
