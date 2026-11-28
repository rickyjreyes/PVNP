import PVNP.SweepFixMul

/-!
# Certified complex fixed-point multiplication, composed from verified programs

The product `(a + bi)(c + di) = (ac − bd) + (ad + bc)i` of two fixed-point complex numbers,
`z = (a + bi)/2^p` and `w = (c + di)/2^p`, runs as one Turing machine. It is a six-stage
composite of verified programs on the common alphabet `CCell`:

1. Four fixed-point products `⌊ac/2^p⌋`, `⌊bd/2^p⌋`, `⌊ad/2^p⌋`, `⌊bc/2^p⌋`. Each is the verified
   multiply-then-divide machine `fmulProg`, lifted onto its own block of tracks.
2. The real part `⌊ac/2^p⌋ − ⌊bd/2^p⌋`, by the verified subtractor reading two quotient tracks.
3. The imaginary part `⌊ad/2^p⌋ + ⌊bc/2^p⌋`, by a modular adder (`addModProg`, the ripple-carry
   pass without the overflow cell) reading the other two quotient tracks.

The stages are chained by `ProgOn.seq_reachFirst`. Frame preservation along independent lenses
keeps each block unchanged while the others run. Every stage reads its inputs where the previous
stages left them, so no copying program is needed.

* `addMod_first`, `addMod_value`, `sub_first`: the single-trip adder and subtractor in
  first-arrival form. The modular adder returns `(x + y) mod 2ⁿ`.
* `stage_fmul`, `stage_sub`, `stage_add`: one stage on the common alphabet, with its frame.
* `cmul_layout`: on the explicit layout `cmulInput`, the composite `cmulProg` first-arrives at its
  exit. The real track holds `(q₁ − q₂) mod 2^L` and the imaginary track `(q₃ + q₄) mod 2^L`,
  where `q_k = ⌊X_k Y_k mod 2^L / 2^p⌋`. The cost is exactly the sum of the six stage costs.
* `cmul_tm`: **signed complex fixed-point multiplication on the compiled TM**, in two's complement.
  Read in `(L − p)`-bit two's complement, the result words are
  `Re = ⌊ac/2^p⌋ − ⌊bd/2^p⌋` and `Im = ⌊ad/2^p⌋ + ⌊bc/2^p⌋`, provided these and the four products
  lie in range. They satisfy `|Re/2^p − Re(zw)| < 2^{−p}` and `|Im/2^p − Im(zw)| < 2·2^{−p}`.
-/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-! ### Single-trip adders in first-arrival form -/

/-- The modular adder: the ripple-carry pass without the overflow extension. -/
def addModProg : Prog where
  D := Cell
  I := AddI
  B := Bool
  lift b := ⟨b, false, false⟩
  start := .go
  init _ := false
  fwd
    | .go => fadd
    | .done => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun _ => .inl .done

theorem addMod_first (l : List Cell) :
    ReachFirst addModProg AddI.done (AddI.go, l) (fscan fadd false l).1 (2 * l.length + 2) := by
  have hs : addModProg.stepP (AddI.go, l) = .inl (AddI.done, (fscan fadd false l).1) := by
    simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, addModProg, bscan_id]
  have h := ReachFirst.last (P := addModProg) (e := AddI.done) hs
  simpa [Prog.tripCost, Prog.fpass, addModProg] using h

/-- The modular adder returns `(x + y) mod 2ⁿ` on the result track. -/
theorem addMod_value (l : List Cell) :
    val ((fscan fadd false l).1.map Cell.r) =
      (val (l.map Cell.a) + val (l.map Cell.b)) % 2 ^ l.length := by
  have h := fscan_add false l
  have hlt := val_lt ((fscan fadd false l).1.map Cell.r)
  rw [List.length_map, fscan_length] at hlt
  simp only [Bool.toNat_false, add_zero] at h
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem sub_first (l : List Cell) :
    ReachFirst subProg AddI.done (AddI.go, l) (fscan fsub false l).1 (2 * l.length + 2) := by
  have hs : subProg.stepP (AddI.go, l) = .inl (AddI.done, (fscan fsub false l).1) := by
    simp [Prog.stepP, Prog.trip, Prog.mid, Prog.fpass, subProg, bscan_id]
  have h := ReachFirst.last (P := subProg) (e := AddI.done) hs
  simpa [Prog.tripCost, Prog.fpass, subProg] using h

/-! ### The common alphabet for complex multiplication -/

/-- Cells for complex multiplication: four product blocks, and the real and imaginary tracks. -/
structure CCell where
  p1 : FCell
  p2 : FCell
  p3 : FCell
  p4 : FCell
  re : Bool
  im : Bool
  deriving DecidableEq, Fintype

def lens1 : TrackLens CCell FCell := ⟨CCell.p1, fun x c => { x with p1 := c }, fun _ _ => rfl⟩
def lens2 : TrackLens CCell FCell := ⟨CCell.p2, fun x c => { x with p2 := c }, fun _ _ => rfl⟩
def lens3 : TrackLens CCell FCell := ⟨CCell.p3, fun x c => { x with p3 := c }, fun _ _ => rfl⟩
def lens4 : TrackLens CCell FCell := ⟨CCell.p4, fun x c => { x with p4 := c }, fun _ _ => rfl⟩
def lensRe : TrackLens CCell Bool := ⟨CCell.re, fun x b => { x with re := b }, fun _ _ => rfl⟩
def lensIm : TrackLens CCell Bool := ⟨CCell.im, fun x b => { x with im := b }, fun _ _ => rfl⟩

/-- The subtractor's view: the quotient tracks of blocks 1 and 2, and the real track. -/
def lensSub : TrackLens CCell Cell where
  get x := ⟨x.p1.2.q, x.p2.2.q, x.re⟩
  put x c := ⟨(x.p1.1, ⟨x.p1.2.n, x.p1.2.d, c.a, x.p1.2.m⟩),
    (x.p2.1, ⟨x.p2.2.n, x.p2.2.d, c.b, x.p2.2.m⟩), x.p3, x.p4, c.r, x.im⟩
  get_put _ _ := rfl

/-- The adder's view: the quotient tracks of blocks 3 and 4, and the imaginary track. -/
def lensAdd : TrackLens CCell Cell where
  get x := ⟨x.p3.2.q, x.p4.2.q, x.im⟩
  put x c := ⟨x.p1, x.p2, (x.p3.1, ⟨x.p3.2.n, x.p3.2.d, c.a, x.p3.2.m⟩),
    (x.p4.1, ⟨x.p4.2.n, x.p4.2.d, c.b, x.p4.2.m⟩), x.re, c.r⟩
  get_put _ _ := rfl

/-- The fill cell. No stage extends the tape. -/
def czC : CCell := ⟨fz, fz, fz, fz, false, false⟩

/-- Raw input bits enter the first multiplicand track. -/
def cbit (b : Bool) : CCell := ⟨fbit b, fz, fz, fz, false, false⟩

theorem fmulProg_ext : ∀ i b, fmulProg.ext i b = none := by
  intro i b
  rcases i with i | i <;> rcases b with b | b <;> rfl

/-! ### One stage on the common alphabet -/

/-- **A product stage on one block.** If the block holds the fixed-point layout of `X` and `Y`,
the lifted multiply-then-divide machine first-arrives at its exit with the stated exact cost. The
block's quotient track then holds `⌊(XY mod 2^L)/2^p⌋`, and every independent track is
unchanged. -/
theorem stage_fmul (ℓ : TrackLens CCell FCell) {L p X Y : ℕ} (hp : p < L) (hX : X < 2 ^ L)
    (hY : Y < 2 ^ L) (l : List CCell) (hl : l.map ℓ.get = fmulInput L p X Y) :
    ∃ l', ReachFirst (fmulProg.viaLens ℓ czC cbit).toProg (Sum.inr DivI.done)
        (Sum.inl MulI.prep, l) l'
        ((trips Y + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2)) ∧
      vQ ((l'.map ℓ.get).map lensD.get) = X * Y % 2 ^ L / 2 ^ p ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens CCell D₂), ℓ.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  obtain ⟨m, hr, hq, _⟩ := fmul_layout L p X Y hp hX hY
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens fmulProg ℓ czC cbit hr l hl.symm
  refine ⟨l', hr', by rw [hv]; exact hq, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame fmulProg ℓ czC cbit fmulProg_ext hi hr'

/-- **The subtraction stage.** -/
theorem stage_sub (l : List CCell) :
    ∃ l', ReachFirst ((ProgOn.ofProg subProg).viaLens lensSub czC cbit).toProg AddI.done
        (AddI.go, l) l' (2 * l.length + 2) ∧
      l'.map lensSub.get = (fscan fsub false (l.map lensSub.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens CCell D₂), lensSub.Indep ℓ₂ →
        l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := sub_first (l.map lensSub.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg subProg) lensSub czC cbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg subProg) lensSub czC cbit
    (fun _ _ => rfl) hi hr'

/-- **The addition stage.** -/
theorem stage_add (l : List CCell) :
    ∃ l', ReachFirst ((ProgOn.ofProg addModProg).viaLens lensAdd czC cbit).toProg AddI.done
        (AddI.go, l) l' (2 * l.length + 2) ∧
      l'.map lensAdd.get = (fscan fadd false (l.map lensAdd.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens CCell D₂), lensAdd.Indep ℓ₂ →
        l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := addMod_first (l.map lensAdd.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ :=
    ProgOn.reachFirst_lens (ProgOn.ofProg addModProg) lensAdd czC cbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg addModProg) lensAdd czC cbit
    (fun _ _ => rfl) hi hr'

/-! ### The layout and the composite machine -/

/-- Four blocks and two zero tracks zipped into cells. -/
def mkC : List FCell → List FCell → List FCell → List FCell → List CCell
  | x1 :: l1, x2 :: l2, x3 :: l3, x4 :: l4 => ⟨x1, x2, x3, x4, false, false⟩ :: mkC l1 l2 l3 l4
  | _, _, _, _ => []

theorem mkC_spec (l1 l2 l3 l4 : List FCell) (h2 : l2.length = l1.length)
    (h3 : l3.length = l1.length) (h4 : l4.length = l1.length) :
    (mkC l1 l2 l3 l4).map lens1.get = l1 ∧ (mkC l1 l2 l3 l4).map lens2.get = l2 ∧
      (mkC l1 l2 l3 l4).map lens3.get = l3 ∧ (mkC l1 l2 l3 l4).map lens4.get = l4 ∧
      (mkC l1 l2 l3 l4).map lensRe.get = List.replicate l1.length false ∧
      (mkC l1 l2 l3 l4).map lensIm.get = List.replicate l1.length false ∧
      (mkC l1 l2 l3 l4).length = l1.length := by
  induction l1 generalizing l2 l3 l4 with
  | nil =>
    rw [List.length_nil, List.length_eq_zero_iff] at h2 h3 h4
    subst h2 h3 h4
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons x1 l1 ih =>
    cases l2 with
    | nil => simp at h2
    | cons x2 l2 =>
      cases l3 with
      | nil => simp at h3
      | cons x3 l3 =>
        cases l4 with
        | nil => simp at h4
        | cons x4 l4 =>
          simp only [List.length_cons, add_left_inj] at h2 h3 h4
          obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := ih l2 l3 l4 h2 h3 h4
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [mkC, List.map_cons, e1]; rfl
          · rw [mkC, List.map_cons, e2]; rfl
          · rw [mkC, List.map_cons, e3]; rfl
          · rw [mkC, List.map_cons, e4]; rfl
          · rw [mkC, List.map_cons, e5, List.length_cons, List.replicate_succ]; rfl
          · rw [mkC, List.map_cons, e6, List.length_cons, List.replicate_succ]; rfl
          · rw [mkC, List.length_cons, e7, List.length_cons]

/-- Layout for complex multiplication on `L` cells. Block 1 multiplies `A·C`, block 2 `B·D`,
block 3 `A·D` and block 4 `B·C`, each on the fixed-point layout `fmulInput`. The real and
imaginary tracks start at zero. -/
def cmulInput (L p A B C D : ℕ) : List CCell :=
  mkC (fmulInput L p A C) (fmulInput L p B D) (fmulInput L p A D) (fmulInput L p B C)

theorem cmulInput_spec (L p A B C D : ℕ) :
    (cmulInput L p A B C D).map lens1.get = fmulInput L p A C ∧
      (cmulInput L p A B C D).map lens2.get = fmulInput L p B D ∧
      (cmulInput L p A B C D).map lens3.get = fmulInput L p A D ∧
      (cmulInput L p A B C D).map lens4.get = fmulInput L p B C ∧
      (cmulInput L p A B C D).map lensRe.get = List.replicate L false ∧
      (cmulInput L p A B C D).map lensIm.get = List.replicate L false ∧
      (cmulInput L p A B C D).length = L := by
  have hl : ∀ X Y, (fmulInput L p X Y).length = L := fun X Y => (fmulInput_views L p X Y).2.2.2.2.2.2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := mkC_spec (fmulInput L p A C) (fmulInput L p B D)
    (fmulInput L p A D) (fmulInput L p B C) (by rw [hl, hl]) (by rw [hl, hl]) (by rw [hl, hl])
  rw [hl] at e5 e6 e7
  exact ⟨e1, e2, e3, e4, e5, e6, e7⟩

/-- The exit of a product stage. -/
abbrev eF : fmulProg.I := Sum.inr DivI.done

def F1 : ProgOn CCell := fmulProg.viaLens lens1 czC cbit
def F2 : ProgOn CCell := fmulProg.viaLens lens2 czC cbit
def F3 : ProgOn CCell := fmulProg.viaLens lens3 czC cbit
def F4 : ProgOn CCell := fmulProg.viaLens lens4 czC cbit
def SUBC : ProgOn CCell := (ProgOn.ofProg subProg).viaLens lensSub czC cbit
def ADDC : ProgOn CCell := (ProgOn.ofProg addModProg).viaLens lensAdd czC cbit

def C12 : ProgOn CCell := ProgOn.seq F1 F2 eF
def C123 : ProgOn CCell := ProgOn.seq C12 F3 (Sum.inr eF)
def C1234 : ProgOn CCell := ProgOn.seq C123 F4 (Sum.inr eF)
def C12345 : ProgOn CCell := ProgOn.seq C1234 SUBC (Sum.inr eF)

/-- **Complex fixed-point multiplication**: four products, then a subtraction and an addition. -/
def cmulProg : ProgOn CCell := ProgOn.seq C12345 ADDC (Sum.inr AddI.done)

/-- The exact cost of a product stage whose multiplier is `Y`. -/
def fcost (L p Y : ℕ) : ℕ := (trips Y + 1) * (2 * L + 2) + (L - 1 - p + 2) * (2 * L + 2)

/-- `L`-bit code of a natural number below `2^L`. -/
theorem tc_natCast {L q : ℕ} (hq : q < 2 ^ L) : tc L (q : ℤ) = q := by
  unfold tc
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hq)]
  simp

/-- **Complex multiplication on the explicit layout.** From `cmulInput L p A B C D` the composite
first-arrives at its exit. The cost is exactly the sum of the six stage costs. The real track holds
`(q₁ − q₂) mod 2^L` and the imaginary track `(q₃ + q₄) mod 2^L`, where
`q₁ = ⌊(AC mod 2^L)/2^p⌋`, `q₂ = ⌊(BD mod 2^L)/2^p⌋`, `q₃ = ⌊(AD mod 2^L)/2^p⌋` and
`q₄ = ⌊(BC mod 2^L)/2^p⌋`. -/
theorem cmul_layout {L p A B C D : ℕ} (hp : p < L) (hA : A < 2 ^ L) (hB : B < 2 ^ L)
    (hC : C < 2 ^ L) (hD : D < 2 ^ L) :
    ∃ l', ReachFirst cmulProg.toProg (Sum.inr AddI.done) (cmulProg.start, cmulInput L p A B C D)
        l' (fcost L p C + fcost L p D + fcost L p D + fcost L p C + (2 * L + 2) + (2 * L + 2)) ∧
      val (l'.map lensRe.get) =
        tc L (((A * C % 2 ^ L / 2 ^ p : ℕ) : ℤ) - ((B * D % 2 ^ L / 2 ^ p : ℕ) : ℤ)) ∧
      val (l'.map lensIm.get) = (A * D % 2 ^ L / 2 ^ p + B * C % 2 ^ L / 2 ^ p) % 2 ^ L := by
  obtain ⟨v1, v2, v3, v4, vre, vim, vlen⟩ := cmulInput_spec L p A B C D
  set l0 := cmulInput L p A B C D with hl0
  -- the four product stages
  obtain ⟨l1, r1, q1, f1⟩ := stage_fmul lens1 hp hA hC l0 v1
  have v2' : l1.map lens2.get = fmulInput L p B D := by rw [f1 lens2 fun _ _ => rfl]; exact v2
  obtain ⟨l2, r2, q2, f2⟩ := stage_fmul lens2 hp hB hD l1 v2'
  have v3' : l2.map lens3.get = fmulInput L p A D := by
    rw [f2 lens3 fun _ _ => rfl, f1 lens3 fun _ _ => rfl]; exact v3
  obtain ⟨l3, r3, q3, f3⟩ := stage_fmul lens3 hp hA hD l2 v3'
  have v4' : l3.map lens4.get = fmulInput L p B C := by
    rw [f3 lens4 fun _ _ => rfl, f2 lens4 fun _ _ => rfl, f1 lens4 fun _ _ => rfl]; exact v4
  obtain ⟨l4, r4, q4, f4⟩ := stage_fmul lens4 hp hB hC l3 v4'
  -- the subtraction and addition stages
  obtain ⟨l5, r5, h5, f5⟩ := stage_sub l4
  obtain ⟨l6, r6, h6, f6⟩ := stage_add l5
  -- lengths
  have len : ∀ (l : List CCell) (ℓ : TrackLens CCell FCell) {X Y : ℕ},
      l.map ℓ.get = fmulInput L p X Y → l.length = L := by
    intro l ℓ X Y h
    have := congrArg List.length h
    rwa [List.length_map, (fmulInput_views L p X Y).2.2.2.2.2.2] at this
  have hl4 : l4.length = L := by
    have h := congrArg List.length (f4 lens1 fun _ _ => rfl)
    rw [List.length_map, List.length_map] at h
    rw [h]; exact len l3 lens4 v4'
  have hl5 : l5.length = L := by
    have h := congrArg List.length (f5 lens3 fun _ _ => rfl)
    rw [List.length_map, List.length_map] at h
    rw [h, hl4]
  -- the composite
  have hc := ProgOn.seq_reachFirst C12345 ADDC (Sum.inr AddI.done)
    (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst C1234 SUBC (Sum.inr eF) (show AddI.go ≠ AddI.done by decide)
      (ProgOn.seq_reachFirst C123 F4 (Sum.inr eF) Sum.inl_ne_inr
        (ProgOn.seq_reachFirst C12 F3 (Sum.inr eF) Sum.inl_ne_inr
          (ProgOn.seq_reachFirst F1 F2 eF Sum.inl_ne_inr r1 r2) r3) r4) r5) r6
  rw [hl4, hl5] at hc
  refine ⟨l6, hc, ?_, ?_⟩
  · -- the real track
    have e6 : l6.map lensRe.get = l5.map lensRe.get := f6 lensRe fun _ _ => rfl
    have eR : l5.map lensRe.get = (fscan fsub false (l4.map lensSub.get)).1.map Cell.r := by
      rw [← h5, List.map_map]; rfl
    have ha : (l4.map lensSub.get).map Cell.a = (l1.map lens1.get).map (fun x => x.2.q) := by
      have e : (l4.map lensSub.get).map Cell.a = (l4.map lens1.get).map (fun x => x.2.q) := by
        rw [List.map_map, List.map_map]; rfl
      rw [e, f4 lens1 fun _ _ => rfl, f3 lens1 fun _ _ => rfl, f2 lens1 fun _ _ => rfl]
    have hb : (l4.map lensSub.get).map Cell.b = (l2.map lens2.get).map (fun x => x.2.q) := by
      have e : (l4.map lensSub.get).map Cell.b = (l4.map lens2.get).map (fun x => x.2.q) := by
        rw [List.map_map, List.map_map]; rfl
      rw [e, f4 lens2 fun _ _ => rfl, f3 lens2 fun _ _ => rfl]
    have hq1 : val ((l1.map lens1.get).map (fun x => x.2.q)) = A * C % 2 ^ L / 2 ^ p := by
      rw [← q1]; simp only [vQ, List.map_map]; rfl
    have hq2 : val ((l2.map lens2.get).map (fun x => x.2.q)) = B * D % 2 ^ L / 2 ^ p := by
      rw [← q2]; simp only [vQ, List.map_map]; rfl
    have hlt1 : A * C % 2 ^ L / 2 ^ p < 2 ^ L :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by positivity))
    have hlt2 : B * D % 2 ^ L / 2 ^ p < 2 ^ L :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by positivity))
    have hs := sub_tc_value (l4.map lensSub.get) L (by rw [List.length_map, hl4])
      ((A * C % 2 ^ L / 2 ^ p : ℕ) : ℤ) ((B * D % 2 ^ L / 2 ^ p : ℕ) : ℤ)
      (by rw [ha, hq1, tc_natCast hlt1]) (by rw [hb, hq2, tc_natCast hlt2])
    rw [e6, eR, hs]
  · -- the imaginary track
    have eI : l6.map lensIm.get = (fscan fadd false (l5.map lensAdd.get)).1.map Cell.r := by
      rw [← h6, List.map_map]; rfl
    have ha : (l5.map lensAdd.get).map Cell.a = (l3.map lens3.get).map (fun x => x.2.q) := by
      have e : (l5.map lensAdd.get).map Cell.a = (l5.map lens3.get).map (fun x => x.2.q) := by
        rw [List.map_map, List.map_map]; rfl
      rw [e, f5 lens3 fun _ _ => rfl, f4 lens3 fun _ _ => rfl]
    have hb : (l5.map lensAdd.get).map Cell.b = (l4.map lens4.get).map (fun x => x.2.q) := by
      have e : (l5.map lensAdd.get).map Cell.b = (l5.map lens4.get).map (fun x => x.2.q) := by
        rw [List.map_map, List.map_map]; rfl
      rw [e, f5 lens4 fun _ _ => rfl]
    have hq3 : val ((l3.map lens3.get).map (fun x => x.2.q)) = A * D % 2 ^ L / 2 ^ p := by
      rw [← q3]; simp only [vQ, List.map_map]; rfl
    have hq4 : val ((l4.map lens4.get).map (fun x => x.2.q)) = B * C % 2 ^ L / 2 ^ p := by
      rw [← q4]; simp only [vQ, List.map_map]; rfl
    rw [eI, addMod_value, ha, hb, hq3, hq4, List.length_map, hl5]

/-! ### Signed complex fixed point in two's complement -/

/-- Reducing an `L`-bit code to its low `L − p` bits gives the `(L − p)`-bit code. -/
theorem tc_mod_pow (L p : ℕ) (z : ℤ) : tc L z % 2 ^ (L - p) = tc (L - p) z := by
  have hdvd : (2 : ℤ) ^ (L - p) ∣ 2 ^ L := pow_dvd_pow 2 (Nat.sub_le L p)
  have h : ((tc L z % 2 ^ (L - p) : ℕ) : ℤ) = ((tc (L - p) z : ℕ) : ℤ) := by
    push_cast
    rw [tc_cast, tc_cast, Int.emod_emod_of_dvd _ hdvd]
  exact_mod_cast h

/-- The code of a difference of codes is the code of the difference. -/
theorem tc_sub_tc (n : ℕ) (x y : ℤ) : tc n ((tc n x : ℤ) - (tc n y : ℤ)) = tc n (x - y) := by
  have h : ((tc n ((tc n x : ℤ) - (tc n y : ℤ)) : ℕ) : ℤ) = ((tc n (x - y) : ℕ) : ℤ) := by
    rw [tc_cast, tc_cast, tc_cast, tc_cast, ← Int.sub_emod]
  exact_mod_cast h

/-- The quotient word of a product stage is the `(L − p)`-bit code of `⌊xy/2^p⌋`. -/
theorem fq_word {L p : ℕ} (hp : p ≤ L) (x y : ℤ) :
    tc L x * tc L y % 2 ^ L / 2 ^ p = tc (L - p) (x * y / 2 ^ p) := by
  rw [tc_mul, tc_shift L p hp]

/-- **The certificates.** `|(s₁ − s₂)/2^p − (u₁ − u₂)| < 2^{−p}` and
`|(s₃ + s₄)/2^p − (u₃ + u₄)| < 2·2^{−p}`, where `s = ⌊xy/2^p⌋` and `u = (x/2^p)(y/2^p)`. -/
theorem cmul_certified (a b c d : ℤ) (p : ℕ) :
    |((a * c / 2 ^ p - b * d / 2 ^ p : ℤ) : ℚ) / 2 ^ p -
        (((a : ℚ) / 2 ^ p) * ((c : ℚ) / 2 ^ p) - ((b : ℚ) / 2 ^ p) * ((d : ℚ) / 2 ^ p))| <
      1 / 2 ^ p ∧
    |((a * d / 2 ^ p + b * c / 2 ^ p : ℤ) : ℚ) / 2 ^ p -
        (((a : ℚ) / 2 ^ p) * ((d : ℚ) / 2 ^ p) + ((b : ℚ) / 2 ^ p) * ((c : ℚ) / 2 ^ p))| <
      2 / 2 ^ p := by
  obtain ⟨h1, h1'⟩ := sfixmul_certified a c p
  obtain ⟨h2, h2'⟩ := sfixmul_certified b d p
  obtain ⟨h3, h3'⟩ := sfixmul_certified a d p
  obtain ⟨h4, h4'⟩ := sfixmul_certified b c p
  have hP : (0 : ℚ) < 2 ^ p := by positivity
  have e1 : ∀ s : ℤ, (((s : ℤ) : ℚ) + 1) / 2 ^ p = (s : ℚ) / 2 ^ p + 1 / 2 ^ p := fun s => by
    rw [add_div]
  rw [e1] at h1' h2' h3' h4'
  push_cast
  rw [sub_div, add_div]
  constructor
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]
    have : (2 : ℚ) / 2 ^ p = 1 / 2 ^ p + 1 / 2 ^ p := by ring
    constructor <;> linarith

/-- **Signed complex fixed-point multiplication on the compiled Turing machine.** Lay out the
`L`-bit codes of integers `a, b, c, d`, that is `z = (a + bi)/2^p` and `w = (c + di)/2^p`. Suppose
the real part `Re = ⌊ac/2^p⌋ − ⌊bd/2^p⌋` and the imaginary part `Im = ⌊ad/2^p⌋ + ⌊bc/2^p⌋` lie in
the `(L − p)`-bit two's-complement range. Then the single-tape TM of `cmulProg` reaches its exit
after exactly the stated number of transitions, at most `4(2L + 2)² + 2(2L + 2)`. Read in
two's complement, the low `L − p` bits of its real and imaginary tracks are `Re` and `Im`, with
`|Re/2^p − Re(zw)| < 2^{−p}` and `|Im/2^p − Im(zw)| < 2·2^{−p}`. -/
theorem cmul_tm {L p : ℕ} (hp : p < L) (a b c d : ℤ)
    (hre1 : -(2 : ℤ) ^ (L - p - 1) ≤ a * c / 2 ^ p - b * d / 2 ^ p)
    (hre2 : a * c / 2 ^ p - b * d / 2 ^ p < 2 ^ (L - p - 1))
    (him1 : -(2 : ℤ) ^ (L - p - 1) ≤ a * d / 2 ^ p + b * c / 2 ^ p)
    (him2 : a * d / 2 ^ p + b * c / 2 ^ p < 2 ^ (L - p - 1))
    (T : ℤ → Sym CCell)
    (hT : cmulProg.toProg.Repr T (cmulInput L p (tc L a) (tc L b) (tc L c) (tc L d))) :
    ∃ l' T', cmulProg.toProg.Repr T' l' ∧
      sval (L - p) (val (l'.map lensRe.get) % 2 ^ (L - p)) = a * c / 2 ^ p - b * d / 2 ^ p ∧
      sval (L - p) (val (l'.map lensIm.get) % 2 ^ (L - p)) = a * d / 2 ^ p + b * c / 2 ^ p ∧
      |((sval (L - p) (val (l'.map lensRe.get) % 2 ^ (L - p)) : ℤ) : ℚ) / 2 ^ p -
          (((a : ℚ) / 2 ^ p) * ((c : ℚ) / 2 ^ p) - ((b : ℚ) / 2 ^ p) * ((d : ℚ) / 2 ^ p))| <
        1 / 2 ^ p ∧
      |((sval (L - p) (val (l'.map lensIm.get) % 2 ^ (L - p)) : ℤ) : ℚ) / 2 ^ p -
          (((a : ℚ) / 2 ^ p) * ((d : ℚ) / 2 ^ p) + ((b : ℚ) / 2 ^ p) * ((c : ℚ) / 2 ^ p))| <
        2 / 2 ^ p ∧
      cmulProg.toProg.toTM.run
          ⟨.fwd cmulProg.start (cmulProg.toProg.init cmulProg.start), T, 0⟩
          (fcost L p (tc L c) + fcost L p (tc L d) + fcost L p (tc L d) + fcost L p (tc L c) +
            (2 * L + 2) + (2 * L + 2)) =
        ⟨.fwd (Sum.inr AddI.done) (cmulProg.toProg.init (Sum.inr AddI.done)), T', 0⟩ ∧
      fcost L p (tc L c) + fcost L p (tc L d) + fcost L p (tc L d) + fcost L p (tc L c) +
          (2 * L + 2) + (2 * L + 2) ≤ 4 * (2 * L + 2) ^ 2 + 2 * (2 * L + 2) := by
  obtain ⟨l', hr, hre, him⟩ :=
    cmul_layout hp (tc_lt L a) (tc_lt L b) (tc_lt L c) (tc_lt L d)
  obtain ⟨T', hT', hrun⟩ := cmulProg.toProg.reach_run hr.reach T hT
  have hpL : p ≤ L := hp.le
  have hn : 0 < L - p := by omega
  -- the real word
  have hRe : sval (L - p) (val (l'.map lensRe.get) % 2 ^ (L - p)) =
      a * c / 2 ^ p - b * d / 2 ^ p := by
    rw [hre, tc_mod_pow L p, fq_word hpL, fq_word hpL, tc_sub_tc]
    exact sval_tc (L - p) hn _ hre1 hre2
  -- the imaginary word
  have hIm : sval (L - p) (val (l'.map lensIm.get) % 2 ^ (L - p)) =
      a * d / 2 ^ p + b * c / 2 ^ p := by
    have hdvd : 2 ^ (L - p) ∣ 2 ^ L := pow_dvd_pow 2 (Nat.sub_le L p)
    rw [him, Nat.mod_mod_of_dvd _ hdvd, fq_word hpL, fq_word hpL, tc_add]
    exact sval_tc (L - p) hn _ him1 him2
  obtain ⟨c1, c2⟩ := cmul_certified a b c d p
  refine ⟨l', T', hT', hRe, hIm, by rw [hRe]; exact c1, by rw [hIm]; exact c2, hrun, ?_⟩
  have b1 := fmul_cost_le L p (tc L c) hp (tc_lt L c)
  have b2 := fmul_cost_le L p (tc L d) hp (tc_lt L d)
  unfold fcost
  linarith

/-! ### Complex addition and subtraction on pairs -/

/-- Cells for complex addition and subtraction: one adder cell per component. -/
structure PCell where
  re : Cell
  im : Cell
  deriving DecidableEq, Fintype

def lensPRe : TrackLens PCell Cell := ⟨PCell.re, fun x c => { x with re := c }, fun _ _ => rfl⟩
def lensPIm : TrackLens PCell Cell := ⟨PCell.im, fun x c => { x with im := c }, fun _ _ => rfl⟩

def pz : PCell := ⟨⟨false, false, false⟩, ⟨false, false, false⟩⟩
def pbit (b : Bool) : PCell := ⟨⟨b, false, false⟩, ⟨false, false, false⟩⟩

/-- **Complex addition**: the modular adder on the real tracks, then on the imaginary tracks. -/
def caddProg : ProgOn PCell :=
  ProgOn.seq ((ProgOn.ofProg addModProg).viaLens lensPRe pz pbit)
    ((ProgOn.ofProg addModProg).viaLens lensPIm pz pbit) AddI.done

/-- **Complex subtraction**: the subtractor on the real tracks, then on the imaginary tracks. -/
def csubProg : ProgOn PCell :=
  ProgOn.seq ((ProgOn.ofProg subProg).viaLens lensPRe pz pbit)
    ((ProgOn.ofProg subProg).viaLens lensPIm pz pbit) AddI.done

/-- **Complex addition, in first-arrival form.** The real and imaginary result tracks hold the
componentwise sums modulo `2ⁿ`, in exactly `2(2n + 2)` transitions. -/
theorem cadd_first (l : List PCell) :
    ∃ l', ReachFirst caddProg.toProg (Sum.inr AddI.done) (caddProg.start, l) l'
        ((2 * l.length + 2) + (2 * l.length + 2)) ∧
      val ((l'.map lensPRe.get).map Cell.r) =
        (val ((l.map lensPRe.get).map Cell.a) + val ((l.map lensPRe.get).map Cell.b)) %
          2 ^ l.length ∧
      val ((l'.map lensPIm.get).map Cell.r) =
        (val ((l.map lensPIm.get).map Cell.a) + val ((l.map lensPIm.get).map Cell.b)) %
          2 ^ l.length := by
  have r1 := addMod_first (l.map lensPRe.get)
  rw [List.length_map] at r1
  obtain ⟨l1, r1', v1⟩ :=
    ProgOn.reachFirst_lens (ProgOn.ofProg addModProg) lensPRe pz pbit r1 l rfl
  have f1 : l1.map lensPIm.get = l.map lensPIm.get :=
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg addModProg) lensPRe pz pbit (fun _ _ => rfl)
      (fun _ _ => rfl) r1'
  have hl1 : l1.length = l.length := by
    have := congrArg List.length f1
    rwa [List.length_map, List.length_map] at this
  have r2 := addMod_first (l1.map lensPIm.get)
  rw [List.length_map] at r2
  obtain ⟨l2, r2', v2⟩ :=
    ProgOn.reachFirst_lens (ProgOn.ofProg addModProg) lensPIm pz pbit r2 l1 rfl
  have f2 : l2.map lensPRe.get = l1.map lensPRe.get :=
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg addModProg) lensPIm pz pbit (fun _ _ => rfl)
      (fun _ _ => rfl) r2'
  have hc := ProgOn.seq_reachFirst ((ProgOn.ofProg addModProg).viaLens lensPRe pz pbit)
    ((ProgOn.ofProg addModProg).viaLens lensPIm pz pbit) AddI.done
    (show AddI.go ≠ AddI.done by decide) r1' r2'
  rw [hl1] at hc
  refine ⟨l2, hc, ?_, ?_⟩
  · rw [f2, v1, addMod_value, List.length_map]
  · rw [v2, addMod_value, List.length_map, hl1, f1]

/-- **Complex subtraction, in first-arrival form.** The result tracks hold the componentwise
differences: `val r + val b ≡ val a (mod 2ⁿ)` on each component. -/
theorem csub_first (l : List PCell) :
    ∃ l', ReachFirst csubProg.toProg (Sum.inr AddI.done) (csubProg.start, l) l'
        ((2 * l.length + 2) + (2 * l.length + 2)) ∧
      (l'.map lensPRe.get) = (fscan fsub false (l.map lensPRe.get)).1 ∧
      (l'.map lensPIm.get) = (fscan fsub false (l.map lensPIm.get)).1 := by
  have r1 := sub_first (l.map lensPRe.get)
  rw [List.length_map] at r1
  obtain ⟨l1, r1', v1⟩ :=
    ProgOn.reachFirst_lens (ProgOn.ofProg subProg) lensPRe pz pbit r1 l rfl
  have f1 : l1.map lensPIm.get = l.map lensPIm.get :=
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg subProg) lensPRe pz pbit (fun _ _ => rfl)
      (fun _ _ => rfl) r1'
  have hl1 : l1.length = l.length := by
    have := congrArg List.length f1
    rwa [List.length_map, List.length_map] at this
  have r2 := sub_first (l1.map lensPIm.get)
  rw [List.length_map] at r2
  obtain ⟨l2, r2', v2⟩ :=
    ProgOn.reachFirst_lens (ProgOn.ofProg subProg) lensPIm pz pbit r2 l1 rfl
  have f2 : l2.map lensPRe.get = l1.map lensPRe.get :=
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg subProg) lensPIm pz pbit (fun _ _ => rfl)
      (fun _ _ => rfl) r2'
  have hc := ProgOn.seq_reachFirst ((ProgOn.ofProg subProg).viaLens lensPRe pz pbit)
    ((ProgOn.ofProg subProg).viaLens lensPIm pz pbit) AddI.done
    (show AddI.go ≠ AddI.done by decide) r1' r2'
  rw [hl1] at hc
  exact ⟨l2, hc, by rw [f2, v1], by rw [v2, f1]⟩

/-- **Signed complex addition and subtraction on the compiled Turing machine.** The component
tracks hold the `n`-bit codes of `z = x₁ + iy₁` and `w = x₂ + iy₂`, and the results lie in the
`n`-bit range. Then `caddProg` computes `z + w` and `csubProg` computes `z − w`, each in exactly
`2(2n + 2)` transitions, read back in two's complement. -/
theorem caddsub_tm (l : List PCell) (n : ℕ) (hl : l.length = n) (hn : 0 < n) (x₁ y₁ x₂ y₂ : ℤ)
    (h1 : val ((l.map lensPRe.get).map Cell.a) = tc n x₁)
    (h2 : val ((l.map lensPRe.get).map Cell.b) = tc n x₂)
    (h3 : val ((l.map lensPIm.get).map Cell.a) = tc n y₁)
    (h4 : val ((l.map lensPIm.get).map Cell.b) = tc n y₂)
    (ha : -(2 : ℤ) ^ (n - 1) ≤ x₁ + x₂ ∧ x₁ + x₂ < 2 ^ (n - 1) ∧
      -(2 : ℤ) ^ (n - 1) ≤ y₁ + y₂ ∧ y₁ + y₂ < 2 ^ (n - 1))
    (hs : -(2 : ℤ) ^ (n - 1) ≤ x₁ - x₂ ∧ x₁ - x₂ < 2 ^ (n - 1) ∧
      -(2 : ℤ) ^ (n - 1) ≤ y₁ - y₂ ∧ y₁ - y₂ < 2 ^ (n - 1))
    (T : ℤ → Sym PCell) (hTa : caddProg.toProg.Repr T l) (hTs : csubProg.toProg.Repr T l) :
    (∃ l' T', caddProg.toProg.Repr T' l' ∧
      sval n (val ((l'.map lensPRe.get).map Cell.r)) = x₁ + x₂ ∧
      sval n (val ((l'.map lensPIm.get).map Cell.r)) = y₁ + y₂ ∧
      caddProg.toProg.toTM.run ⟨.fwd caddProg.start (caddProg.toProg.init caddProg.start), T, 0⟩
          ((2 * n + 2) + (2 * n + 2)) =
        ⟨.fwd (Sum.inr AddI.done) (caddProg.toProg.init (Sum.inr AddI.done)), T', 0⟩) ∧
    (∃ l' T', csubProg.toProg.Repr T' l' ∧
      sval n (val ((l'.map lensPRe.get).map Cell.r)) = x₁ - x₂ ∧
      sval n (val ((l'.map lensPIm.get).map Cell.r)) = y₁ - y₂ ∧
      csubProg.toProg.toTM.run ⟨.fwd csubProg.start (csubProg.toProg.init csubProg.start), T, 0⟩
          ((2 * n + 2) + (2 * n + 2)) =
        ⟨.fwd (Sum.inr AddI.done) (csubProg.toProg.init (Sum.inr AddI.done)), T', 0⟩) := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
  constructor
  · obtain ⟨l', hr, e1, e2⟩ := cadd_first l
    obtain ⟨T', hT', hrun⟩ := caddProg.toProg.reach_run hr.reach T hTa
    rw [hl] at hr hrun e1 e2
    refine ⟨l', T', hT', ?_, ?_, hrun⟩
    · rw [e1, h1, h2, tc_add, sval_tc n hn _ ha1 ha2]
    · rw [e2, h3, h4, tc_add, sval_tc n hn _ ha3 ha4]
  · obtain ⟨l', hr, e1, e2⟩ := csub_first l
    obtain ⟨T', hT', hrun⟩ := csubProg.toProg.reach_run hr.reach T hTs
    rw [hl] at hrun
    refine ⟨l', T', hT', ?_, ?_, hrun⟩
    · rw [e1, sub_tc_value _ n (by rw [List.length_map, hl]) x₁ x₂ h1 h2,
        sval_tc n hn _ hs1 hs2]
    · rw [e2, sub_tc_value _ n (by rw [List.length_map, hl]) y₁ y₂ h3 h4,
        sval_tc n hn _ hs3 hs4]

end PVNP.Discrete.SweepArith
