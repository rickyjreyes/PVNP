import PVNP.SweepGcd
import PVNP.SweepSDiv

/-!
# Normalized rational arithmetic on the Turing machine

Signed fractions `a/b` and `c/d` (numerators in two's complement, positive denominators) are
added and multiplied by one machine each, composed of verified programs on the common alphabet
`GCell`:

* the verified multiplier (`SweepMul`) on the carried tracks `x, y, acc`, which accumulates
  products modulo `2ⁿ`: first `bd`, then `ad + cb` (or `ac`);
* sign and negate (`SweepSDiv`) on the accumulator, which leaves `|P|` and the sign of `P`;
* normalization (`SweepGcd`) of `|P|/Q`, by the verified Euclidean loop and two exact divisions;
* the sign correction (`SweepSDiv`) of the reduced numerator.

Cellwise maps move operands between tracks. Only the results must lie in range: the
products are exact codes modulo `2ⁿ`.

* `stage_mul`, `stage_negA`, `stage_fixR`: one stage on `GCell`, with its frame.
* `radd_layout`, `radd_tm`: **the sum** `a/b + c/d` as a normalized fraction `N/D`:
  `N = P / g`, `D = Q / g`, with `P = ad + cb`, `Q = bd` and `g = gcd(|P|, Q)`.
* `rmul_layout`, `rmul_tm`: **the product** `(a/b)(c/d)`, with `P = ac` and `Q = bd`.
* In both cases `N/D` equals the exact result, `gcd(|N|, D) = 1` and `D > 0`.
-/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-! ### Lenses into the carried block -/

/-- The multiplier's view. -/
def lensMx : TrackLens GCell MCell :=
  ⟨fun g => ⟨g.xc.x, g.xc.y, g.xc.acc⟩,
    fun g m => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
      ⟨m.x, m.y, m.acc, g.xc.fl, g.xc.z, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id⟩⟩,
    fun _ _ => rfl⟩

/-- Sign and negate the accumulator: word `acc`, flag `fl`, untouched flag `z`. -/
def lensNa : TrackLens GCell NCell :=
  ⟨fun g => ⟨g.xc.acc, g.xc.fl, g.xc.z⟩,
    fun g y => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
      ⟨g.xc.x, g.xc.y, y.w, y.f, y.g, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id⟩⟩,
    fun _ _ => rfl⟩

/-- Correct the sign of the reduced numerator: word `rp`, flags `fl` and `z`. -/
def lensNr : TrackLens GCell NCell :=
  ⟨fun g => ⟨g.rp, g.xc.fl, g.xc.z⟩,
    fun g y => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, y.w, g.rq,
      ⟨g.xc.x, g.xc.y, g.xc.acc, y.f, y.g, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id⟩⟩,
    fun _ _ => rfl⟩

/-- Everything the multiplier does not write that the later stages read. -/
def lensRk : TrackLens GCell (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) :=
  ⟨fun g => (g.c0, g.m0, g.xc.fl, g.xc.z, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id, g.qq),
    fun g k => ⟨g.dv, g.c, g.a, g.b, k.1, k.2.1, g.p, k.2.2.2.2.2.2.2.2, g.rp, g.rq,
      ⟨g.xc.x, g.xc.y, g.xc.acc, k.2.2.1, k.2.2.2.1, k.2.2.2.2.1, k.2.2.2.2.2.1, k.2.2.2.2.2.2.1,
        k.2.2.2.2.2.2.2.1⟩⟩,
    fun _ _ => rfl⟩

/-- Everything sign-and-negate does not write that the later stages read. -/
def lensRk2 : TrackLens GCell (Bool × Bool × Bool) :=
  ⟨fun g => (g.c0, g.m0, g.qq),
    fun g k => ⟨g.dv, g.c, g.a, g.b, k.1, k.2.1, g.p, k.2.2, g.rp, g.rq, g.xc⟩,
    fun _ _ => rfl⟩

/-- The reduced denominator, which the sign correction does not write. -/
def lensRq : TrackLens GCell Bool :=
  ⟨GCell.rq, fun g b => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, b, g.xc⟩,
    fun _ _ => rfl⟩

/-! ### The stages -/

/-- Load the multiplier with `b · d`. -/
def mBD (g : GCell) : GCell :=
  ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
    ⟨g.xc.ib, g.xc.id, false, g.xc.fl, g.xc.z, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id⟩⟩

/-- Save the denominator, then load the multiplier with `a · d`. -/
def mAD (g : GCell) : GCell :=
  ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.xc.acc, g.rp, g.rq,
    ⟨g.xc.ia, g.xc.id, false, g.xc.fl, g.xc.z, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id⟩⟩

/-- Load the multiplier with `c · b`, keeping the accumulator. -/
def mCB (g : GCell) : GCell :=
  ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
    ⟨g.xc.ic, g.xc.ib, g.xc.acc, g.xc.fl, g.xc.z, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id⟩⟩

/-- Save the denominator, then load the multiplier with `a · c`. -/
def mAC (g : GCell) : GCell :=
  ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.xc.acc, g.rp, g.rq,
    ⟨g.xc.ia, g.xc.ic, false, g.xc.fl, g.xc.z, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id⟩⟩

/-- Move the accumulator into the numerator track. -/
def mP (g : GCell) : GCell :=
  ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.xc.acc, g.qq, g.rp, g.rq, g.xc⟩

def MULX : ProgOn GCell := (ProgOn.ofProg mulProg).viaLens lensMx gz gbit
def CNEGA : ProgOn GCell := (ProgOn.ofProg cnegProg).viaLens lensNa gz gbit
def FIXR : ProgOn GCell := (ProgOn.ofProg fixProg).viaLens lensNr gz gbit

/-! ### One stage on `GCell` -/

/-- **The multiplier stage**: the accumulator becomes `(acc + x·y) mod 2ⁿ`. -/
theorem stage_mul (l : List GCell) (hl : l ≠ []) :
    ∃ l', ReachFirst MULX.toProg MulI.done (MulI.prep, l) l'
        ((trips (tv (fun g => g.xc.y) l) + 1) * (2 * l.length + 2)) ∧
      l'.length = l.length ∧
      tv (fun g => g.xc.acc) l' = (tv (fun g => g.xc.acc) l +
        tv (fun g => g.xc.x) l * tv (fun g => g.xc.y) l) % 2 ^ l.length ∧
      l'.map lensRk.get = l.map lensRk.get := by
  obtain ⟨m, hr, hlen, _, hv⟩ := mul_first (l.map lensMx.get) (by simpa using hl)
  have ey : vY (l.map lensMx.get) = tv (fun g => g.xc.y) l := by
    unfold vY tv; rw [List.map_map]; rfl
  have ex : vX (l.map lensMx.get) = tv (fun g => g.xc.x) l := by
    unfold vX tv; rw [List.map_map]; rfl
  have ea : vA (l.map lensMx.get) = tv (fun g => g.xc.acc) l := by
    unfold vA tv; rw [List.map_map]; rfl
  rw [ey, List.length_map] at hr
  rw [List.length_map] at hv hlen
  obtain ⟨l', hr', hv'⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg mulProg) lensMx gz gbit hr l rfl
  have hk : l'.map lensRk.get = l.map lensRk.get :=
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg mulProg) lensMx gz gbit (fun _ _ => rfl)
      (fun _ _ => rfl) hr'
  have hl' : l'.length = l.length := by
    have := congrArg List.length hk
    simpa using this
  refine ⟨l', hr', hl', ?_, hk⟩
  have hlt : vA m < 2 ^ l.length := by
    have := val_lt (m.map MCell.acc)
    rw [List.length_map, hlen] at this
    exact this
  have e : tv (fun g => g.xc.acc) l' = vA m := by
    rw [← hv']; unfold tv vA; rw [List.map_map]; rfl
  rw [e, ← Nat.mod_eq_of_lt hlt, hv, ea, ex, ey]

/-- **The sign-and-negate stage** on the accumulator, with its frame. -/
theorem stage_negA (l : List GCell) :
    ∃ l', ReachFirst CNEGA.toProg NegI.done (NegI.sgn, l) l'
        ((2 * l.length + 2) + (2 * l.length + 2)) ∧
      l'.map lensNa.get =
        (fscan (fnegBy NCell.f) true (setF (lastW false (l.map lensNa.get)) (l.map lensNa.get))).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens GCell D₂), lensNa.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := cneg_first (l.map lensNa.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg cnegProg) lensNa gz gbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg cnegProg) lensNa gz gbit (fun _ _ => rfl) hi hr'

/-- **The sign-correction stage** on the reduced numerator, with its frame. -/
theorem stage_fixR (l : List GCell) :
    ∃ l', ReachFirst FIXR.toProg AddI.done (AddI.go, l) l' (2 * l.length + 2) ∧
      l'.map lensNr.get = (fscan (fnegBy (fun z => xor z.f z.g)) true (l.map lensNr.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens GCell D₂), lensNr.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := fix_first (l.map lensNr.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg fixProg) lensNr gz gbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg fixProg) lensNr gz gbit (fun _ _ => rfl) hi hr'

/-! ### The layout -/

def lensIa : TrackLens GCell Bool :=
  ⟨fun g => g.xc.ia, fun g b => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
    ⟨g.xc.x, g.xc.y, g.xc.acc, g.xc.fl, g.xc.z, b, g.xc.ib, g.xc.ic, g.xc.id⟩⟩, fun _ _ => rfl⟩
def lensIb : TrackLens GCell Bool :=
  ⟨fun g => g.xc.ib, fun g b => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
    ⟨g.xc.x, g.xc.y, g.xc.acc, g.xc.fl, g.xc.z, g.xc.ia, b, g.xc.ic, g.xc.id⟩⟩, fun _ _ => rfl⟩
def lensIc : TrackLens GCell Bool :=
  ⟨fun g => g.xc.ic, fun g b => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
    ⟨g.xc.x, g.xc.y, g.xc.acc, g.xc.fl, g.xc.z, g.xc.ia, g.xc.ib, b, g.xc.id⟩⟩, fun _ _ => rfl⟩
def lensId : TrackLens GCell Bool :=
  ⟨fun g => g.xc.id, fun g b => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
    ⟨g.xc.x, g.xc.y, g.xc.acc, g.xc.fl, g.xc.z, g.xc.ia, g.xc.ib, g.xc.ic, b⟩⟩, fun _ _ => rfl⟩
def lensZ : TrackLens GCell Bool :=
  ⟨fun g => g.xc.z, fun g b => ⟨g.dv, g.c, g.a, g.b, g.c0, g.m0, g.p, g.qq, g.rp, g.rq,
    ⟨g.xc.x, g.xc.y, g.xc.acc, g.xc.fl, b, g.xc.ia, g.xc.ib, g.xc.ic, g.xc.id⟩⟩, fun _ _ => rfl⟩

/-- The rational layout on `2W` cells: the counter `W` and the marker `2^W`, and the operands:
the `2W`-bit codes of the numerators `a` and `c` and the denominators `b` and `d`. Every other
track is zero. -/
def ratInput (W : ℕ) (a : ℤ) (b : ℕ) (c : ℤ) (d : ℕ) : List GCell :=
  List.zipWith lensId.put
    (List.zipWith lensIc.put
      (List.zipWith lensIb.put
        (List.zipWith lensIa.put
          (List.zipWith lensM0.put
            (List.zipWith lensC0.put (List.replicate (2 * W) gz) (bitsOf (2 * W) W))
            (bitsOf (2 * W) (2 ^ W)))
          (bitsOf (2 * W) (tc (2 * W) a)))
        (bitsOf (2 * W) b))
      (bitsOf (2 * W) (tc (2 * W) c)))
    (bitsOf (2 * W) d)

theorem ratInput_spec (W : ℕ) (a : ℤ) (b : ℕ) (c : ℤ) (d : ℕ) :
    (ratInput W a b c d).length = 2 * W ∧
      tv GCell.c0 (ratInput W a b c d) = W % 2 ^ (2 * W) ∧
      tv GCell.m0 (ratInput W a b c d) = 2 ^ W % 2 ^ (2 * W) ∧
      tv (fun g => g.xc.ia) (ratInput W a b c d) = tc (2 * W) a ∧
      tv (fun g => g.xc.ib) (ratInput W a b c d) = b % 2 ^ (2 * W) ∧
      tv (fun g => g.xc.ic) (ratInput W a b c d) = tc (2 * W) c ∧
      tv (fun g => g.xc.id) (ratInput W a b c d) = d % 2 ^ (2 * W) ∧
      (ratInput W a b c d).map lensZ.get = (ratInput W a b c d).map (fun _ => false) := by
  set L0 := List.replicate (2 * W) gz with hL0
  have b0 : L0.length = 2 * W := List.length_replicate
  set L1 := List.zipWith lensC0.put L0 (bitsOf (2 * W) W) with hL1
  have b1 : L1.length = 2 * W := by
    rw [hL1, lensC0.length_zipWith _ _ (by rw [bitsOf_length, b0]), b0]
  set L2 := List.zipWith lensM0.put L1 (bitsOf (2 * W) (2 ^ W)) with hL2
  have b2 : L2.length = 2 * W := by
    rw [hL2, lensM0.length_zipWith _ _ (by rw [bitsOf_length, b1]), b1]
  set L3 := List.zipWith lensIa.put L2 (bitsOf (2 * W) (tc (2 * W) a)) with hL3
  have b3 : L3.length = 2 * W := by
    rw [hL3, lensIa.length_zipWith _ _ (by rw [bitsOf_length, b2]), b2]
  set L4 := List.zipWith lensIb.put L3 (bitsOf (2 * W) b) with hL4
  have b4 : L4.length = 2 * W := by
    rw [hL4, lensIb.length_zipWith _ _ (by rw [bitsOf_length, b3]), b3]
  set L5 := List.zipWith lensIc.put L4 (bitsOf (2 * W) (tc (2 * W) c)) with hL5
  have b5 : L5.length = 2 * W := by
    rw [hL5, lensIc.length_zipWith _ _ (by rw [bitsOf_length, b4]), b4]
  have e6 : ratInput W a b c d = List.zipWith lensId.put L5 (bitsOf (2 * W) d) := rfl
  have h6 : (bitsOf (2 * W) d).length = L5.length := by rw [bitsOf_length, b5]
  have h5 : (bitsOf (2 * W) (tc (2 * W) c)).length = L4.length := by rw [bitsOf_length, b4]
  have h4 : (bitsOf (2 * W) b).length = L3.length := by rw [bitsOf_length, b3]
  have h3 : (bitsOf (2 * W) (tc (2 * W) a)).length = L2.length := by rw [bitsOf_length, b2]
  have h2 : (bitsOf (2 * W) (2 ^ W)).length = L1.length := by rw [bitsOf_length, b1]
  have h1 : (bitsOf (2 * W) W).length = L0.length := by rw [bitsOf_length, b0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e6, lensId.length_zipWith _ _ h6, b5]
  · unfold tv
    rw [e6, show GCell.c0 = lensC0.get from rfl,
      lensId.frame_zipWith (ℓ₂ := lensC0) (fun _ _ => rfl) _ _ h6, hL5,
      lensIc.frame_zipWith (ℓ₂ := lensC0) (fun _ _ => rfl) _ _ h5, hL4,
      lensIb.frame_zipWith (ℓ₂ := lensC0) (fun _ _ => rfl) _ _ h4, hL3,
      lensIa.frame_zipWith (ℓ₂ := lensC0) (fun _ _ => rfl) _ _ h3, hL2,
      lensM0.frame_zipWith (ℓ₂ := lensC0) (fun _ _ => rfl) _ _ h2, hL1,
      lensC0.map_get_zipWith _ _ h1, val_bitsOf]
  · unfold tv
    rw [e6, show GCell.m0 = lensM0.get from rfl,
      lensId.frame_zipWith (ℓ₂ := lensM0) (fun _ _ => rfl) _ _ h6, hL5,
      lensIc.frame_zipWith (ℓ₂ := lensM0) (fun _ _ => rfl) _ _ h5, hL4,
      lensIb.frame_zipWith (ℓ₂ := lensM0) (fun _ _ => rfl) _ _ h4, hL3,
      lensIa.frame_zipWith (ℓ₂ := lensM0) (fun _ _ => rfl) _ _ h3, hL2,
      lensM0.map_get_zipWith _ _ h2, val_bitsOf]
  · unfold tv
    rw [e6, show (fun g : GCell => g.xc.ia) = lensIa.get from rfl,
      lensId.frame_zipWith (ℓ₂ := lensIa) (fun _ _ => rfl) _ _ h6, hL5,
      lensIc.frame_zipWith (ℓ₂ := lensIa) (fun _ _ => rfl) _ _ h5, hL4,
      lensIb.frame_zipWith (ℓ₂ := lensIa) (fun _ _ => rfl) _ _ h4, hL3,
      lensIa.map_get_zipWith _ _ h3, val_bitsOf, Nat.mod_eq_of_lt (tc_lt _ _)]
  · unfold tv
    rw [e6, show (fun g : GCell => g.xc.ib) = lensIb.get from rfl,
      lensId.frame_zipWith (ℓ₂ := lensIb) (fun _ _ => rfl) _ _ h6, hL5,
      lensIc.frame_zipWith (ℓ₂ := lensIb) (fun _ _ => rfl) _ _ h5, hL4,
      lensIb.map_get_zipWith _ _ h4, val_bitsOf]
  · unfold tv
    rw [e6, show (fun g : GCell => g.xc.ic) = lensIc.get from rfl,
      lensId.frame_zipWith (ℓ₂ := lensIc) (fun _ _ => rfl) _ _ h6, hL5,
      lensIc.map_get_zipWith _ _ h5, val_bitsOf, Nat.mod_eq_of_lt (tc_lt _ _)]
  · unfold tv
    rw [e6, show (fun g : GCell => g.xc.id) = lensId.get from rfl,
      lensId.map_get_zipWith _ _ h6, val_bitsOf]
  · have hz : (ratInput W a b c d).map lensZ.get = L0.map lensZ.get := by
      rw [e6, lensId.frame_zipWith (ℓ₂ := lensZ) (fun _ _ => rfl) _ _ h6, hL5,
        lensIc.frame_zipWith (ℓ₂ := lensZ) (fun _ _ => rfl) _ _ h5, hL4,
        lensIb.frame_zipWith (ℓ₂ := lensZ) (fun _ _ => rfl) _ _ h4, hL3,
        lensIa.frame_zipWith (ℓ₂ := lensZ) (fun _ _ => rfl) _ _ h3, hL2,
        lensM0.frame_zipWith (ℓ₂ := lensZ) (fun _ _ => rfl) _ _ h2, hL1,
        lensC0.frame_zipWith (ℓ₂ := lensZ) (fun _ _ => rfl) _ _ h1]
    have hlen : (ratInput W a b c d).length = 2 * W := by
      rw [e6, lensId.length_zipWith _ _ h6, b5]
    rw [hz, hL0, List.map_replicate, List.map_const', hlen]
    rfl

/-! ### The common tail: sign, normalize, correct the sign -/

def T1 : ProgOn GCell := ProgOn.seq CNEGA (MAPG mP) NegI.done
def T2 : ProgOn GCell := ProgOn.seq T1 normProg (Sum.inr AddI.done)

/-- **The tail**: sign and negate the accumulator `P`, load `|P|` as the numerator, normalize
`|P|/Q`, and give the reduced numerator the sign of `P`. -/
def TAIL : ProgOn GCell := ProgOn.seq T2 FIXR (Sum.inr (Sum.inr AddI.done))

/-- **The tail on any tape.** If the accumulator holds the `2W`-bit code of `P` with `|P| < 2^W`
and the denominator track holds `0 < Q < 2^W`, the tail first-arrives at its exit with the
reduced numerator `P / g` (read in two's complement) and denominator `Q / g`,
`g = gcd(|P|, Q)`. -/
theorem tail_run {W : ℕ} (hW : 0 < W) (l : List GCell) (hlen : l.length = 2 * W) {P : ℤ} {Q : ℕ}
    (hP : |P| < 2 ^ W) (hQ0 : 0 < Q) (hQ : Q < 2 ^ W)
    (hacc : tv (fun g => g.xc.acc) l = tc (2 * W) P) (hqq : tv GCell.qq l = Q)
    (hc0 : tv GCell.c0 l = W) (hm0 : tv GCell.m0 l = 2 ^ W)
    (hz : l.map lensZ.get = l.map (fun _ => false)) :
    ∃ l', ReachFirst TAIL.toProg (Sum.inr AddI.done) (TAIL.start, l) l'
        ((euclidSteps P.natAbs Q * (4 * W + 6) + 8 * W + 16) * (4 * W + 2)) ∧
      sval (2 * W) (tv GCell.rp l') = P / (Nat.gcd P.natAbs Q : ℤ) ∧
      tv GCell.rq l' = Q / Nat.gcd P.natAbs Q := by
  have hn0 : 0 < 2 * W := by omega
  have hPW : (0 : ℤ) < 2 ^ W := by positivity
  have hn1 : (2 : ℤ) ^ (2 * W - 1) = 2 ^ (W - 1) * 2 ^ W := by
    rw [← pow_add]; congr 1; omega
  have h1W : (1 : ℤ) ≤ 2 ^ (W - 1) := one_le_pow₀ (by norm_num)
  have hWn : (2 : ℤ) ^ W ≤ 2 ^ (2 * W - 1) := by rw [hn1]; exact le_mul_of_one_le_left hPW.le h1W
  obtain ⟨hP1, hP2⟩ := abs_lt.mp (lt_of_lt_of_le hP hWn)
  -- stage 1: sign and negate the accumulator
  obtain ⟨l1, r1, e1, f1⟩ := stage_negA l
  have hne : l.map lensNa.get ≠ [] := by
    intro h
    rw [List.map_eq_nil_iff] at h
    rw [h, List.length_nil] at hlen
    omega
  obtain ⟨s1w, s1f, s1g, -⟩ := cneg_spec (l.map lensNa.get) hne
  have hvl : (l.map lensNa.get).length = 2 * W := by rw [List.length_map, hlen]
  have hvw : vW (l.map lensNa.get) = tc (2 * W) P := by
    rw [← hacc]; unfold vW tv; rw [List.map_map]; rfl
  obtain ⟨absP, sgnP⟩ := cneg_abs (2 * W) hn0 P hP1.le hP2
  rw [hvl, hvw, absP] at s1w
  rw [hvl, hvw] at s1f
  rw [← e1] at s1w s1f s1g
  set sP := decide (2 ^ (2 * W - 1) ≤ tc (2 * W) P) with hsP
  have k1 : l1.map lensRk2.get = l.map lensRk2.get := f1 lensRk2 (fun _ _ => rfl)
  have len1 : l1.length = 2 * W := by
    have := congrArg List.length k1
    simp only [List.length_map] at this
    rw [this, hlen]
  -- stage 2: load the numerator
  have r2 := map_first mP gbit l1
  have len2 : (l1.map mP).length = 2 * W := by rw [List.length_map, len1]
  have p2 : tv GCell.p (l1.map mP) = P.natAbs := by
    rw [tv_map, ← s1w]; unfold vW tv; rw [List.map_map]; rfl
  have qq2 : tv GCell.qq (l1.map mP) = Q := by
    rw [tv_map, ← hqq]
    have := congrArg (List.map (fun k => k.2.2)) k1
    simp only [List.map_map] at this
    unfold tv
    exact congrArg val this
  have c02 : tv GCell.c0 (l1.map mP) = W := by
    rw [tv_map, ← hc0]
    have := congrArg (List.map (fun k => k.1)) k1
    simp only [List.map_map] at this
    unfold tv
    exact congrArg val this
  have m02 : tv GCell.m0 (l1.map mP) = 2 ^ W := by
    rw [tv_map, ← hm0]
    have := congrArg (List.map (fun k => k.2.1)) k1
    simp only [List.map_map] at this
    unfold tv
    exact congrArg val this
  -- stage 3: normalize
  have hPn : P.natAbs < 2 ^ W := by
    have h : ((P.natAbs : ℕ) : ℤ) < ((2 ^ W : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; push_cast; exact hP
    exact_mod_cast h
  obtain ⟨l3, r3, len3, rp3, rq3, x3⟩ := norm_run (l1.map mP) len2 hPn hQ0 hQ p2 qq2 c02 m02
  -- stage 4: correct the sign
  obtain ⟨l4, r4, e4, f4⟩ := stage_fixR l3
  have xc3 : l3.map GCell.xc = l1.map GCell.xc := by
    rw [x3, List.map_map]; rfl
  have a3 : ∀ z ∈ l3.map lensNr.get, z.f = sP := by
    apply all_eq_of_map (k := l)
    have h1 : (l3.map lensNr.get).map NCell.f = (l3.map GCell.xc).map XCell.fl := by
      rw [List.map_map, List.map_map]; rfl
    have h2 : (l1.map GCell.xc).map XCell.fl = (l1.map lensNa.get).map NCell.f := by
      rw [List.map_map, List.map_map]; rfl
    rw [h1, xc3, h2, s1f, List.map_map]
    rfl
  have b3 : ∀ z ∈ l3.map lensNr.get, z.g = false := by
    apply all_eq_of_map (k := l)
    have h1 : (l3.map lensNr.get).map NCell.g = (l3.map GCell.xc).map XCell.z := by
      rw [List.map_map, List.map_map]; rfl
    have h2 : (l1.map GCell.xc).map XCell.z = (l1.map lensNa.get).map NCell.g := by
      rw [List.map_map, List.map_map]; rfl
    have h3 : (l.map lensNa.get).map NCell.g = l.map lensZ.get := by
      rw [List.map_map]; rfl
    rw [h1, xc3, h2, s1g, h3, hz]
  have s4 := fix_spec (l3.map lensNr.get) sP false a3 b3
  rw [← e4] at s4
  have hrp3 : vW (l3.map lensNr.get) = P.natAbs / Nat.gcd P.natAbs Q := by
    rw [← rp3]; unfold vW tv; rw [List.map_map]; rfl
  rw [hrp3, List.length_map, len3, len2] at s4
  -- the composite
  have hc := ProgOn.seq_reachFirst T2 FIXR (Sum.inr (Sum.inr AddI.done))
    (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst T1 normProg (Sum.inr AddI.done) Sum.inl_ne_inr
      (ProgOn.seq_reachFirst CNEGA (MAPG mP) NegI.done (show AddI.go ≠ AddI.done by decide) r1 r2)
      r3) r4
  rw [hlen, len1, len3, len2] at hc
  refine ⟨l4, ?_, ?_, ?_⟩
  · convert hc using 1
    ring
  · -- the reduced numerator
    have eq4 : tv GCell.rp l4 = vW (l4.map lensNr.get) := by
      unfold vW tv; rw [List.map_map]; rfl
    set g := Nat.gcd P.natAbs Q with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hQ0
    have hdvd : g ∣ P.natAbs := Nat.gcd_dvd_left _ _
    set r := P.natAbs / g with hr
    have hrg : P.natAbs = g * r := (Nat.mul_div_cancel' hdvd).symm
    have hrW : r < 2 ^ W := lt_of_le_of_lt (Nat.div_le_self _ _) hPn
    have hrn : r < 2 ^ (2 * W) := lt_of_lt_of_le hrW (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hrz : (r : ℤ) < 2 ^ (2 * W - 1) := by
      have : (r : ℤ) < 2 ^ W := by exact_mod_cast hrW
      exact lt_of_lt_of_le this hWn
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
    rw [eq4, s4]
    by_cases hneg : P < 0
    · have hs : sP = true := by rw [hsP]; exact decide_eq_true (sgnP.mpr hneg)
      rw [if_pos (by rw [hs]; rfl)]
      conv_lhs => rw [← tc_natCast hrn]
      rw [tc_neg, sval_tc (2 * W) hn0 _ (by linarith) (by linarith)]
      symm
      apply Int.ediv_eq_of_eq_mul_right hgz
      have : (P.natAbs : ℤ) = -P := by omega
      have h2 : ((P.natAbs : ℕ) : ℤ) = (g : ℤ) * r := by exact_mod_cast hrg
      linarith
    · have hs : sP = false := by
        rw [hsP]; exact decide_eq_false (fun h => hneg (sgnP.mp h))
      rw [if_neg (by rw [hs]; decide)]
      conv_lhs => rw [← tc_natCast hrn]
      rw [sval_tc (2 * W) hn0 _ (by linarith) hrz]
      symm
      apply Int.ediv_eq_of_eq_mul_right hgz
      have : (P.natAbs : ℤ) = P := by omega
      have h2 : ((P.natAbs : ℕ) : ℤ) = (g : ℤ) * r := by exact_mod_cast hrg
      linarith
  · -- the reduced denominator
    have e : tv GCell.rq l4 = tv GCell.rq l3 := by
      unfold tv
      exact congrArg val (f4 lensRq (fun _ _ => rfl))
    rw [e, rq3]

/-! ### The sum and the product -/

def P1 : ProgOn GCell := ProgOn.seq (MAPG mBD) MULX AddI.done
def P2 : ProgOn GCell := ProgOn.seq P1 (MAPG mAD) (Sum.inr MulI.done)
def P3 : ProgOn GCell := ProgOn.seq P2 MULX (Sum.inr AddI.done)
def P4 : ProgOn GCell := ProgOn.seq P3 (MAPG mCB) (Sum.inr MulI.done)
def PADD : ProgOn GCell := ProgOn.seq P4 MULX (Sum.inr AddI.done)
def Q2 : ProgOn GCell := ProgOn.seq P1 (MAPG mAC) (Sum.inr MulI.done)
def PMUL : ProgOn GCell := ProgOn.seq Q2 MULX (Sum.inr AddI.done)

/-- **The rational adder**: `Q = bd`, `P = ad + cb`, then the tail. -/
def raddProg : ProgOn GCell := ProgOn.seq PADD TAIL (Sum.inr MulI.done)

/-- **The rational multiplier**: `Q = bd`, `P = ac`, then the tail. -/
def rmulProg : ProgOn GCell := ProgOn.seq PMUL TAIL (Sum.inr MulI.done)

/-- The tracks of the first multiplication. -/
theorem first_stage {W : ℕ} (hW : 0 < W) {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbd : b * d < 2 ^ W) :
    ∃ l2, ReachFirst P1.toProg (Sum.inr MulI.done) (P1.start, ratInput W a b c d) l2
        ((1 + (trips d + 1)) * (4 * W + 2)) ∧
      l2.length = 2 * W ∧ tv (fun g => g.xc.acc) l2 = b * d ∧
      tv GCell.c0 l2 = W ∧ tv GCell.m0 l2 = 2 ^ W ∧
      tv (fun g => g.xc.ia) l2 = tc (2 * W) a ∧ tv (fun g => g.xc.ib) l2 = b ∧
      tv (fun g => g.xc.ic) l2 = tc (2 * W) c ∧ tv (fun g => g.xc.id) l2 = d ∧
      l2.map lensZ.get = l2.map (fun _ => false) := by
  obtain ⟨len0, c00, m00, ia0, ib0, ic0, id0, z0⟩ := ratInput_spec W a b c d
  have hWW : 2 ^ W < 2 ^ (2 * W) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hb2 : b < 2 ^ (2 * W) := lt_trans (lt_of_le_of_lt (Nat.le_mul_of_pos_right b hd) hbd) hWW
  have hd2 : d < 2 ^ (2 * W) := lt_trans (lt_of_le_of_lt (Nat.le_mul_of_pos_left d hb) hbd) hWW
  rw [Nat.mod_eq_of_lt (lt_trans Nat.lt_two_pow_self hWW)] at c00
  rw [Nat.mod_eq_of_lt hWW] at m00
  rw [Nat.mod_eq_of_lt hb2] at ib0
  rw [Nat.mod_eq_of_lt hd2] at id0
  have r1 := map_first mBD gbit (ratInput W a b c d)
  have hne : (ratInput W a b c d).map mBD ≠ [] := by
    intro h
    rw [List.map_eq_nil_iff] at h
    rw [h, List.length_nil] at len0
    omega
  obtain ⟨l2, r2, len2, acc2, k2⟩ := stage_mul _ hne
  have ty : tv (fun g => g.xc.y) ((ratInput W a b c d).map mBD) = d := by rw [tv_map]; exact id0
  have tx : tv (fun g => g.xc.x) ((ratInput W a b c d).map mBD) = b := by rw [tv_map]; exact ib0
  have ta : tv (fun g => g.xc.acc) ((ratInput W a b c d).map mBD) = 0 := by
    rw [tv_map]; exact val_false _
  rw [ty, List.length_map, len0, show 2 * (2 * W) + 2 = 4 * W + 2 by ring] at r2
  have hc := ProgOn.seq_reachFirst (MAPG mBD) MULX AddI.done
    (show MulI.prep ≠ MulI.done by decide) r1 r2
  rw [len0] at hc
  have kk : ∀ {β : Type} (π : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool → β),
      l2.map (fun x => π (lensRk.get x)) =
        ((ratInput W a b c d).map mBD).map (fun x => π (lensRk.get x)) := by
    intro β π
    have := congrArg (List.map π) k2
    simpa [List.map_map, Function.comp_def] using this
  refine ⟨l2, by convert hc using 1; ring, by rw [len2, List.length_map, len0], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [acc2, ta, tx, ty, List.length_map, len0, zero_add,
      Nat.mod_eq_of_lt (lt_trans hbd hWW)]
  · have h : l2.map GCell.c0 = ((ratInput W a b c d).map mBD).map GCell.c0 := kk (fun k => k.1)
    unfold tv; rw [h, List.map_map]; exact c00
  · have h : l2.map GCell.m0 = ((ratInput W a b c d).map mBD).map GCell.m0 := kk (fun k => k.2.1)
    unfold tv; rw [h, List.map_map]; exact m00
  · have h : l2.map (fun g => g.xc.ia) = ((ratInput W a b c d).map mBD).map (fun g => g.xc.ia) :=
      kk (fun k => k.2.2.2.2.1)
    unfold tv; exact (congrArg val h).trans (by rw [List.map_map]; exact ia0)
  · have h : l2.map (fun g => g.xc.ib) = ((ratInput W a b c d).map mBD).map (fun g => g.xc.ib) :=
      kk (fun k => k.2.2.2.2.2.1)
    unfold tv; exact (congrArg val h).trans (by rw [List.map_map]; exact ib0)
  · have h : l2.map (fun g => g.xc.ic) = ((ratInput W a b c d).map mBD).map (fun g => g.xc.ic) :=
      kk (fun k => k.2.2.2.2.2.2.1)
    unfold tv; exact (congrArg val h).trans (by rw [List.map_map]; exact ic0)
  · have h : l2.map (fun g => g.xc.id) = ((ratInput W a b c d).map mBD).map (fun g => g.xc.id) :=
      kk (fun k => k.2.2.2.2.2.2.2.1)
    unfold tv; exact (congrArg val h).trans (by rw [List.map_map]; exact id0)
  · have h1 : l2.map lensZ.get = ((ratInput W a b c d).map mBD).map lensZ.get :=
      kk (fun k => k.2.2.2.1)
    have h2 : ((ratInput W a b c d).map mBD).map lensZ.get = (ratInput W a b c d).map lensZ.get := by
      rw [List.map_map]; rfl
    have h3 : l2.length = (ratInput W a b c d).length := by rw [len2, List.length_map]
    rw [h1, h2, z0, List.map_const', List.map_const', h3]

/-- **The rational adder on the layout.** For `0 < b`, `0 < d` with `bd < 2^W` and
`|ad + cb| < 2^W`, the adder first-arrives at its exit in exactly
`(2·trips d + trips b + s(4W + 6) + 8W + 22)(4W + 2)` transitions. Read in `2W`-bit two's
complement, the reduced numerator is `P / g` and the reduced denominator is `Q / g`, with
`P = ad + cb`, `Q = bd` and `g = gcd(|P|, Q)`. -/
theorem radd_layout {W : ℕ} (hW : 0 < W) {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbd : b * d < 2 ^ W) (hP : |a * d + c * b| < 2 ^ W) :
    ∃ l', ReachFirst raddProg.toProg (Sum.inr (Sum.inr AddI.done)) (raddProg.start, ratInput W a b c d) l'
        ((2 * trips d + trips b + euclidSteps (a * d + c * b).natAbs (b * d) * (4 * W + 6) +
          8 * W + 22) * (4 * W + 2)) ∧
      sval (2 * W) (tv GCell.rp l') =
        (a * d + c * b) / (Nat.gcd (a * d + c * b).natAbs (b * d) : ℤ) ∧
      tv GCell.rq l' = b * d / Nat.gcd (a * d + c * b).natAbs (b * d) := by
  obtain ⟨l2, r12, len2, acc2, c02, m02, ia2, ib2, ic2, id2, z2⟩ :=
    first_stage hW (a := a) (c := c) hb hd hbd
  have hWW : 2 ^ W < 2 ^ (2 * W) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hb2 : b < 2 ^ (2 * W) := lt_trans (lt_of_le_of_lt (Nat.le_mul_of_pos_right b hd) hbd) hWW
  have hd2 : d < 2 ^ (2 * W) := lt_trans (lt_of_le_of_lt (Nat.le_mul_of_pos_left d hb) hbd) hWW
  have hbb : tc (2 * W) (b : ℤ) = b := tc_natCast hb2
  have hdd : tc (2 * W) (d : ℤ) = d := tc_natCast hd2
  have hne : ∀ l : List GCell, l.length = 2 * W → l ≠ [] := by
    intro l hl h; rw [h, List.length_nil] at hl; omega
  -- load `a · d`, saving `Q = b · d`
  have r3 := map_first mAD gbit l2
  have len3 : (l2.map mAD).length = 2 * W := by rw [List.length_map, len2]
  obtain ⟨l4, r4, len4, acc4, k4⟩ := stage_mul (l2.map mAD) (hne _ len3)
  have y3 : tv (fun g => g.xc.y) (l2.map mAD) = d := by rw [tv_map]; exact id2
  rw [y3, len3, show 2 * (2 * W) + 2 = 4 * W + 2 by ring] at r4
  have ad : tv (fun g => g.xc.acc) l4 = tc (2 * W) (a * d) := by
    rw [acc4, len3, tv_map, tv_map, tv_map]
    have hx : tv (fun x => (mAD x).xc.x) l2 = tc (2 * W) a := ia2
    have hy : tv (fun x => (mAD x).xc.y) l2 = d := id2
    have ha : tv (fun x => (mAD x).xc.acc) l2 = 0 := val_false l2
    rw [hx, hy, ha, zero_add]
    have := tc_mul (2 * W) a (d : ℤ)
    rwa [hdd] at this
  have kk4 : ∀ {β : Type} (π : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool → β),
      l4.map (fun x => π (lensRk.get x)) = (l2.map mAD).map (fun x => π (lensRk.get x)) := by
    intro β π
    have := congrArg (List.map π) k4
    simpa [List.map_map, Function.comp_def] using this
  -- load `c · b`, keeping the accumulator
  have r5 := map_first mCB gbit l4
  have len4' : l4.length = 2 * W := by rw [len4, len3]
  have len5 : (l4.map mCB).length = 2 * W := by rw [List.length_map, len4']
  obtain ⟨l6, r6, len6, acc6, k6⟩ := stage_mul (l4.map mCB) (hne _ len5)
  have y5 : tv (fun g => g.xc.y) (l4.map mCB) = b := by
    rw [tv_map]
    have h : l4.map (fun g => g.xc.ib) = (l2.map mAD).map (fun g => g.xc.ib) :=
      kk4 (fun k => k.2.2.2.2.2.1)
    unfold tv
    exact (congrArg val h).trans (by rw [List.map_map]; exact ib2)
  have x5 : tv (fun g => g.xc.x) (l4.map mCB) = tc (2 * W) c := by
    rw [tv_map]
    have h : l4.map (fun g => g.xc.ic) = (l2.map mAD).map (fun g => g.xc.ic) :=
      kk4 (fun k => k.2.2.2.2.2.2.1)
    unfold tv
    exact (congrArg val h).trans (by rw [List.map_map]; exact ic2)
  have a5 : tv (fun g => g.xc.acc) (l4.map mCB) = tc (2 * W) (a * d) := by rw [tv_map]; exact ad
  rw [y5, len5, show 2 * (2 * W) + 2 = 4 * W + 2 by ring] at r6
  have hP6 : tv (fun g => g.xc.acc) l6 = tc (2 * W) (a * d + c * b) := by
    rw [acc6, len5, a5, x5, y5]
    have cb := tc_mul (2 * W) c (b : ℤ)
    rw [hbb] at cb
    rw [Nat.add_mod, Nat.mod_eq_of_lt (tc_lt _ _), cb, tc_add]
  have kk6 : ∀ {β : Type} (π : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool → β),
      l6.map (fun x => π (lensRk.get x)) = (l4.map mCB).map (fun x => π (lensRk.get x)) := by
    intro β π
    have := congrArg (List.map π) k6
    simpa [List.map_map, Function.comp_def] using this
  have len6' : l6.length = 2 * W := by rw [len6, len5]
  -- the tracks the tail reads
  have qq6 : tv GCell.qq l6 = b * d := by
    have h6 : l6.map GCell.qq = (l4.map mCB).map GCell.qq := kk6 (fun k => k.2.2.2.2.2.2.2.2)
    have h4 : l4.map GCell.qq = (l2.map mAD).map GCell.qq := kk4 (fun k => k.2.2.2.2.2.2.2.2)
    unfold tv
    rw [h6, List.map_map, show (GCell.qq ∘ mCB) = GCell.qq from rfl, h4, List.map_map]
    exact acc2
  have c06 : tv GCell.c0 l6 = W := by
    have h6 : l6.map GCell.c0 = (l4.map mCB).map GCell.c0 := kk6 (fun k => k.1)
    have h4 : l4.map GCell.c0 = (l2.map mAD).map GCell.c0 := kk4 (fun k => k.1)
    unfold tv
    rw [h6, List.map_map, show (GCell.c0 ∘ mCB) = GCell.c0 from rfl, h4, List.map_map]
    exact c02
  have m06 : tv GCell.m0 l6 = 2 ^ W := by
    have h6 : l6.map GCell.m0 = (l4.map mCB).map GCell.m0 := kk6 (fun k => k.2.1)
    have h4 : l4.map GCell.m0 = (l2.map mAD).map GCell.m0 := kk4 (fun k => k.2.1)
    unfold tv
    rw [h6, List.map_map, show (GCell.m0 ∘ mCB) = GCell.m0 from rfl, h4, List.map_map]
    exact m02
  have z6 : l6.map lensZ.get = l6.map (fun _ => false) := by
    have h6 : l6.map lensZ.get = (l4.map mCB).map lensZ.get := kk6 (fun k => k.2.2.2.1)
    have h4 : l4.map lensZ.get = (l2.map mAD).map lensZ.get := kk4 (fun k => k.2.2.2.1)
    rw [h6, List.map_map, show (lensZ.get ∘ mCB) = lensZ.get from rfl, h4, List.map_map,
      show (lensZ.get ∘ mAD) = lensZ.get from rfl, z2, List.map_const', List.map_const', len6',
      len2]
  -- the tail
  have hQ0 : 0 < b * d := Nat.mul_pos hb hd
  obtain ⟨l7, r7, hrp, hrq⟩ := tail_run hW l6 len6' hP hQ0 hbd hP6 qq6 c06 m06 z6
  -- the composite
  have hc := ProgOn.seq_reachFirst PADD TAIL (Sum.inr MulI.done) Sum.inl_ne_inr
    (ProgOn.seq_reachFirst P4 MULX (Sum.inr AddI.done) (show MulI.prep ≠ MulI.done by decide)
      (ProgOn.seq_reachFirst P3 (MAPG mCB) (Sum.inr MulI.done) (show AddI.go ≠ AddI.done by decide)
        (ProgOn.seq_reachFirst P2 MULX (Sum.inr AddI.done) (show MulI.prep ≠ MulI.done by decide)
          (ProgOn.seq_reachFirst P1 (MAPG mAD) (Sum.inr MulI.done)
            (show AddI.go ≠ AddI.done by decide) r12 r3)
          r4) r5) r6) r7
  rw [len2, len4'] at hc
  refine ⟨l7, ?_, hrp, hrq⟩
  convert hc using 1
  ring

/-- **The rational multiplier on the layout.** For `0 < b`, `0 < d` with `bd < 2^W` and
`|ac| < 2^W`, the multiplier first-arrives at its exit in exactly
`(trips d + trips (tc_{2W} c) + s(4W + 6) + 8W + 20)(4W + 2)` transitions. The reduced numerator
is `P / g` and the reduced denominator `Q / g`, with `P = ac`, `Q = bd` and `g = gcd(|P|, Q)`. -/
theorem rmul_layout {W : ℕ} (hW : 0 < W) {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbd : b * d < 2 ^ W) (hP : |a * c| < 2 ^ W) :
    ∃ l', ReachFirst rmulProg.toProg (Sum.inr (Sum.inr AddI.done)) (rmulProg.start, ratInput W a b c d) l'
        ((trips d + trips (tc (2 * W) c) + euclidSteps (a * c).natAbs (b * d) * (4 * W + 6) +
          8 * W + 20) * (4 * W + 2)) ∧
      sval (2 * W) (tv GCell.rp l') = (a * c) / (Nat.gcd (a * c).natAbs (b * d) : ℤ) ∧
      tv GCell.rq l' = b * d / Nat.gcd (a * c).natAbs (b * d) := by
  obtain ⟨l2, r12, len2, acc2, c02, m02, ia2, ib2, ic2, id2, z2⟩ :=
    first_stage hW (a := a) (c := c) hb hd hbd
  have hne : ∀ l : List GCell, l.length = 2 * W → l ≠ [] := by
    intro l hl h; rw [h, List.length_nil] at hl; omega
  -- load `a · c`, saving `Q = b · d`
  have r3 := map_first mAC gbit l2
  have len3 : (l2.map mAC).length = 2 * W := by rw [List.length_map, len2]
  obtain ⟨l4, r4, len4, acc4, k4⟩ := stage_mul (l2.map mAC) (hne _ len3)
  have y3 : tv (fun g => g.xc.y) (l2.map mAC) = tc (2 * W) c := by rw [tv_map]; exact ic2
  rw [y3, len3, show 2 * (2 * W) + 2 = 4 * W + 2 by ring] at r4
  have hP4 : tv (fun g => g.xc.acc) l4 = tc (2 * W) (a * c) := by
    rw [acc4, len3, tv_map, tv_map, tv_map]
    have hx : tv (fun x => (mAC x).xc.x) l2 = tc (2 * W) a := ia2
    have hy : tv (fun x => (mAC x).xc.y) l2 = tc (2 * W) c := ic2
    have ha : tv (fun x => (mAC x).xc.acc) l2 = 0 := val_false l2
    rw [hx, hy, ha, zero_add, tc_mul]
  have kk4 : ∀ {β : Type} (π : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool → β),
      l4.map (fun x => π (lensRk.get x)) = (l2.map mAC).map (fun x => π (lensRk.get x)) := by
    intro β π
    have := congrArg (List.map π) k4
    simpa [List.map_map, Function.comp_def] using this
  have len4' : l4.length = 2 * W := by rw [len4, len3]
  have qq4 : tv GCell.qq l4 = b * d := by
    have h4 : l4.map GCell.qq = (l2.map mAC).map GCell.qq := kk4 (fun k => k.2.2.2.2.2.2.2.2)
    unfold tv
    rw [h4, List.map_map]
    exact acc2
  have c04 : tv GCell.c0 l4 = W := by
    have h4 : l4.map GCell.c0 = (l2.map mAC).map GCell.c0 := kk4 (fun k => k.1)
    unfold tv
    rw [h4, List.map_map]
    exact c02
  have m04 : tv GCell.m0 l4 = 2 ^ W := by
    have h4 : l4.map GCell.m0 = (l2.map mAC).map GCell.m0 := kk4 (fun k => k.2.1)
    unfold tv
    rw [h4, List.map_map]
    exact m02
  have z4 : l4.map lensZ.get = l4.map (fun _ => false) := by
    have h4 : l4.map lensZ.get = (l2.map mAC).map lensZ.get := kk4 (fun k => k.2.2.2.1)
    rw [h4, List.map_map, show (lensZ.get ∘ mAC) = lensZ.get from rfl, z2, List.map_const',
      List.map_const', len4', len2]
  have hQ0 : 0 < b * d := Nat.mul_pos hb hd
  obtain ⟨l5, r5, hrp, hrq⟩ := tail_run hW l4 len4' hP hQ0 hbd hP4 qq4 c04 m04 z4
  have hc := ProgOn.seq_reachFirst PMUL TAIL (Sum.inr MulI.done) Sum.inl_ne_inr
    (ProgOn.seq_reachFirst Q2 MULX (Sum.inr AddI.done) (show MulI.prep ≠ MulI.done by decide)
      (ProgOn.seq_reachFirst P1 (MAPG mAC) (Sum.inr MulI.done)
        (show AddI.go ≠ AddI.done by decide) r12 r3)
      r4) r5
  rw [len2] at hc
  refine ⟨l5, ?_, hrp, hrq⟩
  convert hc using 1
  ring

/-! ### The reduced fractions -/

/-- **Reduction by the gcd.** For `0 < Q`, the pair `(P / g, Q / g)` with `g = gcd(|P|, Q)` is
coprime, has a positive denominator, and has the value `P / Q`. -/
theorem reduced_frac (P : ℤ) (Q : ℕ) (hQ : 0 < Q) :
    Nat.Coprime (P / (Nat.gcd P.natAbs Q : ℤ)).natAbs (Q / Nat.gcd P.natAbs Q) ∧
      0 < Q / Nat.gcd P.natAbs Q ∧
      ((P / (Nat.gcd P.natAbs Q : ℤ) : ℤ) : ℚ) / ((Q / Nat.gcd P.natAbs Q : ℕ) : ℚ) =
        (P : ℚ) / Q := by
  set g := Nat.gcd P.natAbs Q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hQ
  have hdP : (g : ℤ) ∣ P := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hdQ : g ∣ Q := Nat.gcd_dvd_right _ _
  obtain ⟨k, hk⟩ := hdP
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hPk : P / (g : ℤ) = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hgz
  have habs : P.natAbs / g = k.natAbs := by
    rw [hk, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hg0]
  have hQg : 0 < Q / g := Nat.div_pos (Nat.le_of_dvd hQ hdQ) hg0
  refine ⟨?_, hQg, ?_⟩
  · rw [hPk, ← habs]
    exact Nat.coprime_div_gcd_div_gcd hg0
  · rw [hPk]
    have hQq : (Q : ℚ) = ((Q / g : ℕ) : ℚ) * g := by
      exact_mod_cast (Nat.div_mul_cancel hdQ).symm
    have hPq : (P : ℚ) = (g : ℚ) * k := by exact_mod_cast hk
    have h1 : ((Q / g : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hQg.ne'
    have h2 : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    rw [div_eq_div_iff h1 h2, hQq, hPq]
    ring

/-- **The sum of two fractions on the compiled Turing machine, normalized.** For integers `a, c`
and positive `b, d` with `bd < 2^W` and `|ad + cb| < 2^W`, from the layout `ratInput W a b c d`
the compiled single-tape TM computes a fraction `N/D` in lowest terms with
`N/D = a/b + c/d`: `N` is read in `2W`-bit two's complement, `D > 0` and `gcd(|N|, D) = 1`.
The run takes exactly `(2·trips d + trips b + s(4W + 6) + 8W + 22)(4W + 2)` transitions, which
is at most `(8W² + 23W + 22)(4W + 2)`. -/
theorem radd_tm {W : ℕ} (hW : 0 < W) {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbd : b * d < 2 ^ W) (hP : |a * d + c * b| < 2 ^ W) (T : ℤ → Sym GCell)
    (hT : raddProg.toProg.Repr T (ratInput W a b c d)) :
    ∃ l' T', raddProg.toProg.Repr T' l' ∧
      ((sval (2 * W) (tv GCell.rp l') : ℚ) / (tv GCell.rq l' : ℚ) = (a : ℚ) / b + (c : ℚ) / d) ∧
      Nat.Coprime (sval (2 * W) (tv GCell.rp l')).natAbs (tv GCell.rq l') ∧
      0 < tv GCell.rq l' ∧
      (2 * trips d + trips b + euclidSteps (a * d + c * b).natAbs (b * d) * (4 * W + 6) +
          8 * W + 22) * (4 * W + 2) ≤ (8 * W ^ 2 + 23 * W + 22) * (4 * W + 2) ∧
      raddProg.toProg.toTM.run
          ⟨.fwd raddProg.start (raddProg.toProg.init raddProg.start), T, 0⟩
          ((2 * trips d + trips b + euclidSteps (a * d + c * b).natAbs (b * d) * (4 * W + 6) +
            8 * W + 22) * (4 * W + 2)) =
        ⟨.fwd (Sum.inr (Sum.inr AddI.done)) (raddProg.toProg.init (Sum.inr (Sum.inr AddI.done))),
          T', 0⟩ := by
  obtain ⟨l', hr, hrp, hrq⟩ := radd_layout hW (a := a) (c := c) hb hd hbd hP
  obtain ⟨T', hT', hrun⟩ := raddProg.toProg.reach_run hr.reach T hT
  have hQ0 : 0 < b * d := Nat.mul_pos hb hd
  obtain ⟨hco, hpos, hval⟩ := reduced_frac (a * d + c * b) (b * d) hQ0
  have hbW : b < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_of_pos_right b hd) hbd
  have hdW : d < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_of_pos_left d hb) hbd
  refine ⟨l', T', hT', ?_, by rw [hrp, hrq]; exact hco, by rw [hrq]; exact hpos, ?_, hrun⟩
  · rw [hrp, hrq, hval]
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
  · have t1 := trips_le W d hdW
    have t2 := trips_le W b hbW
    have t3 := euclidSteps_le W (a * d + c * b).natAbs (b * d) hbd
    apply Nat.mul_le_mul_right
    nlinarith

/-- **The product of two fractions on the compiled Turing machine, normalized.** For integers
`a, c` and positive `b, d` with `bd < 2^W` and `|ac| < 2^W`, from the layout `ratInput W a b c d`
the compiled single-tape TM computes a fraction `N/D` in lowest terms with `N/D = (a/b)(c/d)`.
The run takes exactly `(trips d + trips (tc_{2W} c) + s(4W + 6) + 8W + 20)(4W + 2)` transitions,
which is at most `(8W² + 23W + 20)(4W + 2)`. -/
theorem rmul_tm {W : ℕ} (hW : 0 < W) {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hbd : b * d < 2 ^ W) (hP : |a * c| < 2 ^ W) (T : ℤ → Sym GCell)
    (hT : rmulProg.toProg.Repr T (ratInput W a b c d)) :
    ∃ l' T', rmulProg.toProg.Repr T' l' ∧
      ((sval (2 * W) (tv GCell.rp l') : ℚ) / (tv GCell.rq l' : ℚ) = ((a : ℚ) / b) * ((c : ℚ) / d)) ∧
      Nat.Coprime (sval (2 * W) (tv GCell.rp l')).natAbs (tv GCell.rq l') ∧
      0 < tv GCell.rq l' ∧
      (trips d + trips (tc (2 * W) c) + euclidSteps (a * c).natAbs (b * d) * (4 * W + 6) +
          8 * W + 20) * (4 * W + 2) ≤ (8 * W ^ 2 + 23 * W + 20) * (4 * W + 2) ∧
      rmulProg.toProg.toTM.run
          ⟨.fwd rmulProg.start (rmulProg.toProg.init rmulProg.start), T, 0⟩
          ((trips d + trips (tc (2 * W) c) + euclidSteps (a * c).natAbs (b * d) * (4 * W + 6) +
            8 * W + 20) * (4 * W + 2)) =
        ⟨.fwd (Sum.inr (Sum.inr AddI.done)) (rmulProg.toProg.init (Sum.inr (Sum.inr AddI.done))),
          T', 0⟩ := by
  obtain ⟨l', hr, hrp, hrq⟩ := rmul_layout hW (a := a) (c := c) hb hd hbd hP
  obtain ⟨T', hT', hrun⟩ := rmulProg.toProg.reach_run hr.reach T hT
  have hQ0 : 0 < b * d := Nat.mul_pos hb hd
  obtain ⟨hco, hpos, hval⟩ := reduced_frac (a * c) (b * d) hQ0
  have hdW : d < 2 ^ W := lt_of_le_of_lt (Nat.le_mul_of_pos_left d hb) hbd
  refine ⟨l', T', hT', ?_, by rw [hrp, hrq]; exact hco, by rw [hrq]; exact hpos, ?_, hrun⟩
  · rw [hrp, hrq, hval]
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
  · have t1 := trips_le W d hdW
    have t2 := trips_le (2 * W) (tc (2 * W) c) (tc_lt _ _)
    have t3 := euclidSteps_le W (a * c).natAbs (b * d) hbd
    apply Nat.mul_le_mul_right
    nlinarith

end PVNP.Discrete.SweepArith
