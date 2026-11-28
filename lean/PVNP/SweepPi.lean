import PVNP.SweepConv
import PVNP.SweepRat

/-!
# Certified `π` on the Turing machine

One compiled single-tape TM computes an integer `A` with `|4A/2^q − π| ≤ (16q + 14)/2^q`, in a
number of transitions that is a polynomial of degree 3 in `q` (`pi_tm_prec`).

**The series.** Euler's formula `π = 4 (arctan(1/2) + arctan(1/3))` (`pi_euler`) and the
arctangent series (`Real.hasSum_arctan`) give `π` as a sum of two alternating series. The tail of
`arctan x` after `J` terms is at most `(4/3) x^{2J+1}` for `0 ≤ x ≤ 1/2` (`arctan_tail`). The
machine computes the terms `⌊Z / ((2n + 1) m^{2n+1})⌋`. Each has error below `1`, so the
alternating sum is within `J + (4/3) Z m^{−(2J+1)}` of `Z arctan(1/m)` (`atSum_err`).

**The arctangent loop** (`atLoop`, `at_loop`) is a loop of verified programs on the alphabet
`GCell` of `SweepGcd`. One step (`body_at`):

1. `u := ⌊u/m²⌋`, by the verified shift-and-divide stage `shdiv`;
2. `t := ⌊u/d⌋`, by `shdiv` again;
3. `S := t − S`, by the subtractor. The sign alternates without a conditional, because after `J`
   steps `S = (−1)^{J+1} Σ_{n<J} (−1)ⁿ tₙ` (`atR_eq`);
4. `d := d + 2`, as `d − (−2)` by the subtractor;
5. the counter decrements.

It starts from `u = mZ`, so the `n`-th term is `⌊Z/((2n+1) m^{2n+1})⌋` (`atU_term`).

**The π machine** (`piProg`, `pi_run`, `pi_tm`):
- the loop runs `J` steps for `m = 2` (`J` odd, so `S = atSum`);
- a cellwise map saves the sum and loads the data for `m = 3`;
- the loop runs `J + 1` steps (an even count, so `S = −atSum`);
- the subtractor forms `atSum Z 2 J + atSum Z 3 (J + 1)`.

The certificate is `|4A − Zπ| ≤ 8J + 4 + (16/3) Z/4^J` (`piA_err`).

**The layout** (`piInput`) holds the loops' data `2Z, 4, 1, J` and `3Z, 9, 1, J + 1`, the code of
`−2`, the counter constant `W` and the marker `2^W`. No series is evaluated in the layout.
-/

namespace PVNP.PiSeries

open Real Finset

/-- **Euler's formula** `π = 4 (arctan(1/2) + arctan(1/3))`. -/
theorem pi_euler : π = 4 * (arctan (1 / 2) + arctan (1 / 3)) := by
  rw [arctan_add (by norm_num)]
  norm_num [arctan_one]
  ring

/-- The tail of the arctangent series: for `0 ≤ x ≤ 1/2`,
`|arctan x − Σ_{n<J} (−1)ⁿ x^{2n+1}/(2n+1)| ≤ (4/3) x^{2J+1}`. -/
theorem arctan_tail {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (J : ℕ) :
    |arctan x - ∑ n ∈ range J, (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1)| ≤
      4 / 3 * x ^ (2 * J + 1) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; linarith)
  have ht := (hasSum_nat_add_iff' J).2 hs
  have hq : x ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun n : ℕ => x ^ (2 * J + 1) * (x ^ 2) ^ n)
      (x ^ (2 * J + 1) * (1 - x ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (sq_nonneg x) hq).mul_left _
  have hb := ht.norm_le_of_bounded hg (fun n => by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_of_nonneg hx0]
    have hd : (1 : ℝ) ≤ |((2 * (n + J) + 1 : ℕ) : ℝ)| := by
      rw [abs_of_nonneg (by positivity)]; exact_mod_cast Nat.le_add_left 1 _
    calc x ^ (2 * (n + J) + 1) / |((2 * (n + J) + 1 : ℕ) : ℝ)| ≤ x ^ (2 * (n + J) + 1) :=
          div_le_self (by positivity) hd
      _ = x ^ (2 * J + 1) * (x ^ 2) ^ n := by rw [← pow_mul, ← pow_add]; ring_nf)
  have hsum : (∑ n ∈ range J, (-1) ^ n * x ^ (2 * n + 1) / ↑(2 * n + 1) : ℝ) =
      ∑ n ∈ range J, (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1) := by
    refine sum_congr rfl fun n _ => ?_
    push_cast; ring
  rw [hsum, Real.norm_eq_abs] at hb
  refine hb.trans ?_
  have h1 : (1 - x ^ 2)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; nlinarith
  have h2 : 0 ≤ x ^ (2 * J + 1) := by positivity
  nlinarith

/-- The `n`-th term the machine computes: `⌊Z / ((2n+1) m^{2n+1})⌋`. -/
def atTerm (Z m n : ℕ) : ℕ := Z / ((2 * n + 1) * m ^ (2 * n + 1))

/-- The alternating sum of the terms. -/
def atSum (Z m J : ℕ) : ℤ := ∑ n ∈ range J, (-1) ^ n * (atTerm Z m n : ℤ)

theorem atTerm_err (Z m n : ℕ) (hm : 1 ≤ m) :
    |(atTerm Z m n : ℝ) - Z * ((1 / m : ℝ) ^ (2 * n + 1) / (2 * n + 1))| ≤ 1 := by
  set D : ℕ := (2 * n + 1) * m ^ (2 * n + 1) with hD
  have hDpos : 0 < D := by positivity
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDpos
  have e : (Z : ℝ) * ((1 / m : ℝ) ^ (2 * n + 1) / (2 * n + 1)) = (Z : ℝ) / D := by
    rw [hD, one_div_pow]; push_cast
    have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    field_simp
  rw [e]
  have h1 : (atTerm Z m n : ℝ) ≤ (Z : ℝ) / D := by
    unfold atTerm; rw [← hD]; exact Nat.cast_div_le
  have h2 : (Z : ℝ) / D - 1 ≤ (atTerm Z m n : ℝ) := by
    unfold atTerm; rw [← hD]
    have hlt : Z < Z / D * D + D := Nat.lt_div_mul_add hDpos
    have hlt' : (Z : ℝ) < ((Z / D : ℕ) : ℝ) * D + D := by exact_mod_cast hlt
    rw [sub_le_iff_le_add, div_le_iff₀ hDr]
    nlinarith
  rw [abs_le]; constructor <;> linarith

/-- **The machine's alternating sum approximates `Z arctan(1/m)`**: for `m ≥ 2`,
`|atSum Z m J − Z arctan(1/m)| ≤ J + (4/3) Z m^{−(2J+1)}`. -/
theorem atSum_err (Z m J : ℕ) (hm : 2 ≤ m) :
    |(atSum Z m J : ℝ) - Z * arctan (1 / m)| ≤ J + 4 / 3 * Z * (1 / m : ℝ) ^ (2 * J + 1) := by
  have hx0 : (0 : ℝ) ≤ 1 / m := by positivity
  have hx : (1 / m : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num; exact_mod_cast hm
  have ht := arctan_tail hx0 hx J
  have hsplit : (atSum Z m J : ℝ) - Z * arctan (1 / m) =
      ∑ n ∈ range J, (-1) ^ n * ((atTerm Z m n : ℝ) - Z * ((1 / m : ℝ) ^ (2 * n + 1) / (2 * n + 1))) -
        Z * (arctan (1 / m) - ∑ n ∈ range J, (-1) ^ n * (1 / m : ℝ) ^ (2 * n + 1) / (2 * n + 1)) := by
    unfold atSum
    push_cast
    rw [mul_sub, Finset.mul_sum]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring_nf
  rw [hsplit]
  have hA : |∑ n ∈ range J, (-1) ^ n * ((atTerm Z m n : ℝ) -
      Z * ((1 / m : ℝ) ^ (2 * n + 1) / (2 * n + 1)))| ≤ J := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ n ∈ range J, |(-1 : ℝ) ^ n * ((atTerm Z m n : ℝ) -
        Z * ((1 / m : ℝ) ^ (2 * n + 1) / (2 * n + 1)))| ≤ 1 := by
      intro n _
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact atTerm_err Z m n (by omega)
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have hB : |(Z : ℝ) * (arctan (1 / m) - ∑ n ∈ range J, (-1) ^ n * (1 / m : ℝ) ^ (2 * n + 1) /
      (2 * n + 1))| ≤ 4 / 3 * Z * (1 / m : ℝ) ^ (2 * J + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Z)]
    calc (Z : ℝ) * |arctan (1 / m) - ∑ n ∈ range J, (-1) ^ n * (1 / m : ℝ) ^ (2 * n + 1) /
          (2 * n + 1)| ≤ Z * (4 / 3 * (1 / m : ℝ) ^ (2 * J + 1)) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ = 4 / 3 * Z * (1 / m : ℝ) ^ (2 * J + 1) := by ring
  calc _ ≤ |∑ n ∈ range J, (-1) ^ n * ((atTerm Z m n : ℝ) -
          Z * ((1 / m : ℝ) ^ (2 * n + 1) / (2 * n + 1)))| +
        |(Z : ℝ) * (arctan (1 / m) - ∑ n ∈ range J, (-1) ^ n * (1 / m : ℝ) ^ (2 * n + 1) /
          (2 * n + 1))| := abs_sub _ _
    _ ≤ _ := add_le_add hA hB

/-- **The machine's approximation of `π`**: `|4(atSum Z 2 J + atSum Z 3 J) − Zπ| ≤ 8J + (16/3) Z/4^J`. -/
theorem piSum_err (Z J : ℕ) :
    |(4 * (atSum Z 2 J + atSum Z 3 J) : ℝ) - Z * π| ≤ 8 * J + 16 / 3 * Z / 4 ^ J := by
  have h2 := atSum_err Z 2 J le_rfl
  have h3 := atSum_err Z 3 J (by norm_num)
  have e : (4 * (atSum Z 2 J + atSum Z 3 J) : ℝ) - Z * π =
      4 * (((atSum Z 2 J : ℝ) - Z * arctan (1 / 2)) + ((atSum Z 3 J : ℝ) - Z * arctan (1 / 3))) := by
    rw [pi_euler]; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hab := abs_add_le ((atSum Z 2 J : ℝ) - Z * arctan (1 / 2)) ((atSum Z 3 J : ℝ) - Z * arctan (1 / 3))
  push_cast at h2 h3
  have p3 : ((1 : ℝ) / 3) ^ (2 * J + 1) ≤ ((1 : ℝ) / 2) ^ (2 * J + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have p2 : ((1 : ℝ) / 2) ^ (2 * J + 1) = 1 / 2 * (1 / 4 ^ J) := by
    rw [pow_succ, pow_mul, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num, one_div_pow]; ring
  have hZ : (0 : ℝ) ≤ Z := by positivity
  have h4 : (0 : ℝ) < 4 ^ J := by positivity
  have key : 4 / 3 * (Z : ℝ) * ((1 : ℝ) / 2) ^ (2 * J + 1) + 4 / 3 * Z * ((1 : ℝ) / 3) ^ (2 * J + 1) ≤
      4 / 3 * Z / 4 ^ J := by
    rw [p2] at p3 ⊢
    have : 4 / 3 * (Z : ℝ) * ((1 : ℝ) / 3) ^ (2 * J + 1) ≤ 4 / 3 * Z * (1 / 2 * (1 / 4 ^ J)) :=
      mul_le_mul_of_nonneg_left p3 (by positivity)
    have e2 : 4 / 3 * (Z : ℝ) / 4 ^ J = 2 * (4 / 3 * Z * (1 / 2 * (1 / 4 ^ J))) := by
      field_simp
    rw [e2]; linarith
  set X := (atSum Z 2 J : ℝ) - Z * arctan (1 / 2)
  set Y := (atSum Z 3 J : ℝ) - Z * arctan (1 / 3)
  set A := 4 / 3 * (Z : ℝ) * ((1 : ℝ) / 2) ^ (2 * J + 1)
  set B := 4 / 3 * (Z : ℝ) * ((1 : ℝ) / 3) ^ (2 * J + 1)
  calc 4 * |X + Y| ≤ 4 * (|X| + |Y|) := by linarith
    _ ≤ 4 * ((J + A) + (J + B)) := by linarith
    _ = 8 * J + 4 * (A + B) := by ring
    _ ≤ 8 * J + 4 * (4 / 3 * Z / 4 ^ J) := by linarith
    _ = 8 * J + 16 / 3 * Z / 4 ^ J := by ring

end PVNP.PiSeries

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep

/-! ### The arctangent loop on `GCell`

Tracks: `a` the power term `u`, `b` the divisor `m²`, `p` the odd number `d = 2n + 1`, `rp` the
term `t`, `qq` the alternating sum `S` (two's complement), `rq` its successor, `xc.z` the code of
`−2`, `xc.ic` the next odd number, `xc.ia` the counter and `xc.ib` its scratch track. -/

/-- Store the quotient `⌊u/m²⌋` in `a`, and load the divider with dividend that quotient and
divisor the odd number `p`. -/
def stU (x : GCell) : GCell :=
  ⟨⟨x.dv.q, x.p, false, x.m0⟩, x.c0, x.dv.q, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩

/-- Move the new sum to `qq` and the new odd number to `p`. -/
def mvS (x : GCell) : GCell :=
  ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.xc.ic, x.rq, x.rp, x.rq, x.xc⟩

/-- The sum update `rq := rp − qq`, i.e. `S' = t − S`. -/
def lensTS : TrackLens GCell Cell :=
  ⟨fun x => ⟨x.rp, x.qq, x.rq⟩,
    fun x c => ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.p, c.b, c.a, c.r, x.xc⟩, fun _ _ => rfl⟩

/-- The odd-number step `ic := p − z`, with `z` the code of `−2`. -/
def lensDD : TrackLens GCell Cell :=
  ⟨fun x => ⟨x.p, x.xc.z, x.xc.ic⟩,
    fun x c => ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, c.a, x.qq, x.rp, x.rq,
      ⟨x.xc.x, x.xc.y, x.xc.acc, x.xc.fl, c.b, x.xc.ia, x.xc.ib, c.r, x.xc.id⟩⟩, fun _ _ => rfl⟩

/-- The counter step `ia := ia − 1` (the scratch track `ib` rides along). -/
def lensCN : TrackLens GCell SCell :=
  ⟨fun x => ⟨x.xc.ib, x.xc.ia⟩,
    fun x s => ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq,
      ⟨x.xc.x, x.xc.y, x.xc.acc, x.xc.fl, x.xc.z, s.c, s.x, x.xc.ic, x.xc.id⟩⟩, fun _ _ => rfl⟩

def SUBTS : ProgOn GCell := (ProgOn.ofProg subProg).viaLens lensTS gz gbit
def SUBDD : ProgOn GCell := (ProgOn.ofProg subProg).viaLens lensDD gz gbit
def DECN : ProgOn GCell := (ProgOn.ofProg decProg).viaLens lensCN gz gbit

def A1 : ProgOn GCell := ProgOn.seq (MAPG setupF) SHG AddI.done
def A2 : ProgOn GCell := ProgOn.seq A1 DVG (Sum.inr (Sum.inl TstI.no))
def A3 : ProgOn GCell := ProgOn.seq A2 (MAPG stU) (Sum.inr DivI.done)
def A4 : ProgOn GCell := ProgOn.seq A3 SHG (Sum.inr AddI.done)
def A5 : ProgOn GCell := ProgOn.seq A4 DVG (Sum.inr (Sum.inl TstI.no))
def A6 : ProgOn GCell := ProgOn.seq A5 (MAPG savePF) (Sum.inr DivI.done)
def A7 : ProgOn GCell := ProgOn.seq A6 SUBTS (Sum.inr AddI.done)
def A8 : ProgOn GCell := ProgOn.seq A7 SUBDD (Sum.inr AddI.done)
def A9 : ProgOn GCell := ProgOn.seq A8 (MAPG mvS) (Sum.inr AddI.done)

/-- **One arctangent step**: `u := ⌊u/m²⌋`, `t := ⌊u/d⌋`, `S := t − S`, `d := d + 2`, and the
counter decrements. -/
def BODYA : ProgOn GCell := ProgOn.seq A9 DECN (Sum.inr AddI.done)

/-- The zero test of the counter `xc.ia`. -/
def fnzA (nz : Bool) (x : GCell) : GCell × Bool := (x, nz || x.xc.ia)

def testA : Prog where
  D := GCell
  I := TstI
  B := Bool
  lift := gbit
  start := .test
  init _ := false
  fwd
    | .test => fnzA
    | _ => fun c x => (x, c)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next
    | .test => fun b => if b then .inl .yes else .inl .no
    | .yes => fun _ => .inl .yes
    | .no => fun _ => .inl .no

def TSA : ProgOn GCell := ProgOn.ofProg testA

/-- **The arctangent loop.** -/
def atLoop : ProgOn GCell := ProgOn.loop TSA BODYA TstI.yes (Sum.inr AddI.done)

theorem fscan_nzA : ∀ (b : Bool) (l : List GCell),
    (fscan fnzA b l).1 = l ∧ (fscan fnzA b l).2 = (b || decide (tv (fun x => x.xc.ia) l ≠ 0))
  | b, [] => by simp [fscan, tv, val]
  | b, ⟨dv, c, a, xb, c0, m0, p, qq, rp, rq, ⟨x1, y1, acc1, fl1, z1, ia1, ib1, ic1, id1⟩⟩ :: l => by
    obtain ⟨h1, h2⟩ := fscan_nzA (b || ia1) l
    refine ⟨by simp only [fscan, fnzA, h1], ?_⟩
    simp only [fscan, fnzA, h2, tv, List.map_cons, val]
    cases b <;> cases ia1 <;> simp

theorem testA_step (l : List GCell) :
    TSA.toProg.stepP (TstI.test, l) =
      .inl (if tv (fun x => x.xc.ia) l ≠ 0 then TstI.yes else TstI.no, l) := by
  obtain ⟨h1, h2⟩ := fscan_nzA false l
  have ht : testA.trip TstI.test l = (l, decide (tv (fun x => x.xc.ia) l ≠ 0)) := by
    simp only [Prog.trip, Prog.mid, Prog.fpass, testA, bscan_id]
    rw [h1, h2]
    simp
  show testA.stepP (TstI.test, l) = _
  simp only [Prog.stepP, ht]
  by_cases h : tv (fun x => x.xc.ia) l ≠ 0
  · have hn : testA.next TstI.test (decide (tv (fun x => x.xc.ia) l ≠ 0)) = .inl TstI.yes := by
      simp [testA, h]
    rw [hn, if_pos h]
  · have hn : testA.next TstI.test (decide (tv (fun x => x.xc.ia) l ≠ 0)) = .inl TstI.no := by
      simp [testA, h]
    rw [hn, if_neg h]

theorem testA_cost (l : List GCell) : TSA.toProg.tripCost TSA.start l = 2 * l.length + 2 := by
  show testA.tripCost TstI.test l = _
  simp [Prog.tripCost, Prog.fpass, testA]

/-! ### Stages on `GCell` -/

def lensAa : TrackLens GCell Bool :=
  ⟨GCell.a, fun x b => ⟨x.dv, x.c, b, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩, fun _ _ => rfl⟩
def lensBb : TrackLens GCell Bool :=
  ⟨GCell.b, fun x b => ⟨x.dv, x.c, x.a, b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq, x.xc⟩, fun _ _ => rfl⟩

/-- The five carried tracks of `xc` that the arctangent loop never writes. -/
def lensX5 : TrackLens GCell (Bool × Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.xc.x, x.xc.y, x.xc.acc, x.xc.fl, x.xc.id),
    fun x k => ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.p, x.qq, x.rp, x.rq,
      ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.1, x.xc.z, x.xc.ia, x.xc.ib, x.xc.ic, k.2.2.2.2⟩⟩,
    fun _ _ => rfl⟩

/-- A subtractor stage on `GCell` along a lens, with its frame. -/
theorem stg_sub (ℓ : TrackLens GCell Cell) (l : List GCell) :
    ∃ l', ReachFirst ((ProgOn.ofProg subProg).viaLens ℓ gz gbit).toProg AddI.done (AddI.go, l) l'
        (2 * l.length + 2) ∧
      l'.map ℓ.get = (fscan fsub false (l.map ℓ.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens GCell D₂), ℓ.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := sub_first (l.map ℓ.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg subProg) ℓ gz gbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg subProg) ℓ gz gbit (fun _ _ => rfl) hi hr'

/-- The counter stage on `GCell`, with its frame. -/
theorem stg_dec (l : List GCell) :
    ∃ l', ReachFirst DECN.toProg AddI.done (AddI.go, l) l' (2 * l.length + 2) ∧
      l'.map lensCN.get = (fscan fdec true (l.map lensCN.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens GCell D₂), lensCN.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := dec_first (l.map lensCN.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg decProg) lensCN gz gbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg decProg) lensCN gz gbit (fun _ _ => rfl) hi hr'

/-- The decrement of a positive counter. -/
theorem dec_value (l : List SCell) {j : ℕ} (h : vSc l = j + 1) :
    val ((fscan fdec true l).1.map SCell.c) = j := by
  have h1 := fscan_dec true l
  have hlt := val_lt ((fscan fdec true l).1.map SCell.c)
  rw [List.length_map, fscan_length] at hlt
  have hlt2 : vSc l < 2 ^ l.length := by unfold vSc; have := val_lt (l.map SCell.c); simpa using this
  rw [h, Bool.toNat_true] at h1
  cases hc : (fscan fdec true l).2
  · rw [hc, Bool.toNat_false, mul_zero, add_zero] at h1; omega
  · rw [hc, Bool.toNat_true, mul_one] at h1; omega

/-- **One arctangent step.** From a tape of length `2W` with power term `u < 2^W`, divisor
`0 < M < 2^W`, odd number `0 < d` with `d + 2 < 2^W`, sum code `tc(S)`, counter `j + 1`, the code of
`−2`, counter constant `W` and marker `2^W`, the body first-arrives at its exit in exactly
`(8W + 13)(4W + 2)` transitions with `u' = ⌊u/M⌋`, `d' = d + 2`, `S' = ⌊u'/d⌋ − S` and counter
`j`; the constants are unchanged. -/
theorem body_at {W : ℕ} (l : List GCell) (hlen : l.length = 2 * W)
    {u M d j : ℕ} {S : ℤ} (hu : u < 2 ^ W) (hM0 : 0 < M) (hM : M < 2 ^ W)
    (hd0 : 0 < d) (hd : d + 2 < 2 ^ W)
    (ha : tv GCell.a l = u) (hb : tv GCell.b l = M) (hp : tv GCell.p l = d)
    (hqq : tv GCell.qq l = tc (2 * W) S) (hz : tv (fun x => x.xc.z) l = tc (2 * W) (-2))
    (hcnt : tv (fun x => x.xc.ia) l = j + 1)
    (hc0 : tv GCell.c0 l = W) (hm0 : tv GCell.m0 l = 2 ^ W) :
    ∃ l', ReachFirst BODYA.toProg (Sum.inr AddI.done) (BODYA.start, l) l'
        ((8 * W + 13) * (4 * W + 2)) ∧
      l'.length = 2 * W ∧ tv GCell.a l' = u / M ∧ tv GCell.b l' = M ∧ tv GCell.p l' = d + 2 ∧
      tv GCell.qq l' = tc (2 * W) (((u / M / d : ℕ) : ℤ) - S) ∧
      tv (fun x => x.xc.z) l' = tc (2 * W) (-2) ∧ tv (fun x => x.xc.ia) l' = j ∧
      tv GCell.c0 l' = W ∧ tv GCell.m0 l' = 2 ^ W ∧ l'.map lensX5.get = l.map lensX5.get := by
  have hW2 : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- stage 1: load the divider with `u / M`
  have r1 := map_first setupF gbit l
  have len1 : (l.map setupF).length = 2 * W := by rw [List.length_map, hlen]
  have n1 : tv (fun x => x.dv.n) (l.map setupF) = u := by rw [tv_map]; exact ha
  have d1 : tv (fun x => x.dv.d) (l.map setupF) = M := by rw [tv_map]; exact hb
  have q1 : tv (fun x => x.dv.q) (l.map setupF) = 0 := by rw [tv_map]; exact val_false l
  have m1 : tv (fun x => x.dv.m) (l.map setupF) = 2 ^ W := by rw [tv_map]; exact hm0
  have c1 : tv GCell.c (l.map setupF) = W := by rw [tv_map]; exact hc0
  -- stages 2, 3: shift and divide
  obtain ⟨l2, l3, r2, r3, len3, q3, -, k3⟩ := shdiv (l.map setupF) len1 hu hM0 hM n1 d1 q1 m1 c1
  rw [len1] at len3
  -- the tracks kept from `l` through stage 3
  have K3 : ∀ {β : Type} (π : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × XCell → β),
      l3.map (fun x => π (lensKeep.get x)) = l.map (fun x => π (lensKeep.get x)) := by
    intro β π
    refine (keep_map k3 π).trans ?_
    rw [List.map_map]; rfl
  -- stage 4: store `u' = ⌊u/M⌋` and load the divider with `u' / d`
  have r4 := map_first stU gbit l3
  have len4 : (l3.map stU).length = 2 * W := by rw [List.length_map, len3]
  have hu' : u / M < 2 ^ W := lt_of_le_of_lt (Nat.div_le_self _ _) hu
  have n4 : tv (fun x => x.dv.n) (l3.map stU) = u / M := by rw [tv_map]; exact q3
  have d4 : tv (fun x => x.dv.d) (l3.map stU) = d := by
    rw [tv_map]; exact (tv_congr (f := GCell.p) (K3 (fun k => k.2.2.2.2.1))).trans hp
  have q4 : tv (fun x => x.dv.q) (l3.map stU) = 0 := by rw [tv_map]; exact val_false l3
  have m4 : tv (fun x => x.dv.m) (l3.map stU) = 2 ^ W := by
    rw [tv_map]; exact (tv_congr (f := GCell.m0) (K3 (fun k => k.2.2.2.1))).trans hm0
  have c4 : tv GCell.c (l3.map stU) = W := by
    rw [tv_map]; exact (tv_congr (f := GCell.c0) (K3 (fun k => k.2.2.1))).trans hc0
  -- stages 5, 6: shift and divide
  obtain ⟨l5, l6, r5, r6, len6, q6, -, k6⟩ := shdiv (l3.map stU) len4 hu' hd0 (by omega) n4 d4 q4
    m4 c4
  rw [len4] at len6
  have K6 : ∀ {β : Type} (π : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × XCell → β),
      l6.map (fun x => π (lensKeep.get x)) = (l3.map stU).map (fun x => π (lensKeep.get x)) :=
    fun π => keep_map k6 π
  -- stage 7: store the term `t = ⌊u'/d⌋` in `rp`
  have r7 := map_first savePF gbit l6
  set l7 := l6.map savePF with hl7
  have len7 : l7.length = 2 * W := by rw [hl7, List.length_map, len6]
  set t := u / M / d with ht
  have ht' : t < 2 ^ (2 * W) := lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hu' hW2)
  have rp7 : tv GCell.rp l7 = t := by rw [hl7, tv_map]; exact q6
  -- the tracks of `l7` that come from `l3` (and hence from `l` or stage 4)
  have a7 : l7.map GCell.a = (l3.map stU).map GCell.a := by
    rw [hl7, List.map_map]; exact K6 (fun k => k.1)
  have b7 : l7.map GCell.b = l.map GCell.b := by
    rw [hl7, List.map_map]
    refine (K6 (fun k => k.2.1)).trans ?_
    rw [List.map_map]; exact K3 (fun k => k.2.1)
  have p7 : l7.map GCell.p = l.map GCell.p := by
    rw [hl7, List.map_map]
    refine (K6 (fun k => k.2.2.2.2.1)).trans ?_
    rw [List.map_map]; exact K3 (fun k => k.2.2.2.2.1)
  have qq7 : l7.map GCell.qq = l.map GCell.qq := by
    rw [hl7, List.map_map]
    refine (K6 (fun k => k.2.2.2.2.2.1)).trans ?_
    rw [List.map_map]; exact K3 (fun k => k.2.2.2.2.2.1)
  have c07 : l7.map GCell.c0 = l.map GCell.c0 := by
    rw [hl7, List.map_map]
    refine (K6 (fun k => k.2.2.1)).trans ?_
    rw [List.map_map]; exact K3 (fun k => k.2.2.1)
  have m07 : l7.map GCell.m0 = l.map GCell.m0 := by
    rw [hl7, List.map_map]
    refine (K6 (fun k => k.2.2.2.1)).trans ?_
    rw [List.map_map]; exact K3 (fun k => k.2.2.2.1)
  have xc7 : l7.map GCell.xc = l.map GCell.xc := by
    rw [hl7, List.map_map]
    refine (K6 (fun k => k.2.2.2.2.2.2.2.2)).trans ?_
    rw [List.map_map]; exact K3 (fun k => k.2.2.2.2.2.2.2.2)
  have a7v : tv GCell.a l7 = u / M := by
    rw [tv_congr a7, tv_map]; exact q3
  -- stage 8: `rq := t − S`
  obtain ⟨l8, r8, v8, f8⟩ := stg_sub lensTS l7
  have ha8 : val ((l7.map lensTS.get).map Cell.a) = tc (2 * W) (t : ℤ) := by
    rw [List.map_map, tc_natCast ht']; exact rp7
  have hb8 : val ((l7.map lensTS.get).map Cell.b) = tc (2 * W) S := by
    rw [List.map_map]; exact (tv_congr qq7).trans hqq
  have hs8 := sub_tc_value (l7.map lensTS.get) (2 * W) (by rw [List.length_map, len7]) _ _ ha8 hb8
  obtain ⟨-, sb8⟩ := fscan_sub_ab false (l7.map lensTS.get)
  have len8 : l8.length = 2 * W := by
    have := congrArg List.length v8
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, len7]
  have rq8 : tv GCell.rq l8 = tc (2 * W) ((t : ℤ) - S) := by
    have e : tv GCell.rq l8 = val ((l8.map lensTS.get).map Cell.r) := by
      unfold tv; rw [List.map_map]; rfl
    rw [e, v8]; exact hs8
  have a8 : l8.map GCell.a = l7.map GCell.a := f8 lensAa (fun _ _ => rfl)
  have b8 : l8.map GCell.b = l7.map GCell.b := f8 lensBb (fun _ _ => rfl)
  have p8 : l8.map GCell.p = l7.map GCell.p := f8 lensP (fun _ _ => rfl)
  have c08 : l8.map GCell.c0 = l7.map GCell.c0 := f8 lensC0 (fun _ _ => rfl)
  have m08 : l8.map GCell.m0 = l7.map GCell.m0 := f8 lensM0 (fun _ _ => rfl)
  have z8 : l8.map (fun x => x.xc.z) = l7.map (fun x => x.xc.z) := f8 lensZ (fun _ _ => rfl)
  have ia8 : l8.map (fun x => x.xc.ia) = l7.map (fun x => x.xc.ia) := f8 lensIa (fun _ _ => rfl)
  have x58 : l8.map lensX5.get = l7.map lensX5.get := f8 lensX5 (fun _ _ => rfl)
  -- stage 9: `ic := d − (−2) = d + 2`
  obtain ⟨l9, r9, v9, f9⟩ := stg_sub lensDD l8
  have zz : l7.map (fun x => x.xc.z) = l.map (fun x => x.xc.z) := by
    have := congrArg (List.map XCell.z) xc7
    simpa [List.map_map, Function.comp_def] using this
  have iaa : l7.map (fun x => x.xc.ia) = l.map (fun x => x.xc.ia) := by
    have := congrArg (List.map XCell.ia) xc7
    simpa [List.map_map, Function.comp_def] using this
  have ha9 : val ((l8.map lensDD.get).map Cell.a) = tc (2 * W) (d : ℤ) := by
    rw [List.map_map, tc_natCast (lt_of_lt_of_le (by omega : d < 2 ^ W) hW2)]
    exact (tv_congr (p8.trans p7)).trans hp
  have hb9 : val ((l8.map lensDD.get).map Cell.b) = tc (2 * W) (-2) := by
    rw [List.map_map]; exact (tv_congr (z8.trans zz)).trans hz
  have hs9 := sub_tc_value (l8.map lensDD.get) (2 * W) (by rw [List.length_map, len8]) _ _ ha9 hb9
  have len9 : l9.length = 2 * W := by
    have := congrArg List.length v9
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, len8]
  have ic9 : tv (fun x => x.xc.ic) l9 = d + 2 := by
    have e : tv (fun x => x.xc.ic) l9 = val ((l9.map lensDD.get).map Cell.r) := by
      unfold tv; rw [List.map_map]; rfl
    rw [e, v9, hs9, show (d : ℤ) - -2 = ((d + 2 : ℕ) : ℤ) by push_cast; ring,
      tc_natCast (lt_of_lt_of_le hd hW2)]
  obtain ⟨-, sb9⟩ := fscan_sub_ab false (l8.map lensDD.get)
  have z9 : l9.map (fun x => x.xc.z) = l8.map (fun x => x.xc.z) := by
    have := congrArg (List.map Cell.b) v9
    rw [sb9, List.map_map, List.map_map] at this
    exact this
  have a9 : l9.map GCell.a = l8.map GCell.a := f9 lensAa (fun _ _ => rfl)
  have b9 : l9.map GCell.b = l8.map GCell.b := f9 lensBb (fun _ _ => rfl)
  have c09 : l9.map GCell.c0 = l8.map GCell.c0 := f9 lensC0 (fun _ _ => rfl)
  have m09 : l9.map GCell.m0 = l8.map GCell.m0 := f9 lensM0 (fun _ _ => rfl)
  have rq9 : l9.map GCell.rq = l8.map GCell.rq := f9 lensRq (fun _ _ => rfl)
  have ia9 : l9.map (fun x => x.xc.ia) = l8.map (fun x => x.xc.ia) := f9 lensIa (fun _ _ => rfl)
  have x59 : l9.map lensX5.get = l8.map lensX5.get := f9 lensX5 (fun _ _ => rfl)
  -- stage 10: `p := ic`, `qq := rq`
  have r10 := map_first mvS gbit l9
  set l10 := l9.map mvS with hl10
  have len10 : l10.length = 2 * W := by rw [hl10, List.length_map, len9]
  -- stage 11: the counter
  obtain ⟨l11, r11, v11, f11⟩ := stg_dec l10
  have hc11 : vSc (l10.map lensCN.get) = j + 1 := by
    unfold vSc; rw [hl10, List.map_map, List.map_map]
    exact (tv_congr (ia9.trans (ia8.trans iaa))).trans hcnt
  have len11 : l11.length = 2 * W := by
    have := congrArg List.length v11
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, len10]
  have a11 : l11.map GCell.a = l10.map GCell.a := f11 lensAa (fun _ _ => rfl)
  have b11 : l11.map GCell.b = l10.map GCell.b := f11 lensBb (fun _ _ => rfl)
  have p11 : l11.map GCell.p = l10.map GCell.p := f11 lensP (fun _ _ => rfl)
  have qq11 : l11.map GCell.qq = l10.map GCell.qq := f11 lensQQ (fun _ _ => rfl)
  have c011 : l11.map GCell.c0 = l10.map GCell.c0 := f11 lensC0 (fun _ _ => rfl)
  have m011 : l11.map GCell.m0 = l10.map GCell.m0 := f11 lensM0 (fun _ _ => rfl)
  have z11 : l11.map (fun x => x.xc.z) = l10.map (fun x => x.xc.z) := f11 lensZ (fun _ _ => rfl)
  have x511 : l11.map lensX5.get = l10.map lensX5.get := f11 lensX5 (fun _ _ => rfl)
  -- the composite
  have hc := ProgOn.seq_reachFirst A9 DECN (Sum.inr AddI.done) (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst A8 (MAPG mvS) (Sum.inr AddI.done) (show AddI.go ≠ AddI.done by decide)
      (ProgOn.seq_reachFirst A7 SUBDD (Sum.inr AddI.done) (show AddI.go ≠ AddI.done by decide)
        (ProgOn.seq_reachFirst A6 SUBTS (Sum.inr AddI.done) (show AddI.go ≠ AddI.done by decide)
          (ProgOn.seq_reachFirst A5 (MAPG savePF) (Sum.inr DivI.done)
            (show AddI.go ≠ AddI.done by decide)
            (ProgOn.seq_reachFirst A4 DVG (Sum.inr (Sum.inl TstI.no))
              (show DivI.prep ≠ DivI.done by decide)
              (ProgOn.seq_reachFirst A3 SHG (Sum.inr AddI.done)
                (show (Sum.inl TstI.test : TstI ⊕ (AddI ⊕ AddI)) ≠ Sum.inl TstI.no by decide)
                (ProgOn.seq_reachFirst A2 (MAPG stU) (Sum.inr DivI.done)
                  (show AddI.go ≠ AddI.done by decide)
                  (ProgOn.seq_reachFirst A1 DVG (Sum.inr (Sum.inl TstI.no))
                    (show DivI.prep ≠ DivI.done by decide)
                    (ProgOn.seq_reachFirst (MAPG setupF) SHG AddI.done
                      (show (Sum.inl TstI.test : TstI ⊕ (AddI ⊕ AddI)) ≠ Sum.inl TstI.no by decide)
                      r1 r2) r3) r4) r5) r6) r7) r8) r9) r10) r11
  rw [hlen, len3, len6, len7, len8, len9, len10] at hc
  have ea : l11.map GCell.a = l7.map GCell.a := by
    refine a11.trans ?_
    rw [hl10, List.map_map]; exact a9.trans a8
  have eb : l11.map GCell.b = l.map GCell.b := by
    refine b11.trans ?_
    rw [hl10, List.map_map]; exact b9.trans (b8.trans b7)
  have ez : l11.map (fun x => x.xc.z) = l.map (fun x => x.xc.z) := by
    refine z11.trans ?_
    rw [hl10, List.map_map]; exact z9.trans (z8.trans zz)
  have ec0 : l11.map GCell.c0 = l.map GCell.c0 := by
    refine c011.trans ?_
    rw [hl10, List.map_map]; exact c09.trans (c08.trans c07)
  have em0 : l11.map GCell.m0 = l.map GCell.m0 := by
    refine m011.trans ?_
    rw [hl10, List.map_map]; exact m09.trans (m08.trans m07)
  have x57 : l7.map lensX5.get = l.map lensX5.get := by
    have := congrArg (List.map (fun c : XCell => (c.x, c.y, c.acc, c.fl, c.id))) xc7
    simpa [List.map_map, Function.comp_def] using this
  have ex5 : l11.map lensX5.get = l.map lensX5.get := by
    refine x511.trans ?_
    rw [hl10, List.map_map]; exact x59.trans (x58.trans x57)
  refine ⟨l11, ?_, len11, (tv_congr ea).trans a7v, (tv_congr eb).trans hb, ?_, ?_,
    (tv_congr ez).trans hz, ?_, (tv_congr ec0).trans hc0, (tv_congr em0).trans hm0, ex5⟩
  · convert hc using 1
    ring
  · rw [tv_congr p11, hl10, tv_map]; exact ic9
  · rw [tv_congr qq11, hl10, tv_map]
    exact (tv_congr rq9).trans rq8
  · have e : tv (fun x => x.xc.ia) l11 = val ((l11.map lensCN.get).map SCell.c) := by
      unfold tv; rw [List.map_map]; rfl
    rw [e, v11]
    exact dec_value _ hc11

/-! ### The loop and its sums -/

/-- The power terms of the loop: `atU U M (k + 1) = ⌊atU U M k / M⌋`. -/
def atU (U M : ℕ) : ℕ → ℕ
  | 0 => U
  | k + 1 => atU U M k / M

/-- The sums of the loop: `atR (k + 1) = ⌊atU (k + 1) / (2k + 1)⌋ − atR k`. -/
def atR (U M : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => ((atU U M (k + 1) / (2 * k + 1) : ℕ) : ℤ) - atR U M k

theorem atU_le (U M : ℕ) : ∀ k, atU U M k ≤ U
  | 0 => le_rfl
  | k + 1 => (Nat.div_le_self _ _).trans (atU_le U M k)

/-- **The arctangent loop.** From a tape with power term `atU U M k`, odd number `2k + 1`, sum
code `tc(atR k)` and counter `j`, the loop first-arrives at its stop exit with power term
`atU U M (k + j)`, odd number `2(k + j) + 1` and sum code `tc(atR (k + j))`, in exactly
`(j(8W + 14) + 1)(4W + 2)` transitions. The carried tracks are unchanged. -/
theorem at_loop {W U M : ℕ} (hU : U < 2 ^ W) (hM0 : 0 < M) (hM : M < 2 ^ W) :
    ∀ (j k : ℕ) (l : List GCell), l.length = 2 * W → 2 * (k + j) + 1 < 2 ^ W →
      tv GCell.a l = atU U M k → tv GCell.b l = M → tv GCell.p l = 2 * k + 1 →
      tv GCell.qq l = tc (2 * W) (atR U M k) → tv (fun x => x.xc.z) l = tc (2 * W) (-2) →
      tv (fun x => x.xc.ia) l = j → tv GCell.c0 l = W → tv GCell.m0 l = 2 ^ W →
      ∃ l', ReachFirst atLoop.toProg (Sum.inl TstI.no) (Sum.inl TstI.test, l) l'
          ((j * (8 * W + 14) + 1) * (4 * W + 2)) ∧
        l'.length = 2 * W ∧ tv GCell.a l' = atU U M (k + j) ∧ tv GCell.b l' = M ∧
        tv GCell.p l' = 2 * (k + j) + 1 ∧ tv GCell.qq l' = tc (2 * W) (atR U M (k + j)) ∧
        tv (fun x => x.xc.z) l' = tc (2 * W) (-2) ∧ tv GCell.c0 l' = W ∧
        tv GCell.m0 l' = 2 ^ W ∧ l'.map lensX5.get = l.map lensX5.get := by
  intro j
  induction j with
  | zero =>
    intro k l hlen hd ha hb hp hqq hz hcnt hc0 hm0
    have ht := testA_step l
    rw [hcnt, if_neg (by simp)] at ht
    refine ⟨l, ?_, hlen, ha, hb, hp, hqq, hz, hc0, hm0, rfl⟩
    have h := ProgOn.loop_stop TSA BODYA TstI.yes (Sum.inr AddI.done) (eF := TstI.no)
      (show TstI.no ≠ TstI.yes by decide) ht
    rw [testA_cost, hlen] at h
    convert h using 1
    ring
  | succ j ih =>
    intro k l hlen hd ha hb hp hqq hz hcnt hc0 hm0
    have ht := testA_step l
    rw [hcnt, if_pos (by omega)] at ht
    obtain ⟨l1, r1, len1, a1, b1, p1, qq1, z1, ia1, c01, m01, x51⟩ :=
      body_at l hlen (u := atU U M k) (M := M) (d := 2 * k + 1) (j := j) (S := atR U M k)
        (lt_of_le_of_lt (atU_le U M k) hU) hM0 hM (by omega) (by omega) ha hb hp hqq hz hcnt
        hc0 hm0
    obtain ⟨l2, r2, len2, a2, b2, p2, qq2, z2, c02, m02, x52⟩ := ih (k + 1) l1 len1 (by omega)
      a1 b1 (by rw [p1]; ring) qq1 z1 ia1 c01 m01
    refine ⟨l2, ?_, len2, by rw [a2, show k + 1 + j = k + (j + 1) by omega], b2,
      by rw [p2, show k + 1 + j = k + (j + 1) by omega],
      by rw [qq2, show k + 1 + j = k + (j + 1) by omega], z2, c02, m02, x52.trans x51⟩
    have h := ProgOn.loop_iter TSA BODYA TstI.yes (Sum.inr AddI.done) (eF := TstI.no)
      (show TstI.test ≠ TstI.no by decide) ht r1 r2
    rw [testA_cost, hlen] at h
    convert h using 1
    ring

theorem atU_eq (U M : ℕ) : ∀ k, atU U M k = U / M ^ k
  | 0 => by simp [atU]
  | k + 1 => by rw [atU, atU_eq U M k, Nat.div_div_eq_div_mul, pow_succ]

/-- The loop's terms are the machine terms `atTerm`. -/
theorem atU_term (Z m : ℕ) (hm : 0 < m) (n : ℕ) :
    atU (Z * m) (m ^ 2) (n + 1) / (2 * n + 1) = PVNP.PiSeries.atTerm Z m n := by
  rw [atU_eq, ← pow_mul, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ,
    Nat.mul_div_mul_right _ _ hm, Nat.div_div_eq_div_mul, PVNP.PiSeries.atTerm, Nat.mul_comm]

/-- **The loop computes the alternating sum**, up to the sign `(−1)^{J+1}`. -/
theorem atR_eq (Z m : ℕ) (hm : 0 < m) :
    ∀ J, atR (Z * m) (m ^ 2) J = (-1) ^ (J + 1) * PVNP.PiSeries.atSum Z m J
  | 0 => by simp [atR, PVNP.PiSeries.atSum]
  | J + 1 => by
    have ih := atR_eq Z m hm J
    have hs : PVNP.PiSeries.atSum Z m (J + 1) =
        PVNP.PiSeries.atSum Z m J + (-1) ^ J * (PVNP.PiSeries.atTerm Z m J : ℤ) := by
      unfold PVNP.PiSeries.atSum; rw [Finset.sum_range_succ]
    rw [atR, ih, atU_term Z m hm J, hs]
    have hsq : ((-1 : ℤ) ^ J) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    linear_combination (-(PVNP.PiSeries.atTerm Z m J : ℤ)) * hsq

/-! ### The π machine: two arctangent loops and a subtraction -/

/-- Save the first sum in `xc.id` and load the second loop: power term `xc.x`, divisor `xc.y`,
odd number `xc.acc`, sum `0`, counter `xc.fl`. -/
def reinitF (x : GCell) : GCell :=
  ⟨x.dv, x.c, x.xc.x, x.xc.y, x.c0, x.m0, x.xc.acc, false, x.rp, x.rq,
    ⟨x.xc.x, x.xc.y, x.xc.acc, x.xc.fl, x.xc.z, x.xc.fl, x.xc.ib, x.xc.ic, x.qq⟩⟩

/-- The final combination `rq := id − qq`. -/
def lensFin : TrackLens GCell Cell :=
  ⟨fun x => ⟨x.xc.id, x.qq, x.rq⟩,
    fun x c => ⟨x.dv, x.c, x.a, x.b, x.c0, x.m0, x.p, c.b, x.rp, c.r,
      ⟨x.xc.x, x.xc.y, x.xc.acc, x.xc.fl, x.xc.z, x.xc.ia, x.xc.ib, x.xc.ic, c.a⟩⟩,
    fun _ _ => rfl⟩

def SUBF : ProgOn GCell := (ProgOn.ofProg subProg).viaLens lensFin gz gbit
def PI1 : ProgOn GCell := ProgOn.seq atLoop (MAPG reinitF) (Sum.inl TstI.no)
def PI2 : ProgOn GCell := ProgOn.seq PI1 atLoop (Sum.inr AddI.done)

/-- **The π machine.** -/
def piProg : ProgOn GCell := ProgOn.seq PI2 SUBF (Sum.inr (Sum.inl TstI.no))

/-- The approximation of `π/4` that the machine computes. -/
def piA (Z J : ℕ) : ℤ := PVNP.PiSeries.atSum Z 2 J + PVNP.PiSeries.atSum Z 3 (J + 1)

/-- **The π machine on any tape.** For odd `J`, from a tape of length `2W` holding the first
loop's data (power term `2Z`, divisor `4`, odd number `1`, sum `0`, counter `J`), the second
loop's data on the carried tracks (`3Z`, `9`, `1`, counter `J + 1`), the code of `−2`, the
counter constant `W` and the marker `2^W`, the machine first-arrives at its exit with
`rq = tc_{2W}(atSum Z 2 J + atSum Z 3 (J + 1))`, in exactly
`((2J + 1)(8W + 14) + 4)(4W + 2)` transitions. -/
theorem pi_run {W Z J : ℕ} (hJ : Odd J) (hZ : Z * 3 < 2 ^ W) (hJW : 2 * (J + 1) + 1 < 2 ^ W)
    (hW4 : 9 < 2 ^ W) (l : List GCell) (hlen : l.length = 2 * W)
    (ha : tv GCell.a l = Z * 2) (hb : tv GCell.b l = 2 ^ 2) (hp : tv GCell.p l = 1)
    (hqq : tv GCell.qq l = 0) (hia : tv (fun x => x.xc.ia) l = J)
    (hz : tv (fun x => x.xc.z) l = tc (2 * W) (-2)) (hc0 : tv GCell.c0 l = W)
    (hm0 : tv GCell.m0 l = 2 ^ W) (hx : tv (fun x => x.xc.x) l = Z * 3)
    (hy : tv (fun x => x.xc.y) l = 3 ^ 2) (hacc : tv (fun x => x.xc.acc) l = 1)
    (hfl : tv (fun x => x.xc.fl) l = J + 1) :
    ∃ l', ReachFirst piProg.toProg (Sum.inr AddI.done)
        (Sum.inl (Sum.inl (Sum.inl (Sum.inl TstI.test))), l) l'
        (((2 * J + 1) * (8 * W + 14) + 4) * (4 * W + 2)) ∧
      l'.length = 2 * W ∧ tv GCell.rq l' = tc (2 * W) (piA Z J) := by
  -- the first loop, for `arctan(1/2)`
  have hU2 : Z * 2 < 2 ^ W := by omega
  obtain ⟨l1, r1, len1, -, -, -, qq1, z1, c01, m01, x51⟩ :=
    at_loop (W := W) (U := Z * 2) (M := 2 ^ 2) hU2 (by norm_num) (by omega) J 0 l hlen
      (by omega) ha hb hp (by rw [hqq]; rfl) hz hia hc0 hm0
  -- reload for `arctan(1/3)`
  have r2 := map_first reinitF gbit l1
  have len2 : (l1.map reinitF).length = 2 * W := by rw [List.length_map, len1]
  have X5 : ∀ {β : Type} (π : Bool × Bool × Bool × Bool × Bool → β),
      l1.map (fun x => π (lensX5.get x)) = l.map (fun x => π (lensX5.get x)) := by
    intro β π
    have := congrArg (List.map π) x51
    simpa [List.map_map, Function.comp_def] using this
  have a2 : tv GCell.a (l1.map reinitF) = Z * 3 := by
    rw [tv_map]; exact (tv_congr (f := fun x => x.xc.x) (X5 (fun k => k.1))).trans hx
  have b2 : tv GCell.b (l1.map reinitF) = 3 ^ 2 := by
    rw [tv_map]; exact (tv_congr (f := fun x => x.xc.y) (X5 (fun k => k.2.1))).trans hy
  have p2 : tv GCell.p (l1.map reinitF) = 2 * 0 + 1 := by
    rw [tv_map]; exact (tv_congr (f := fun x => x.xc.acc) (X5 (fun k => k.2.2.1))).trans hacc
  have qq2 : tv GCell.qq (l1.map reinitF) = tc (2 * W) (atR (Z * 3) (3 ^ 2) 0) := by
    rw [tv_map]; exact val_false l1
  have ia2 : tv (fun x => x.xc.ia) (l1.map reinitF) = J + 1 := by
    rw [tv_map]; exact (tv_congr (f := fun x => x.xc.fl) (X5 (fun k => k.2.2.2.1))).trans hfl
  have z2 : tv (fun x => x.xc.z) (l1.map reinitF) = tc (2 * W) (-2) := by
    rw [tv_map]; exact z1
  have c02 : tv GCell.c0 (l1.map reinitF) = W := by rw [tv_map]; exact c01
  have m02 : tv GCell.m0 (l1.map reinitF) = 2 ^ W := by rw [tv_map]; exact m01
  -- the second loop
  obtain ⟨l3, r3, len3, -, -, -, qq3, -, -, -, x53⟩ :=
    at_loop (W := W) (U := Z * 3) (M := 3 ^ 2) hZ (by norm_num) (by omega) (J + 1) 0
      (l1.map reinitF) len2 (by omega) a2 b2 p2 qq2 z2 ia2 c02 m02
  -- the saved first sum
  have id3 : tv (fun x => x.xc.id) l3 = tc (2 * W) (atR (Z * 2) (2 ^ 2) (0 + J)) := by
    have e : l3.map (fun x => x.xc.id) = (l1.map reinitF).map (fun x => x.xc.id) := by
      have := congrArg (List.map (fun k : Bool × Bool × Bool × Bool × Bool => k.2.2.2.2)) x53
      simpa [List.map_map, Function.comp_def] using this
    exact (tv_congr e).trans (by rw [tv_map]; exact qq1)
  -- the final subtraction
  obtain ⟨l4, r4, v4, -⟩ := stg_sub lensFin l3
  have ha4 : val ((l3.map lensFin.get).map Cell.a) = tc (2 * W) (atR (Z * 2) (2 ^ 2) (0 + J)) := by
    rw [List.map_map]; exact id3
  have hb4 : val ((l3.map lensFin.get).map Cell.b) =
      tc (2 * W) (atR (Z * 3) (3 ^ 2) (0 + (J + 1))) := by
    rw [List.map_map]; exact qq3
  have hs4 := sub_tc_value (l3.map lensFin.get) (2 * W) (by rw [List.length_map, len3]) _ _ ha4 hb4
  have len4 : l4.length = 2 * W := by
    have := congrArg List.length v4
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, len3]
  have hc := ProgOn.seq_reachFirst PI2 SUBF (Sum.inr (Sum.inl TstI.no))
    (show AddI.go ≠ AddI.done by decide)
    (ProgOn.seq_reachFirst PI1 atLoop (Sum.inr AddI.done)
      (show atLoop.start ≠ Sum.inl TstI.no by decide)
      (ProgOn.seq_reachFirst atLoop (MAPG reinitF) (Sum.inl TstI.no)
        (show AddI.go ≠ AddI.done by decide) r1 r2) r3) r4
  rw [len1, len3] at hc
  refine ⟨l4, ?_, len4, ?_⟩
  · convert hc using 1
    ring
  · have e : tv GCell.rq l4 = val ((l4.map lensFin.get).map Cell.r) := by
      unfold tv; rw [List.map_map]; rfl
    rw [e, v4, hs4, zero_add, zero_add, atR_eq Z 2 (by norm_num), atR_eq Z 3 (by norm_num)]
    obtain ⟨K, rfl⟩ := hJ
    unfold piA
    congr 1
    have h1 : ((-1 : ℤ) ^ (2 * K + 1 + 1)) = 1 := by
      rw [show 2 * K + 1 + 1 = 2 * (K + 1) by ring, pow_mul]; norm_num
    have h2 : ((-1 : ℤ) ^ (2 * K + 1 + 1 + 1)) = -1 := by
      rw [show 2 * K + 1 + 1 + 1 = 2 * (K + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
    rw [h1, h2]
    ring

/-! ### The certificate, the layout and the compiled machine -/

/-- **The certificate**: `|4 piA Z J − Zπ| ≤ 8J + 4 + (16/3) Z/4^J`. -/
theorem piA_err (Z J : ℕ) :
    |4 * (piA Z J : ℝ) - Z * Real.pi| ≤ 8 * J + 4 + 16 / 3 * Z / 4 ^ J := by
  have h2 := PVNP.PiSeries.atSum_err Z 2 J le_rfl
  have h3 := PVNP.PiSeries.atSum_err Z 3 (J + 1) (by norm_num)
  have e : 4 * (piA Z J : ℝ) - Z * Real.pi =
      4 * (((PVNP.PiSeries.atSum Z 2 J : ℝ) - Z * Real.arctan (1 / 2)) +
        ((PVNP.PiSeries.atSum Z 3 (J + 1) : ℝ) - Z * Real.arctan (1 / 3))) := by
    rw [PVNP.PiSeries.pi_euler]; unfold piA; push_cast; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  push_cast at h2 h3
  set X := (PVNP.PiSeries.atSum Z 2 J : ℝ) - Z * Real.arctan (1 / 2)
  set Y := (PVNP.PiSeries.atSum Z 3 (J + 1) : ℝ) - Z * Real.arctan (1 / 3)
  have hab := abs_add_le X Y
  have hZ : (0 : ℝ) ≤ Z := by positivity
  have p3 : ((1 : ℝ) / 3) ^ (2 * (J + 1) + 1) ≤ ((1 : ℝ) / 2) ^ (2 * J + 1) := by
    calc ((1 : ℝ) / 3) ^ (2 * (J + 1) + 1) ≤ ((1 : ℝ) / 3) ^ (2 * J + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ ((1 : ℝ) / 2) ^ (2 * J + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have p2 : ((1 : ℝ) / 2) ^ (2 * J + 1) = 1 / 2 * (1 / 4 ^ J) := by
    rw [pow_succ, pow_mul, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num, one_div_pow]; ring
  set A := 4 / 3 * (Z : ℝ) * ((1 : ℝ) / 2) ^ (2 * J + 1)
  set B := 4 / 3 * (Z : ℝ) * ((1 : ℝ) / 3) ^ (2 * (J + 1) + 1)
  have hB : B ≤ A := mul_le_mul_of_nonneg_left p3 (by positivity)
  have hA : A = 2 / 3 * Z / 4 ^ J := by
    simp only [A]; rw [p2]; field_simp; ring
  calc 4 * |X + Y| ≤ 4 * (|X| + |Y|) := by linarith
    _ ≤ 4 * ((J + A) + ((J + 1 : ℕ) + B)) := by push_cast at h3 ⊢; linarith
    _ ≤ 4 * ((J + A) + ((J + 1 : ℕ) + A)) := by linarith
    _ = 8 * J + 4 + 8 * A := by push_cast; ring
    _ = 8 * J + 4 + 16 / 3 * Z / 4 ^ J := by rw [hA]; ring

theorem atSum_abs_le (Z m J : ℕ) : |PVNP.PiSeries.atSum Z m J| ≤ J * Z := by
  unfold PVNP.PiSeries.atSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ n ∈ Finset.range J, |(-1 : ℤ) ^ n * (PVNP.PiSeries.atTerm Z m n : ℤ)| ≤ Z := by
    intro n _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    exact_mod_cast Nat.div_le_self _ _
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- The π layout on `2W` cells: the first loop's data `2Z, 4, 1, J`, the second loop's data
`3Z, 9, 1, J + 1` on the carried tracks, the code of `−2`, the counter constant `W` and the
marker `2^W`. Every other track is zero. -/
def piInput (W Z J : ℕ) : List GCell :=
  (List.range (2 * W)).map fun i =>
    ⟨⟨false, false, false, false⟩, false, (bitsOf (2 * W) (Z * 2)).getD i false,
      (bitsOf (2 * W) 4).getD i false, (bitsOf (2 * W) W).getD i false,
      (bitsOf (2 * W) (2 ^ W)).getD i false, (bitsOf (2 * W) 1).getD i false, false, false, false,
      ⟨(bitsOf (2 * W) (Z * 3)).getD i false, (bitsOf (2 * W) 9).getD i false,
        (bitsOf (2 * W) 1).getD i false, (bitsOf (2 * W) (J + 1)).getD i false,
        (bitsOf (2 * W) (tc (2 * W) (-2))).getD i false, (bitsOf (2 * W) J).getD i false,
        false, false, false⟩⟩

theorem tv_range (X n : ℕ) :
    val ((List.range n).map (fun i => (bitsOf n X).getD i false)) = X % 2 ^ n := by
  rw [map_range_getD _ _ (bitsOf_length _ _), val_bitsOf]

/-- **Certified `π` on the compiled Turing machine.** For odd `J`, with `3Z < 2^W`,
`2J + 3 < 2^W` and `9 < 2^W`, from the layout `piInput W Z J` the compiled single-tape TM runs
exactly `((2J + 1)(8W + 14) + 4)(4W + 2)` transitions. Its result track, read in `2W`-bit two's
complement, is an integer `A = piA Z J` with `|4A − Zπ| ≤ 8J + 4 + (16/3) Z/4^J`. -/
theorem pi_tm {W Z J : ℕ} (hJ : Odd J) (hZ : Z * 3 < 2 ^ W) (hJW : 2 * (J + 1) + 1 < 2 ^ W)
    (hW9 : 9 < 2 ^ W) (T : ℤ → Sym GCell) (hT : piProg.toProg.Repr T (piInput W Z J)) :
    ∃ l' T', piProg.toProg.Repr T' l' ∧
      tv GCell.rq l' = tc (2 * W) (piA Z J) ∧ sval (2 * W) (tv GCell.rq l') = piA Z J ∧
      |4 * (piA Z J : ℝ) - Z * Real.pi| ≤ 8 * J + 4 + 16 / 3 * Z / 4 ^ J ∧
      piProg.toProg.toTM.run
          ⟨.fwd piProg.start (piProg.toProg.init piProg.start), T, 0⟩
          (((2 * J + 1) * (8 * W + 14) + 4) * (4 * W + 2)) =
        ⟨.fwd (Sum.inr AddI.done) (piProg.toProg.init (Sum.inr AddI.done)), T', 0⟩ := by
  have hW1 : 0 < W := by
    rcases Nat.eq_zero_or_pos W with h | h
    · rw [h] at hW9; norm_num at hW9
    · exact h
  have hW2 : 2 ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hWW : W < 2 ^ (2 * W) := lt_of_lt_of_le Nat.lt_two_pow_self hW2
  have hlt : ∀ X, X < 2 ^ W → X < 2 ^ (2 * W) := fun X h => lt_of_lt_of_le h hW2
  have hlen : (piInput W Z J).length = 2 * W := by simp [piInput]
  have ha : tv GCell.a (piInput W Z J) = Z * 2 := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (hlt _ (by omega)))
  have hb : tv GCell.b (piInput W Z J) = 2 ^ 2 := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (hlt _ (by omega)))
  have hp : tv GCell.p (piInput W Z J) = 1 := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (hlt _ (by omega)))
  have hqq : tv GCell.qq (piInput W Z J) = 0 := by
    unfold tv piInput; rw [List.map_map]; exact val_false _
  have hia : tv (fun x => x.xc.ia) (piInput W Z J) = J := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (hlt _ (by omega)))
  have hz : tv (fun x => x.xc.z) (piInput W Z J) = tc (2 * W) (-2) := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (tc_lt _ _))
  have hc0 : tv GCell.c0 (piInput W Z J) = W := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt hWW)
  have hm0 : tv GCell.m0 (piInput W Z J) = 2 ^ W := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  have hx : tv (fun x => x.xc.x) (piInput W Z J) = Z * 3 := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (hlt _ hZ))
  have hy : tv (fun x => x.xc.y) (piInput W Z J) = 3 ^ 2 := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (hlt _ (by omega)))
  have hacc : tv (fun x => x.xc.acc) (piInput W Z J) = 1 := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (hlt _ (by omega)))
  have hfl : tv (fun x => x.xc.fl) (piInput W Z J) = J + 1 := by
    unfold tv piInput; rw [List.map_map]
    exact (tv_range _ _).trans (Nat.mod_eq_of_lt (hlt _ (by omega)))
  obtain ⟨l', hr, -, hrq⟩ := pi_run hJ hZ hJW hW9 (piInput W Z J) hlen ha hb hp hqq hia hz hc0
    hm0 hx hy hacc hfl
  obtain ⟨T', hT', hrun⟩ := piProg.toProg.reach_run hr.reach T hT
  refine ⟨l', T', hT', hrq, ?_, piA_err Z J, hrun⟩
  -- decoding: `|piA Z J| ≤ (2J + 1) Z < 2^{2W − 1}`
  have b2 := atSum_abs_le Z 2 J
  have b3 := atSum_abs_le Z 3 (J + 1)
  have hbound : |piA Z J| ≤ (2 * J + 1) * Z := by
    unfold piA
    refine (abs_add_le _ _).trans ?_
    push_cast at b2 b3 ⊢
    linarith
  have hprod : ((2 * J + 1) * Z : ℤ) * 3 < (2 : ℤ) ^ W * 2 ^ W := by
    have h1 : ((2 * J + 1 : ℕ) : ℤ) < 2 ^ W := by exact_mod_cast (by omega : 2 * J + 1 < 2 ^ W)
    have h2 : ((Z * 3 : ℕ) : ℤ) < 2 ^ W := by exact_mod_cast hZ
    push_cast at h1 h2
    calc ((2 * J + 1) * Z : ℤ) * 3 = (2 * J + 1) * (Z * 3) := by ring
      _ < 2 ^ W * 2 ^ W := mul_lt_mul'' h1 h2 (by positivity) (by positivity)
  have hpw : (2 : ℤ) ^ W * 2 ^ W = 2 * 2 ^ (2 * W - 1) := by
    rw [← pow_add, ← pow_succ']; congr 1; omega
  have hP : (0 : ℤ) ≤ 2 ^ (2 * W - 1) := by positivity
  have h3 : -(2 : ℤ) ^ (2 * W - 1) ≤ piA Z J := by
    have := neg_abs_le (piA Z J)
    linarith
  have h4 : piA Z J < (2 : ℤ) ^ (2 * W - 1) := by
    have := le_abs_self (piA Z J)
    linarith
  rw [hrq]
  exact sval_tc (2 * W) (by omega) _ h3 h4

/-- **Certified `π` to precision `q`.** With `Z = 2^q`, `J = 2q + 1` and `W = q + 3` (`q ≥ 1`), the
compiled TM runs exactly `((4q + 3)(8q + 38) + 4)(4q + 14)` transitions, a polynomial of degree 3
in `q`, and its result `A` (in `2W`-bit two's complement) satisfies
`|4A/2^q − π| ≤ (16q + 14)/2^q`. -/
theorem pi_tm_prec {q : ℕ} (hq : 1 ≤ q) (T : ℤ → Sym GCell)
    (hT : piProg.toProg.Repr T (piInput (q + 3) (2 ^ q) (2 * q + 1))) :
    ∃ l' T', piProg.toProg.Repr T' l' ∧
      |4 * (sval (2 * (q + 3)) (tv GCell.rq l') : ℝ) / 2 ^ q - Real.pi| ≤ (16 * q + 14) / 2 ^ q ∧
      piProg.toProg.toTM.run
          ⟨.fwd piProg.start (piProg.toProg.init piProg.start), T, 0⟩
          (((4 * q + 3) * (8 * q + 38) + 4) * (4 * q + 14)) =
        ⟨.fwd (Sum.inr AddI.done) (piProg.toProg.init (Sum.inr AddI.done)), T', 0⟩ := by
  have hq2 : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
  have h8 : 2 ^ (q + 3) = 8 * 2 ^ q := by rw [pow_add]; ring
  obtain ⟨l', T', hT', -, hs, herr, hrun⟩ := pi_tm (W := q + 3) (Z := 2 ^ q) (J := 2 * q + 1)
    ⟨q, rfl⟩ (by omega) (by omega) (by omega) T hT
  refine ⟨l', T', hT', ?_, ?_⟩
  · rw [hs]
    have hZ : (0 : ℝ) < 2 ^ q := by positivity
    have h4 : (2 : ℝ) ^ q * 4 ≤ 4 ^ (2 * q + 1) := by
      rw [pow_succ, pow_mul]
      have : (2 : ℝ) ^ q ≤ (4 ^ 2) ^ q := pow_le_pow_left₀ (by norm_num) (by norm_num) q
      nlinarith
    have htail : 16 / 3 * ((2 ^ q : ℕ) : ℝ) / 4 ^ (2 * q + 1) ≤ 4 / 3 := by
      push_cast
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have e1 : |4 * (piA (2 ^ q) (2 * q + 1) : ℝ) / 2 ^ q - Real.pi| =
        |4 * (piA (2 ^ q) (2 * q + 1) : ℝ) - ((2 ^ q : ℕ) : ℝ) * Real.pi| / 2 ^ q := by
      rw [← abs_of_pos hZ, ← abs_div, abs_of_pos hZ]
      congr 1
      push_cast
      field_simp
    rw [e1, div_le_div_iff_of_pos_right hZ]
    push_cast at herr htail ⊢
    linarith
  · rw [show 2 * (2 * q + 1) + 1 = 4 * q + 3 by ring, show 8 * (q + 3) + 14 = 8 * q + 38 by ring,
      show 4 * (q + 3) + 2 = 4 * q + 14 by ring] at hrun
    exact hrun

end PVNP.Discrete.SweepArith
