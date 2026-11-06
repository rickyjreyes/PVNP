import PVNP.CookLevinKit

/-!
# CL-1, part 2b: unary polynomial evaluation by sweeps

`hCtrl P` evaluates the Horner scheme of a coefficient list `P.cs` (highest degree first) at the
input length `n`, in unary: it leaves exactly `horner P.cs n` marks, on the cells
`0, …, horner P.cs n − 1`, of track `P.T1`.  Each Horner step computes `acc · n + c` with two
cursors (`ca` over the accumulator, `cw` over the input) and a write pointer `pb`; the
accumulator alternates between `P.T1` and `P.T2`.

`horner_phase`: from any list with input region `n`, at least one cell and clear tracks `T1`,
`T2`, the program reaches its final state with `Run T1 (horner cs n)`, changing only the tracks
`T1, T2, ca, cw, pb`, in at most `hBound` round trips.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim

/-- Horner value of a coefficient list, highest degree first. -/
def horner (cs : List ℕ) (n : ℕ) : ℕ := cs.foldl (fun a c => a * n + c) 0

theorem horner_take_succ (cs : List ℕ) (n s : ℕ) (hs : s < cs.length) :
    horner (cs.take (s + 1)) n = horner (cs.take s) n * n + cs[s] := by
  unfold horner
  rw [List.take_succ, List.getElem?_eq_getElem hs, Option.toList_some, List.foldl_append]
  rfl

/-- Control states of the Horner phase. -/
inductive HSt (L A : ℕ) where
  | clr (s : Fin L) | p0 (s : Fin L) | a0 (s : Fin L) | w0 (s : Fin L)
  | outer (s : Fin L) | inner (s : Fin L) | set (s : Fin L) | sp (s : Fin L) | sw (s : Fin L)
  | sa (s : Fin L) | wr (s : Fin L)
  | add (s : Fin L) (j : Fin (A + 1)) | addS (s : Fin L) (j : Fin (A + 1))
  | fin
  deriving DecidableEq, Fintype

/-- Parameters: coefficient list and the two accumulator tracks. -/
structure HPar where
  cs : List ℕ
  T1 : Mk
  T2 : Mk

namespace HPar

variable (P : HPar)

/-- Track receiving step `s`. -/
def dst (s : ℕ) : Mk := if (P.cs.length - 1 - s) % 2 = 0 then P.T1 else P.T2

/-- Track read by step `s`. -/
def src (s : ℕ) : Mk := if (P.cs.length - 1 - s) % 2 = 0 then P.T2 else P.T1

theorem coef_le (s : Fin P.cs.length) : P.cs[s] ≤ P.cs.sum :=
  List.le_sum_of_mem (List.getElem_mem _)

/-- The coefficient of step `s`, as a counter. -/
def coef (s : Fin P.cs.length) : Fin (P.cs.sum + 1) := ⟨P.cs[s], Nat.lt_succ_of_le (P.coef_le s)⟩

/-- The Horner program. -/
def ctrl : Ctrl where
  C := HSt P.cs.length P.cs.sum
  start := if h : 0 < P.cs.length then .clr ⟨0, h⟩ else .fin
  op
    | .clr s => .clear (P.dst s)
    | .p0 _ => .first .pb
    | .a0 _ => .first .ca
    | .w0 _ => .first .cw
    | .outer s => .read (.mark .ca (P.src s))
    | .inner _ => .read (.inp .cw)
    | .set s => .setM .pb (P.dst s) true
    | .sp _ => .shift .pb
    | .sw _ => .shift .cw
    | .sa _ => .shift .ca
    | .wr _ => .first .cw
    | .add s j => if j.val = 0 then .read (.zero .pb) else .setM .pb (P.dst s) true
    | .addS _ _ => .shift .pb
    | .fin => .read (.zero .pb)
  nxt
    | .clr s, _ => .inl (.p0 s)
    | .p0 s, _ => .inl (.a0 s)
    | .a0 s, _ => .inl (.w0 s)
    | .w0 s, _ => .inl (.outer s)
    | .outer s, r => if r = .b true then .inl (.inner s) else .inl (.add s (P.coef s))
    | .inner s, r => if r = .o none then .inl (.sa s) else .inl (.set s)
    | .set s, _ => .inl (.sp s)
    | .sp s, _ => .inl (.sw s)
    | .sw s, _ => .inl (.inner s)
    | .sa s, _ => .inl (.wr s)
    | .wr s, _ => .inl (.outer s)
    | .add s j, _ => if j.val = 0 then
          (if h : s.val + 1 < P.cs.length then .inl (.clr ⟨s.val + 1, h⟩) else .inl .fin)
        else .inl (.addS s j)
    | .addS s j, _ => .inl (.add s ⟨j.val - 1, by omega⟩)
    | .fin, _ => .inr true

/-- Tracks the phase may change. -/
def ch (k : Mk) : Bool :=
  decide (k = P.T1) || decide (k = P.T2) || decide (k = .ca) || decide (k = .cw) || decide (k = .pb)

/-- Track hypotheses. -/
structure Good : Prop where
  t12 : P.T1 ≠ P.T2
  t1a : P.T1 ≠ .ca
  t1w : P.T1 ≠ .cw
  t1p : P.T1 ≠ .pb
  t2a : P.T2 ≠ .ca
  t2w : P.T2 ≠ .cw
  t2p : P.T2 ≠ .pb

variable {P}

theorem dst_or (s : ℕ) : P.dst s = P.T1 ∨ P.dst s = P.T2 := by unfold dst; split_ifs <;> simp
theorem src_or (s : ℕ) : P.src s = P.T1 ∨ P.src s = P.T2 := by unfold src; split_ifs <;> simp

theorem src_succ {s : ℕ} (hs : s + 1 < P.cs.length) : P.src (s + 1) = P.dst s := by
  unfold src dst
  have : (P.cs.length - 1 - s) = (P.cs.length - 1 - (s + 1)) + 1 := by omega
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one (P.cs.length - 1 - (s + 1)) with h | h
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg (by omega), if_pos (by omega)]

theorem dst_last (h : 0 < P.cs.length) : P.dst (P.cs.length - 1) = P.T1 := by
  unfold dst; simp

theorem src_dst_ne (hg : P.Good) (s : ℕ) : P.src s ≠ P.dst s := by
  unfold src dst; split_ifs
  · exact hg.t12.symm
  · exact hg.t12

theorem ch_T1 : P.ch P.T1 = true := by simp [ch]
theorem ch_T2 : P.ch P.T2 = true := by simp [ch]
theorem ch_dst (s : ℕ) : P.ch (P.dst s) = true := by rcases dst_or (P := P) s with h | h <;> simp [h, ch]
theorem ch_ca : P.ch .ca = true := by simp [ch]
theorem ch_cw : P.ch .cw = true := by simp [ch]
theorem ch_pb : P.ch .pb = true := by simp [ch]

theorem dst_ne (hg : P.Good) (s : ℕ) : P.dst s ≠ .ca ∧ P.dst s ≠ .cw ∧ P.dst s ≠ .pb := by
  rcases dst_or (P := P) s with h | h <;> rw [h]
  · exact ⟨hg.t1a, hg.t1w, hg.t1p⟩
  · exact ⟨hg.t2a, hg.t2w, hg.t2p⟩

theorem src_ne (hg : P.Good) (s : ℕ) : P.src s ≠ .ca ∧ P.src s ≠ .cw ∧ P.src s ≠ .pb := by
  rcases src_or (P := P) s with h | h <;> rw [h]
  · exact ⟨hg.t1a, hg.t1w, hg.t1p⟩
  · exact ⟨hg.t2a, hg.t2w, hg.t2p⟩

end HPar

/-! ## Correctness of the Horner phase -/

theorem clear_run (k : Mk) (l : List Cell) : Run (Op.eff (.clear k) l) k 0 := by
  refine ⟨Nat.zero_le _, fun j hj => ?_⟩
  rw [eff_map_get (eff_clear k)]; simp

namespace HPar

variable {P : HPar} (hg : P.Good) (n : ℕ)

/-- Invariant of the inner loop (`w` input cells already copied for accumulator cell `i`). -/
structure II (s acc i w : ℕ) (l : List Cell) : Prop where
  src : Run l (P.src s) acc
  dst : Run l (P.dst s) (i * n + w)
  pb : Uniq l .pb (i * n + w)
  ca : Uniq l .ca i
  cw : Uniq l .cw w
  inp : InpR l n
  wn : w ≤ n
  ia : i < acc

/-- Invariant of the outer loop. -/
structure OI (s acc i : ℕ) (l : List Cell) : Prop where
  src : Run l (P.src s) acc
  dst : Run l (P.dst s) (i * n)
  pb : Uniq l .pb (i * n)
  ca : Uniq l .ca i
  cw : Uniq l .cw 0
  inp : InpR l n
  ia : i ≤ acc

include hg

theorem inner_loop {s : Fin P.cs.length} {acc i : ℕ} :
    ∀ (d w : ℕ) (l : List Cell), w + d = n → II (P := P) n s acc i w l →
      ∃ l', RN P.ctrl.prog (.inner s, l) (.outer s, l') (4 * d + 3) ∧
        OI (P := P) n s acc (i + 1) l' ∧ Fr (AgS P.ch) l l' := by
  have hd := dst_ne hg s
  have hs := src_ne hg s
  have hsd := src_dst_ne hg s
  intro d
  induction d with
  | zero =>
    intro w l hw I
    simp only [Nat.add_zero] at hw
    subst w
    -- inner read: past the input
    have hr : (Op.read (.inp .cw)).res l = .o none := by
      rw [read_inp I.cw]
      have := I.inp.2 n I.cw.1
      simp only [lt_irrefl, decide_false] at this
      revert this
      cases (l[n]'I.cw.1).inp <;> simp
    have h1 : RN P.ctrl.prog (.inner s, l) (.sa s, l) 1 := by
      have := Ctrl.step_of P.ctrl (.inner s) (.sa s) l (by
        show (if (Op.read (.inp .cw)).res l = .o none then _ else _) = _
        rw [if_pos hr])
      simpa [eff_read] using this
    -- shift ca
    set l1 := Op.eff (.shift .ca) l with hl1
    have f1 : Fr (AgS P.ch) l l1 := Fr.agK_agS ch_ca (fr_shift .ca l)
    have h2 : RN P.ctrl.prog (.sa s, l) (.wr s, l1) 1 := Ctrl.step_of P.ctrl (.sa s) (.wr s) l rfl
    -- first cw
    set l2 := Op.eff (.first .cw) l1 with hl2
    have f2 : Fr (AgS P.ch) l1 l2 := Fr.agK_agS ch_cw (fr_first .cw l1)
    have h3 : RN P.ctrl.prog (.wr s, l1) (.outer s, l2) 1 := Ctrl.step_of P.ctrl (.wr s) (.outer s) l1 rfl
    have hca : Uniq l1 .ca (i + 1) := (shift_uniq I.ca).1
    have hlen1 : 0 < l1.length := by have := hca.1; omega
    refine ⟨l2, (h1.trans h2).trans h3, ?_, ?_⟩
    · have hne1 : ∀ {k : Mk}, k ≠ .ca → Fr (AgK .ca) l l1 := fun _ => fr_shift .ca l
      refine ⟨?_, ?_, ?_, ?_, first_uniq hlen1, ?_, by have := I.ia; omega⟩
      · exact (I.src.fr (fr_shift .ca l) hs.1).fr (fr_first .cw l1) hs.2.1
      · have := (I.dst.fr (fr_shift .ca l) hd.1).fr (fr_first .cw l1) hd.2.1
        rwa [show i * n + n = (i + 1) * n by ring] at this
      · have := (I.pb.fr (fr_shift .ca l) (by decide)).fr (fr_first .cw l1) (by decide)
        rwa [show i * n + n = (i + 1) * n by ring] at this
      · exact hca.fr (fr_first .cw l1) (by decide)
      · exact (I.inp.fr f1).fr f2
    · exact (f1.trans f2).mono (fun a b h => h.mono (fun k hk => by simpa using hk))
  | succ d ih =>
    intro w l hw I
    have hwn : w < n := by omega
    have hr : (Op.read (.inp .cw)).res l ≠ .o none := by
      rw [read_inp I.cw]
      have := I.inp.2 w I.cw.1
      simp only [hwn, decide_true] at this
      intro h
      simp only [RRes.o.injEq] at h
      rw [h] at this; simp at this
    have h1 : RN P.ctrl.prog (.inner s, l) (.set s, l) 1 := by
      have := Ctrl.step_of P.ctrl (.inner s) (.set s) l (by
        show (if (Op.read (.inp .cw)).res l = .o none then _ else _) = _
        rw [if_neg hr])
      simpa [eff_read] using this
    -- set the destination mark at the pointer
    set l1 := Op.eff (.setM .pb (P.dst s) true) l with hl1
    have f1 : Fr (AgS P.ch) l l1 := Fr.agK_agS (ch_dst s) (fr_setM .pb (P.dst s) true l)
    have hset := setM_run I.pb I.dst (Ne.symm hd.2.2)
    have h2 : RN P.ctrl.prog (.set s, l) (.sp s, l1) 1 := Ctrl.step_of P.ctrl (.set s) (.sp s) l rfl
    -- shift the pointer
    set l2 := Op.eff (.shift .pb) l1 with hl2
    have f2 : Fr (AgS P.ch) l1 l2 := Fr.agK_agS ch_pb (fr_shift .pb l1)
    have h3 : RN P.ctrl.prog (.sp s, l1) (.sw s, l2) 1 := Ctrl.step_of P.ctrl (.sp s) (.sw s) l1 rfl
    -- shift the input cursor
    set l3 := Op.eff (.shift .cw) l2 with hl3
    have f3 : Fr (AgS P.ch) l2 l3 := Fr.agK_agS ch_cw (fr_shift .cw l2)
    have h4 : RN P.ctrl.prog (.sw s, l2) (.inner s, l3) 1 := Ctrl.step_of P.ctrl (.sw s) (.inner s) l2 rfl
    have I' : II (P := P) n s acc i (w + 1) l3 := by
      have fs1 := fr_setM .pb (P.dst s) true l
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, I.ia⟩
      · exact ((I.src.fr fs1 hsd).fr (fr_shift .pb l1) hs.2.2).fr (fr_shift .cw l2) hs.2.1
      · have := (hset.1.fr (fr_shift .pb l1) hd.2.2).fr (fr_shift .cw l2) hd.2.1
        rwa [show i * n + w + 1 = i * n + (w + 1) by ring] at this
      · have := ((shift_uniq hset.2).1).fr (fr_shift .cw l2) (by decide)
        rwa [show i * n + w + 1 = i * n + (w + 1) by ring] at this
      · exact ((I.ca.fr fs1 hd.1.symm).fr (fr_shift .pb l1) (by decide)).fr (fr_shift .cw l2)
          (by decide)
      · exact (shift_uniq ((I.cw.fr fs1 hd.2.1.symm).fr (fr_shift .pb l1) (by decide))).1
      · exact ((I.inp.fr f1).fr f2).fr f3
    obtain ⟨l', hrn, hO, hf⟩ := ih (w + 1) l3 (by omega) I'
    refine ⟨l', RN.cast_k ((((h1.trans h2).trans h3).trans h4).trans hrn) (by omega), hO, ?_⟩
    exact (((f1.trans f2).trans f3).trans hf).mono (fun a b h => h.mono (fun k hk => by simpa using hk))

theorem outer_loop {s : Fin P.cs.length} {acc : ℕ} :
    ∀ (e i : ℕ) (l : List Cell), i + e = acc → OI (P := P) n s acc i l →
      ∃ l', RN P.ctrl.prog (.outer s, l) (.add s (P.coef s), l') (e * (4 * n + 4) + 1) ∧
        Run l' (P.dst s) (acc * n) ∧ Uniq l' .pb (acc * n) ∧ Run l' (P.src s) acc ∧
        InpR l' n ∧ Fr (AgS P.ch) l l' := by
  intro e
  induction e with
  | zero =>
    intro i l hi O
    simp only [Nat.add_zero] at hi
    subst hi
    have hr : (Op.read (.mark .ca (P.src s))).res l = .b false := by
      rw [read_mark O.ca, O.src.2 _ O.ca.1]; simp
    have h1 := Ctrl.step_of P.ctrl (.outer s) (.add s (P.coef s)) l (by
      show (if (Op.read (.mark .ca (P.src s))).res l = .b true then _ else _) = _
      rw [hr]; simp)
    refine ⟨l, by simpa [eff_read] using h1, O.dst, O.pb, O.src, O.inp, Fr.refl_agS _ _⟩
  | succ e ih =>
    intro i l hi O
    have hia : i < acc := by omega
    have hr : (Op.read (.mark .ca (P.src s))).res l = .b true := by
      rw [read_mark O.ca, O.src.2 _ O.ca.1]; simp [hia]
    have h1 := Ctrl.step_of P.ctrl (.outer s) (.inner s) l (by
      show (if (Op.read (.mark .ca (P.src s))).res l = .b true then _ else _) = _
      rw [if_pos hr])
    have I : II (P := P) n s acc i 0 l :=
      ⟨O.src, by simpa using O.dst, by simpa using O.pb, O.ca, O.cw, O.inp, Nat.zero_le _, hia⟩
    obtain ⟨l1, h2, O1, f1⟩ := inner_loop hg n n 0 l (by omega) I
    obtain ⟨l2, h3, d2, p2, s2, i2, f2⟩ := ih (i + 1) l1 (by omega) O1
    refine ⟨l2, RN.cast_k ((by simpa [eff_read] using h1 : RN P.ctrl.prog (.outer s, l) (.inner s, l) 1).trans
      (h2.trans h3)) (by ring), d2, p2, s2, i2, ?_⟩
    exact (f1.trans f2).mono (fun a b h => h.mono (fun k hk => by simpa using hk))

/-- Successor state after step `s`. -/
def nextS (s : Fin P.cs.length) : HSt P.cs.length P.cs.sum :=
  if h : s.val + 1 < P.cs.length then .clr ⟨s.val + 1, h⟩ else .fin

theorem add_loop {s : Fin P.cs.length} :
    ∀ (j : ℕ) (hj : j < P.cs.sum + 1) (r : ℕ) (l : List Cell), Run l (P.dst s) r →
      Uniq l .pb r → InpR l n → Run l (P.src s) (horner (P.cs.take s) n) →
      ∃ l', RN P.ctrl.prog (.add s ⟨j, hj⟩, l) (nextS s, l') (2 * j + 1) ∧
        Run l' (P.dst s) (r + j) ∧ Run l' (P.src s) (horner (P.cs.take s) n) ∧ InpR l' n ∧
        Fr (AgS P.ch) l l' := by
  have hd := dst_ne hg s
  have hsd := src_dst_ne hg s
  intro j
  induction j with
  | zero =>
    intro hj r l hd' hp hi hs
    have h1 := Ctrl.step_of P.ctrl (.add s ⟨0, hj⟩) (nextS s) l (by
      simp only [HPar.ctrl, nextS]; split_ifs <;> simp_all)
    refine ⟨l, ?_, by simpa using hd', hs, hi, Fr.refl_agS _ _⟩
    have : (P.ctrl.op (.add s ⟨0, hj⟩)) = .read (.zero .pb) := rfl
    simpa [this, eff_read] using h1
  | succ j ih =>
    intro hj r l hd' hp hi hs
    have hop : P.ctrl.op (.add s ⟨j + 1, hj⟩) = .setM .pb (P.dst s) true := rfl
    have h1 := Ctrl.step_of P.ctrl (.add s ⟨j + 1, hj⟩) (.addS s ⟨j + 1, hj⟩) l rfl
    rw [hop] at h1
    set l1 := Op.eff (.setM .pb (P.dst s) true) l with hl1
    have hset := setM_run hp hd' (Ne.symm hd.2.2)
    have f1 : Fr (AgS P.ch) l l1 := Fr.agK_agS (ch_dst s) (fr_setM .pb (P.dst s) true l)
    have h2 := Ctrl.step_of P.ctrl (.addS s ⟨j + 1, hj⟩) (.add s ⟨j, by omega⟩) l1 rfl
    set l2 := Op.eff (.shift .pb) l1 with hl2
    have f2 : Fr (AgS P.ch) l1 l2 := Fr.agK_agS ch_pb (fr_shift .pb l1)
    have hp2 : Uniq l2 .pb (r + 1) := (shift_uniq hset.2).1
    have hd2 : Run l2 (P.dst s) (r + 1) := hset.1.fr (fr_shift .pb l1) hd.2.2
    have hs2 : Run l2 (P.src s) (horner (P.cs.take s) n) :=
      (hs.fr (fr_setM .pb (P.dst s) true l) hsd).fr (fr_shift .pb l1) (src_ne hg s).2.2
    obtain ⟨l3, h3, d3, s3, i3, f3⟩ := ih (by omega) (r + 1) l2 hd2 hp2 ((hi.fr f1).fr f2) hs2
    refine ⟨l3, RN.cast_k ((h1.trans h2).trans h3) (by ring), by rwa [show r + 1 + j = r + (j + 1)
      by ring] at d3, s3, i3, ?_⟩
    exact ((f1.trans f2).trans f3).mono (fun a b h => h.mono (fun k hk => by simpa using hk))

/-- **One Horner step**: from `clr s` to the next step, computing `acc · n + c`. -/
theorem step_phase (s : Fin P.cs.length) (l : List Cell) (hl : 0 < l.length) (hi : InpR l n)
    (hs : Run l (P.src s) (horner (P.cs.take s) n)) :
    ∃ l', RN P.ctrl.prog (.clr s, l) (nextS s, l')
        (4 + (horner (P.cs.take s) n * (4 * n + 4) + 1) + (2 * P.cs[s] + 1)) ∧
      Run l' (P.dst s) (horner (P.cs.take (s + 1)) n) ∧ InpR l' n ∧ Fr (AgS P.ch) l l' := by
  have hd := dst_ne hg s
  have hsd := src_dst_ne hg s
  have hsn := src_ne hg s
  set acc := horner (P.cs.take s) n with hacc
  -- clear the destination, place the pointer and both cursors
  have h1 := Ctrl.step_of P.ctrl (.clr s) (.p0 s) l rfl
  set l1 := Op.eff (.clear (P.dst s)) l
  have f1 : Fr (AgS P.ch) l l1 := Fr.agK_agS (ch_dst s) (fr_clear (P.dst s) l)
  have h2 := Ctrl.step_of P.ctrl (.p0 s) (.a0 s) l1 rfl
  set l2 := Op.eff (.first .pb) l1
  have f2 : Fr (AgS P.ch) l1 l2 := Fr.agK_agS ch_pb (fr_first .pb l1)
  have h3 := Ctrl.step_of P.ctrl (.a0 s) (.w0 s) l2 rfl
  set l3 := Op.eff (.first .ca) l2
  have f3 : Fr (AgS P.ch) l2 l3 := Fr.agK_agS ch_ca (fr_first .ca l2)
  have h4 := Ctrl.step_of P.ctrl (.w0 s) (.outer s) l3 rfl
  set l4 := Op.eff (.first .cw) l3
  have f4 : Fr (AgS P.ch) l3 l4 := Fr.agK_agS ch_cw (fr_first .cw l3)
  have hl1 : 0 < l1.length := lt_of_lt_of_le hl f1.1
  have hl2 : 0 < l2.length := lt_of_lt_of_le hl1 f2.1
  have hl3 : 0 < l3.length := lt_of_lt_of_le hl2 f3.1
  have O : OI (P := P) n s acc 0 l4 := by
    refine ⟨?_, ?_, ?_, ?_, first_uniq hl3, ((((hi.fr f1).fr f2).fr f3).fr f4), Nat.zero_le _⟩
    · exact (((hs.fr (fr_clear (P.dst s) l) hsd).fr (fr_first .pb l1) hsn.2.2).fr
        (fr_first .ca l2) hsn.1).fr (fr_first .cw l3) hsn.2.1
    · simpa using (((clear_run (P.dst s) l).fr (fr_first .pb l1) hd.2.2).fr
        (fr_first .ca l2) hd.1).fr (fr_first .cw l3) hd.2.1
    · simpa using ((first_uniq hl1 : Uniq l2 .pb 0).fr (fr_first .ca l2) (by decide)).fr
        (fr_first .cw l3) (by decide)
    · exact (first_uniq hl2 : Uniq l3 .ca 0).fr (fr_first .cw l3) (by decide)
  obtain ⟨l5, h5, d5, p5, s5, i5, f5⟩ := outer_loop hg n acc 0 l4 (by omega) O
  obtain ⟨l6, h6, d6, s6, i6, f6⟩ := add_loop hg n (s := s) P.cs[s] (P.coef s).isLt (acc * n) l5 d5 p5
    i5 s5
  refine ⟨l6, RN.cast_k ((((h1.trans h2).trans h3).trans h4).trans (h5.trans h6)) (by ring), ?_,
    i6, ?_⟩
  · rw [horner_take_succ _ _ _ s.isLt]; exact d6
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono
      (fun a b h => h.mono (fun k hk => by simpa using hk))

omit hg in
theorem horner_le : ∀ (s : ℕ), s ≤ P.cs.length →
    horner (P.cs.take s) n ≤ P.cs.sum * (n + 1) ^ s
  | 0, _ => by simp [horner]
  | s + 1, hs => by
    rw [horner_take_succ _ _ _ (by omega)]
    have ih := horner_le s (by omega)
    have hc := P.coef_le ⟨s, by omega⟩
    have h1 : 1 ≤ (n + 1) ^ s := Nat.one_le_pow _ _ (by omega)
    calc horner (P.cs.take s) n * n + P.cs[s] ≤ P.cs.sum * (n + 1) ^ s * n + P.cs.sum := by
          gcongr; exact hc
      _ ≤ P.cs.sum * (n + 1) ^ s * n + P.cs.sum * (n + 1) ^ s := by
          gcongr; exact Nat.le_mul_of_pos_right _ h1
      _ = P.cs.sum * (n + 1) ^ (s + 1) := by ring

/-- Round-trip bound of one Horner step. -/
def stepBound (P : HPar) (n : ℕ) : ℕ :=
  6 + 2 * P.cs.sum + P.cs.sum * (n + 1) ^ P.cs.length * (4 * n + 4)

theorem aux_phase : ∀ (m : ℕ) (s : Fin P.cs.length), s.val + m + 1 = P.cs.length →
    ∀ (l : List Cell), 0 < l.length → InpR l n → Run l (P.src s) (horner (P.cs.take s) n) →
      ∃ l' k, RN P.ctrl.prog (.clr s, l) (.fin, l') k ∧ Run l' P.T1 (horner P.cs n) ∧
        InpR l' n ∧ Fr (AgS P.ch) l l' ∧ k ≤ (m + 1) * stepBound P n := by
  have hbound : ∀ s : Fin P.cs.length,
      4 + (horner (P.cs.take s) n * (4 * n + 4) + 1) + (2 * P.cs[s] + 1) ≤ stepBound P n := by
    intro s
    have h1 := horner_le (P := P) n s (le_of_lt s.isLt)
    have h2 : (n + 1) ^ (s : ℕ) ≤ (n + 1) ^ P.cs.length :=
      Nat.pow_le_pow_right (by omega) (le_of_lt s.isLt)
    have h3 := P.coef_le s
    have h4 : horner (P.cs.take s) n ≤ P.cs.sum * (n + 1) ^ P.cs.length :=
      le_trans h1 (Nat.mul_le_mul_left _ h2)
    unfold stepBound
    have := Nat.mul_le_mul_right (4 * n + 4) h4
    omega
  intro m
  induction m with
  | zero =>
    intro s hs l hl hi hsrc
    obtain ⟨l', h, d, i, f⟩ := step_phase hg n s l hl hi hsrc
    have hn : nextS s = .fin := by unfold nextS; rw [dif_neg (by omega)]
    rw [hn] at h
    refine ⟨l', _, h, ?_, i, f, by simpa using hbound s⟩
    have ht : P.cs.take (s + 1) = P.cs := by rw [List.take_of_length_le (by omega)]
    rw [ht] at d
    have hdl : P.dst s = P.T1 := by
      have := dst_last (P := P) (by omega)
      rwa [show P.cs.length - 1 = s by omega] at this
    rwa [hdl] at d
  | succ m ih =>
    intro s hs l hl hi hsrc
    obtain ⟨l1, h1, d1, i1, f1⟩ := step_phase hg n s l hl hi hsrc
    have hlt : s.val + 1 < P.cs.length := by omega
    have hn : nextS s = .clr ⟨s.val + 1, hlt⟩ := by unfold nextS; rw [dif_pos hlt]
    rw [hn] at h1
    have hsrc' : Run l1 (P.src (s.val + 1)) (horner (P.cs.take (s.val + 1)) n) := by
      rw [src_succ hlt]; exact d1
    obtain ⟨l2, k, h2, d2, i2, f2, hk⟩ := ih ⟨s.val + 1, hlt⟩ (by simp; omega) l1
      (lt_of_lt_of_le hl f1.1) i1 hsrc'
    refine ⟨l2, _, h1.trans h2, d2, i2, (f1.trans f2).mono
      (fun a b h => h.mono (fun k hk => by simpa using hk)), ?_⟩
    have := hbound s
    nlinarith

/-- **Horner phase.**  From a list with input region `n`, at least one cell and clear accumulator
tracks, the program leaves exactly `horner cs n` marks on `T1`, touching only its own tracks. -/
theorem horner_phase (l : List Cell) (hl : 0 < l.length) (hi : InpR l n)
    (h1 : Run l P.T1 0) (h2 : Run l P.T2 0) :
    ∃ l' k, RN P.ctrl.prog (P.ctrl.start, l) (.fin, l') k ∧ Run l' P.T1 (horner P.cs n) ∧
      InpR l' n ∧ Fr (AgS P.ch) l l' ∧ k ≤ P.cs.length * stepBound P n := by
  by_cases hL : 0 < P.cs.length
  · have hst : P.ctrl.start = .clr ⟨0, hL⟩ := by simp [HPar.ctrl, hL]
    rw [hst]
    have hsrc : Run l (P.src 0) (horner (P.cs.take 0) n) := by
      simp only [List.take_zero, horner, List.foldl_nil]
      rcases src_or (P := P) 0 with h | h <;> rw [h]
      · exact h1
      · exact h2
    obtain ⟨l', k, h, d, i, f, hk⟩ := aux_phase hg n (P.cs.length - 1) ⟨0, hL⟩ (by simp; omega) l hl
      hi hsrc
    exact ⟨l', k, h, d, i, f, by rwa [show P.cs.length - 1 + 1 = P.cs.length by omega] at hk⟩
  · have hnil : P.cs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hst : P.ctrl.start = .fin := by simp [HPar.ctrl, hL]
    rw [hst]
    refine ⟨l, 0, RN.refl _, by simpa [hnil, horner] using h1, hi, Fr.refl_agS _ _, Nat.zero_le _⟩

end HPar

end PVNP.CookLevin.Gen
