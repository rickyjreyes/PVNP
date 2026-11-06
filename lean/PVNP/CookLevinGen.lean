import PVNP.CookLevinLabels
import PVNP.CookLevinHorner

/-!
# CL-1, part 2f: the uniform Cook–Levin generator

`genCtrl d` is one round-trip sweep program.  On input `x` it

1. appends a cell (`growC`);
2. writes `T + 1` marks on the row track `ut`, `T = t(|x|)` (Horner phase for `t + 1`);
3. writes `Q` marks on the witness track `uq`, `Q = q(|x|)` (Horner phase for `q`);
4. writes the column labels and places the main-loop cursors (`labCtrl`);
5. writes `inst x = encDense (numVars M T) (phi M x Q T)` on the `out` track (`mainCtrl`).

`gen_run` proves that it reaches its final state within `genBound d |x|` round trips with the
whole instance on the `out` track.  `genBound` is a polynomial expression in `|x|`.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim PVNP.PartI PVNP.CookLevin

/-! ## Polynomials in Horner form -/

/-- Coefficients of `p`, highest degree first. -/
noncomputable def hcoeffs (p : Polynomial ℕ) : List ℕ :=
  (List.range (p.natDegree + 1)).reverse.map p.coeff

theorem foldl_horner (n : ℕ) : ∀ (l : List ℕ) (a : ℕ),
    l.foldl (fun a c => a * n + c) a = a * n ^ l.length + l.foldl (fun a c => a * n + c) 0
  | [], a => by simp
  | c :: l, a => by
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_horner n l (a * n + c), foldl_horner n l (0 * n + c)]
    ring

theorem horner_range (f : ℕ → ℕ) (n : ℕ) : ∀ m : ℕ,
    horner ((List.range m).reverse.map f) n = ∑ i ∈ Finset.range m, f i * n ^ i
  | 0 => by simp [horner]
  | m + 1 => by
    rw [List.range_succ, List.reverse_append, List.map_append, Finset.sum_range_succ]
    simp only [List.reverse_singleton, List.map_cons, List.map_nil, List.singleton_append]
    have ih := horner_range f n m
    unfold horner at ih ⊢
    rw [List.foldl_cons, foldl_horner, ih, List.length_map, List.length_reverse, List.length_range]
    ring

theorem horner_hcoeffs (p : Polynomial ℕ) (n : ℕ) : horner (hcoeffs p) n = p.eval n := by
  rw [hcoeffs, horner_range, Polynomial.eval_eq_sum_range]

/-! ## The phases -/

/-- One `grow`. -/
def growC : Ctrl where
  C := Unit
  start := ()
  op _ := .grow
  nxt _ _ := .inr true

/-- Horner parameters for `T + 1` on the row track. -/
noncomputable def hparT (t : Polynomial ℕ) : HPar := ⟨hcoeffs (t + 1), .ut, .st⟩

/-- Horner parameters for `Q` on the witness track. -/
noncomputable def hparQ (q : Polynomial ℕ) : HPar := ⟨hcoeffs q, .uq, .sq⟩

theorem good_T (t : Polynomial ℕ) : (hparT t).Good :=
  ⟨(by decide : Mk.ut ≠ .st), (by decide : Mk.ut ≠ .ca), (by decide : Mk.ut ≠ .cw),
    (by decide : Mk.ut ≠ .pb), (by decide : Mk.st ≠ .ca), (by decide : Mk.st ≠ .cw),
    (by decide : Mk.st ≠ .pb)⟩

theorem good_Q (q : Polynomial ℕ) : (hparQ q).Good :=
  ⟨(by decide : Mk.uq ≠ .sq), (by decide : Mk.uq ≠ .ca), (by decide : Mk.uq ≠ .cw),
    (by decide : Mk.uq ≠ .pb), (by decide : Mk.sq ≠ .ca), (by decide : Mk.sq ≠ .cw),
    (by decide : Mk.sq ≠ .pb)⟩

theorem chT_uq (t : Polynomial ℕ) : (hparT t).ch .uq = false := rfl
theorem chT_sq (t : Polynomial ℕ) : (hparT t).ch .sq = false := rfl
theorem chQ_ut (q : Polynomial ℕ) : (hparQ q).ch .ut = false := rfl

/-- **The generator.** -/
noncomputable def genCtrl (d : Data) : Ctrl :=
  seq growC (seq (hparT d.t).ctrl (seq (hparQ d.q).ctrl (seq labCtrl (mainCtrl d.M))))

/-- Its final state. -/
noncomputable def genDone (d : Data) : (genCtrl d).C := .inr (.inr (.inr (.inr .done)))

theorem genDone_exit (d : Data) (l : List Cell) :
    (genCtrl d).nxt (genDone d) (((genCtrl d).op (genDone d)).res l) = .inr true := rfl

/-- The round-trip bound of the generator. -/
noncomputable def genBound (d : Data) (n : ℕ) : ℕ :=
  4 + (hcoeffs (d.t + 1)).length * HPar.stepBound (hparT d.t) n +
    (hcoeffs d.q).length * HPar.stepBound (hparQ d.q) n + (8 * d.t.eval n + 21) +
    mainBound d.M (d.t.eval n)

/-! ## The tape after `grow` -/

section Grow

variable (x : List Bool)

theorem grow_length : (Op.eff .grow (x.map liftC)).length = x.length + 1 := by
  simp [eff_grow]

theorem grow_get (c : ℕ) (hc : c < (Op.eff .grow (x.map liftC)).length) :
    (Op.eff .grow (x.map liftC))[c] = if h : c < x.length then liftC x[c] else dflt := by
  simp only [eff_grow] at hc ⊢
  split_ifs with h
  · rw [List.getElem_append_left (by simpa using h), List.getElem_map]
  · rw [List.getElem_append_right (by simpa using h)]
    simp only [List.length_map, List.length_append, List.length_singleton] at hc
    simp only [List.length_map, show c - x.length = 0 by omega, List.getElem_cons_zero]

theorem grow_inp (c : ℕ) (hc : c < (Op.eff .grow (x.map liftC)).length) :
    (Op.eff .grow (x.map liftC))[c].inp = x[c]? := by
  rw [grow_get]
  split_ifs with h
  · rw [List.getElem?_eq_getElem h]; rfl
  · rw [List.getElem?_eq_none (by omega)]; rfl

theorem grow_out (c : ℕ) (hc : c < (Op.eff .grow (x.map liftC)).length) :
    (Op.eff .grow (x.map liftC))[c].out = none := by
  rw [grow_get]; split_ifs <;> rfl

theorem grow_run (k : Mk) : Run (Op.eff .grow (x.map liftC)) k 0 := by
  refine ⟨Nat.zero_le _, fun c hc => ?_⟩
  rw [grow_get]; split_ifs <;> rfl

theorem grow_inpR : InpR (Op.eff .grow (x.map liftC)) x.length := by
  refine ⟨by rw [grow_length]; omega, fun c hc => ?_⟩
  rw [grow_inp]
  by_cases h : c < x.length <;> simp [h]

end Grow

/-! ## The run -/

section Run

variable (d : Data) (x : List Bool)

/-- **The generator writes the Cook–Levin instance.**  When `2|x| + 1 + q(|x|) ≤ t(|x|)`, it
reaches its final state within `genBound d |x|` round trips, and the `out` track then holds
`inst x` (`TI` with output pointer `|inst x|`). -/
theorem gen_run (hT : 2 * x.length + 1 + d.q.eval x.length ≤ d.t.eval x.length) :
    ∃ l' k, RN (genCtrl d).prog ((genCtrl d).start, x.map liftC) (genDone d, l') k ∧
      k ≤ genBound d x.length ∧
      TI (M := d.M) x (d.q.eval x.length) (d.t.eval x.length) (K (d.t.eval x.length) - 1) 0
        (instOf d.M x (d.q.eval x.length) (d.t.eval x.length)).length l' := by
  set n := x.length with hn
  set Q := d.q.eval n with hQ
  set T := d.t.eval n with hTdef
  -- the tail programs
  set R3 := seq labCtrl (mainCtrl d.M) with hR3
  set R2 := seq (hparQ d.q).ctrl R3 with hR2
  set R1 := seq (hparT d.t).ctrl R2 with hR1
  have hG : genCtrl d = seq growC R1 := rfl
  -- 1. grow
  set l1 := Op.eff .grow (x.map liftC) with hl1
  have s1 : RN (genCtrl d).prog (.inl (), x.map liftC) (.inr R1.start, l1) 1 :=
    RN.seq_exit (G₁ := growC) (G₂ := R1) (c := ()) rfl
  have hl1pos : 0 < l1.length := by rw [hl1, grow_length]; omega
  -- 2. Horner phase for `T + 1`
  obtain ⟨l2, k2, h2, run2, inp2, fr2, hk2⟩ := HPar.horner_phase (good_T d.t) n l1 hl1pos
    (grow_inpR x) (grow_run x _) (grow_run x _)
  have hut2 : Run l2 .ut (T + 1) := by
    have := run2
    rwa [show (hparT d.t).cs = hcoeffs (d.t + 1) from rfl, horner_hcoeffs,
      Polynomial.eval_add, Polynomial.eval_one] at this
  have s2 : RN (genCtrl d).prog (.inr R1.start, l1) (.inr (.inl .fin), l2) k2 :=
    RN.seq_right (G₁ := growC) (RN.seq_left (G₂ := R2) h2)
  have s2e : RN (genCtrl d).prog (.inr (.inl .fin), l2) (.inr (.inr R2.start), l2) 1 :=
    RN.seq_right (G₁ := growC) (RN.seq_exit (G₁ := (hparT d.t).ctrl) (G₂ := R2) (c := .fin) rfl)
  -- 3. Horner phase for `Q`
  have hl2pos : 0 < l2.length := lt_of_lt_of_le hl1pos fr2.1
  obtain ⟨l3, k3, h3, run3, inp3, fr3, hk3⟩ := HPar.horner_phase (good_Q d.q) n l2 hl2pos inp2
    ((grow_run x .uq).frS fr2 (chT_uq d.t)) ((grow_run x .sq).frS fr2 (chT_sq d.t))
  have huq3 : Run l3 .uq Q := by
    have := run3
    rwa [show (hparQ d.q).cs = hcoeffs d.q from rfl, horner_hcoeffs] at this
  have s3 : RN (genCtrl d).prog (.inr (.inr R2.start), l2) (.inr (.inr (.inl .fin)), l3) k3 :=
    RN.seq_right (G₁ := growC) (RN.seq_right (G₁ := (hparT d.t).ctrl)
      (RN.seq_left (G₂ := R3) h3))
  have s3e : RN (genCtrl d).prog (.inr (.inr (.inl .fin)), l3) (.inr (.inr (.inr R3.start)), l3)
      1 :=
    RN.seq_right (G₁ := growC) (RN.seq_right (G₁ := (hparT d.t).ctrl)
      (RN.seq_exit (G₁ := (hparQ d.q).ctrl) (G₂ := R3) (c := .fin) rfl))
  -- 4. labels
  have hpl : PL x Q T l3 := by
    have hlen : x.length ≤ l1.length := by rw [hl1, grow_length]; omega
    refine ⟨(hut2.frS fr3 (chQ_ut d.q)), huq3, inp3.1, lt_of_lt_of_le hl2pos fr3.1, ?_, ?_⟩
    · exact inp_frS fr3 (le_trans hlen fr2.1) (inp_frS fr2 hlen (grow_inp x))
    · exact out_frS fr3 (out_frS fr2 (grow_out x))
  obtain ⟨l4, k4, h4, hk4, I4⟩ := label_phase (M := d.M) hT hpl
  have s4 : RN (genCtrl d).prog (.inr (.inr (.inr R3.start)), l3)
      (.inr (.inr (.inr (.inl .f4))), l4) k4 :=
    RN.seq_right (G₁ := growC) (RN.seq_right (G₁ := (hparT d.t).ctrl)
      (RN.seq_right (G₁ := (hparQ d.q).ctrl) (RN.seq_left (G₂ := mainCtrl d.M) h4)))
  have s4e : RN (genCtrl d).prog (.inr (.inr (.inr (.inl .f4))), l4)
      (.inr (.inr (.inr (.inr (mainCtrl d.M).start))), Op.eff (.first .op) l4) 1 :=
    RN.seq_right (G₁ := growC) (RN.seq_right (G₁ := (hparT d.t).ctrl)
      (RN.seq_right (G₁ := (hparQ d.q).ctrl)
        (RN.seq_exit (G₁ := labCtrl) (G₂ := mainCtrl d.M) (c := .f4) (lab_exit l4))))
  -- 5. the main loop
  obtain ⟨l6, k6, h6, hk6, I6⟩ := main_loop I4
  have s6 : RN (genCtrl d).prog (.inr (.inr (.inr (.inr (mainCtrl d.M).start))),
      Op.eff (.first .op) l4) (genDone d, l6) k6 :=
    RN.seq_right (G₁ := growC) (RN.seq_right (G₁ := (hparT d.t).ctrl)
      (RN.seq_right (G₁ := (hparQ d.q).ctrl) (RN.seq_right (G₁ := labCtrl) h6)))
  refine ⟨l6, _, (((((((s1.trans s2).trans s2e).trans s3).trans s3e).trans s4).trans s4e).trans
    s6), ?_, I6⟩
  unfold genBound
  have e2 : (hparT d.t).cs.length = (hcoeffs (d.t + 1)).length := rfl
  have e3 : (hparQ d.q).cs.length = (hcoeffs d.q).length := rfl
  rw [e2] at hk2
  rw [e3] at hk3
  rw [← hTdef]
  omega

end Run

end PVNP.CookLevin.Gen
