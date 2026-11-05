import PVNP.UniformSimLoad

/-!
# Milestone 5, part 8: the round invariant and the pre-round phases

* `Good x t l`: at instruction `dprep`, the list carries the input, the box and member flags, the
  ruler, and the configuration `C_t` of the uniform machine on the box cells.
* `pre_round`: from the input the program reaches `dprep` with `Good x 0`, in a number of round
  trips and with a list length that are linear in `max(n,1) + p_L(n) + p_E(n)`.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

namespace Spec

variable (σ : Spec)

/-- Box radius for the input `x`. -/
abbrev Rx (x : List Bool) : ℕ := σ.W.R x.length

/-- Number of box cells for the input `x`. -/
abbrev Bx (x : List Bool) : ℕ := side (σ.Rx x) ^ σ.W.d

/-- Member indices for the input `x`. -/
abbrev Mx (x : List Bool) : List ℕ := mems σ.W.d (σ.Rx x) (σ.W.Λ x.length)

/-- Membership bit of data cell `j`. -/
def bmx (x : List Bool) (j : ℕ) : Bool :=
  decide (site σ.W.d (σ.Rx x) (j - (σ.Rx x + 1)) ∈ σ.W.Λ x.length)

/-- **Round invariant** at instruction `dprep`, round `t`. -/
structure Good (x : List Bool) (t : ℕ) (l : List (Cell σ)) : Prop where
  room : x.length + 2 + (σ.Mx x).length * σ.W.w ≤ l.length
  boxIn : σ.Rx x + 1 + σ.Bx x ≤ l.length
  inp : ∀ (j : ℕ) (hj : j < l.length), l[j].inp = x[j]?
  fst : ∀ (j : ℕ) (hj : j < l.length), l[j].fst = decide (j = 0)
  box : ∀ (j : ℕ) (hj : j < l.length),
    l[j].box = decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x)
  mem : ∀ (j : ℕ) (hj : j < l.length),
    l[j].mem = (decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) && σ.bmx x j)
  rfst : ∀ (j : ℕ) (hj : j < l.length), l[j].rfst = decide (j = σ.Rx x + 1)
  rul : ∀ (j : ℕ) (hj : j < l.length), l[j].rul = decide (σ.Rx x + 1 ≤ j ∧ j < 3 * σ.Rx x + 2)
  cur : ∀ (j : ℕ) (hj : j < l.length), σ.Rx x + 1 ≤ j → j < σ.Rx x + 1 + σ.Bx x →
    l[j].cur = σ.W.cfg x t (site σ.W.d (σ.Rx x) (j - (σ.Rx x + 1)))

theorem bm_eq (x : List Bool) (j : ℕ) :
    (decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) &&
        (decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) && σ.bmx x j)) =
      decide (σ.Rx x + 1 ≤ j ∧ j - (σ.Rx x + 1) ∈ σ.Mx x) := by
  have eB : σ.Bx x = side (σ.Rx x) ^ σ.W.d := rfl
  rw [← Bool.and_assoc, Bool.and_self]
  simp only [bmx, ← Bool.decide_and]
  refine decide_eq_decide.2 ?_
  rw [mem_mems]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

theorem Good.bm {x : List Bool} {t : ℕ} {l : List (Cell σ)} (hg : σ.Good x t l) (j : ℕ)
    (hj : j < l.length) :
    (l[j].box && l[j].mem) = decide (σ.Rx x + 1 ≤ j ∧ j - (σ.Rx x + 1) ∈ σ.Mx x) := by
  rw [hg.box j hj, hg.mem j hj, σ.bm_eq x j]

/-- The static fields of a cell. -/
def stat (c : Cell σ) : Option Bool × Bool × Bool × Bool × Bool × Bool × FCell σ.ME.Γ :=
  (c.inp, c.fst, c.box, c.mem, c.rfst, c.rul, c.enc)

/-- The static fields after the parse and the ruler. -/
def statAt (x : List Bool) (e : ℕ → FCell σ.ME.Γ) (j : ℕ) :
    Option Bool × Bool × Bool × Bool × Bool × Bool × FCell σ.ME.Γ :=
  (x[j]?, decide (j = 0), decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x),
    decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) && σ.bmx x j, decide (j = σ.Rx x + 1),
    decide (σ.Rx x + 1 ≤ j ∧ j < 3 * σ.Rx x + 2), e j)

theorem one_le_Bx (x : List Bool) : 1 ≤ σ.Bx x := Nat.one_le_pow _ _ (side_pos _)

theorem side_le_Bx (x : List Bool) : side (σ.Rx x) ≤ σ.Bx x := by
  have h := σ.W.d_pos
  calc side (σ.Rx x) = side (σ.Rx x) ^ 1 := (pow_one _).symm
    _ ≤ side (σ.Rx x) ^ σ.W.d := Nat.pow_le_pow_right (side_pos _) h

/-- **The pre-round phases.**  From the input, the program reaches `dprep` with the round
invariant for `C_0`. -/
theorem pre_round (hC : σ.Correct) (x : List Bool) (hg : σ.guard = false ∨ PS.run .tag x = .ok) :
    ∃ (l : List (Cell σ)) (k : ℕ), RN σ.prog (.init, x.map σ.lift) (.dprep, l) k ∧
      σ.Good x 0 l ∧
      k ≤ (σ.W.w + 6) * (max x.length 1 + hC.pL.eval x.length + hC.pE.eval x.length) + 6 ∧
      l.length ≤ (σ.W.w + 3) * (max x.length 1 + hC.pL.eval x.length + hC.pE.eval x.length) := by
  obtain ⟨l2, k2, cL, cE, hrn2, hk2, hrepL, hsL, hrepE, hsE, hbase, hlo2, hhi2⟩ :=
    σ.pre_machines hC x hg
  have eB : σ.Bx x = side (σ.Rx x) ^ σ.W.d := rfl
  have eR : σ.Rx x = σ.W.R x.length := rfl
  have eS : side (σ.Rx x) = 2 * σ.Rx x + 1 := rfl
  have hBd1 := σ.one_le_Bx x
  have hside := σ.side_le_Bx x
  have hy0 := σ.shows_len hrepL hsL
  rw [latCode_length] at hy0
  have hy : σ.Rx x + 1 + σ.Bx x ≤ l2.length := hy0
  clear hy0
  -- the parse
  have hlatr : ∀ (j : ℕ) (hj : j < l2.length), l2[j].lat.r = cL.tape j := fun j hj => by
    have h := congrArg FCell.r (hrepL.cell j hj)
    exact h
  have hlat : ∀ (j : ℕ) (hj : j < l2.length),
      (j < σ.Rx x → l2[j].lat.r = σ.ML.inp true) ∧ (j = σ.Rx x → l2[j].lat.r = σ.ML.inp false) ∧
      (σ.Rx x + 1 ≤ j → j < σ.Rx x + 1 + σ.Bx x → l2[j].lat.r = σ.ML.inp (σ.bmx x j)) ∧
      (j = σ.Rx x + 1 + σ.Bx x → l2[j].lat.r = σ.ML.blank) := by
    intro j hj
    have hc : j ≤ σ.Rx x + 1 + σ.Bx x →
        l2[j].lat.r = inSym σ.ML (latCode σ.W.d (σ.Rx x) (σ.W.Λ x.length))[j]? := fun hjy => by
      rw [hlatr j hj]
      exact shows_cell hsL j (by rw [latCode_length]; exact hjy)
    refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩
    · rw [hc (by omega), latCode_pre _ _ _ j h]; rfl
    · rw [hc (by omega), h, latCode_sep]; rfl
    · rw [hc (by omega)]
      have := latCode_box σ.W.d (σ.Rx x) (σ.W.Λ x.length) (j - (σ.Rx x + 1)) (by omega)
      rw [show σ.Rx x + 1 + (j - (σ.Rx x + 1)) = j by omega] at this
      rw [this]; rfl
    · rw [hc (by omega), List.getElem?_eq_none (by rw [latCode_length]; omega)]; rfl
  obtain ⟨hlen3, hget3⟩ := σ.parse_trip (σ.Rx x) (σ.Bx x) hBd1 (σ.bmx x) l2 hlat
  set l3 : List (Cell σ) := (σ.prog.trip .parse l2).1 with hl3
  have hs3 : σ.prog.stepP (.parse, l2) = .inl (.rulStep, l3) := σ.stepP_inl_of rfl
  -- the ruler
  have hpre3 : ∀ (j : ℕ) (hj : j < l3.length), l3[j].pre = decide (j < σ.Rx x) := fun j hj => by
    rw [hget3 j hj (by omega)]; rfl
  obtain ⟨l4, hrn4, hlen4, hget4⟩ := σ.rul_loop (σ.Rx x) l3 (by omega) hpre3 (σ.Rx x) 0
    (by omega) l3 rfl (fun j hj hj' => by
      have e := hget3 j hj (by omega)
      unfold rulCell
      rw [show decide (j = 0 ∧ 0 < σ.Rx x) = l3[j].pp by rw [e]; rfl,
        show decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 2 + 2 * 0) = l3[j].rul by
          rw [e]; exact decide_eq_decide.2 (by omega)])
  -- making room
  have hbox4 : ∀ (j : ℕ) (hj : j < l4.length),
      l4[j].box = decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) := fun j hj => by
    rw [hget4 j hj (by omega), hget3 j (by omega) (by omega)]; rfl
  obtain ⟨l5, hrn5, hlen5, herase5⟩ := σ.grow_loop (σ.Rx x) (σ.Bx x) l4 (by omega) hbox4
    (σ.Bx x) 0 (by omega) l4
    ⟨by simp, fun j hj => by rw [List.getD_eq_getElem _ _ hj], fun j hj _ => by
      rw [hget4 j hj (by omega), hget3 j (by omega) (by omega)]; simp [parsed]⟩
  -- the static fields
  have hstat4 : ∀ j : ℕ, σ.stat (l4.getD j σ.dflt) =
      σ.statAt x (fun p => (l2.getD p σ.dflt).enc) j := by
    intro j
    by_cases hj : j < l4.length
    · have hj2 : j < l2.length := by omega
      have hb := hbase j hj2
      have hinp : l2[j].inp = x[j]? := by rw [hb]; rfl
      have hfst : l2[j].fst = decide (j = 0) := by rw [hb]; rfl
      rw [List.getD_eq_getElem _ _ hj, hget4 j hj (by omega), hget3 j (by omega) hj2]
      simp only [stat, statAt, parsed, List.getD_eq_getElem _ _ hj2, hinp, hfst]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp only [stat, statAt]
      rw [List.getD_eq_default _ _ (show l2.length ≤ j by omega)]
      have e1 : x[j]? = none := List.getElem?_eq_none (by omega)
      have e2 : decide (j = 0) = false := decide_eq_false (by omega)
      have e3 : decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) = false :=
        decide_eq_false (by omega)
      have e5 : decide (j = σ.Rx x + 1) = false := decide_eq_false (by omega)
      have e6 : decide (σ.Rx x + 1 ≤ j ∧ j < 3 * σ.Rx x + 2) = false := decide_eq_false (by omega)
      rw [e1, e2, e3, e5, e6, Bool.false_and]
      rfl
  have hstat5 : ∀ (j : ℕ) (hj : j < l5.length),
      σ.stat l5[j] = σ.statAt x (fun p => (l2.getD p σ.dflt).enc) j := fun j hj => by
    rw [← hstat4 j]
    have h := congrArg σ.stat (herase5 j hj)
    exact h
  -- load0
  obtain ⟨hs6, hlen6, hget6⟩ := σ.load0_trip l5
  set l6 : List (Cell σ) := (σ.prog.trip .load0 l5).1 with hl6
  have hstat6 : ∀ (j : ℕ) (hj : j < l6.length),
      σ.stat l6[j] = σ.statAt x (fun p => (l2.getD p σ.dflt).enc) j := fun j hj => by
    rw [← hstat5 j (by omega), hget6 j hj (by omega)]
    rfl
  -- loading
  have hM := mems_sorted σ.W.d (σ.Rx x) (σ.W.Λ x.length)
  have hMlen : (σ.Mx x).length ≤ σ.Bx x := mems_length_le σ.W.d (σ.Rx x) (σ.W.Λ x.length)
  have hcode : (cfgCode σ.W.bits σ.W.d (σ.Rx x) (σ.W.Λ x.length) (σ.W.enc x)).length =
      (σ.Mx x).length * σ.W.w :=
    cfgCode_length σ.W.d (σ.Rx x) (σ.W.Λ x.length) σ.W.bits σ.W.w σ.W.bits_len (σ.W.enc x)
  have hcodel : (cfgCode σ.W.bits σ.W.d (σ.Rx x) (σ.W.Λ x.length) (σ.W.enc x)).length ≤
      l2.length := σ.shows_len hrepE hsE
  have hsE' : σ.ME.Shows cE (cfgCode σ.W.bits σ.W.d (σ.Rx x) (σ.W.Λ x.length) (σ.W.enc x)) := hsE
  have hfr6 : ∀ (j : ℕ) (hj : j < l6.length),
      l6[j].box = decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) ∧
        l6[j].mem = (decide (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) && σ.bmx x j) ∧
        l6[j].fst = decide (j = 0) ∧ l6[j].enc = (l2.getD j σ.dflt).enc := by
    intro j hj
    have h := hstat6 j hj
    simp only [stat, statAt, Prod.mk.injEq] at h
    exact ⟨h.2.2.1, h.2.2.2.1, h.2.1, h.2.2.2.2.2.2⟩
  have hval : ∀ (m : ℕ) (hm : m < (σ.Mx x).length),
      σ.decodeBits (fun k : Fin σ.W.w => decide (m * σ.W.w + k < l6.length) &&
        symBit σ.ME (l6.getD (m * σ.W.w + k) σ.dflt).enc.r) =
        σ.W.enc x (site σ.W.d (σ.Rx x) (σ.Mx x)[m]) := by
    intro m hm
    apply σ.decodeBits_bits
    apply List.ext_getElem
    · simp [σ.W.bits_len]
    · intro k h1 h2
      simp only [List.getElem_ofFn]
      have hk : k < σ.W.w := by simpa using h1
      have hmw : m * σ.W.w + k < (σ.Mx x).length * σ.W.w := by
        have : (m + 1) * σ.W.w ≤ (σ.Mx x).length * σ.W.w := Nat.mul_le_mul_right _ hm
        rw [Nat.succ_mul] at this
        omega
      have hp : m * σ.W.w + k < l6.length := by omega
      rw [decide_eq_true hp, Bool.true_and, List.getD_eq_getElem _ _ hp, (hfr6 _ hp).2.2.2,
        List.getD_eq_getElem _ _ (by omega)]
      have hr := congrArg FCell.r (hrepE.cell (m * σ.W.w + k) (by omega))
      simp only [encL] at hr
      rw [hr, shows_cell hsE' _ (by omega),
        cfgCode_block σ.W.d (σ.Rx x) (σ.W.Λ x.length) σ.W.bits σ.W.w σ.W.bits_len (σ.W.enc x) m k
          hm hk, List.getElem?_eq_getElem (by rw [σ.W.bits_len]; exact hk)]
      exact symBit_inp σ.ME _
  have hroom : ∀ (m : ℕ) (hm : m < (σ.Mx x).length), σ.Rx x + 1 + (σ.Mx x)[m] < l6.length := by
    intro m hm
    have : (σ.Mx x)[m] < σ.Bx x := (mems_get_mem σ.W.d (σ.Rx x) (σ.W.Λ x.length) m hm).1
    omega
  have hst0 : σ.LoadSt (σ.Rx x + 1) 0 (σ.Mx x) (fun idx => σ.W.enc x (site σ.W.d (σ.Rx x) idx))
      l6 l6 := by
    refine ⟨rfl, fun _ _ _ => rfl, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
      fun j hj => ?_⟩
    · have e := hget6 j hj (by omega)
      have hf := (hfr6 j hj).2.2.1
      rw [e] at hf ⊢
      simp only at hf ⊢
      rw [hf, Nat.zero_mul]
    · rw [hget6 j hj (by omega)]; simp
    · rw [hget6 j hj (by omega)]
    · rw [hget6 j hj (by omega)]; simp
  obtain ⟨l7, hrn7, hfin⟩ := σ.load_loop (σ.Rx x + 1) (σ.Mx x) hM
    (fun idx => σ.W.enc x (site σ.W.d (σ.Rx x) idx)) l6
    (fun j hj => by rw [(hfr6 j hj).1, (hfr6 j hj).2.1, σ.bm_eq x j]) hroom hval
    (σ.Mx x).length 0 (by omega) l6 hst0
  have hstat7 : ∀ (j : ℕ) (hj : j < l7.length),
      σ.stat l7[j] = σ.statAt x (fun p => (l2.getD p σ.dflt).enc) j := fun j hj => by
    rw [← hstat6 j (by rw [← hfin.len]; exact hj)]
    have h := congrArg σ.stat (hfin.frame j hj (by rw [← hfin.len]; exact hj))
    exact h
  have hlen7 : l7.length = l2.length + σ.Bx x * (σ.W.w + 2) := by
    rw [hfin.len, hlen6, hlen5, hlen4, hlen3]
  -- the invariant
  have hgood : σ.Good x 0 l7 := by
    refine ⟨?_, by omega, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
      fun j hj => ?_, fun j hj => ?_, fun j hj h1 h2 => ?_⟩
    · have : (σ.Mx x).length * σ.W.w ≤ σ.Bx x * σ.W.w := Nat.mul_le_mul_right _ hMlen
      rw [hlen7, Nat.mul_add]
      omega
    all_goals try (have h := hstat7 j hj; simp only [stat, statAt, Prod.mk.injEq] at h)
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2.1
    · rw [hfin.cur j hj]
      have hjm : (σ.Rx x + 1 ≤ j ∧ j - (σ.Rx x + 1) ∈ σ.Mx x) ↔
          site σ.W.d (σ.Rx x) (j - (σ.Rx x + 1)) ∈ σ.W.Λ x.length := by
        rw [mem_mems]; constructor
        · rintro ⟨_, _, h⟩; exact h
        · intro h; exact ⟨h1, by omega, h⟩
      simp only [UWCC.cfg, Function.iterate_zero, id, UWCC.init]
      by_cases hs : site σ.W.d (σ.Rx x) (j - (σ.Rx x + 1)) ∈ σ.W.Λ x.length
      · rw [if_pos (hjm.2 hs), if_pos hs]
      · rw [if_neg (fun h => hs (hjm.1 h)), if_neg hs]
  refine ⟨l7, k2 + 1 + (σ.Rx x + 1) + (σ.Bx x * (σ.W.w + 3) + 1) + 1 + ((σ.Mx x).length + 1),
    ?_, hgood, ?_, ?_⟩
  · have h1 := hrn2.trans (RN.single hs3)
    have h2 := h1.trans hrn4
    have h3 := h2.trans hrn5
    have h4 := h3.trans (RN.single hs6)
    have h5 := h4.trans hrn7
    simpa [Nat.zero_add] using h5
  · have : σ.Bx x * (σ.W.w + 3) ≤
        (max x.length 1 + hC.pL.eval x.length + hC.pE.eval x.length) * (σ.W.w + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have hmax : 1 ≤ max x.length 1 := le_max_right _ _
    nlinarith
  · rw [hlen7]
    have : σ.Bx x * (σ.W.w + 2) ≤
        (max x.length 1 + hC.pL.eval x.length + hC.pE.eval x.length) * (σ.W.w + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

end Spec

end PVNP.UniformSim
