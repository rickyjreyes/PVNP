import PVNP.UniformSimApply

/-!
# Milestone 5, part 12: one round of the uniform machine

* `decode_phase`: from the round invariant for `C_t`, the program writes the decoder input
  `1^n 0 cfgCode(C_t)`, runs the decoder to its first halt and stops at `dread`.
* `dread_halt`, `dread_run`: the decoder's first output decides: `some b` halts with answer `b`,
  `none` continues.
* `round_spec`: if the decoder outputs `none` on `C_t`, the round ends at `dprep` with the
  invariant for `C_{t+1} = UWCC.step n C_t`.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

namespace Spec

variable (σ : Spec)

theorem eraseD_stat {a b : Cell σ} (h : σ.eraseD a = σ.eraseD b) :
    a.inp = b.inp ∧ a.fst = b.fst ∧ a.box = b.box ∧ a.mem = b.mem ∧ a.rfst = b.rfst ∧
      a.rul = b.rul ∧ a.cur = b.cur := by
  have h1 := congrArg Cell.inp h
  have h2 := congrArg Cell.fst h
  have h3 := congrArg Cell.box h
  have h4 := congrArg Cell.mem h
  have h5 := congrArg Cell.rfst h
  have h6 := congrArg Cell.rul h
  have h7 := congrArg Cell.cur h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem eraseW_stat {a b : Cell σ} (h : σ.eraseW a = σ.eraseW b) :
    a.inp = b.inp ∧ a.fst = b.fst ∧ a.box = b.box ∧ a.mem = b.mem ∧ a.rfst = b.rfst ∧
      a.rul = b.rul ∧ a.cur = b.cur := by
  have h1 := congrArg Cell.inp h
  have h2 := congrArg Cell.fst h
  have h3 := congrArg Cell.box h
  have h4 := congrArg Cell.mem h
  have h5 := congrArg Cell.rfst h
  have h6 := congrArg Cell.rul h
  have h7 := congrArg Cell.cur h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The decoder input of round `t`. -/
def decInput (x : List Bool) (t : ℕ) : List Bool :=
  List.replicate x.length true ++
    false :: cfgCode σ.W.bits σ.W.d (σ.W.R x.length) (σ.W.Λ x.length) (σ.W.cfg x t)

/-! ### Decoding -/

/-- **Decoding phase.** -/
theorem decode_phase (hC : σ.Correct) (x : List Bool) (t : ℕ) (l : List (Cell σ))
    (hg : σ.Good x t l) :
    ∃ (l3 : List (Cell σ)) (k : ℕ) (cD : σ.MD.Cfg), RN σ.prog (.dprep, l) (.dread, l3) k ∧
      k ≤ (σ.Mx x).length + 2 + hC.pD.eval x.length ∧
      l.length ≤ l3.length ∧ l3.length ≤ l.length + hC.pD.eval x.length ∧
      (∀ (j : ℕ) (hj : j < l3.length), σ.eraseD l3[j] = σ.eraseD (l.getD j σ.dflt)) ∧
      FRep σ.decL.get σ.MD.blank l3 cD.tape cD.head ∧
      σ.MD.Shows cD (decOut (σ.W.dec x.length (σ.W.cfg x t))) := by
  have hroomG := hg.room
  have hboxG := hg.boxIn
  -- dprep
  obtain ⟨hs1, hlen1, hget1⟩ := σ.dprep_trip x l hg.inp
  set l1 : List (Cell σ) := (σ.prog.trip .dprep l).1 with hl1
  -- pack
  set code := cfgCode σ.W.bits σ.W.d (σ.Rx x) (σ.W.Λ x.length) (σ.W.cfg x t) with hcodedef
  have hcodelen : code.length = (σ.Mx x).length * σ.W.w :=
    cfgCode_length σ.W.d (σ.Rx x) (σ.W.Λ x.length) σ.W.bits σ.W.w σ.W.bits_len _
  have hM := mems_sorted σ.W.d (σ.Rx x) (σ.W.Λ x.length)
  have hcode : ∀ (m k : ℕ) (hm : m < (σ.Mx x).length) (hk : k < σ.W.w),
      code[m * σ.W.w + k]? =
        some (σ.bitOf (σ.W.cfg x t (site σ.W.d (σ.Rx x) (σ.Mx x)[m])) ⟨k, hk⟩) := by
    intro m k hm hk
    rw [hcodedef, cfgCode_block σ.W.d (σ.Rx x) (σ.W.Λ x.length) σ.W.bits σ.W.w σ.W.bits_len _ m k
      hm hk, List.getElem?_eq_getElem (by rw [σ.W.bits_len]; exact hk)]
    simp only [bitOf, Option.some.injEq]
    rw [List.getD_eq_getElem _ _ (by rw [σ.W.bits_len]; exact hk)]
  have hst0 : σ.PackSt x.length (σ.Rx x + 1) 0 (σ.Mx x) code l1 l1 := by
    refine ⟨rfl, fun _ _ _ => rfl, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [hget1 j hj (by omega), hg.fst j (by omega)]
      simp only [packCell, packSym, decSym, Nat.zero_mul, add_zero, decide_eq_true_eq]
      congr 1
      by_cases h1 : j < x.length
      · rw [if_pos h1, if_pos h1]
      · by_cases h2 : j = x.length
        · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, if_neg (by omega)]
    · rw [hget1 j hj (by omega)]
      simp
    · rw [hget1 j hj (by omega)]
      simp
  have hbm1 : ∀ (j : ℕ) (hj : j < l1.length),
      (l1[j].box && l1[j].mem) = decide (σ.Rx x + 1 ≤ j ∧ j - (σ.Rx x + 1) ∈ σ.Mx x) := by
    intro j hj
    rw [hget1 j hj (by omega)]
    exact hg.bm σ j (by omega)
  have hcur1 : ∀ (m : ℕ) (hm : m < (σ.Mx x).length) (hj : σ.Rx x + 1 + (σ.Mx x)[m] < l1.length),
      l1[σ.Rx x + 1 + (σ.Mx x)[m]].cur =
        (fun idx => σ.W.cfg x t (site σ.W.d (σ.Rx x) idx)) (σ.Mx x)[m] := by
    intro m hm hj
    have hb : (σ.Mx x)[m] < σ.Bx x := (mems_get_mem σ.W.d (σ.Rx x) (σ.W.Λ x.length) m hm).1
    rw [hget1 _ hj (by omega)]
    simp only
    rw [hg.cur _ (by omega) (by omega) (by omega)]
    congr 2
    omega
  have hroom1 : ∀ (m : ℕ) (hm : m < (σ.Mx x).length), σ.Rx x + 1 + (σ.Mx x)[m] < l1.length := by
    intro m hm
    have hb : (σ.Mx x)[m] < σ.Bx x := (mems_get_mem σ.W.d (σ.Rx x) (σ.W.Λ x.length) m hm).1
    omega
  obtain ⟨l2, hrn2, hfin2⟩ := σ.pack_loop x.length (σ.Rx x + 1) (σ.Mx x) hM
    (fun idx => σ.W.cfg x t (site σ.W.d (σ.Rx x) idx)) code hcode l1 hbm1 hcur1 hroom1
    (σ.Mx x).length 0 (by omega) l1 hst0
  have hlen2 : l2.length = l.length := by rw [hfin2.len, hlen1]
  have hrep2 : FRep σ.decL.get σ.MD.blank l2 (σ.MD.inputTape (σ.decInput x t)) 0 :=
    σ.packFin_frep hfin2 hcodelen (by omega)
  -- the decoder
  obtain ⟨tD, htD, hfD, hsD⟩ := hC.hD x.length (σ.W.cfg x t)
  obtain ⟨l3, hrn3, hrep3, hag3, hlen3⟩ := σ.machine_phase_D (σ.decInput x t) l2 hrep2 hfD
  refine ⟨l3, 1 + ((σ.Mx x).length + 1) + tD, _, ?_, by omega, by have := hag3.1; omega,
    by omega, fun j hj => ?_, hrep3, hsD⟩
  · have h := ((RN.single hs1).trans hrn2).trans hrn3
    simpa using h
  · rw [hag3.2 j hj]
    by_cases hj2 : j < l2.length
    · rw [List.getD_eq_getElem _ _ hj2, List.getD_eq_getElem _ _ (by omega)]
      have hf := hfin2.frame j hj2 (by omega)
      show σ.eraseD l2[j] = _
      rw [hf, hget1 j (by omega) (by omega)]
      rfl
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      rfl

/-! ### Reading the decision -/

/-- Buffer of `dread` after `j` cells. -/
def bufDr (l : List (Cell σ)) (j : ℕ) : Buf σ :=
  {σ.buf0 with dout := if j = 0 then none else some (l.getD 0 σ.dflt).dec.r}

theorem dread_trip (l : List (Cell σ)) (hpos : 0 < l.length)
    (hfst : ∀ (j : ℕ) (hj : j < l.length), l[j].fst = decide (j = 0)) :
    σ.prog.trip .dread l = (l, {σ.buf0 with dout := some l[0].dec.r}) := by
  have hc : ∀ (j : ℕ) (hj : j < l.length), σ.fwd .dread (σ.bufDr l j) l[j] =
      (l[j], σ.bufDr l (j + 1)) := by
    intro j hj
    simp only [fwd, hfst j hj, bufDr, Nat.add_one_ne_zero, if_false]
    by_cases h0 : j = 0
    · subst h0
      simp [List.getElem?_eq_getElem hj]
    · simp [h0]
  obtain ⟨hlen, hget, hbuf⟩ := σ.trip_fwd_get .dread (fun _ _ => rfl) (fun _ => rfl) l
    (σ.bufDr l) (by simp [bufDr, buf0]) (fun j hj => by rw [hc j hj])
  refine Prod.ext ?_ ?_
  · apply List.ext_getElem hlen
    intro j h1 h2
    rw [hget j h2 h1, hc j h2]
  · rw [hbuf]
    simp [bufDr, show l.length ≠ 0 by omega, List.getElem?_eq_getElem hpos]

theorem dread_halt (l : List (Cell σ)) (hpos : 0 < l.length)
    (hfst : ∀ (j : ℕ) (hj : j < l.length), l[j].fst = decide (j = 0)) (b : Bool)
    (h0 : (l[0]'hpos).dec.r = σ.MD.inp b) :
    σ.prog.stepP (.dread, l) = .inr (b, l) := by
  have ht := σ.dread_trip l hpos hfst
  have hn : σ.next .dread (σ.prog.trip .dread l).2 = .inr b := by
    rw [ht]
    simp only [next, h0]
    cases b
    · rw [if_neg (fun h => Bool.false_ne_true (σ.MD.inp_inj h)), if_pos rfl]
    · rw [if_pos rfl]
  have := σ.stepP_inr_of hn
  rwa [ht] at this

theorem dread_run (l : List (Cell σ)) (hpos : 0 < l.length)
    (hfst : ∀ (j : ℕ) (hj : j < l.length), l[j].fst = decide (j = 0))
    (h0 : (l[0]'hpos).dec.r = σ.MD.blank) :
    σ.prog.stepP (.dread, l) = .inl (.wcopy ⟨0, σ.K_pos⟩, l) := by
  have ht := σ.dread_trip l hpos hfst
  have hn : σ.next .dread (σ.prog.trip .dread l).2 = .inl (.wcopy ⟨0, σ.K_pos⟩) := by
    rw [ht]
    simp only [next, h0]
    rw [if_neg (fun h => σ.MD.inp_ne_blank _ h.symm),
      if_neg (fun h => σ.MD.inp_ne_blank _ h.symm)]
  have := σ.stepP_inl_of hn
  rwa [ht] at this

/-! ### One round -/

/-- Round trips of one round of the simulator. -/
def roundCost (hC : σ.Correct) (x : List Bool) : ℕ :=
  (σ.Mx x).length + 2 + hC.pD.eval x.length + 1 +
    σ.K * (2 + σ.W.d * σ.W.r * (2 * side (σ.Rx x) + 1) ^ σ.W.d) + 1

theorem cfg_succ (x : List Bool) (t : ℕ) :
    σ.W.cfg x (t + 1) = σ.W.step x.length (σ.W.cfg x t) := by
  simp only [UWCC.cfg, Function.iterate_succ_apply']

/-- The ruler facts hold after decoding. -/
theorem ruler_after (x : List Bool) (t : ℕ) (l l3 : List (Cell σ)) (hg : σ.Good x t l)
    (hlen : l.length ≤ l3.length)
    (hfr : ∀ (j : ℕ) (hj : j < l3.length), σ.eraseD l3[j] = σ.eraseD (l.getD j σ.dflt)) :
    σ.RulerOK (σ.Rx x + 1) (side (σ.Rx x)) l3 := by
  have hroom := hg.room
  have hbox := hg.boxIn
  have hs := σ.side_le_Bx x
  have eS : side (σ.Rx x) = 2 * σ.Rx x + 1 := rfl
  refine ⟨by omega, by omega, side_pos _, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [(σ.eraseD_stat (hfr j hj)).2.1]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.fst j hjl]
    · rw [List.getD_eq_default _ _ (by omega)]; exact (decide_eq_false (by omega)).symm
  · rw [(σ.eraseD_stat (hfr j hj)).2.2.2.2.1]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.rfst j hjl]
    · rw [List.getD_eq_default _ _ (by omega)]; exact (decide_eq_false (by omega)).symm
  · rw [(σ.eraseD_stat (hfr j hj)).2.2.2.2.2.1]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.rul j hjl]
      exact decide_eq_decide.2 (by omega)
    · rw [List.getD_eq_default _ _ (by omega)]; exact (decide_eq_false (by omega)).symm

/-- **A deciding round**: if the decoder outputs `some b` on `C_t`, the program reaches `dread`
and halts with answer `b`. -/
theorem round_halt (hC : σ.Correct) (x : List Bool) (t : ℕ) (l : List (Cell σ))
    (hg : σ.Good x t l) (b : Bool) (hb : σ.W.dec x.length (σ.W.cfg x t) = some b) :
    ∃ (l3 : List (Cell σ)) (k : ℕ), RN σ.prog (.dprep, l) (.dread, l3) k ∧
      k ≤ (σ.Mx x).length + 2 + hC.pD.eval x.length ∧
      l3.length ≤ l.length + hC.pD.eval x.length ∧ σ.prog.stepP (.dread, l3) = .inr (b, l3) := by
  obtain ⟨l3, k, cD, hrn, hk, hlo, hhi, hfr, hrep, hsh⟩ := σ.decode_phase hC x t l hg
  have hroom := hg.room
  have hpos : 0 < l3.length := by omega
  have hr := σ.ruler_after x t l l3 hg hlo hfr
  have h0 : (l3[0]'hpos).dec.r = σ.MD.inp b := by
    have h := congrArg FCell.r (hrep.cell 0 hpos)
    have e : (l3[0]'hpos).dec.r = cD.tape ((0 : ℕ) : ℤ) := h
    rw [e]
    rw [hb] at hsh
    have := hsh.1 0 (by simp [decOut])
    simpa [decOut] using this
  exact ⟨l3, k, hrn, hk, hhi, σ.dread_halt l3 hpos hr.fst b h0⟩

/-- **One round of the uniform machine.**  If the decoder outputs `none` on `C_t`, the round ends
at `dprep` with the round invariant for `C_{t+1} = UWCC.step n C_t`. -/
theorem round_spec (hC : σ.Correct) (x : List Bool) (t : ℕ) (l : List (Cell σ))
    (hg : σ.Good x t l) (hnone : σ.W.dec x.length (σ.W.cfg x t) = none) :
    ∃ (l' : List (Cell σ)) (k : ℕ), RN σ.prog (.dprep, l) (.dprep, l') k ∧
      k ≤ σ.roundCost hC x ∧ l.length ≤ l'.length ∧
      l'.length ≤ l.length + hC.pD.eval x.length ∧ σ.Good x (t + 1) l' := by
  obtain ⟨l3, k1, cD, hrn1, hk1, hlo, hhi, hfr, hrep, hsh⟩ := σ.decode_phase hC x t l hg
  have hroom := hg.room
  have hboxIn := hg.boxIn
  have hpos : 0 < l3.length := by omega
  have hr := σ.ruler_after x t l l3 hg hlo hfr
  -- the decoder says `run`
  have h0 : (l3[0]'hpos).dec.r = σ.MD.blank := by
    have h := congrArg FCell.r (hrep.cell 0 hpos)
    have e : (l3[0]'hpos).dec.r = cD.tape ((0 : ℕ) : ℤ) := h
    rw [e]
    rw [hnone] at hsh
    simpa [decOut] using hsh.2
  have hs2 := σ.dread_run l3 hpos hr.fst h0
  -- the windows
  obtain ⟨l4, c4, hrn4, hc4, hoff⟩ := σ.offset_loop (σ.Rx x + 1) (side (σ.Rx x)) l3 hr
    (σ.K - 1) 0 σ.K_pos (by have := σ.K_pos; omega) l3
    ⟨rfl, fun _ _ _ => rfl, fun _ _ i' h => absurd h (Nat.not_lt_zero _)⟩
  -- the local rule
  obtain ⟨hs5, hlen5, hget5⟩ := σ.apply_trip l4
  set l5 : List (Cell σ) := (σ.prog.trip .apply l4).1 with hl5
  have hlen4 := hoff.len
  have hlen55 : l5.length = l3.length := by rw [hlen5, hlen4]
  -- static fields of the new list
  have hstat : ∀ (j : ℕ) (hj : j < l5.length),
      l5[j].inp = (l.getD j σ.dflt).inp ∧ l5[j].fst = (l.getD j σ.dflt).fst ∧
      l5[j].box = (l.getD j σ.dflt).box ∧ l5[j].mem = (l.getD j σ.dflt).mem ∧
      l5[j].rfst = (l.getD j σ.dflt).rfst ∧ l5[j].rul = (l.getD j σ.dflt).rul := by
    intro j hj
    have hA := σ.eraseW_stat (hoff.frame j (by omega) (by omega))
    have hD := σ.eraseD_stat (hfr j (by omega))
    rw [hget5 j hj (by omega)]
    exact ⟨hA.1.trans hD.1, hA.2.1.trans hD.2.1, hA.2.2.1.trans hD.2.2.1,
      hA.2.2.2.1.trans hD.2.2.2.1, hA.2.2.2.2.1.trans hD.2.2.2.2.1,
      hA.2.2.2.2.2.1.trans hD.2.2.2.2.2.1⟩
  have eB : σ.Bx x = side (σ.Rx x) ^ σ.W.d := rfl
  have eS : side (σ.Rx x) = 2 * σ.Rx x + 1 := rfl
  have hside := σ.side_le_Bx x
  refine ⟨l5, k1 + 1 + c4 + 1, ?_, ?_, by omega, by omega, ?_⟩
  · exact ((hrn1.trans (RN.single hs2)).trans hrn4).trans (RN.single hs5)
  · simp only [roundCost]
    have : σ.K - 1 + 1 = σ.K := by have := σ.K_pos; omega
    rw [this] at hc4
    omega
  refine ⟨by omega, by omega, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj h1 h2 => ?_⟩
  · rw [(hstat j hj).1]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.inp j hjl]
    · rw [List.getD_eq_default _ _ (by omega), List.getElem?_eq_none (by omega)]; rfl
  · rw [(hstat j hj).2.1]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.fst j hjl]
    · rw [List.getD_eq_default _ _ (by omega)]; exact (decide_eq_false (by omega)).symm
  · rw [(hstat j hj).2.2.1]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.box j hjl]
    · rw [List.getD_eq_default _ _ (by omega)]; exact (decide_eq_false (by omega)).symm
  · rw [(hstat j hj).2.2.2.1]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.mem j hjl]
    · rw [List.getD_eq_default _ _ (by omega),
        decide_eq_false (show ¬ (σ.Rx x + 1 ≤ j ∧ j < σ.Rx x + 1 + σ.Bx x) by omega),
        Bool.false_and]
      rfl
  · rw [(hstat j hj).2.2.2.2.1]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.rfst j hjl]
    · rw [List.getD_eq_default _ _ (by omega)]; exact (decide_eq_false (by omega)).symm
  · rw [(hstat j hj).2.2.2.2.2]
    by_cases hjl : j < l.length
    · rw [List.getD_eq_getElem _ _ hjl, hg.rul j hjl]
    · rw [List.getD_eq_default _ _ (by omega)]; exact (decide_eq_false (by omega)).symm
  · -- the configuration on the box
    have hjl : j < l.length := by omega
    have hA := σ.eraseW_stat (hoff.frame j (by omega) (by omega))
    have hD := σ.eraseD_stat (hfr j (by omega))
    rw [List.getD_eq_getElem _ _ hjl] at hD
    have hbox4 : l4[j].box = true := by
      rw [hA.2.2.1, hD.2.2.1, hg.box j hjl]; exact decide_eq_true ⟨h1, h2⟩
    have hmem4 : l4[j].mem = σ.bmx x j := by
      rw [hA.2.2.2.1, hD.2.2.2.1, hg.mem j hjl, decide_eq_true ⟨h1, h2⟩, Bool.true_and]
    rw [hget5 j hj (by omega)]
    simp only [hbox4, if_true, hmem4]
    rw [cfg_succ]
    simp only [UWCC.step]
    by_cases hmem : site σ.W.d (σ.Rx x) (j - (σ.Rx x + 1)) ∈ σ.W.Λ x.length
    · have hb : σ.bmx x j = true := decide_eq_true hmem
      rw [hb, if_pos rfl, if_pos hmem]
      congr 1
      funext v
      rw [hoff.win_all σ j (by omega) v]
      obtain ⟨idx', hidx', hδ, hsite⟩ := σ.member_nbr x (j - (σ.Rx x + 1)) (by omega) hmem v
      have hcyc : cyc l3.length j (σ.delta (side (σ.Rx x)) v) = σ.Rx x + 1 + idx' := by
        have hc := cyc_of_lt (ℓ := l3.length) (j := j) (s := σ.delta (side (σ.Rx x)) v)
          (by omega) (by omega)
        have : (j : ℤ) + σ.delta (side (σ.Rx x)) v = ((σ.Rx x + 1 + idx' : ℕ) : ℤ) := by
          push_cast at hδ ⊢; omega
        rw [this] at hc
        exact_mod_cast hc
      rw [hcyc, List.getD_eq_getElem _ _ (by omega)]
      have hD' := σ.eraseD_stat (hfr (σ.Rx x + 1 + idx') (by omega))
      rw [hD'.2.2.2.2.2.2, List.getD_eq_getElem _ _ (by omega),
        hg.cur _ (by omega) (by omega) (by omega)]
      rw [show σ.Rx x + 1 + idx' - (σ.Rx x + 1) = idx' by omega, hsite]
    · have hb : σ.bmx x j = false := decide_eq_false hmem
      rw [hb, if_neg (by simp), if_neg hmem]

end Spec

end PVNP.UniformSim
