import PVNP.UniformSimPre

/-!
# Milestone 5, part 6: the ruler and the extra room

* `rul_loop`: `R + 1` round trips of `rulStep` turn the single ruler cell into the ruler
  `[R+1, 3R+2)` of `B = 2R+1` cells.
* `grow_loop`: `growA`/`growB` append `B^d·(w+2)` cells.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

/-- Close a goal of `decide`d linear arithmetic. -/
macro "dec_omega" : tactic =>
  `(tactic| (simp only [← Bool.decide_and, ← Bool.decide_or, ← decide_not,
    decide_eq_decide] <;> omega))

namespace Spec

variable (σ : Spec)

/-! ### The ruler -/

/-- Cells during the ruler construction: pointer at `i`, ruler `[R+1, R+2+2i)`. -/
def rulCell (R i j : ℕ) (c : Cell σ) : Cell σ :=
  {c with pp := decide (j = i ∧ 0 < R), rul := decide (R + 1 ≤ j ∧ j < R + 2 + 2 * i)}

/-- Buffer of a ruler step after `j` cells. -/
def bufRS (R i j : ℕ) : Buf σ :=
  {σ.buf0 with
    f1 := decide (0 < j ∧ j - 1 = i ∧ 0 < R)
    f2 := decide (i < j ∧ i < R)
    f3 := decide (R + 2 ≤ j ∧ j ≤ R + 2 + 2 * i)
    ph := if i < R ∧ R + 3 + 2 * i ≤ j then (if j = R + 3 + 2 * i then 1 else 2) else 0}

theorem rul_cell (R i j : ℕ) (hi : i ≤ R) (c : Cell σ) (hpre : c.pre = decide (j < R)) :
    σ.fwd .rulStep (σ.bufRS R i j) (σ.rulCell R i j c) =
      ({c with
          pp := decide (j = i + 1 ∧ 0 < R)
          rul := decide (R + 1 ≤ j ∧ j < R + 2 + 2 * i + (if i < R then 2 else 0))},
        σ.bufRS R i (j + 1)) := by
  rcases Nat.lt_or_ge i R with hiR | hiR
  · rcases Nat.lt_or_ge j i with h1 | h1
    · simp (disch := omega) only [fwd, bufRS, rulCell, hpre, decide_eq_true, decide_eq_false,
        if_pos, if_neg]
      simp
    rcases Nat.lt_or_ge R j with h2 | h2
    · rcases Nat.lt_or_ge j (R + 2 + 2 * i) with h3 | h3
      · simp (disch := omega) only [fwd, bufRS, rulCell, hpre, decide_eq_true, decide_eq_false,
          if_pos, if_neg]
        simp
      rcases Nat.lt_or_ge (R + 2 + 2 * i) j with h4 | h4
      · rcases Nat.lt_or_ge (R + 3 + 2 * i) j with h5 | h5
        · simp (disch := omega) only [fwd, bufRS, rulCell, hpre, decide_eq_true, decide_eq_false,
            if_pos, if_neg]
          simp
        · have hj : j = R + 3 + 2 * i := by omega
          simp (disch := omega) only [fwd, bufRS, rulCell, hpre, decide_eq_true, decide_eq_false,
            if_pos, if_neg]
          simp
      · have hj : j = R + 2 + 2 * i := by omega
        simp (disch := omega) only [fwd, bufRS, rulCell, hpre, decide_eq_true, decide_eq_false,
          if_pos, if_neg]
        simp
    · simp (disch := omega) only [fwd, bufRS, rulCell, hpre, decide_eq_true, decide_eq_false,
        if_pos, if_neg]
      simp
      dec_omega
  · have hiR' : i = R := by omega
    subst hiR'
    simp (disch := omega) only [fwd, bufRS, rulCell, hpre, decide_eq_false, if_pos, if_neg]
    simp
    dec_omega

theorem bufRS_zero (R i : ℕ) : σ.bufRS R i 0 = σ.buf0 := by
  simp [bufRS, buf0]

/-- One ruler trip. -/
theorem rul_trip (R i : ℕ) (hi : i ≤ R) (lP l : List (Cell σ)) (hlen : l.length = lP.length)
    (hR : R < lP.length) (hpre : ∀ (j : ℕ) (hj : j < lP.length), lP[j].pre = decide (j < R))
    (hl : ∀ (j : ℕ) (hj : j < l.length) (hj' : j < lP.length), l[j] = σ.rulCell R i j lP[j]) :
    σ.prog.stepP (.rulStep, l) =
        .inl ((if i < R then .rulStep else .growA), (σ.prog.trip .rulStep l).1) ∧
      (σ.prog.trip .rulStep l).1.length = lP.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip .rulStep l).1.length) (hj' : j < lP.length),
        (σ.prog.trip .rulStep l).1[j] =
          {lP[j] with
            pp := decide (j = i + 1 ∧ 0 < R)
            rul := decide (R + 1 ≤ j ∧ j < R + 2 + 2 * i + (if i < R then 2 else 0))} := by
  have hc : ∀ (j : ℕ) (hj : j < l.length), σ.fwd .rulStep (σ.bufRS R i j) l[j] =
      ({lP[j]'(by omega) with
          pp := decide (j = i + 1 ∧ 0 < R)
          rul := decide (R + 1 ≤ j ∧ j < R + 2 + 2 * i + (if i < R then 2 else 0))},
        σ.bufRS R i (j + 1)) := by
    intro j hj
    rw [hl j hj (by omega)]
    exact σ.rul_cell R i j hi _ (hpre j (by omega))
  obtain ⟨hlen', hget, hbuf⟩ := σ.trip_fwd_get .rulStep (fun _ _ => rfl) (fun _ => rfl) l
    (σ.bufRS R i) (σ.bufRS_zero R i) (fun j hj => by rw [hc j hj])
  refine ⟨σ.stepP_inl_of ?_, by omega, fun j hj hj' => ?_⟩
  · rw [hbuf]
    by_cases h : i < R
    · have e : decide (i < l.length ∧ i < R) = true := decide_eq_true ⟨by omega, h⟩
      simp only [next, bufRS, e, if_pos h, if_true]
    · have e : decide (i < l.length ∧ i < R) = false := decide_eq_false (by omega)
      simp only [next, bufRS, e, if_neg h]
      rfl
  · rw [hget j (by omega) (by omega), hc j (by omega)]

/-- **The ruler.**  From pointer position `i`, `R + 1 − i` trips of `rulStep` produce the ruler
`[R+1, 3R+2)` and continue with `growA`. -/
theorem rul_loop (R : ℕ) (lP : List (Cell σ)) (hR : R < lP.length)
    (hpre : ∀ (j : ℕ) (hj : j < lP.length), lP[j].pre = decide (j < R)) :
    ∀ (k i : ℕ), i + k = R → ∀ l : List (Cell σ), l.length = lP.length →
      (∀ (j : ℕ) (hj : j < l.length) (hj' : j < lP.length), l[j] = σ.rulCell R i j lP[j]) →
      ∃ l', RN σ.prog (.rulStep, l) (.growA, l') (k + 1) ∧ l'.length = lP.length ∧
        ∀ (j : ℕ) (hj : j < l'.length) (hj' : j < lP.length),
          l'[j] = {lP[j] with
            pp := decide (j = R + 1 ∧ 0 < R)
            rul := decide (R + 1 ≤ j ∧ j < 3 * R + 2)} := by
  intro k
  induction k with
  | zero =>
    intro i hik l hlen hl
    have hiR : i = R := by omega
    subst hiR
    obtain ⟨hs, hlen', hget⟩ := σ.rul_trip i i le_rfl lP l hlen hR hpre hl
    rw [if_neg (lt_irrefl i)] at hs
    refine ⟨_, RN.single hs, hlen', fun j hj hj' => ?_⟩
    rw [hget j hj hj']
    have e : decide (i + 1 ≤ j ∧ j < i + 2 + 2 * i + (if i < i then 2 else 0)) =
        decide (i + 1 ≤ j ∧ j < 3 * i + 2) := by
      rw [if_neg (lt_irrefl i)]
      exact decide_eq_decide.2 (by omega)
    rw [e]
  | succ k ih =>
    intro i hik l hlen hl
    have hiR : i < R := by omega
    obtain ⟨hs, hlen', hget⟩ := σ.rul_trip R i hiR.le lP l hlen hR hpre hl
    rw [if_pos hiR] at hs
    obtain ⟨l', hrn, hlen'', hget'⟩ := ih (i + 1) (by omega) _ hlen' (fun j hj hj' => by
      refine (hget j hj hj').trans ?_
      have e : decide (R + 1 ≤ j ∧ j < R + 2 + 2 * i + (if i < R then 2 else 0)) =
          decide (R + 1 ≤ j ∧ j < R + 2 + 2 * (i + 1)) := by
        rw [if_pos hiR]
        exact decide_eq_decide.2 (by omega)
      rw [e]
      rfl)
    exact ⟨l', RN.step hs hrn, hlen'', hget'⟩

/-! ### Making room -/

/-- `growB` trips append default cells. -/
theorem growB_chain (l : List (Cell σ)) :
    ∀ (m k : ℕ) (hk : k < σ.W.w + 2), k + m = σ.W.w + 1 →
      RN σ.prog (.growB ⟨k, hk⟩, l) (.growA, l ++ List.replicate (m + 1) σ.dflt) (m + 1) := by
  intro m
  induction m generalizing l with
  | zero =>
    intro k hk hkm
    have htrip : σ.prog.trip (.growB ⟨k, hk⟩) l = (l ++ [σ.dflt], σ.buf0) := by
      rw [trip_def]
      have hf : fscan (σ.fwd (.growB ⟨k, hk⟩)) σ.buf0 l = (l, σ.buf0) := by
        clear hkm
        induction l with
        | nil => rfl
        | cons a l ih => simp only [fscan, fwd, ih]
      rw [hf]
      have hb : ∀ (b : Buf σ) (l' : List (Cell σ)), bscan (σ.bwd (.growB ⟨k, hk⟩)) b l' = (l', b) := by
        intro b l'
        induction l' generalizing b with
        | nil => rfl
        | cons a l' ih => simp only [bscan, ih, bwd]
      rw [hb]
      rfl
    have hs : σ.prog.stepP (.growB ⟨k, hk⟩, l) = .inl (.growA, l ++ [σ.dflt]) := by
      have := σ.stepP_inl_of (i := .growB ⟨k, hk⟩) (i' := .growA) (l := l) (by
        rw [htrip]
        simp only [next]
        rw [dif_neg (by simp; omega)])
      rwa [htrip] at this
    simpa using RN.single hs
  | succ m ih =>
    intro k hk hkm
    have htrip : σ.prog.trip (.growB ⟨k, hk⟩) l = (l ++ [σ.dflt], σ.buf0) := by
      rw [trip_def]
      have hf : fscan (σ.fwd (.growB ⟨k, hk⟩)) σ.buf0 l = (l, σ.buf0) := by
        clear hkm ih
        induction l with
        | nil => rfl
        | cons a l ih => simp only [fscan, fwd, ih]
      rw [hf]
      have hb : ∀ (b : Buf σ) (l' : List (Cell σ)), bscan (σ.bwd (.growB ⟨k, hk⟩)) b l' = (l', b) := by
        intro b l'
        induction l' generalizing b with
        | nil => rfl
        | cons a l' ih => simp only [bscan, ih, bwd]
      rw [hb]
      rfl
    have hs : σ.prog.stepP (.growB ⟨k, hk⟩, l) = .inl (.growB ⟨k + 1, by omega⟩, l ++ [σ.dflt]) := by
      have := σ.stepP_inl_of (i := .growB ⟨k, hk⟩) (i' := .growB ⟨k + 1, by omega⟩) (l := l) (by
        rw [htrip]
        simp only [next]
        rw [dif_pos (by simp; omega)])
      rwa [htrip] at this
    have := RN.step hs (ih (l ++ [σ.dflt]) (k + 1) (by omega) (by omega))
    rw [List.append_assoc, List.singleton_append, ← List.replicate_succ] at this
    simpa [Nat.add_comm] using this

/-- Buffer of a `growA` trip after `j` cells. -/
def bufG (R Bd i : ℕ) (l : List (Cell σ)) (j : ℕ) : Buf σ :=
  {σ.buf0 with
    f1 := if j = 0 then false else (l.getD (j - 1) σ.dflt).gp
    f2 := decide (R + 1 + i < j ∧ i < Bd)}

/-- State of the room-making loop at iteration `i`. -/
structure GrowSt (R Bd i : ℕ) (lR l : List (Cell σ)) : Prop where
  len : l.length = lR.length + i * (σ.W.w + 2)
  erase : ∀ (j : ℕ) (hj : j < l.length),
    {l[j] with gp := false} = {lR.getD j σ.dflt with gp := false}
  gp : ∀ (j : ℕ) (hj : j < l.length), j < R + 1 + Bd → l[j].gp = decide (j = R + 1 + i)

theorem GrowSt.box {R Bd i : ℕ} {lR l : List (Cell σ)} (hs : σ.GrowSt R Bd i lR l)
    (hlR : R + 1 + Bd ≤ lR.length)
    (hbox : ∀ (j : ℕ) (hj : j < lR.length), lR[j].box = decide (R + 1 ≤ j ∧ j < R + 1 + Bd))
    (j : ℕ) (hj : j < l.length) : l[j].box = decide (R + 1 ≤ j ∧ j < R + 1 + Bd) := by
  have := congrArg Cell.box (hs.erase j hj)
  simp only at this
  rw [this]
  by_cases hjl : j < lR.length
  · rw [List.getD_eq_getElem _ _ hjl, hbox j hjl]
  · rw [List.getD_eq_default _ _ (by omega)]
    exact (decide_eq_false (by omega)).symm

/-- One `growA` trip. -/
theorem growA_trip (R Bd i : ℕ) (hi : i ≤ Bd) (lR l : List (Cell σ)) (hs : σ.GrowSt R Bd i lR l)
    (hlR : R + 1 + Bd ≤ lR.length)
    (hbox : ∀ (j : ℕ) (hj : j < lR.length), lR[j].box = decide (R + 1 ≤ j ∧ j < R + 1 + Bd)) :
    σ.prog.stepP (.growA, l) =
        .inl ((if i < Bd then .growB 0 else .load0), (σ.prog.trip .growA l).1) ∧
      (σ.prog.trip .growA l).1.length = l.length ∧
      (∀ (j : ℕ) (hj : j < (σ.prog.trip .growA l).1.length),
        {(σ.prog.trip .growA l).1[j] with gp := false} = {lR.getD j σ.dflt with gp := false}) ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip .growA l).1.length), j < R + 1 + Bd →
        (σ.prog.trip .growA l).1[j].gp = decide (j = R + 2 + i) := by
  have hlen0 := hs.len
  have hc : ∀ (j : ℕ) (hj : j < l.length), σ.fwd .growA (σ.bufG R Bd i l j) l[j] =
      ({l[j] with gp := (σ.bufG R Bd i l j).f1}, σ.bufG R Bd i l (j + 1)) := by
    intro j hj
    have hb := hs.box σ hlR hbox j hj
    simp only [fwd, bufG, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
      List.getD_eq_getElem _ _ hj, hb]
    congr 2
    by_cases hjB : j < R + 1 + Bd
    · rw [hs.gp j hj hjB]; dec_omega
    · rw [decide_eq_false (show ¬ (R + 1 ≤ j ∧ j < R + 1 + Bd) by omega), Bool.and_false,
        Bool.or_false]
      dec_omega
  obtain ⟨hlen', hget, hbuf⟩ := σ.trip_fwd_get .growA (fun _ _ => rfl) (fun _ => rfl) l
    (σ.bufG R Bd i l) (by simp [bufG, buf0]) (fun j hj => by rw [hc j hj])
  refine ⟨σ.stepP_inl_of ?_, hlen', fun j hj => ?_, fun j hj hjB => ?_⟩
  · rw [hbuf]
    by_cases h : i < Bd
    · have e : decide (R + 1 + i < l.length ∧ i < Bd) = true := decide_eq_true ⟨by omega, h⟩
      simp only [next, bufG, e, if_pos h, if_true]
    · have e : decide (R + 1 + i < l.length ∧ i < Bd) = false := decide_eq_false (by omega)
      simp only [next, bufG, e, if_neg h]
      rfl
  · rw [hget j (by omega) hj, hc j (by omega)]
    exact hs.erase j (by omega)
  · rw [hget j (by omega) hj, hc j (by omega)]
    simp only [bufG]
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp; omega
    · rw [if_neg (by omega), List.getD_eq_getElem _ _ (by omega), hs.gp (j - 1) (by omega)
        (by omega)]
      exact decide_eq_decide.2 (by omega)

/-- **Making room.**  From iteration `i`, the `growA`/`growB` loop appends `(Bd − i)·(w+2)`
default cells and continues with `load0`. -/
theorem grow_loop (R Bd : ℕ) (lR : List (Cell σ)) (hlR : R + 1 + Bd ≤ lR.length)
    (hbox : ∀ (j : ℕ) (hj : j < lR.length), lR[j].box = decide (R + 1 ≤ j ∧ j < R + 1 + Bd)) :
    ∀ (k i : ℕ), i + k = Bd → ∀ l : List (Cell σ), σ.GrowSt R Bd i lR l →
      ∃ l', RN σ.prog (.growA, l) (.load0, l') (k * (σ.W.w + 3) + 1) ∧
        l'.length = lR.length + Bd * (σ.W.w + 2) ∧
        ∀ (j : ℕ) (hj : j < l'.length),
          {l'[j] with gp := false} = {lR.getD j σ.dflt with gp := false} := by
  intro k
  induction k with
  | zero =>
    intro i hik l hs
    have hiB : i = Bd := by omega
    subst hiB
    obtain ⟨hst, hlen', herase, -⟩ := σ.growA_trip R i i le_rfl lR l hs hlR hbox
    rw [if_neg (lt_irrefl i)] at hst
    exact ⟨_, by simpa using RN.single hst, by rw [hlen', hs.len], herase⟩
  | succ k ih =>
    intro i hik l hs
    have hiB : i < Bd := by omega
    obtain ⟨hst, hlen', herase, hgp⟩ := σ.growA_trip R Bd i hiB.le lR l hs hlR hbox
    rw [if_pos hiB] at hst
    set l1 : List (Cell σ) := (σ.prog.trip .growA l).1 with hl1
    have hch := σ.growB_chain l1 (σ.W.w + 1) 0 (by omega) (by omega)
    have e0 : (⟨0, by omega⟩ : Fin (σ.W.w + 2)) = 0 := Fin.ext (by simp)
    rw [e0] at hch
    have hlen0 := hs.len
    have hs2 : σ.GrowSt R Bd (i + 1) lR (l1 ++ List.replicate (σ.W.w + 1 + 1) σ.dflt) := by
      refine ⟨by simp [hlen', hlen0]; ring, fun j hj => ?_, fun j hj hjB => ?_⟩
      · by_cases hj1 : j < l1.length
        · rw [List.getElem_append_left hj1]; exact herase j hj1
        · rw [List.getElem_append_right (by omega)]
          simp only [List.getElem_replicate]
          rw [List.getD_eq_default _ _ (by omega)]
      · rw [List.getElem_append_left (by omega)]
        exact (hgp j (by omega) hjB).trans (decide_eq_decide.2 (by omega))
    obtain ⟨l', hrn, hlen'', herase'⟩ := ih (i + 1) (by omega) _ hs2
    refine ⟨l', ?_, hlen'', herase'⟩
    have := (RN.single hst).trans (hch.trans hrn)
    convert this using 1
    ring

end Spec

end PVNP.UniformSim
