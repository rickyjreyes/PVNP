import PVNP.UniformSimInit

/-!
# Milestone 5, part 9: the decoder input

* `dprep_trip`: the decoder track receives `1^n 0` with the head on cell `0`.
* `pack_trip`, `pack_loop`: the states of the members, in flattened order, are written `w` bits
  each after `1^n 0`.  The decoder track then holds the decoder input
  `1^n 0 cfgCode(C_t)` (`packSym_eq_inputTape`).
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

namespace Spec

variable (σ : Spec)

/-! ### `dprep` -/

/-- Phase of `dprep` after `j` cells. -/
def phDp (n j : ℕ) : Fin 3 := if j ≤ n then 0 else if j = n + 1 then 1 else 2

/-- Buffer of `dprep` after `j` cells. -/
def bufDp (n j : ℕ) : Buf σ := {σ.buf0 with ph := phDp n j}

/-- The decoder tape after `dprep`: `1^n 0`, blank beyond. -/
def decSym (n j : ℕ) : σ.MD.Γ :=
  if j < n then σ.MD.inp true else if j = n then σ.MD.inp false else σ.MD.blank

theorem dprep_cell (x : List Bool) (j : ℕ) (a : Cell σ) (hinp : a.inp = x[j]?) :
    σ.fwd .dprep (σ.bufDp x.length j) a =
      ({a with
          dec := ⟨σ.decSym x.length j, σ.MD.blank, if a.fst then some true else none, none⟩
          sp := decide (j = x.length + 1)
          pk := false
          lab := none}, σ.bufDp x.length (j + 1)) := by
  rcases Nat.lt_or_ge j x.length with h1 | h1
  · have e1 : phDp x.length j = 0 := by unfold phDp; rw [if_pos (by omega)]
    have e2 : phDp x.length (j + 1) = 0 := by unfold phDp; rw [if_pos (by omega)]
    rw [List.getElem?_eq_getElem h1] at hinp
    simp [fwd, bufDp, e1, e2, hinp, dprepSym, dprepPh, decSym, h1,
      show ¬ j = x.length + 1 by omega]
  have hnone : a.inp = none := by rw [hinp]; exact List.getElem?_eq_none h1
  rcases Nat.lt_or_ge x.length j with h2 | h2
  · rcases Nat.lt_or_ge (x.length + 1) j with h3 | h3
    · have e1 : phDp x.length j = 2 := by unfold phDp; rw [if_neg (by omega), if_neg (by omega)]
      have e2 : phDp x.length (j + 1) = 2 := by
        unfold phDp; rw [if_neg (by omega), if_neg (by omega)]
      simp [fwd, bufDp, e1, e2, hnone, dprepSym, dprepPh, decSym, show ¬ j < x.length by omega,
        show ¬ j = x.length by omega, show ¬ j = x.length + 1 by omega]
    · have hj : j = x.length + 1 := by omega
      subst hj
      have e1 : phDp x.length (x.length + 1) = 1 := by
        unfold phDp; rw [if_neg (by omega), if_pos rfl]
      have e2 : phDp x.length (x.length + 1 + 1) = 2 := by
        unfold phDp; rw [if_neg (by omega), if_neg (by omega)]
      simp [fwd, bufDp, e1, e2, hnone, dprepSym, dprepPh, decSym]
  · have hj : j = x.length := by omega
    subst hj
    have e1 : phDp x.length x.length = 0 := by unfold phDp; rw [if_pos le_rfl]
    have e2 : phDp x.length (x.length + 1) = 1 := by
      unfold phDp; rw [if_neg (by omega), if_pos rfl]
    simp [fwd, bufDp, e1, e2, hnone, dprepSym, dprepPh, decSym]

theorem dprep_trip (x : List Bool) (l : List (Cell σ))
    (hinp : ∀ (j : ℕ) (hj : j < l.length), l[j].inp = x[j]?) :
    σ.prog.stepP (.dprep, l) = .inl (.pack, (σ.prog.trip .dprep l).1) ∧
      (σ.prog.trip .dprep l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip .dprep l).1.length) (hj' : j < l.length),
        (σ.prog.trip .dprep l).1[j] =
          {l[j] with
            dec := ⟨σ.decSym x.length j, σ.MD.blank, if l[j].fst then some true else none, none⟩
            sp := decide (j = x.length + 1)
            pk := false
            lab := none} := by
  have hc := fun (j : ℕ) (hj : j < l.length) => σ.dprep_cell x j l[j] (hinp j hj)
  obtain ⟨hlen, hget, -⟩ := σ.trip_fwd_get .dprep (fun _ _ => rfl) (fun _ => rfl) l
    (σ.bufDp x.length) (by simp [bufDp, phDp, buf0]) (fun j hj => by rw [hc j hj])
  exact ⟨σ.stepP_inl_of rfl, hlen, fun j hj hj' => by rw [hget j hj' hj, hc j hj']⟩

/-! ### `pack` -/

/-- Buffer of pack trip `m` after `j` cells; `s0` is the state of member `m`, `P` the slot. -/
def bufPk (o m P : ℕ) (M : List ℕ) (s0 : σ.W.S) (j : ℕ) : Buf σ :=
  {σ.buf0 with
    f1 := decide (m < M.length ∧ o + M.getD m 0 < j)
    cS := if m < M.length ∧ o + M.getD m 0 < j then some s0 else none
    ph := phW σ.W.w P j
    rc := rcW σ.W.w P j}

theorem bufPk_zero (o m P : ℕ) (M : List ℕ) (s0 : σ.W.S) : σ.bufPk o m P M s0 0 = σ.buf0 := by
  simp only [bufPk, buf0, phW, rcW, Nat.zero_le, if_true, Nat.zero_sub, Nat.zero_min,
    Nat.not_lt_zero, and_false, decide_false, if_false]
  rfl

theorem pack_cell (o m P : ℕ) (M : List ℕ) (hM : M.Pairwise (· < ·)) (s0 : σ.W.S)
    (l : List (Cell σ)) (j : ℕ) (hj : j < l.length)
    (hbm : (l[j].box && l[j].mem) = decide (o ≤ j ∧ j - o ∈ M))
    (hpk : l[j].pk = decide (o ≤ j ∧ j - o ∈ M.take m))
    (hsp : l[j].sp = decide (j = P))
    (hs0 : m < M.length → j = o + M.getD m 0 → l[j].cur = s0) :
    σ.fwd .pack (σ.bufPk o m P M s0 j) l[j] =
      ({l[j] with
          pk := l[j].pk || decide (m < M.length ∧ j = o + M.getD m 0)
          sp := decide (j = P + σ.W.w)
          lab := labW σ.W.w P j},
        σ.bufPk o m P M s0 (j + 1)) := by
  have hc : (l[j].box && l[j].mem && !l[j].pk && !(σ.bufPk o m P M s0 j).f1) =
      decide (m < M.length ∧ j = o + M.getD m 0) := by
    rw [hbm, hpk]
    simp only [bufPk]
    simp only [← decide_not, ← Bool.decide_and]
    exact decide_eq_decide.2 (first_unloaded hM o m j)
  have hw := walk_spec σ.W.w P j
  by_cases hcv : m < M.length ∧ j = o + M.getD m 0
  · have hmark : σ.pkMark (σ.bufPk o m P M s0 j) l[j] =
        ({l[j] with pk := true}, {σ.bufPk o m P M s0 j with f1 := true, cS := some l[j].cur}) := by
      unfold pkMark
      rw [hc, decide_eq_true hcv, if_pos rfl]
    simp only [fwd, hmark]
    simp only [bufPk, hsp] at hw ⊢
    rw [hw, decide_eq_true hcv, Bool.or_true]
    simp only [Prod.mk.injEq, true_and]
    have e : m < M.length ∧ o + M.getD m 0 < j + 1 := ⟨hcv.1, by omega⟩
    rw [decide_eq_true e, if_pos e, hs0 hcv.1 hcv.2]
  · have hmark : σ.pkMark (σ.bufPk o m P M s0 j) l[j] = (l[j], σ.bufPk o m P M s0 j) := by
      unfold pkMark
      rw [hc, decide_eq_false hcv]
      rfl
    simp only [fwd, hmark]
    simp only [bufPk, hsp] at hw ⊢
    rw [hw, decide_eq_false hcv, Bool.or_false]
    have e : (m < M.length ∧ o + M.getD m 0 < j + 1) ↔ (m < M.length ∧ o + M.getD m 0 < j) := by
      omega
    simp only [e]

/-- The decoder-tape symbol written for slot cell `j`. -/
def packDec (m P : ℕ) (M : List ℕ) (s0 : σ.W.S) (j : ℕ) (d : FCell σ.MD.Γ) : FCell σ.MD.Γ :=
  if h : m < M.length ∧ P ≤ j ∧ j < P + σ.W.w then
    ⟨σ.MD.inp (σ.bitOf s0 ⟨j - P, by omega⟩), d.l, d.hd, d.pl⟩
  else d

/-- One `pack` trip: member `m` (if any) is written into slot `[P, P + w)`. -/
theorem pack_trip (o m P : ℕ) (M : List ℕ) (hM : M.Pairwise (· < ·)) (s0 : σ.W.S)
    (l : List (Cell σ))
    (hbm : ∀ (j : ℕ) (hj : j < l.length), (l[j].box && l[j].mem) = decide (o ≤ j ∧ j - o ∈ M))
    (hpk : ∀ (j : ℕ) (hj : j < l.length), l[j].pk = decide (o ≤ j ∧ j - o ∈ M.take m))
    (hsp : ∀ (j : ℕ) (hj : j < l.length), l[j].sp = decide (j = P))
    (hs0 : ∀ (j : ℕ) (hj : j < l.length), m < M.length → j = o + M.getD m 0 → l[j].cur = s0)
    (hroom : m < M.length → o + M.getD m 0 < l.length) :
    σ.prog.stepP (.pack, l) =
        .inl ((if m < M.length then .pack else σ.decEntry), (σ.prog.trip .pack l).1) ∧
      (σ.prog.trip .pack l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip .pack l).1.length) (hj' : j < l.length),
        (σ.prog.trip .pack l).1[j] =
          {l[j] with
            pk := l[j].pk || decide (m < M.length ∧ j = o + M.getD m 0)
            sp := decide (j = P + σ.W.w)
            lab := none
            dec := σ.packDec m P M s0 j l[j].dec} := by
  have hc := fun (j : ℕ) (hj : j < l.length) =>
    σ.pack_cell o m P M hM s0 l j hj (hbm j hj) (hpk j hj) (hsp j hj) (hs0 j hj)
  obtain ⟨hlen, hget, hbuf⟩ := σ.trip_const_bwd .pack (fun _ => rfl)
    (fun b a => by simp only [bwd]; split <;> rfl) l (σ.bufPk o m P M s0)
    (σ.bufPk_zero o m P M s0) (fun j hj => by rw [hc j hj])
  refine ⟨σ.stepP_inl_of ?_, hlen, fun j hj hj' => ?_⟩
  · rw [hbuf]
    by_cases h : m < M.length
    · have e : decide (m < M.length ∧ o + M.getD m 0 < l.length) = true :=
        decide_eq_true ⟨h, hroom h⟩
      simp only [next, bufPk, e, if_pos h, if_true]
    · have e : decide (m < M.length ∧ o + M.getD m 0 < l.length) = false :=
        decide_eq_false (fun h' => h h'.1)
      simp only [next, bufPk, e, if_neg h]
      rfl
  · rw [hget j hj hj', hc j hj']
    have hcS : (σ.bufPk o m P M s0 l.length).cS = if m < M.length then some s0 else none := by
      simp only [bufPk]
      by_cases h : m < M.length
      · rw [if_pos ⟨h, hroom h⟩, if_pos h]
      · rw [if_neg (fun h' => h h'.1), if_neg h]
    simp only [bwd, hcS, packDec, labW]
    by_cases hP : P ≤ j ∧ j < P + σ.W.w
    · rw [dif_pos hP]
      by_cases h : m < M.length
      · rw [if_pos h, dif_pos ⟨h, hP⟩]
      · rw [if_neg h, dif_neg (fun h' => h h'.1)]
    · rw [dif_neg hP, dif_neg (fun h' => hP h'.2)]

/-- Decoder-tape symbol of cell `j` after `m` pack trips. -/
def packSym (n m : ℕ) (code : List Bool) (j : ℕ) : σ.MD.Γ :=
  if j < n then σ.MD.inp true else if j = n then σ.MD.inp false
  else if j < n + 1 + m * σ.W.w then inSym σ.MD code[j - (n + 1)]? else σ.MD.blank

/-- The folded decoder cell after `m` pack trips. -/
def packCell (n m : ℕ) (code : List Bool) (j : ℕ) : FCell σ.MD.Γ :=
  ⟨σ.packSym n m code j, σ.MD.blank, if j = 0 then some true else none, none⟩

/-- Erasure of the fields written by `dprep` and `pack`. -/
def eraseD (c : Cell σ) : Cell σ := {c with dec := σ.dflt.dec, sp := false, pk := false, lab := none}

theorem eraseD_fields {a b : Cell σ} (h : σ.eraseD a = σ.eraseD b) :
    a.box = b.box ∧ a.mem = b.mem ∧ a.cur = b.cur := by
  have h1 := congrArg Cell.box h
  have h2 := congrArg Cell.mem h
  have h3 := congrArg Cell.cur h
  exact ⟨h1, h2, h3⟩

/-- State of the pack loop after `m` members. -/
structure PackSt (n o m : ℕ) (M : List ℕ) (code : List Bool) (lB l : List (Cell σ)) : Prop where
  len : l.length = lB.length
  frame : ∀ (j : ℕ) (hj : j < l.length) (hj' : j < lB.length), σ.eraseD l[j] = σ.eraseD lB[j]
  dec : ∀ (j : ℕ) (hj : j < l.length), l[j].dec = σ.packCell n m code j
  sp : ∀ (j : ℕ) (hj : j < l.length), l[j].sp = decide (j = n + 1 + m * σ.W.w)
  pk : ∀ (j : ℕ) (hj : j < l.length), l[j].pk = decide (o ≤ j ∧ j - o ∈ M.take m)

/-- Result of the pack loop. -/
structure PackFin (n : ℕ) (M : List ℕ) (code : List Bool) (lB l : List (Cell σ)) : Prop where
  len : l.length = lB.length
  frame : ∀ (j : ℕ) (hj : j < l.length) (hj' : j < lB.length), σ.eraseD l[j] = σ.eraseD lB[j]
  dec : ∀ (j : ℕ) (hj : j < l.length), l[j].dec = σ.packCell n M.length code j

/-- **Packing.**  The pack trips write the code blocks of the remaining members and continue with
the decoder. -/
theorem pack_loop (n o : ℕ) (M : List ℕ) (hM : M.Pairwise (· < ·)) (val : ℕ → σ.W.S)
    (code : List Bool) (hcode : ∀ (m k : ℕ) (hm : m < M.length) (hk : k < σ.W.w),
      code[m * σ.W.w + k]? = some (σ.bitOf (val M[m]) ⟨k, hk⟩))
    (lB : List (Cell σ))
    (hbm : ∀ (j : ℕ) (hj : j < lB.length), (lB[j].box && lB[j].mem) = decide (o ≤ j ∧ j - o ∈ M))
    (hcur : ∀ (m : ℕ) (hm : m < M.length) (hj : o + M[m] < lB.length), lB[o + M[m]].cur = val M[m])
    (hroom : ∀ (m : ℕ) (hm : m < M.length), o + M[m] < lB.length) :
    ∀ (k m : ℕ), m + k = M.length → ∀ l : List (Cell σ), σ.PackSt n o m M code lB l →
      ∃ l', RN σ.prog (.pack, l) (σ.decEntry, l') (k + 1) ∧ σ.PackFin n M code lB l' := by
  intro k
  induction k with
  | zero =>
    intro m hmk l hs
    have hmM : m = M.length := by omega
    subst hmM
    obtain ⟨hst, hlen, hget⟩ := σ.pack_trip o M.length (n + 1 + M.length * σ.W.w) M hM σ.W.sbd l
      (fun j hj => by
        have hjB : j < lB.length := by rw [← hs.len]; exact hj
        have h := σ.eraseD_fields (hs.frame j hj hjB)
        rw [h.1, h.2.1]
        exact hbm j hjB)
      hs.pk hs.sp (fun _ _ h => absurd h (lt_irrefl _)) (fun h => absurd h (lt_irrefl _))
    rw [if_neg (lt_irrefl _)] at hst
    refine ⟨_, by simpa using RN.single hst, ⟨by rw [hlen, hs.len], fun j hj hj' => ?_,
      fun j hj => ?_⟩⟩
    · rw [← hs.frame j (by omega) hj', hget j hj (by omega)]
      rfl
    · rw [hget j hj (by omega)]
      simp only [packDec, lt_irrefl, false_and, dif_neg, not_false_eq_true]
      exact hs.dec j (by omega)
  | succ k ih =>
    intro m hmk l hs
    have hmM : m < M.length := by omega
    have hgd : M.getD m 0 = M[m] := List.getD_eq_getElem _ _ hmM
    have hfr : ∀ (j : ℕ) (hj : j < l.length), l[j].cur = (lB[j]'(by rw [← hs.len]; exact hj)).cur ∧
        (l[j].box && l[j].mem) = ((lB[j]'(by rw [← hs.len]; exact hj)).box &&
          (lB[j]'(by rw [← hs.len]; exact hj)).mem) := by
      intro j hj
      have h := σ.eraseD_fields (hs.frame j hj (by rw [← hs.len]; exact hj))
      exact ⟨h.2.2, by rw [h.1, h.2.1]⟩
    obtain ⟨hst, hlen, hget⟩ := σ.pack_trip o m (n + 1 + m * σ.W.w) M hM (val M[m]) l
      (fun j hj => (hfr j hj).2.trans (hbm j (by rw [← hs.len]; exact hj)))
      hs.pk hs.sp
      (fun j hj _ hjm => by
        rw [(hfr j hj).1]
        subst hjm
        simp only [hgd]
        exact hcur m hmM _)
      (fun _ => by rw [hgd, hs.len]; exact hroom m hmM)
    rw [if_pos hmM] at hst
    have hs1 : σ.PackSt n o (m + 1) M code lB (σ.prog.trip .pack l).1 := by
      refine ⟨by rw [hlen, hs.len], fun j hj hj' => ?_, fun j hj => ?_, fun j hj => ?_,
        fun j hj => ?_⟩
      · rw [← hs.frame j (by omega) hj', hget j hj (by omega)]
        rfl
      · rw [hget j hj (by omega), hs.dec j (by omega)]
        simp only [packDec, packCell]
        by_cases hP : n + 1 + m * σ.W.w ≤ j ∧ j < n + 1 + m * σ.W.w + σ.W.w
        · rw [dif_pos ⟨hmM, hP⟩]
          have hk : j - (n + 1 + m * σ.W.w) < σ.W.w := by omega
          have hc := hcode m (j - (n + 1 + m * σ.W.w)) hmM hk
          rw [show m * σ.W.w + (j - (n + 1 + m * σ.W.w)) = j - (n + 1) by omega] at hc
          simp only [packSym, show ¬ j < n by omega, show ¬ j = n by omega, if_false]
          rw [if_pos (show j < n + 1 + (m + 1) * σ.W.w by rw [Nat.succ_mul]; omega), hc]
          rfl
        · rw [dif_neg (fun h => hP h.2)]
          simp only [packSym, Nat.succ_mul]
          split_ifs <;> first | rfl | (exfalso; omega)
      · rw [hget j hj (by omega)]
        exact decide_eq_decide.2 (by rw [Nat.succ_mul]; omega)
      · rw [hget j hj (by omega)]
        simp only [hs.pk j (by omega), hgd, hmM, true_and]
        rw [← Bool.decide_or]
        exact decide_eq_decide.2 (take_succ_mem o m j hmM).symm
    obtain ⟨l', hrn, hfin⟩ := ih (m + 1) (by omega) _ hs1
    exact ⟨l', RN.step hst hrn, hfin⟩

/-- After all members, the decoder track holds the decoder input with the head on cell `0`. -/
theorem packSym_eq_inputTape (n : ℕ) (M : List ℕ) (code : List Bool)
    (hlen : code.length = M.length * σ.W.w) (j : ℕ) :
    σ.packSym n M.length code j = σ.MD.inputTape (List.replicate n true ++ false :: code) j := by
  have hz : (List.replicate n true ++ false :: code).length = n + 1 + code.length := by
    simp; omega
  unfold packSym
  by_cases h1 : j < n
  · rw [if_pos h1, MTM.inputTape_ne_blank _ (by omega) (by rw [hz]; omega)]
    congr 1
    simp only [Int.toNat_natCast]
    rw [List.getD_eq_getElem _ _ (by rw [hz]; omega), List.getElem_append_left (by simpa using h1)]
    simp
  by_cases h2 : j = n
  · subst h2
    rw [if_neg h1, if_pos rfl, MTM.inputTape_ne_blank _ (by omega) (by rw [hz]; omega)]
    congr 1
    simp only [Int.toNat_natCast]
    rw [List.getD_eq_getElem _ _ (by rw [hz]; omega), List.getElem_append_right (by simp)]
    simp
  rw [if_neg h1, if_neg h2]
  by_cases h3 : j < n + 1 + M.length * σ.W.w
  · rw [if_pos h3, MTM.inputTape_ne_blank _ (by omega) (by rw [hz]; omega),
      List.getElem?_eq_getElem (by omega)]
    simp only [Int.toNat_natCast]
    rw [List.getD_eq_getElem _ _ (by rw [hz]; omega), List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate]
    simp [List.getElem_cons, show j - n ≠ 0 by omega, Nat.sub_sub, inSym]
  · rw [if_neg h3, MTM.inputTape_blank _ (Or.inr (by rw [hz]; omega))]

theorem packFin_frep {n : ℕ} {M : List ℕ} {code : List Bool} {lB l : List (Cell σ)}
    (hf : σ.PackFin n M code lB l) (hlen : code.length = M.length * σ.W.w)
    (hroom : n + 2 + M.length * σ.W.w ≤ l.length) :
    FRep σ.decL.get σ.MD.blank l (σ.MD.inputTape (List.replicate n true ++ false :: code)) 0 := by
  have hz : (List.replicate n true ++ false :: code).length = n + 1 + code.length := by
    simp; omega
  refine ⟨fun j hj => ?_, fun i hi => σ.MD.inputTape_blank (by rw [hz]; omega), by omega,
    by omega⟩
  show l[j].dec = _
  rw [hf.dec j hj, packCell, σ.packSym_eq_inputTape n M code hlen j, inputTape_negSide,
    headAt_zero]

end Spec

end PVNP.UniformSim
