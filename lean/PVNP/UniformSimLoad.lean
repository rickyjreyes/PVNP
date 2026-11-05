import PVNP.UniformSimGrow

/-!
# Milestone 5, part 7: slot walks and loading the initial configuration

* `walk_spec`: the slot walk labels the `w` cells after its pointer and moves the pointer by `w`.
* `first_unloaded`: in a strictly increasing member list, the first member outside the first `m`
  is the one of rank `m`.
* `load_trip`, `load_loop`: one `load` trip decodes code block `m` into member `m`; the loop loads
  every member.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

/-! ### Strictly increasing member lists -/

section Sorted

variable {M : List ℕ} (hM : M.Pairwise (· < ·))

include hM in
theorem sorted_getElem_le {i j : ℕ} (hi : i < M.length) (hj : j < M.length) (h : i ≤ j) :
    M[i] ≤ M[j] := by
  rcases Nat.lt_or_ge i j with h' | h'
  · exact le_of_lt (List.pairwise_iff_getElem.1 hM i j hi hj h')
  · have : i = j := by omega
    subst this
    exact le_rfl

include hM in
/-- The first member outside the first `m` is the one of rank `m`. -/
theorem first_unloaded (o m j : ℕ) :
    (((o ≤ j ∧ j - o ∈ M) ∧ ¬ (o ≤ j ∧ j - o ∈ M.take m)) ∧
        ¬ (m < M.length ∧ o + M.getD m 0 < j)) ↔
      (m < M.length ∧ j = o + M.getD m 0) := by
  have hnd : M.Nodup := hM.nodup
  constructor
  · rintro ⟨⟨⟨hoj, hjM⟩, hnt⟩, hnf⟩
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 hjM
    have him : m ≤ i := by
      by_contra h
      exact hnt ⟨hoj, List.mem_take_iff_getElem.2 ⟨i, by omega, hiv⟩⟩
    have hmM : m < M.length := by omega
    have hle := sorted_getElem_le hM hmM hi him
    rw [List.getD_eq_getElem _ _ hmM] at hnf ⊢
    refine ⟨hmM, ?_⟩
    have : ¬ (o + M[m] < j) := fun h => hnf ⟨hmM, h⟩
    omega
  · rintro ⟨hmM, hj⟩
    rw [List.getD_eq_getElem _ _ hmM] at hj ⊢
    have hjo : j - o = M[m] := by omega
    refine ⟨⟨⟨by omega, hjo ▸ List.getElem_mem hmM⟩, ?_⟩, by omega⟩
    rintro ⟨_, ht⟩
    rw [hjo] at ht
    obtain ⟨i, hi, hiv⟩ := List.mem_take_iff_getElem.1 ht
    have := (hnd.getElem_inj_iff (hi := by omega) (hj := hmM)).1 hiv
    omega

omit hM in
theorem take_succ_mem (o m j : ℕ) (hm : m < M.length) :
    (o ≤ j ∧ j - o ∈ M.take (m + 1)) ↔ ((o ≤ j ∧ j - o ∈ M.take m) ∨ j = o + M[m]) := by
  rw [List.take_succ, List.getElem?_eq_getElem hm]
  simp only [Option.toList_some, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hoj, h | h⟩
    · exact Or.inl ⟨hoj, h⟩
    · right; omega
  · rintro (⟨hoj, h⟩ | h)
    · exact ⟨hoj, Or.inl h⟩
    · exact ⟨by omega, Or.inr (by omega)⟩

end Sorted

namespace Spec

/-! ### Slot walks -/

/-- Phase of a slot walk with pointer at `P` after `j` cells. -/
def phW (w P j : ℕ) : Fin 3 := if j ≤ P then 0 else if j ≤ P + w then 1 else 2

/-- Counter of a slot walk. -/
def rcW (w P j : ℕ) : Fin (w + 1) := ⟨min (j - P) w, by omega⟩

/-- Label of cell `j` in a slot walk. -/
def labW (w P j : ℕ) : Option (Fin w) :=
  if h : P ≤ j ∧ j < P + w then some ⟨j - P, by omega⟩ else none

theorem walk_spec (w P j : ℕ) :
    walk w (phW w P j) (rcW w P j) (decide (j = P)) =
      (phW w P (j + 1), rcW w P (j + 1), decide (j = P + w), labW w P j) := by
  rcases Nat.lt_or_ge j P with h1 | h1
  · have e1 : phW w P j = 0 := by unfold phW; rw [if_pos (by omega)]
    have e2 : phW w P (j + 1) = 0 := by unfold phW; rw [if_pos (by omega)]
    have e3 : labW w P j = none := by unfold labW; rw [dif_neg (by omega)]
    rw [e1, e2, e3]
    simp only [walk, decide_eq_false (show ¬ j = P by omega),
      decide_eq_false (show ¬ j = P + w by omega), Bool.false_eq_true, if_false]
    simp only [rcW, Prod.mk.injEq, Fin.mk.injEq, true_and, and_true]
    omega
  rcases Nat.lt_or_ge P j with h2 | h2
  · rcases Nat.lt_or_ge j (P + w) with h3 | h3
    · have e1 : phW w P j = 1 := by unfold phW; rw [if_neg (by omega), if_pos (by omega)]
      have e2 : phW w P (j + 1) = 1 := by unfold phW; rw [if_neg (by omega), if_pos (by omega)]
      have e3 : labW w P j = some ⟨j - P, by omega⟩ := by unfold labW; rw [dif_pos (by omega)]
      rw [e1, e2, e3]
      have hr : (rcW w P j).val < w := by simp only [rcW]; omega
      simp only [walk, dif_pos hr, decide_eq_false (show ¬ j = P by omega),
        decide_eq_false (show ¬ j = P + w by omega)]
      simp only [rcW, Prod.mk.injEq, Fin.mk.injEq, Option.some.injEq, true_and]
      omega
    · have e2 : phW w P (j + 1) = 2 := by unfold phW; rw [if_neg (by omega), if_neg (by omega)]
      have e3 : labW w P j = none := by unfold labW; rw [dif_neg (by omega)]
      rw [e2, e3]
      rcases Nat.lt_or_ge (P + w) j with h4 | h4
      · have e1 : phW w P j = 2 := by unfold phW; rw [if_neg (by omega), if_neg (by omega)]
        rw [e1]
        simp only [walk, decide_eq_false (show ¬ j = P by omega),
          decide_eq_false (show ¬ j = P + w by omega)]
        simp only [rcW, Prod.mk.injEq, Fin.mk.injEq, true_and, and_true]
        omega
      · have e1 : phW w P j = 1 := by unfold phW; rw [if_neg (by omega), if_pos (by omega)]
        have hr : ¬ (rcW w P j).val < w := by simp only [rcW]; omega
        rw [e1]
        simp only [walk, dif_neg hr, decide_eq_true (show j = P + w by omega)]
        simp only [rcW, Prod.mk.injEq, Fin.mk.injEq, true_and, and_true]
        omega
  · have hj : j = P := by omega
    subst hj
    have e1 : phW w j j = 0 := by unfold phW; rw [if_pos le_rfl]
    rw [e1]
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      have e2 : phW 0 j (j + 1) = 2 := by unfold phW; rw [if_neg (by omega), if_neg (by omega)]
      have e3 : labW 0 j j = none := by unfold labW; rw [dif_neg (by omega)]
      rw [e2, e3]
      simp only [walk, decide_true, if_true, lt_irrefl, add_zero]
      rw [dif_neg (fun h => h)]
      simp only [rcW, Prod.mk.injEq, Fin.mk.injEq, true_and, and_true]
      omega
    · have e2 : phW w j (j + 1) = 1 := by unfold phW; rw [if_neg (by omega), if_pos (by omega)]
      have e3 : labW w j j = some ⟨0, hw⟩ := by
        unfold labW; rw [dif_pos (by omega)]; simp
      rw [e2, e3]
      simp only [walk, decide_true, if_true, dif_pos hw,
        decide_eq_false (show ¬ j = j + w by omega)]
      simp only [rcW, Prod.mk.injEq, Fin.mk.injEq, true_and, and_true]
      omega

theorem readBit_step (w P j : ℕ) (g : ℕ → Bool) :
    readBit (labW w P j) (fun k : Fin w => decide (P + k < j) && g (P + k)) (g j) =
      fun k : Fin w => decide (P + k < j + 1) && g (P + k) := by
  funext k
  unfold labW
  by_cases h : P ≤ j ∧ j < P + w
  · rw [dif_pos h]
    simp only [readBit]
    by_cases hk : k = ⟨j - P, by omega⟩
    · subst hk
      simp only [Function.update_self]
      rw [show P + (j - P) = j by omega, decide_eq_true (by omega : j < j + 1)]
      simp
    · rw [Function.update_of_ne hk]
      have : (k : ℕ) ≠ j - P := fun h' => hk (Fin.ext h')
      rw [show decide (P + k < j + 1) = decide (P + k < j) from decide_eq_decide.2 (by omega)]
  · rw [dif_neg h]
    simp only [readBit]
    rw [show decide (P + k < j + 1) = decide (P + k < j) from decide_eq_decide.2 (by omega)]

variable (σ : Spec)

/-! ### Trips whose backward pass keeps the buffer -/

theorem trip_const_bwd (i : Ins σ) (he : ∀ b, σ.ext i b = none) (hb : ∀ b a, (σ.bwd i b a).2 = b)
    (l : List (Cell σ)) (bufAt : ℕ → Buf σ) (h0 : bufAt 0 = σ.buf0)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (σ.fwd i (bufAt j) l[j]).2 = bufAt (j + 1)) :
    (σ.prog.trip i l).1.length = l.length ∧
      (∀ (j : ℕ) (hj : j < (σ.prog.trip i l).1.length) (hj' : j < l.length),
        (σ.prog.trip i l).1[j] = (σ.bwd i (bufAt l.length) (σ.fwd i (bufAt j) l[j]).1).1) ∧
      (σ.prog.trip i l).2 = bufAt l.length := by
  have hfb : (fscan (σ.fwd i) σ.buf0 l).2 = bufAt l.length := by
    rw [← h0]; exact fscan_spec_buf _ l bufAt hstep
  have hT : σ.prog.trip i l =
      bscan (σ.bwd i) (bufAt l.length) (fscan (σ.fwd i) σ.buf0 l).1 := by
    rw [trip_def, he, Option.toList_none, List.append_nil, hfb]
  have hlen : (fscan (σ.fwd i) σ.buf0 l).1.length = l.length := fscan_length _ _ _
  have hst' : ∀ (j : ℕ) (hj : j < (fscan (σ.fwd i) σ.buf0 l).1.length),
      (σ.bwd i ((fun _ => bufAt l.length) (j + 1)) (fscan (σ.fwd i) σ.buf0 l).1[j]).2 =
        (fun _ => bufAt l.length) j := fun j _ => hb _ _
  refine ⟨by rw [hT, bscan_length, hlen], fun j hj hj' => ?_, ?_⟩
  · have e := bscan_spec_get (σ.bwd i) (fscan (σ.fwd i) σ.buf0 l).1 (fun _ => bufAt l.length) hst' j
      (by omega)
    simp only at e
    refine (List.getElem_of_eq (congrArg Prod.fst hT) _).trans (e.trans ?_)
    congr 2
    simpa [h0] using fscan_spec_get _ l bufAt hstep j hj'
  · have e := bscan_spec_buf (σ.bwd i) (fscan (σ.fwd i) σ.buf0 l).1 (fun _ => bufAt l.length) hst'
    simp only at e
    rw [hT]
    exact e

/-! ### Loading -/

/-- Buffer of load trip `m` after `j` cells. -/
def bufLd (o m : ℕ) (M : List ℕ) (l : List (Cell σ)) (j : ℕ) : Buf σ :=
  {σ.buf0 with
    f1 := decide (m < M.length ∧ o + M.getD m 0 < j)
    ph := phW σ.W.w (m * σ.W.w) j
    rc := rcW σ.W.w (m * σ.W.w) j
    bits := fun k => decide (m * σ.W.w + k < j) &&
      symBit σ.ME (l.getD (m * σ.W.w + k) σ.dflt).enc.r}

theorem bufLd_zero (o m : ℕ) (M : List ℕ) (l : List (Cell σ)) : σ.bufLd o m M l 0 = σ.buf0 := by
  simp only [bufLd, buf0, phW, rcW, Nat.zero_le, if_true, Nat.zero_sub, Nat.zero_min,
    Nat.not_lt_zero, and_false, decide_false, Bool.false_and]
  rfl

theorem load_cell (o m : ℕ) (M : List ℕ) (hM : M.Pairwise (· < ·)) (l : List (Cell σ)) (j : ℕ)
    (hj : j < l.length)
    (hbm : (l[j].box && l[j].mem) = decide (o ≤ j ∧ j - o ∈ M))
    (hld : l[j].ld = decide (o ≤ j ∧ j - o ∈ M.take m))
    (hrp : l[j].rp = decide (j = m * σ.W.w)) :
    σ.fwd .load (σ.bufLd o m M l j) l[j] =
      ({l[j] with
          tgt := l[j].tgt || decide (m < M.length ∧ j = o + M.getD m 0)
          rp := decide (j = m * σ.W.w + σ.W.w)},
        σ.bufLd o m M l (j + 1)) := by
  have hc : (l[j].box && l[j].mem && !l[j].ld && !(σ.bufLd o m M l j).f1) =
      decide (m < M.length ∧ j = o + M.getD m 0) := by
    rw [hbm, hld]
    simp only [bufLd]
    simp only [← decide_not, ← Bool.decide_and]
    exact decide_eq_decide.2 (first_unloaded hM o m j)
  have hw := walk_spec σ.W.w (m * σ.W.w) j
  have hg := readBit_step σ.W.w (m * σ.W.w) j (fun i => symBit σ.ME (l.getD i σ.dflt).enc.r)
  simp only [List.getD_eq_getElem _ _ hj] at hg
  by_cases hcv : m < M.length ∧ j = o + M.getD m 0
  · have hmark : σ.ldMark (σ.bufLd o m M l j) l[j] =
        ({l[j] with tgt := true}, {σ.bufLd o m M l j with f1 := true}) := by
      unfold ldMark
      rw [hc, decide_eq_true hcv, if_pos rfl]
    simp only [fwd, hmark]
    simp only [bufLd, hrp] at hw hg ⊢
    rw [hw, hg, decide_eq_true hcv, Bool.or_true]
    simp only [Prod.mk.injEq, true_and]
    congr 1
    exact (decide_eq_true ⟨hcv.1, by omega⟩).symm
  · have hmark : σ.ldMark (σ.bufLd o m M l j) l[j] = (l[j], σ.bufLd o m M l j) := by
      unfold ldMark
      rw [hc, decide_eq_false hcv]
      rfl
    simp only [fwd, hmark]
    simp only [bufLd, hrp] at hw hg ⊢
    rw [hw, hg, decide_eq_false hcv, Bool.or_false]
    simp only [Prod.mk.injEq]
    refine ⟨trivial, ?_⟩
    congr 1
    exact decide_eq_decide.2 (by omega)

/-- One `load` trip: member `m` (if any) receives the decoded block `m`. -/
theorem load_trip (o m : ℕ) (M : List ℕ) (hM : M.Pairwise (· < ·)) (l : List (Cell σ))
    (hbm : ∀ (j : ℕ) (hj : j < l.length), (l[j].box && l[j].mem) = decide (o ≤ j ∧ j - o ∈ M))
    (hld : ∀ (j : ℕ) (hj : j < l.length), l[j].ld = decide (o ≤ j ∧ j - o ∈ M.take m))
    (hrp : ∀ (j : ℕ) (hj : j < l.length), l[j].rp = decide (j = m * σ.W.w))
    (htgt : ∀ (j : ℕ) (hj : j < l.length), l[j].tgt = false)
    (hroom : m < M.length → o + M.getD m 0 < l.length) :
    σ.prog.stepP (.load, l) =
        .inl ((if m < M.length then .load else .dprep), (σ.prog.trip .load l).1) ∧
      (σ.prog.trip .load l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip .load l).1.length) (hj' : j < l.length),
        (σ.prog.trip .load l).1[j] =
          {l[j] with
            tgt := false
            rp := decide (j = m * σ.W.w + σ.W.w)
            ld := l[j].ld || decide (m < M.length ∧ j = o + M.getD m 0)
            cur := if m < M.length ∧ j = o + M.getD m 0 then
              σ.decodeBits (σ.bufLd o m M l l.length).bits else l[j].cur} := by
  have hc := fun (j : ℕ) (hj : j < l.length) =>
    σ.load_cell o m M hM l j hj (hbm j hj) (hld j hj) (hrp j hj)
  obtain ⟨hlen, hget, hbuf⟩ := σ.trip_const_bwd .load (fun _ => rfl)
    (fun b a => by simp only [bwd]; split <;> rfl) l (σ.bufLd o m M l) (σ.bufLd_zero o m M l)
    (fun j hj => by rw [hc j hj])
  refine ⟨σ.stepP_inl_of ?_, hlen, fun j hj hj' => ?_⟩
  · rw [hbuf]
    by_cases h : m < M.length
    · have e : decide (m < M.length ∧ o + M.getD m 0 < l.length) = true :=
        decide_eq_true ⟨h, hroom h⟩
      simp only [next, bufLd, e, if_pos h, if_true]
    · have e : decide (m < M.length ∧ o + M.getD m 0 < l.length) = false :=
        decide_eq_false (fun h' => h h'.1)
      simp only [next, bufLd, e, if_neg h]
      rfl
  · rw [hget j hj hj', hc j hj']
    simp only [bwd, htgt j hj', Bool.false_or]
    by_cases hcv : m < M.length ∧ j = o + M.getD m 0
    · rw [decide_eq_true hcv, if_pos rfl, if_pos hcv, Bool.or_true]
    · rw [decide_eq_false hcv, if_neg (by simp), if_neg hcv, Bool.or_false]

theorem load0_trip (l : List (Cell σ)) :
    σ.prog.stepP (.load0, l) = .inl (.load, (σ.prog.trip .load0 l).1) ∧
      (σ.prog.trip .load0 l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip .load0 l).1.length) (hj' : j < l.length),
        (σ.prog.trip .load0 l).1[j] =
          {l[j] with cur := σ.W.sbd, ld := false, tgt := false, rp := l[j].fst} := by
  obtain ⟨hlen, hget, -⟩ := σ.trip_fwd_get .load0 (fun _ _ => rfl) (fun _ => rfl) l
    (fun _ => σ.buf0) rfl (fun _ _ => rfl)
  exact ⟨σ.stepP_inl_of rfl, hlen, fun j hj hj' => hget j hj' hj⟩

/-- State of the load loop after `m` members. -/
structure LoadSt (o m : ℕ) (M : List ℕ) (val : ℕ → σ.W.S) (lA l : List (Cell σ)) : Prop where
  len : l.length = lA.length
  frame : ∀ (j : ℕ) (hj : j < l.length) (hj' : j < lA.length),
    {l[j] with cur := σ.W.sbd, ld := false, tgt := false, rp := false} =
      {lA[j] with cur := σ.W.sbd, ld := false, tgt := false, rp := false}
  rp : ∀ (j : ℕ) (hj : j < l.length), l[j].rp = decide (j = m * σ.W.w)
  ld : ∀ (j : ℕ) (hj : j < l.length), l[j].ld = decide (o ≤ j ∧ j - o ∈ M.take m)
  tgt : ∀ (j : ℕ) (hj : j < l.length), l[j].tgt = false
  cur : ∀ (j : ℕ) (hj : j < l.length),
    l[j].cur = if o ≤ j ∧ j - o ∈ M.take m then val (j - o) else σ.W.sbd

/-- Result of the load loop. -/
structure LoadFin (o : ℕ) (M : List ℕ) (val : ℕ → σ.W.S) (lA l : List (Cell σ)) : Prop where
  len : l.length = lA.length
  frame : ∀ (j : ℕ) (hj : j < l.length) (hj' : j < lA.length),
    {l[j] with cur := σ.W.sbd, ld := false, tgt := false, rp := false} =
      {lA[j] with cur := σ.W.sbd, ld := false, tgt := false, rp := false}
  cur : ∀ (j : ℕ) (hj : j < l.length),
    l[j].cur = if o ≤ j ∧ j - o ∈ M then val (j - o) else σ.W.sbd

theorem LoadSt.enc_getD {o m : ℕ} {M : List ℕ} {val : ℕ → σ.W.S} {lA l : List (Cell σ)}
    (hs : σ.LoadSt o m M val lA l) (p : ℕ) : (l.getD p σ.dflt).enc = (lA.getD p σ.dflt).enc := by
  by_cases hp : p < l.length
  · rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ (by rw [← hs.len]; exact hp)]
    have h := congrArg Cell.enc (hs.frame p hp (by rw [← hs.len]; exact hp))
    exact h
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by rw [← hs.len]; omega)]

theorem LoadSt.bm {o m : ℕ} {M : List ℕ} {val : ℕ → σ.W.S} {lA l : List (Cell σ)}
    (hs : σ.LoadSt o m M val lA l) (j : ℕ) (hj : j < l.length) (hj' : j < lA.length) :
    (l[j].box && l[j].mem) = (lA[j].box && lA[j].mem) := by
  have h := hs.frame j hj hj'
  rw [congrArg Cell.box h, congrArg Cell.mem h]

/-- **Loading.**  From member `m`, the load trips decode every remaining block into its member,
and continue with `dprep`. -/
theorem load_loop (o : ℕ) (M : List ℕ) (hM : M.Pairwise (· < ·)) (val : ℕ → σ.W.S)
    (lA : List (Cell σ))
    (hbm : ∀ (j : ℕ) (hj : j < lA.length), (lA[j].box && lA[j].mem) = decide (o ≤ j ∧ j - o ∈ M))
    (hroom : ∀ (m : ℕ) (hm : m < M.length), o + M[m] < lA.length)
    (hval : ∀ (m : ℕ) (hm : m < M.length),
      σ.decodeBits (fun k : Fin σ.W.w => decide (m * σ.W.w + k < lA.length) &&
        symBit σ.ME (lA.getD (m * σ.W.w + k) σ.dflt).enc.r) = val M[m]) :
    ∀ (k m : ℕ), m + k = M.length → ∀ l : List (Cell σ), σ.LoadSt o m M val lA l →
      ∃ l', RN σ.prog (.load, l) (.dprep, l') (k + 1) ∧ σ.LoadFin o M val lA l' := by
  intro k
  induction k with
  | zero =>
    intro m hmk l hs
    have hmM : m = M.length := by omega
    subst hmM
    obtain ⟨hst, hlen, hget⟩ := σ.load_trip o M.length M hM l
      (fun j hj => (hs.bm σ j hj (by rw [← hs.len]; exact hj)).trans
        (hbm j (by rw [← hs.len]; exact hj)))
      hs.ld hs.rp hs.tgt (fun h => absurd h (lt_irrefl _))
    rw [if_neg (lt_irrefl _)] at hst
    refine ⟨_, by simpa using RN.single hst, ⟨by rw [hlen, hs.len], fun j hj hj' => ?_,
      fun j hj => ?_⟩⟩
    · rw [hget j hj (by omega)]
      exact hs.frame j (by omega) hj'
    · rw [hget j hj (by omega)]
      simp only [lt_irrefl, false_and, if_false]
      rw [hs.cur j (by omega), List.take_length]
  | succ k ih =>
    intro m hmk l hs
    have hmM : m < M.length := by omega
    have hgd : M.getD m 0 = M[m] := List.getD_eq_getElem _ _ hmM
    obtain ⟨hst, hlen, hget⟩ := σ.load_trip o m M hM l
      (fun j hj => (hs.bm σ j hj (by rw [← hs.len]; exact hj)).trans
        (hbm j (by rw [← hs.len]; exact hj)))
      hs.ld hs.rp hs.tgt (fun _ => by rw [hgd, hs.len]; exact hroom m hmM)
    rw [if_pos hmM] at hst
    have hbits : (σ.bufLd o m M l l.length).bits = fun k : Fin σ.W.w =>
        decide (m * σ.W.w + k < lA.length) &&
          symBit σ.ME (lA.getD (m * σ.W.w + k) σ.dflt).enc.r := by
      funext k
      simp only [bufLd, hs.len, hs.enc_getD σ]
    have hs1 : σ.LoadSt o (m + 1) M val lA (σ.prog.trip .load l).1 := by
      refine ⟨by rw [hlen, hs.len], fun j hj hj' => ?_, fun j hj => ?_, fun j hj => ?_,
        fun j hj => ?_, fun j hj => ?_⟩
      · rw [hget j hj (by omega)]
        exact hs.frame j (by omega) hj'
      · rw [hget j hj (by omega)]
        exact decide_eq_decide.2 (by rw [Nat.succ_mul])
      · rw [hget j hj (by omega)]
        simp only [hs.ld j (by omega), hgd, hmM, true_and]
        rw [← Bool.decide_or]
        exact decide_eq_decide.2 (take_succ_mem o m j hmM).symm
      · rw [hget j hj (by omega)]
      · rw [hget j hj (by omega)]
        simp only [hgd]
        by_cases hcv : j = o + M[m]
        · rw [if_pos ⟨hmM, hcv⟩, if_pos ((take_succ_mem o m j hmM).2 (Or.inr hcv)), hbits,
            hval m hmM, show j - o = M[m] by omega]
        · rw [if_neg (fun h => hcv h.2), hs.cur j (by omega)]
          have := take_succ_mem (M := M) o m j hmM
          by_cases h1 : o ≤ j ∧ j - o ∈ M.take m
          · rw [if_pos h1, if_pos (this.2 (Or.inl h1))]
          · rw [if_neg h1, if_neg (fun h => (this.1 h).elim h1 hcv)]
    obtain ⟨l', hrn, hfin⟩ := ih (m + 1) (by omega) _ hs1
    exact ⟨l', RN.step hst hrn, hfin⟩

end Spec

end PVNP.UniformSim
