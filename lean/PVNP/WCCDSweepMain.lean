import PVNP.WCCDSweepBuild

/-!
# D-1: the WCCD sweep program decides what the WCCD decides, in polynomial time

* `arrAns_eq`: at `chk`, the tape's answer is exactly the WCCD output at time `t`
  (acceptance precedence, blank exterior included).
* `restart`, `enter`, `init_phase`: horizon restarts and the input-encoding phase.
* `halts_of_first`: if the WCCD's first answer is `b` at time `s`, the sweep program
  halts with answer `b` within an explicit cost.
* `toTM_decides`, `P_WCCD_subset_P_TM`, `P_WCCD_eq_P_TM`, `NP_WCCD_eq_NP_TM`.
-/

namespace PVNP.Discrete.WCCDSweep

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.Discrete.WCCD

variable {d : ℕ} (A : WCCD d)

/-! ### Output -/

/-- **The tape answer is the WCCD answer.** -/
theorem arrAns_eq (x : List Bool) (G t : ℕ) (l : L A) (hI : Inv A x G t l) :
    arrAns A l = A.out x t := by
  have hN : base x G ^ (d + 1) ≤ l.length := by rw [hI.len]; omega
  haveI : NeZero l.length := ⟨by rw [hI.len]; omega⟩
  have key : ∀ P : A.S → Bool,
      ((P A.blank || decide (∃ i, ∃ h : i < l.length, P l[i].cur = true)) = true) ↔
        ∃ p, P (A.run (A.init x) t p) = true := by
    intro P
    rw [← A.cyclic_out x G l.length hN t hI.ht P, Bool.or_eq_true, decide_eq_true_iff]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨(i : ZMod l.length), by rw [← hI.cur i hi]; exact h⟩
    · rintro (h | ⟨z, hz⟩)
      · exact Or.inl h
      · refine Or.inr ⟨z.val, ZMod.val_lt z, ?_⟩
        rw [hI.cur _ _, ZMod.natCast_zmod_val]
        exact hz
  unfold arrAns WCCD.out WCCD.outCfg
  congr 1
  · apply Bool.eq_iff_iff.2
    rw [key A.acc]
    simp only [decide_eq_true_eq]
  · apply Bool.eq_iff_iff.2
    rw [key A.rej]
    simp only [decide_eq_true_eq]

theorem Inv.gN {x : List Bool} {G t : ℕ} {l : L A} (hI : Inv A x G t l) : G + 1 < l.length := by
  have := hI.len_gt; have := base_ge x G; omega

/-- **Halting at `chk`** with the WCCD answer. -/
theorem halt_chk (x : List Bool) (G t : ℕ) (l : L A) (hI : Inv A x G t l) (b : Bool)
    (hb : A.out x t = some b) : (prog A).Halts (.chk, l) b (2 * l.length + 2) := by
  obtain ⟨hs, hc⟩ := step_chk A l G t (hI.gN A) hI.ht hI.gm hI.rp
  rw [arrAns_eq A x G t l hI, hb] at hs
  have h : (prog A).Halts (.chk, l) b ((prog A).tripCost .chk l) := Prog.Halts.last hs
  rwa [hc] at h

/-! ### Restart with the next horizon -/

theorem Inv.getD {x : List Bool} {G t : ℕ} {l : L A} (hI : Inv A x G t l) (i : ℕ) :
    (l.getD i (dflt A)).inp = x[i]? ∧ (l.getD i (dflt A)).fst = decide (i = 0) ∧
      (l.getD i (dflt A)).ptr = decide (i = 0) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact ⟨hI.inp i hi, hI.fst i hi, hI.ptr i hi⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    have := hI.len_gt
    have := len_lt_base x G
    exact ⟨(List.getElem?_eq_none (by omega)).symm, (decide_eq_false (by omega)).symm,
      (decide_eq_false (by omega)).symm⟩

theorem base_succ (x : List Bool) (G : ℕ) : base x (G + 1) = base x G + 2 := by unfold base; omega

theorem pow_add_two (M d : ℕ) (hM : 1 ≤ M) : M ^ (d + 1) + 2 ≤ (M + 2) ^ (d + 1) := by
  have h1 : M ^ d ≤ (M + 2) ^ d := Nat.pow_le_pow_left (by omega) d
  have h2 : 1 ≤ M ^ d := Nat.one_le_pow _ _ (by omega)
  have e1 : M ^ (d + 1) = M * M ^ d := by ring
  have e2 : (M + 2) ^ (d + 1) = (M + 2) * (M + 2) ^ d := by ring
  rw [e1, e2]
  nlinarith

def gmUp (G j : ℕ) (a : Cell A.S d) : Cell A.S d := {a with gm := decide (j ≤ G + 1)}
def cntUp (M j : ℕ) (a : Cell A.S d) : Cell A.S d := {a with cnt := decide (j < M + 1)}

/-- Set the `gm` and `cnt` tracks of a cell. -/
def setGC (g c : Bool) (a : Cell A.S d) : Cell A.S d := {a with gm := g, cnt := c}

/-- **Restart**: from `chk` at round `G` of horizon `G` (no answer yet), the
program widens `gm` and `cnt`, resets `rp`, and reaches `r0` for horizon `G+1`. -/
theorem restart (x : List Bool) (G : ℕ) (l : L A) (hI : Inv A x G G l) (hans : arrAns A l = none) :
    ∃ (l' : L A) (c : ℕ), (prog A).Reach (.chk, l) (.r0, l') c ∧ c ≤ 5 * (2 * l.length + 4) ∧
      Pre A x (G + 1) l' := by
  have hMN : base x G < l.length := hI.len_gt
  have hGN : G + 1 < l.length := hI.gN A
  have hM3 := base_ge x G
  -- chk
  have hs0 : (prog A).stepP (.chk, l) = .inl (.ggm, l) := by
    rw [(step_chk A l G G hGN le_rfl hI.gm hI.rp).1, hans]
    simp
  have hc0 := (step_chk A l G G hGN le_rfl hI.gm hI.rp).2
  -- ggm
  obtain ⟨hs1, hc1⟩ := step_ggm A l G hGN hI.gm
  have hs1' : (prog A).stepP (.ggm, l) = .inl (.gcnt 0, l.mapIdx (gmUp A G)) := hs1
  obtain ⟨l1, hl1⟩ : ∃ l1, l1 = l.mapIdx (gmUp A G) := ⟨_, rfl⟩
  rw [← hl1] at hs1'
  have hl1len : l1.length = l.length := by simp [hl1]
  have hl1get : ∀ i (h : i < l1.length), l1[i] = gmUp A G i (l[i]'(by rw [hl1len] at h; exact h)) := by
    intro i h; simp [hl1]
  have hcnt1 : ∀ j (h : j < l1.length), l1[j].cnt = decide (j < base x G) := by
    intro j h; rw [hl1get j h]; exact hI.cnt j _
  -- gcnt 0
  obtain ⟨hs2, hc2⟩ := step_gcnt A 0 l1 (base x G) (by rw [hl1len]; omega) hcnt1
  have hs2' : (prog A).stepP (.gcnt 0, l1) = .inl (.gcnt 1, l1.mapIdx (cntUp A (base x G))) := by
    rw [hs2, if_neg (show base x G ≠ l1.length by rw [hl1len]; omega), List.append_nil]
    rfl
  rw [if_neg (show base x G ≠ l1.length by rw [hl1len]; omega)] at hc2
  obtain ⟨l2, hl2⟩ : ∃ l2, l2 = l1.mapIdx (cntUp A (base x G)) := ⟨_, rfl⟩
  rw [← hl2] at hs2'
  have hl2len : l2.length = l.length := by simp [hl2, hl1len]
  have hl2get : ∀ i (h : i < l2.length), l2[i] =
      setGC A (decide (i ≤ G + 1)) (decide (i < base x G + 1)) (l[i]'(by rw [hl2len] at h; exact h)) := by
    intro i h
    simp only [hl2, List.getElem_mapIdx]
    rw [hl1get i (by rw [hl1len]; rw [hl2len] at h; exact h)]
    rfl
  have hcnt2 : ∀ j (h : j < l2.length), l2[j].cnt = decide (j < base x G + 1) := by
    intro j h; rw [hl2get j h]; rfl
  -- gcnt 1
  obtain ⟨hs3, hc3⟩ := step_gcnt A 1 l2 (base x G + 1) (by rw [hl2len]; omega) hcnt2
  have hs3' : (prog A).stepP (.gcnt 1, l2) = .inl (.grst, l2.mapIdx (cntUp A (base x G + 1)) ++
      (if base x G + 1 = l2.length then [{dflt A with cnt := true}] else [])) := by
    rw [hs3]
    rfl
  obtain ⟨l3, hl3⟩ : ∃ l3, l3 = l2.mapIdx (cntUp A (base x G + 1)) ++
      (if base x G + 1 = l2.length then [{dflt A with cnt := true}] else []) := ⟨_, rfl⟩
  rw [← hl3] at hs3'
  have hl3len : l3.length = l.length + (if base x G + 1 = l.length then 1 else 0) := by
    rw [hl3, List.length_append, List.length_mapIdx, hl2len]
    split_ifs <;> simp
  have hl3get : ∀ i (h : i < l3.length), l3[i] =
      setGC A (decide (i ≤ G + 1)) (decide (i < base x G + 2)) (l.getD i (dflt A)) := by
    intro i h
    by_cases hi : i < l.length
    · have h2 : i < (l2.mapIdx (cntUp A (base x G + 1))).length := by simp [hl2len]; exact hi
      have e : l3[i] = (l2.mapIdx (cntUp A (base x G + 1)))[i] := by
        simp only [hl3]
        rw [List.getElem_append_left h2]
      rw [e, List.getElem_mapIdx, hl2get i (by rw [hl2len]; exact hi), List.getD_eq_getElem _ _ hi]
      rfl
    · have hlen := hl3len
      have hd : base x G + 1 = l.length := by
        by_contra hc
        rw [if_neg hc] at hlen
        omega
      have hiN : i = l.length := by rw [hl3len, if_pos hd] at h; omega
      subst hiN
      have e : l3[l.length] = {dflt A with cnt := true} := by
        have hd2 : base x G + 1 = l2.length := by rw [hl2len]; exact hd
        have hl3' : l3 = l2.mapIdx (cntUp A (base x G + 1)) ++ [{dflt A with cnt := true}] := by
          rw [hl3, if_pos hd2]
        subst hl3'
        rw [List.getElem_append_right (by simp [hl2len])]
        simp [hl2len]
      rw [e, List.getD_eq_default _ _ (le_refl _)]
      have h1 : decide (l.length ≤ G + 1) = false := decide_eq_false (by omega)
      have h2 : decide (l.length < base x G + 2) = true := decide_eq_true (by omega)
      rw [h1, h2]
      rfl
  -- grst
  obtain ⟨hs4, hc4⟩ := step_grst A l3
  refine ⟨l3.map (gGrst A), _, Prog.Reach.step hs0 (Prog.Reach.step hs1' (Prog.Reach.step hs2'
    (Prog.Reach.step hs3' (Prog.Reach.single (prog A) hs4)))), ?_, ?_⟩
  · show (prog A).tripCost .chk l + ((prog A).tripCost .ggm l + ((prog A).tripCost (.gcnt 0) l1 +
      ((prog A).tripCost (.gcnt 1) l2 + (prog A).tripCost .grst l3))) ≤ 5 * (2 * l.length + 4)
    rw [hc0, hc1, hc2, hc3, hc4, hl3len, hl2len, hl1len]
    split_ifs <;> omega
  · have hg := hI.getD A
    have hbase := base_succ x G
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map, hl3len, hbase]
      split_ifs with hd
      · omega
      · omega
    · rw [List.length_map, hl3len, hbase, hI.len]
      have := pow_add_two (base x G) d (by omega)
      split_ifs <;> omega
    · intro i h
      simp only [List.getElem_map, gGrst]
      rw [hl3get i (by simpa using h)]
      exact (hg i).1
    · intro i h
      simp only [List.getElem_map, gGrst]
      rw [hl3get i (by simpa using h)]
      exact (hg i).2.1
    · intro i h
      simp only [List.getElem_map, gGrst]
      rw [hl3get i (by simpa using h), hbase]
      rfl
    · intro i h
      simp only [List.getElem_map, gGrst]
      rw [hl3get i (by simpa using h)]
      rfl
    · intro i h
      simp only [List.getElem_map, gGrst]
      rw [hl3get i (by simpa using h)]
      exact (hg i).2.1
    · intro i h
      simp only [List.getElem_map, gGrst]
      rw [hl3get i (by simpa using h)]
      exact (hg i).2.2

/-! ### Entering a horizon: references, `xfin` -/

theorem cost_enter {D X U L c1 : ℕ} (hc1 : c1 ≤ D * ((X + 1) * (2 * U + 3))) (hL : L ≤ U) (hD : 1 ≤ D) :
    2 * L + 2 + (c1 + (2 * U + 2)) ≤ D * ((X + 3) * (2 * U + 4)) := by
  have e : D * ((X + 3) * (2 * U + 4)) = D * ((X + 1) * (2 * U + 3)) + D * (X + 4 * U + 9) := by ring
  have h2 : X + 4 * U + 9 ≤ D * (X + 4 * U + 9) := Nat.le_mul_of_pos_left _ hD
  omega

/-- **Entering horizon `G`**: `r0`, the reference construction and `xfin`. -/
theorem enter (x : List Bool) (G : ℕ) (l : L A) (hP : Pre A x G l) :
    ∃ (l' : L A) (c : ℕ), (prog A).Reach (.r0, l) (.chk, l') c ∧
      c ≤ (d + 1) * ((base x G * (2 * base x G ^ d + 3) + 3) * (2 * (base x G ^ (d + 1) + 1) + 4)) ∧
      Inv A x G 0 l' := by
  obtain ⟨hs0, hc0⟩ := step_r0 A l hP.fst
  have hB0 := r0_inv A x G l hP
  obtain ⟨l1, c1, hR1, hc1, hB1⟩ := build_axes A x G (d + 1) 0 (by omega) (gR0 A l) hB0
  rw [buildIns_zero] at hR1
  obtain ⟨hs2, hc2⟩ := step_xfin A l1
  have hlen1 : l1.length = base x G ^ (d + 1) + 1 := by have := hB1.lenK; have := hB1.lenHi; omega
  refine ⟨l1.map (gXfin A), _, Prog.Reach.step hs0 (Prog.Reach.trans (prog A) hR1
    (Prog.Reach.single (prog A) hs2)), ?_, xfin_inv A x G l1 hB1⟩
  show (prog A).tripCost .r0 l + (c1 + (prog A).tripCost .xfin l1) ≤ _
  rw [hc0, hc2, hlen1]
  exact cost_enter hc1 hP.lenHi (by omega)

/-! ### Input encoding -/

/-- The cell `i` after the input phase. -/
def initCell (x : List Bool) (i : ℕ) : Cell A.S d :=
  {dflt A with inp := x[i]?, cnt := true, fst := decide (i = 0)}

theorem iext_cells (x : List Bool) (l : L A) (hx : x.length ≤ l.length)
    (hl : ∀ i (h : i < l.length), l[i] = initCell A x i) :
    ∀ i (h : i < (l ++ [extCell A (decide (l.length = 0))]).length),
      (l ++ [extCell A (decide (l.length = 0))])[i] = initCell A x i := by
  intro i h
  by_cases hi : i < l.length
  · rw [List.getElem_append_left hi]; exact hl i hi
  · have hiL : i = l.length := by simp at h; omega
    subst hiL
    rw [List.getElem_append_right (le_refl _)]
    simp only [Nat.sub_self, List.getElem_cons_zero, extCell, initCell]
    rw [List.getElem?_eq_none hx]
    rfl

theorem iext_step (x : List Bool) (r : Fin 3) (l : L A) (hx : x.length ≤ l.length)
    (hl : ∀ i (h : i < l.length), l[i] = initCell A x i) :
    ∃ l' : L A, (prog A).stepP (.iext r, l) = .inl (iextNext r, l') ∧
      (prog A).tripCost (.iext r) l = 2 * l.length + 3 ∧ l'.length = l.length + 1 ∧
      ∀ i (h : i < l'.length), l'[i] = initCell A x i := by
  obtain ⟨hs, hc⟩ := step_iext A r l
  exact ⟨_, hs, hc, by simp, iext_cells A x l hx hl⟩

/-- **Input phase**: `i0`, three `iext` and `igm` reach `r0` with `Pre` at horizon `0`. -/
theorem init_phase (x : List Bool) :
    ∃ (l : L A) (c : ℕ), (prog A).Reach (.i0, x.map (liftB A)) (.r0, l) c ∧
      c ≤ 10 * x.length + 25 ∧ Pre A x 0 l := by
  obtain ⟨hs0, hc0⟩ := step_i0 A (x.map (liftB A))
  have hl0len : (gI0 A (x.map (liftB A))).length = x.length := by simp [gI0_length]
  have hl0 : ∀ i (h : i < (gI0 A (x.map (liftB A))).length),
      (gI0 A (x.map (liftB A)))[i] = initCell A x i := by
    intro i h
    have hi : i < x.length := by rw [hl0len] at h; exact h
    simp only [gI0, List.getElem_mapIdx, List.getElem_map, setI0, liftB, initCell,
      List.getElem?_eq_getElem hi]
  obtain ⟨l1, hs1, hc1, hl1len, hl1⟩ := iext_step A x 0 _ (by rw [hl0len]) hl0
  obtain ⟨l2, hs2, hc2, hl2len, hl2⟩ := iext_step A x 1 l1 (by omega) hl1
  obtain ⟨l3, hs3, hc3, hl3len, hl3⟩ := iext_step A x 2 l2 (by omega) hl2
  have e1 : iextNext (d := d) 0 = .iext 1 := rfl
  have e2 : iextNext (d := d) 1 = .iext 2 := rfl
  have e3 : iextNext (d := d) 2 = .igm := rfl
  rw [e1] at hs1
  rw [e2] at hs2
  rw [e3] at hs3
  obtain ⟨hs4, hc4⟩ := step_igm A l3
  refine ⟨l3.map (gIgm A), _, Prog.Reach.step hs0 (Prog.Reach.step hs1 (Prog.Reach.step hs2
    (Prog.Reach.step hs3 (Prog.Reach.single (prog A) hs4)))), ?_, ?_⟩
  · show (prog A).tripCost .i0 _ + ((prog A).tripCost (.iext 0) _ + ((prog A).tripCost (.iext 1) l1 +
      ((prog A).tripCost (.iext 2) l2 + (prog A).tripCost .igm l3))) ≤ _
    rw [hc0, hc1, hc2, hc3, hc4, hl3len, hl2len, hl1len, hl0len]
    simp
    omega
  · have hlen : (l3.map (gIgm A)).length = x.length + 3 := by simp [hl3len, hl2len, hl1len, hl0len]
    have hbase : base x 0 = x.length + 3 := by unfold base; omega
    have hget : ∀ i (h : i < (l3.map (gIgm A)).length), (l3.map (gIgm A))[i] =
        gIgm A (initCell A x i) := by
      intro i h
      rw [List.getElem_map, hl3 i (by simpa using h)]
    refine ⟨by rw [hlen, hbase], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlen, hbase]
      have := pow_ge (x.length + 3) (by omega) d
      omega
    · intro i h; rw [hget i h]; rfl
    · intro i h; rw [hget i h]; rfl
    · intro i h; rw [hget i h]
      exact (decide_eq_true (by rw [hbase]; rw [hlen] at h; exact h)).symm
    · intro i h; rw [hget i h]
      exact decide_iff_eq (by omega)
    · intro i h; rw [hget i h]; rfl
    · intro i h; rw [hget i h]; rfl

/-! ### Cost bounds at the final horizon -/

/-- Cost bound for one round (also bounds a restart and the final `chk`) at horizon `s`. -/
def Rb (e : ℕ) (x : List Bool) (s : ℕ) : ℕ :=
  (e + 5) * ((4 * base x s ^ e + 4) * (2 * (base x s ^ (e + 1) + 1) + 4))

/-- Cost bound for entering a horizon `≤ s`. -/
def Bb (e : ℕ) (x : List Bool) (s : ℕ) : ℕ :=
  (e + 1) * ((base x s * (2 * base x s ^ e + 3) + 3) * (2 * (base x s ^ (e + 1) + 1) + 4))

theorem base_mono (x : List Bool) {G s : ℕ} (h : G ≤ s) : base x G ≤ base x s := by unfold base; omega

theorem round_le_Rb (x : List Bool) {G s : ℕ} (hGs : G ≤ s) (N : ℕ) (hN : N = base x G ^ (d + 1) + 1) :
    (d + 5) * ((4 * base x G ^ d + 4) * (2 * N + 2)) ≤ Rb d x s := by
  unfold Rb
  have h1 := base_mono x hGs
  have h2 : base x G ^ d ≤ base x s ^ d := Nat.pow_le_pow_left h1 d
  have h3 : base x G ^ (d + 1) ≤ base x s ^ (d + 1) := Nat.pow_le_pow_left h1 (d + 1)
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul <;> omega

theorem small_le_Rb (x : List Bool) {G s : ℕ} (hGs : G ≤ s) (N : ℕ) (hN : N = base x G ^ (d + 1) + 1) :
    5 * (2 * N + 4) ≤ Rb d x s := by
  unfold Rb
  have h1 := base_mono x hGs
  have h3 : base x G ^ (d + 1) ≤ base x s ^ (d + 1) := Nat.pow_le_pow_left h1 (d + 1)
  have h4 : 2 * N + 4 ≤ (4 * base x s ^ d + 4) * (2 * (base x s ^ (d + 1) + 1) + 4) := by
    have : 2 * N + 4 ≤ 2 * (base x s ^ (d + 1) + 1) + 4 := by omega
    exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
  calc 5 * (2 * N + 4) ≤ (d + 5) * (2 * N + 4) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ _ := Nat.mul_le_mul_left _ h4

theorem Bb_mono (x : List Bool) {G s : ℕ} (hGs : G ≤ s) :
    (d + 1) * ((base x G * (2 * base x G ^ d + 3) + 3) * (2 * (base x G ^ (d + 1) + 1) + 4)) ≤
      Bb d x s := by
  unfold Bb
  have h1 := base_mono x hGs
  have h2 : base x G ^ d ≤ base x s ^ d := Nat.pow_le_pow_left h1 d
  have h3 : base x G ^ (d + 1) ≤ base x s ^ (d + 1) := Nat.pow_le_pow_left h1 (d + 1)
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul
  · have := Nat.mul_le_mul h1 (show 2 * base x G ^ d + 3 ≤ 2 * base x s ^ d + 3 by omega)
    omega
  · omega

/-! ### The main inductions -/

/-- Rounds of the final horizon `s`: the program halts with the first answer. -/
theorem rounds_answer (x : List Bool) (s : ℕ) (b : Bool) (hb : A.out x s = some b)
    (hnone : ∀ s' < s, A.out x s' = none) :
    ∀ (k t : ℕ) (l : L A), t + k = s → Inv A x s t l →
      ∃ c, (prog A).Halts (.chk, l) b c ∧ c ≤ (k + 1) * Rb d x s
  | 0, t, l, htk, hI => by
    have ht : t = s := by omega
    subst ht
    refine ⟨_, halt_chk A x t t l hI b hb, ?_⟩
    have := small_le_Rb (d := d) x (le_refl t) l.length hI.len
    omega
  | k + 1, t, l, htk, hI => by
    have hts : t < s := by omega
    have hans : arrAns A l = none := by rw [arrAns_eq A x s t l hI]; exact hnone t hts
    obtain ⟨l', c, hR, hc, hI'⟩ := round A x s t l hI hts hans
    obtain ⟨c', hH, hc'⟩ := rounds_answer x s b hb hnone k (t + 1) l' (by omega) hI'
    refine ⟨c + c', Prog.Reach.halts (prog A) hR hH, ?_⟩
    have h1 := round_le_Rb (d := d) x (le_refl s) l.length hI.len
    have e : (k + 1 + 1) * Rb d x s = (k + 1) * Rb d x s + Rb d x s := by ring
    omega

/-- Rounds of a horizon `G < s`: the program reaches the restart for `G + 1`. -/
theorem rounds_restart (x : List Bool) (s G : ℕ) (hGs : G < s) (hnone : ∀ s' < s, A.out x s' = none) :
    ∀ (k t : ℕ) (l : L A), t + k = G → Inv A x G t l →
      ∃ (l' : L A) (c : ℕ), (prog A).Reach (.chk, l) (.r0, l') c ∧ c ≤ (k + 1) * Rb d x s ∧
        Pre A x (G + 1) l'
  | 0, t, l, htk, hI => by
    have ht : t = G := by omega
    subst ht
    have hans : arrAns A l = none := by rw [arrAns_eq A x t t l hI]; exact hnone t hGs
    obtain ⟨l', c, hR, hc, hP⟩ := restart A x t l hI hans
    have := small_le_Rb (d := d) x (le_of_lt hGs) l.length hI.len
    exact ⟨l', c, hR, by omega, hP⟩
  | k + 1, t, l, htk, hI => by
    have htG : t < G := by omega
    have hans : arrAns A l = none := by rw [arrAns_eq A x G t l hI]; exact hnone t (by omega)
    obtain ⟨l1, c1, hR1, hc1, hI1⟩ := round A x G t l hI htG hans
    obtain ⟨l', c', hR', hc', hP⟩ := rounds_restart x s G hGs hnone k (t + 1) l1 (by omega) hI1
    have h1 := round_le_Rb (d := d) x (le_of_lt hGs) l.length hI.len
    have e : (k + 1 + 1) * Rb d x s = (k + 1) * Rb d x s + Rb d x s := by ring
    exact ⟨l', c1 + c', Prog.Reach.trans (prog A) hR1 hR', by omega, hP⟩

/-- Horizons `G, G+1, …, s`. -/
theorem guesses (x : List Bool) (s : ℕ) (b : Bool) (hb : A.out x s = some b)
    (hnone : ∀ s' < s, A.out x s' = none) :
    ∀ (k G : ℕ) (l : L A), G + k = s → Pre A x G l →
      ∃ c, (prog A).Halts (.r0, l) b c ∧ c ≤ (k + 1) * (Bb d x s + (s + 1) * Rb d x s)
  | 0, G, l, hGk, hP => by
    have hG : G = s := by omega
    subst hG
    obtain ⟨l1, c1, hR1, hc1, hI1⟩ := enter A x G l hP
    obtain ⟨c2, hH, hc2⟩ := rounds_answer A x G b hb hnone G 0 l1 (by omega) hI1
    refine ⟨c1 + c2, Prog.Reach.halts (prog A) hR1 hH, ?_⟩
    have := Bb_mono (d := d) x (le_refl G)
    omega
  | k + 1, G, l, hGk, hP => by
    have hGs : G < s := by omega
    obtain ⟨l1, c1, hR1, hc1, hI1⟩ := enter A x G l hP
    obtain ⟨l2, c2, hR2, hc2, hP2⟩ := rounds_restart A x s G hGs hnone G 0 l1 (by omega) hI1
    obtain ⟨c3, hH, hc3⟩ := guesses x s b hb hnone k (G + 1) l2 (by omega) hP2
    refine ⟨c1 + (c2 + c3), Prog.Reach.halts (prog A) hR1 (Prog.Reach.halts (prog A) hR2 hH), ?_⟩
    have h1 := Bb_mono (d := d) x (le_of_lt hGs)
    have h2 : (G + 1) * Rb d x s ≤ (s + 1) * Rb d x s := Nat.mul_le_mul_right _ (by omega)
    have e : (k + 1 + 1) * (Bb d x s + (s + 1) * Rb d x s) =
        (k + 1) * (Bb d x s + (s + 1) * Rb d x s) + (Bb d x s + (s + 1) * Rb d x s) := by ring
    omega

/-- **Halting with the first WCCD answer.** -/
theorem halts_of_first (x : List Bool) (s : ℕ) (b : Bool) (hb : A.out x s = some b)
    (hnone : ∀ s' < s, A.out x s' = none) :
    ∃ C, (prog A).Halts ((prog A).start, x.map (prog A).lift) b C ∧
      C ≤ 10 * x.length + 25 + (s + 1) * (Bb d x s + (s + 1) * Rb d x s) := by
  obtain ⟨l0, c0, hR0, hc0, hP0⟩ := init_phase A x
  obtain ⟨c1, hH, hc1⟩ := guesses A x s b hb hnone s 0 l0 (by omega) hP0
  exact ⟨c0 + c1, Prog.Reach.halts (prog A) hR0 hH, by omega⟩

/-! ### The polynomial bound -/

theorem final_arith (d n s Q Mx : ℕ) (hMx : Mx ≤ Q) (hM3 : 3 ≤ Mx) (hs : s + 1 ≤ Q) (hn : n ≤ Q) :
    10 * n + 25 + (s + 1) * ((d + 1) * ((Mx * (2 * Mx ^ d + 3) + 3) * (2 * (Mx ^ (d + 1) + 1) + 4)) +
      (s + 1) * ((d + 5) * ((4 * Mx ^ d + 4) * (2 * (Mx ^ (d + 1) + 1) + 4)))) + 2 ≤
    (128 * d + 421) * Q ^ (2 * d + 3) := by
  have hQ : 3 ≤ Q := le_trans hM3 hMx
  have ha : 1 ≤ Q ^ d := Nat.one_le_pow _ _ (by omega)
  have hm : Mx ^ d ≤ Q ^ d := Nat.pow_le_pow_left hMx d
  have eM : Mx ^ (d + 1) = Mx * Mx ^ d := by ring
  have eQ : Q ^ (2 * d + 3) = Q * (Q * (Q * (Q ^ d * Q ^ d))) := by ring
  rw [eM, eQ]
  generalize Q ^ d = a at *
  generalize Mx ^ d = m at *
  have hQa : Q ≤ Q * a := Nat.le_mul_of_pos_right _ (by omega)
  have hQa1 : 1 ≤ Q * a := by nlinarith
  have hMm : Mx * m ≤ Q * a := Nat.mul_le_mul hMx hm
  have E1 : 2 * (Mx * m + 1) + 4 ≤ 8 * (Q * a) := by omega
  have E2 : 4 * m + 4 ≤ 8 * a := by omega
  have E3 : Mx * (2 * m + 3) + 3 ≤ 8 * (Q * a) := by
    have : Mx * (2 * m + 3) = 2 * (Mx * m) + 3 * Mx := by ring
    omega
  have B : (d + 1) * ((Mx * (2 * m + 3) + 3) * (2 * (Mx * m + 1) + 4)) ≤
      (d + 1) * (64 * (Q * (Q * (a * a)))) := by
    apply Nat.mul_le_mul_left
    calc (Mx * (2 * m + 3) + 3) * (2 * (Mx * m + 1) + 4) ≤ (8 * (Q * a)) * (8 * (Q * a)) :=
          Nat.mul_le_mul E3 E1
      _ = 64 * (Q * (Q * (a * a))) := by ring
  have R : (d + 5) * ((4 * m + 4) * (2 * (Mx * m + 1) + 4)) ≤ (d + 5) * (64 * (Q * (a * a))) := by
    apply Nat.mul_le_mul_left
    calc (4 * m + 4) * (2 * (Mx * m + 1) + 4) ≤ (8 * a) * (8 * (Q * a)) := Nat.mul_le_mul E2 E1
      _ = 64 * (Q * (a * a)) := by ring
  have sR : (s + 1) * ((d + 5) * ((4 * m + 4) * (2 * (Mx * m + 1) + 4))) ≤
      (d + 5) * (64 * (Q * (Q * (a * a)))) := by
    calc (s + 1) * ((d + 5) * ((4 * m + 4) * (2 * (Mx * m + 1) + 4)))
        ≤ Q * ((d + 5) * (64 * (Q * (a * a)))) := Nat.mul_le_mul hs R
      _ = (d + 5) * (64 * (Q * (Q * (a * a)))) := by ring
  have S : (d + 1) * ((Mx * (2 * m + 3) + 3) * (2 * (Mx * m + 1) + 4)) +
      (s + 1) * ((d + 5) * ((4 * m + 4) * (2 * (Mx * m + 1) + 4))) ≤
      (128 * d + 384) * (Q * (Q * (a * a))) := by
    have e : (d + 1) * (64 * (Q * (Q * (a * a)))) + (d + 5) * (64 * (Q * (Q * (a * a)))) =
        (128 * d + 384) * (Q * (Q * (a * a))) := by ring
    omega
  have T : (s + 1) * ((d + 1) * ((Mx * (2 * m + 3) + 3) * (2 * (Mx * m + 1) + 4)) +
      (s + 1) * ((d + 5) * ((4 * m + 4) * (2 * (Mx * m + 1) + 4)))) ≤
      (128 * d + 384) * (Q * (Q * (Q * (a * a)))) := by
    calc _ ≤ Q * ((128 * d + 384) * (Q * (Q * (a * a)))) := Nat.mul_le_mul hs S
      _ = (128 * d + 384) * (Q * (Q * (Q * (a * a)))) := by ring
  have hbig : Q ≤ Q * (Q * (Q * (a * a))) := by
    have h1 : 1 ≤ Q * (Q * (a * a)) := by
      have : 1 ≤ a * a := Nat.one_le_iff_ne_zero.2 (by positivity)
      nlinarith
    nlinarith
  have e : (128 * d + 421) * (Q * (Q * (Q * (a * a)))) =
      (128 * d + 384) * (Q * (Q * (Q * (a * a)))) + 37 * (Q * (Q * (Q * (a * a)))) := by ring
  omega


/-- **The compiled single-tape TM decides what the WCCD decides**, within
`(128 d + 421)·(n + 2T(n) + 3)^(2d+3)` steps. -/
theorem toTM_decides {L : Set (List Bool)} {T : ℕ → ℕ} (hA : A.Decides L T) :
    (toTM A).Decides L (fun n => (128 * d + 421) * (n + 2 * T n + 3) ^ (2 * d + 3)) := by
  intro x
  obtain ⟨b, ⟨s, hsT, hs, hnone⟩, hbL⟩ := hA x
  obtain ⟨C, hC, hCb⟩ := halts_of_first A x s b hs hnone
  refine ⟨b, ?_, hbL⟩
  obtain ⟨s', hs', h1, h2⟩ := Prog.toTM_firstAnswer (prog A) x hC
  refine ⟨s', le_trans hs' ?_, h1, h2⟩
  show C + 2 ≤ (128 * d + 421) * (x.length + 2 * T x.length + 3) ^ (2 * d + 3)
  have hMx : base x s ≤ x.length + 2 * T x.length + 3 := by unfold base; omega
  have hF := final_arith d x.length s (x.length + 2 * T x.length + 3) (base x s) hMx
    (by have := base_ge x s; omega) (by omega) (by omega)
  unfold Bb Rb at hCb
  omega

end PVNP.Discrete.WCCDSweep

namespace PVNP.Discrete

open WCCDSweep

/-- **D-1: every polynomial-time `(1+d)`-dimensional WCC language is decided in
polynomial time by an ordinary single-tape Turing machine.** -/
theorem P_WCCD_subset_P_TM (d : ℕ) : P_WCCD d ⊆ P_TM := by
  rintro L ⟨A, p, hA⟩
  refine ⟨toTM A, Polynomial.C (128 * d + 421) * (Polynomial.X + 2 * p + 3) ^ (2 * d + 3), ?_⟩
  intro x
  have hx := toTM_decides A hA x
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  exact hx

/-- **D-1: `P_WCCD(d) = P_TM`** for every lattice dimension `1 + d`. -/
theorem P_WCCD_eq_P_TM (d : ℕ) : P_WCCD d = P_TM :=
  Set.Subset.antisymm (P_WCCD_subset_P_TM d) (P_TM_subset_P_WCCD d)

/-- **D-1: `NP_WCCD(d) = NP_TM`** (verifier-based NP over the two base classes). -/
theorem NP_WCCD_eq_NP_TM (d : ℕ) : NPOf (P_WCCD d) = NP_TM := by
  rw [P_WCCD_eq_P_TM]
  rfl

end PVNP.Discrete
