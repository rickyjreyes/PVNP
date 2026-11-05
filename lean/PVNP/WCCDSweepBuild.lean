import PVNP.WCCDSweepRound

/-!
# D-1: building the reference markers `ref k` at cells `M^k`

For each axis `k`, an outer loop with the unary pointer `ptr` runs `M` times; each
iteration copies the marker `ref k` (cell `M^k`) into the count-down marker `bb`
and moves the marker `mv` right by one cell per count-down step (appending a
fresh cell when `mv` leaves the segment).  After `M` iterations `mv` sits at
`M^(k+1)`, and `rset` stores it in `ref (k+1)`.  Every move is a one-cell move.
-/

namespace PVNP.Discrete.WCCDSweep

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.Discrete.WCCD

variable {d : ℕ} (A : WCCD d)

/-- Set the moving marker and the count-down marker. -/
def setMB (a : Cell A.S d) (m b : Bool) : Cell A.S d := {a with mv := m, bb := b}

theorem setMB_setMB (a : Cell A.S d) (m b m' b' : Bool) :
    setMB A (setMB A a m b) m' b' = setMB A a m' b' := rfl

theorem mvRight_length (l : L A) (hl : 0 < l.length) :
    (mvRight A l hl).length = l.length + (if l[l.length - 1].mv then 1 else 0) := by
  unfold mvRight; split_ifs <;> simp

theorem mvRight_get (l : L A) (hl : 0 < l.length) (i : ℕ) (h : i < (mvRight A l hl).length) :
    (mvRight A l hl)[i] =
      {l.getD i (dflt A) with mv := if h' : 0 < i ∧ i - 1 < l.length then l[i - 1].mv else false} := by
  by_cases hi : i < l.length
  · unfold mvRight
    rw [List.getElem_append_left (by simpa using hi), List.getD_eq_getElem _ _ hi]
    simp [setMv]
  · have hlen := mvRight_length A l hl
    have hlast : l[l.length - 1].mv = true := by
      by_contra hc
      rw [if_neg hc] at hlen
      omega
    have hiL : i = l.length := by
      rw [if_pos hlast] at hlen
      omega
    subst hiL
    unfold mvRight
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_mapIdx, Nat.sub_self, List.getD_eq_default _ _ (le_refl _)]
    rw [dif_pos ⟨hl, by omega⟩]
    simp [hlast]

/-- **Inner loop** `rchk/rmov`: `mv` moves right by `b` cells while `bb`
counts down from `b` to `0`. -/
theorem inner_loop (k : Fin (d + 1)) : ∀ (b m : ℕ) (l : L A), m < l.length → b < l.length →
    (∀ i (h : i < l.length), l[i].fst = decide (i = 0)) →
    (∀ i (h : i < l.length), l[i].bb = decide (i = b)) →
    (∀ i (h : i < l.length), l[i].mv = decide (i = m)) →
    ∃ (l' : L A) (c : ℕ), (prog A).Reach (.rchk k, l) (.rnext k, l') c ∧
      c ≤ (2 * b + 1) * (2 * max l.length (m + b + 1) + 3) ∧
      l'.length = max l.length (m + b + 1) ∧
      ∀ i (h : i < l'.length), l'[i] = setMB A (l.getD i (dflt A)) (decide (i = m + b)) (decide (i = 0))
  | 0, m, l, hm, hb, hfst, hbb, hmv => by
    have hl : 0 < l.length := by omega
    have hbb0 : l[0].bb = true := by rw [hbb 0 hl]; simp
    obtain ⟨hs, hc⟩ := step_rchk_done A k l hl hfst hbb0
    have hmax : max l.length (m + 0 + 1) = l.length := by omega
    refine ⟨l, _, Prog.Reach.single (prog A) hs, ?_, hmax.symm, ?_⟩
    · simp only [hc]; rw [hmax]; omega
    · intro i h
      rw [List.getD_eq_getElem _ _ h]
      simp only [setMB, Nat.add_zero]
      rw [← hmv i h, ← hbb i h]
  | b + 1, m, l, hm, hb, hfst, hbb, hmv => by
    have hl : 0 < l.length := by omega
    have hbb0 : l[0].bb = false := by rw [hbb 0 hl]; simp
    obtain ⟨hs1, hc1⟩ := step_rchk_move A k l hl hfst hbb0
    obtain ⟨hs2, hc2⟩ := step_rmov A k (mvRight A l hl)
    have hlast : l[l.length - 1].mv = decide (l.length - 1 = m) := hmv _ _
    have hl1len : (mvRight A l hl).length = max l.length (m + 2) := by
      rw [mvRight_length, hlast]
      by_cases h : l.length - 1 = m
      · rw [if_pos (by simp [h])]; omega
      · rw [if_neg (by simp [h])]; omega
    have hl2len : (bbLeft A (mvRight A l hl)).length = max l.length (m + 2) := by
      rw [bbLeft_length, hl1len]
    -- cells of `mvRight`
    have hl1get : ∀ i (h : i < (mvRight A l hl).length), (mvRight A l hl)[i] =
        setMB A (l.getD i (dflt A)) (decide (i = m + 1)) (decide (i = b + 1)) := by
      intro i h
      rw [mvRight_get]
      by_cases hi : i < l.length
      · rw [List.getD_eq_getElem _ _ hi]
        simp only [setMB]
        rw [← hbb i hi]
        by_cases h0 : 0 < i
        · rw [dif_pos ⟨h0, by omega⟩, hmv (i - 1) (by omega)]
          congr 1
          exact decide_iff_eq (by omega)
        · rw [dif_neg (fun h' => h0 h'.1)]
          congr 1
          exact (decide_eq_false (by omega)).symm
      · rw [List.getD_eq_default _ _ (by omega)]
        simp only [setMB]
        have hiL : i = l.length := by rw [hl1len] at h; omega
        rw [dif_pos ⟨by omega, by omega⟩, hmv (i - 1) (by omega)]
        have h1 : decide (i = b + 1) = false := decide_eq_false (by omega)
        have h2 : decide (i - 1 = m) = decide (i = m + 1) := decide_iff_eq (by omega)
        rw [h1, h2]
        rfl
    -- cells of `bbLeft (mvRight l)`
    have hl2get : ∀ i (h : i < (bbLeft A (mvRight A l hl)).length), (bbLeft A (mvRight A l hl))[i] =
        setMB A (l.getD i (dflt A)) (decide (i = m + 1)) (decide (i = b)) := by
      intro i h
      have h1 : i < (mvRight A l hl).length := by rw [hl2len, ← hl1len] at h; exact h
      rw [bbLeft_get' A _ i h1, hl1get i h1]
      by_cases hi : i + 1 < (mvRight A l hl).length
      · rw [dif_pos hi, hl1get (i + 1) hi]
        simp only [setMB]
        congr 1
        exact decide_iff_eq (by omega)
      · rw [dif_neg hi]
        simp only [setMB]
        congr 1
        exact (decide_eq_false (by omega)).symm
    have hfst2 : ∀ i (h : i < (bbLeft A (mvRight A l hl)).length),
        (bbLeft A (mvRight A l hl))[i].fst = decide (i = 0) := by
      intro i h
      rw [hl2get i h]
      by_cases hi : i < l.length
      · rw [List.getD_eq_getElem _ _ hi]; exact hfst i hi
      · rw [List.getD_eq_default _ _ (by omega)]
        exact (decide_eq_false (by omega)).symm
    have hbb2 : ∀ i (h : i < (bbLeft A (mvRight A l hl)).length),
        (bbLeft A (mvRight A l hl))[i].bb = decide (i = b) := by
      intro i h; rw [hl2get i h]; rfl
    have hmv2 : ∀ i (h : i < (bbLeft A (mvRight A l hl)).length),
        (bbLeft A (mvRight A l hl))[i].mv = decide (i = m + 1) := by
      intro i h; rw [hl2get i h]; rfl
    obtain ⟨l', c, hR, hc, hlen', hget'⟩ :=
      inner_loop k b (m + 1) (bbLeft A (mvRight A l hl)) (by omega) (by omega) hfst2 hbb2 hmv2
    have hmax : max (bbLeft A (mvRight A l hl)).length (m + 1 + b + 1) = max l.length (m + (b + 1) + 1) := by
      omega
    refine ⟨l', _, Prog.Reach.step hs1 (Prog.Reach.step hs2 hR), ?_, by rw [hlen', hmax], ?_⟩
    · simp only [hc1, hc2]
      rw [hmax] at hc
      have e1 : (if l[l.length - 1].mv then 1 else 0) ≤ 1 := by split_ifs <;> omega
      have e2 : (mvRight A l hl).length ≤ max l.length (m + (b + 1) + 1) := by omega
      have e3 : l.length ≤ max l.length (m + (b + 1) + 1) := by omega
      nlinarith
    · intro i h
      rw [hget' i h]
      by_cases hi : i < (bbLeft A (mvRight A l hl)).length
      · rw [List.getD_eq_getElem _ _ hi, hl2get i hi, setMB_setMB]
        congr 1
        exact decide_iff_eq (by omega)
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        congr 1
        exact decide_iff_eq (by omega)

/-! ### The building invariant -/

theorem len_lt_base (x : List Bool) (G : ℕ) : x.length < base x G := by unfold base; omega

/-- **Invariant of the reference-building phase**: axis `k` (references
`ref 0, …, ref k` are in place), pointer `p`, moving marker at `m`. -/
structure BInv (x : List Bool) (G k p m : ℕ) (l : L A) : Prop where
  lenM : base x G ≤ l.length
  lenK : base x G ^ k < l.length
  lenHi : l.length ≤ base x G ^ (d + 1) + 1
  hm : m < l.length
  hp : p < base x G
  inp : ∀ i (h : i < l.length), l[i].inp = x[i]?
  fst : ∀ i (h : i < l.length), l[i].fst = decide (i = 0)
  cnt : ∀ i (h : i < l.length), l[i].cnt = decide (i < base x G)
  gm : ∀ i (h : i < l.length), l[i].gm = decide (i ≤ G)
  rp : ∀ i (h : i < l.length), l[i].rp = decide (i = 0)
  ptr : ∀ i (h : i < l.length), l[i].ptr = decide (i = p)
  mv : ∀ i (h : i < l.length), l[i].mv = decide (i = m)
  ref : ∀ i (h : i < l.length) (j : Fin (d + 2)),
    l[i].ref j = (decide (j.val ≤ k) && decide (i = base x G ^ j.val))

/-- The invariant extends to the fresh cells beyond the segment. -/
theorem BInv.getD {x : List Bool} {G k p m : ℕ} {l : L A} (hB : BInv A x G k p m l) (i : ℕ) :
    (l.getD i (dflt A)).inp = x[i]? ∧ (l.getD i (dflt A)).fst = decide (i = 0) ∧
    (l.getD i (dflt A)).cnt = decide (i < base x G) ∧ (l.getD i (dflt A)).gm = decide (i ≤ G) ∧
    (l.getD i (dflt A)).rp = decide (i = 0) ∧ (l.getD i (dflt A)).ptr = decide (i = p) ∧
    (l.getD i (dflt A)).mv = decide (i = m) ∧
    ∀ j : Fin (d + 2), (l.getD i (dflt A)).ref j = (decide (j.val ≤ k) && decide (i = base x G ^ j.val)) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact ⟨hB.inp i hi, hB.fst i hi, hB.cnt i hi, hB.gm i hi, hB.rp i hi, hB.ptr i hi, hB.mv i hi,
      hB.ref i hi⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    have h1 := hB.lenM
    have h2 := hB.lenK
    have h3 := hB.hm
    have h4 := hB.hp
    have h5 := len_lt_base x G
    have h6 : G < base x G := by unfold base; omega
    refine ⟨(List.getElem?_eq_none (by omega)).symm, (decide_eq_false (by omega)).symm,
      (decide_eq_false (by omega)).symm, (decide_eq_false (by omega)).symm,
      (decide_eq_false (by omega)).symm, (decide_eq_false (by omega)).symm,
      (decide_eq_false (by omega)).symm, fun j => ?_⟩
    by_cases hj : j.val ≤ k
    · have : base x G ^ j.val ≤ base x G ^ k := Nat.pow_le_pow_right (by omega) hj
      simp only [decide_eq_true hj, Bool.true_and]
      exact (decide_eq_false (by omega)).symm
    · simp only [decide_eq_false hj, Bool.false_and]
      rfl

theorem getD_map_gCopy (k : Fin (d + 1)) (l : L A) (i : ℕ) :
    (l.map (gCopy A k)).getD i (dflt A) = gCopy A k (l.getD i (dflt A)) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rfl

/-- **Outer loop** of axis `k`: `M` iterations, each moving `mv` right by `M^k`. -/
theorem outer_loop (x : List Bool) (G : ℕ) (k : Fin (d + 1)) :
    ∀ (q p : ℕ) (l : L A), p + q = base x G → 0 < q →
    BInv A x G k.val p (p * base x G ^ k.val) l →
    ∃ (l' : L A) (c : ℕ), (prog A).Reach (.rcopy k, l) (.rset k, l') c ∧
      c ≤ q * ((2 * base x G ^ k.val + 3) * (2 * (base x G ^ (d + 1) + 1) + 3)) ∧
      BInv A x G k.val 0 (base x G ^ (k.val + 1)) l'
  | 0, _, _, _, hq, _ => absurd hq (lt_irrefl 0)
  | q + 1, p, l, hpq, _, hB => by
    set M := base x G with hMdef
    set B := M ^ k.val with hBdef
    set U := M ^ (d + 1) + 1 with hUdef
    have hMU : M ^ (d + 1) = base x G ^ (d + 1) := rfl
    have hM3 : 3 ≤ M := by have := base_ge x G; omega
    have hBpos : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
    have hBk : (p + 1) * B ≤ M ^ (d + 1) := by
      calc (p + 1) * B ≤ M * M ^ k.val := Nat.mul_le_mul_right _ (by omega)
        _ = M ^ (k.val + 1) := by ring
        _ ≤ M ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hL := hB.lenHi
    -- rcopy
    obtain ⟨hs1, hc1⟩ := step_rcopy A k l
    have hfst1 : ∀ i (h : i < (l.map (gCopy A k)).length), (l.map (gCopy A k))[i].fst = decide (i = 0) := by
      intro i h; rw [List.getElem_map]; exact hB.fst i _
    have hbb1 : ∀ i (h : i < (l.map (gCopy A k)).length), (l.map (gCopy A k))[i].bb = decide (i = B) := by
      intro i h
      rw [List.getElem_map]
      simp only [gCopy]
      rw [hB.ref i _ k.castSucc]
      simp only [Fin.coe_castSucc, le_refl, decide_true, Bool.true_and]
      rfl
    have hmv1 : ∀ i (h : i < (l.map (gCopy A k)).length),
        (l.map (gCopy A k))[i].mv = decide (i = p * B) := by
      intro i h; rw [List.getElem_map]; exact hB.mv i _
    obtain ⟨l1, c1, hR1, hc1', hl1len, hl1get⟩ := inner_loop A k B (p * B) (l.map (gCopy A k))
      (by simpa using hB.hm) (by simpa using hB.lenK) hfst1 hbb1 hmv1
    simp only [List.length_map] at hl1len hc1'
    -- cells of `l1`
    have hl1f : ∀ i (h : i < l1.length),
        l1[i] = setMB A (gCopy A k (l.getD i (dflt A))) (decide (i = (p + 1) * B)) (decide (i = 0)) := by
      intro i h
      rw [hl1get i h, getD_map_gCopy]
      congr 1
      exact decide_iff_eq (by rw [Nat.succ_mul])
    have hl1fst : ∀ i (h : i < l1.length), l1[i].fst = decide (i = 0) := by
      intro i h; rw [hl1f i h]; exact (hB.getD A i).2.1
    have hl1cnt : ∀ i (h : i < l1.length), l1[i].cnt = decide (i < M) := by
      intro i h; rw [hl1f i h]; exact (hB.getD A i).2.2.1
    have hl1ptr : ∀ i (h : i < l1.length), l1[i].ptr = decide (i = p) := by
      intro i h; rw [hl1f i h]; exact (hB.getD A i).2.2.2.2.2.1
    have hpM : p < M := hB.hp
    obtain ⟨hs2, hc2⟩ := step_rnext A k l1 M p (by omega) (by have := hB.lenM; omega) hpM hl1fst hl1cnt hl1ptr
    set p' := if p + 1 = M then 0 else p + 1 with hp'
    set l2 := l1.mapIdx (setPtr A p') with hl2
    have hl2len : l2.length = max l.length (p * B + B + 1) := by simp [hl2, hl1len]
    have hl2get : ∀ i (h : i < l2.length), l2[i] = {setMB A (gCopy A k (l.getD i (dflt A)))
        (decide (i = (p + 1) * B)) (decide (i = 0)) with ptr := decide (i = p')} := by
      intro i h
      simp only [hl2, List.getElem_mapIdx, setPtr]
      rw [hl1f i (by simpa [hl2] using h)]
    have hB2 : BInv A x G k.val p' ((p + 1) * B) l2 := by
      have hg := hB.getD A
      refine ⟨by have := hB.lenM; omega, by have := hB.lenK; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
      · rw [hl2len]
        have : p * B + B = (p + 1) * B := by ring
        omega
      · rw [hl2len]
        have : p * B + B = (p + 1) * B := by ring
        omega
      · rw [hp']; split_ifs <;> omega
      · intro i h; rw [hl2get i h]; exact (hg i).1
      · intro i h; rw [hl2get i h]; exact (hg i).2.1
      · intro i h; rw [hl2get i h]; exact (hg i).2.2.1
      · intro i h; rw [hl2get i h]; exact (hg i).2.2.2.1
      · intro i h; rw [hl2get i h]; exact (hg i).2.2.2.2.1
      · intro i h; rw [hl2get i h]
      · intro i h; rw [hl2get i h]; rfl
      · intro i h j; rw [hl2get i h]; exact (hg i).2.2.2.2.2.2.2 j
    have hcost1 : 2 * l.length + 2 + c1 + (2 * l1.length + 2) ≤
        (2 * B + 3) * (2 * U + 3) := by
      have e1 : max l.length (p * B + B + 1) ≤ U := by
        have : p * B + B = (p + 1) * B := by ring
        omega
      have e2 : c1 ≤ (2 * B + 1) * (2 * U + 3) :=
        le_trans hc1' (Nat.mul_le_mul_left _ (by omega))
      rw [hl1len]
      nlinarith
    by_cases hq : q = 0
    · subst hq
      have hpM' : p + 1 = M := by omega
      have hp0 : p' = 0 := by rw [hp', if_pos hpM']
      have hmM : (p + 1) * B = M ^ (k.val + 1) := by rw [hpM', hBdef]; ring
      rw [if_pos hpM'] at hs2
      refine ⟨l2, _, Prog.Reach.step hs1 (Prog.Reach.trans (prog A) hR1 (Prog.Reach.single (prog A) hs2)),
        ?_, ?_⟩
      · show (prog A).tripCost (Ins.rcopy k) l + (c1 + (prog A).tripCost (Ins.rnext k) l1) ≤
          (0 + 1) * ((2 * B + 3) * (2 * U + 3))
        rw [hc1, hc2, Nat.zero_add, Nat.one_mul]
        omega
      · rw [← hp0, ← hmM]
        exact hB2
    · have hpM' : p + 1 ≠ M := by omega
      have hp1 : p' = p + 1 := by rw [hp', if_neg hpM']
      rw [hp1] at hB2
      obtain ⟨l', c', hR', hc', hB'⟩ := outer_loop x G k q (p + 1) l2 (by omega) (by omega) hB2
      rw [if_neg hpM'] at hs2
      refine ⟨l', _, Prog.Reach.step hs1 (Prog.Reach.trans (prog A) hR1 (Prog.Reach.step hs2 hR')), ?_, hB'⟩
      show (prog A).tripCost (Ins.rcopy k) l + (c1 + ((prog A).tripCost (Ins.rnext k) l1 + c')) ≤
        (q + 1) * ((2 * B + 3) * (2 * U + 3))
      rw [hc1, hc2]
      have hc'' : c' ≤ q * ((2 * B + 3) * (2 * U + 3)) := hc'
      have e : (q + 1) * ((2 * B + 3) * (2 * U + 3)) =
          q * ((2 * B + 3) * (2 * U + 3)) + (2 * B + 3) * (2 * U + 3) := by ring
      omega

/-- `rset`: store the moving marker in `ref (k+1)`, return `mv` to cell `0`. -/
theorem rset_inv (x : List Bool) (G : ℕ) (k : Fin (d + 1)) (l : L A)
    (hB : BInv A x G k.val 0 (base x G ^ (k.val + 1)) l) :
    BInv A x G (k.val + 1) 0 0 (l.map (gRset A k)) := by
  have h3 := base_ge x G
  have hm := hB.hm
  refine ⟨by simpa using hB.lenM, by simpa using hB.hm, by simpa using hB.lenHi, by simp; omega, hB.hp,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h; simp only [List.getElem_map, gRset]; exact hB.inp i _
  · intro i h; simp only [List.getElem_map, gRset]; exact hB.fst i _
  · intro i h; simp only [List.getElem_map, gRset]; exact hB.cnt i _
  · intro i h; simp only [List.getElem_map, gRset]; exact hB.gm i _
  · intro i h; simp only [List.getElem_map, gRset]; exact hB.rp i _
  · intro i h; simp only [List.getElem_map, gRset]; exact hB.ptr i _
  · intro i h; simp only [List.getElem_map, gRset]; exact hB.fst i _
  · intro i h j
    simp only [List.getElem_map, gRset]
    rw [Function.update_apply]
    split_ifs with hj
    · subst hj
      rw [hB.mv i _]
      simp [Fin.val_succ]
    · rw [hB.ref i _ j]
      have hj' : j.val ≠ k.val + 1 := fun h' => hj (Fin.ext (by rw [h', Fin.val_succ]))
      congr 1
      exact decide_iff_eq (by omega)

theorem cost_build {M U m c1 c' L1 Md : ℕ} (hc1 : c1 ≤ M * ((2 * Md + 3) * (2 * U + 3)))
    (hc' : c' ≤ m * ((M * (2 * Md + 3) + 1) * (2 * U + 3))) (hL1 : L1 ≤ U) :
    c1 + (2 * L1 + 2 + c') ≤ (m + 1) * ((M * (2 * Md + 3) + 1) * (2 * U + 3)) := by
  have e : (m + 1) * ((M * (2 * Md + 3) + 1) * (2 * U + 3)) =
      m * ((M * (2 * Md + 3) + 1) * (2 * U + 3)) + M * ((2 * Md + 3) * (2 * U + 3)) + (2 * U + 3) := by
    ring
  omega

/-- Instruction at the start of building axis `k` (`xfin` after the last). -/
def buildIns (k : ℕ) : Ins d := if h : k < d + 1 then .rcopy ⟨k, h⟩ else .xfin

theorem buildIns_zero : buildIns (d := d) 0 = .rcopy 0 := by
  simp only [buildIns, dif_pos (Nat.succ_pos d)]
  rfl

theorem buildIns_last : buildIns (d := d) (d + 1) = .xfin := by simp [buildIns]

/-- **All axes of the reference construction.** -/
theorem build_axes (x : List Bool) (G : ℕ) : ∀ (m k : ℕ), k + m = d + 1 → ∀ (l : L A),
    BInv A x G k 0 0 l →
    ∃ (l' : L A) (c : ℕ), (prog A).Reach (buildIns k, l) (.xfin, l') c ∧
      c ≤ m * ((base x G * (2 * base x G ^ d + 3) + 1) * (2 * (base x G ^ (d + 1) + 1) + 3)) ∧
      BInv A x G (d + 1) 0 0 l'
  | 0, k, hkm, l, hB => by
    have hk : k = d + 1 := by omega
    subst hk
    exact ⟨l, 0, by rw [buildIns_last]; exact Prog.Reach.refl _, by simp, hB⟩
  | m + 1, k, hkm, l, hB => by
    have hk : k < d + 1 := by omega
    set M := base x G with hMdef
    set U := M ^ (d + 1) + 1 with hUdef
    have hM3 : 3 ≤ M := by have := base_ge x G; omega
    have hB0 : BInv A x G (⟨k, hk⟩ : Fin (d + 1)).val 0 (0 * M ^ k) l := by simpa using hB
    obtain ⟨l1, c1, hR1, hc1, hB1⟩ := outer_loop A x G ⟨k, hk⟩ M 0 l (by omega) (by omega) hB0
    obtain ⟨hs2, hc2⟩ := step_rset A ⟨k, hk⟩ l1
    have hB2 := rset_inv A x G ⟨k, hk⟩ l1 hB1
    obtain ⟨l', c', hR', hc', hB'⟩ :=
      build_axes x G m (k + 1) (by omega) (l1.map (gRset A ⟨k, hk⟩)) hB2
    have hs2' : (prog A).stepP (.rset ⟨k, hk⟩, l1) =
        .inl (buildIns (k + 1), l1.map (gRset A ⟨k, hk⟩)) := by
      rw [hs2]
      by_cases h1 : k + 1 < d + 1
      · have e1 : nextAxis (⟨k, hk⟩ : Fin (d + 1)) = some ⟨k + 1, h1⟩ := by simp [nextAxis, h1]
        have e2 : buildIns (d := d) (k + 1) = .rcopy ⟨k + 1, h1⟩ := by simp [buildIns, h1]
        rw [e1, e2]
      · have e1 : nextAxis (⟨k, hk⟩ : Fin (d + 1)) = none := by simp [nextAxis, h1]
        have e2 : buildIns (d := d) (k + 1) = .xfin := by simp [buildIns, h1]
        rw [e1, e2]
    have hk' : buildIns (d := d) k = .rcopy ⟨k, hk⟩ := by simp [buildIns, hk]
    have hR : (prog A).Reach (buildIns k, l) (.xfin, l')
        (c1 + ((prog A).tripCost (Ins.rset ⟨k, hk⟩) l1 + c')) := by
      rw [hk']
      exact Prog.Reach.trans (prog A) hR1 (Prog.Reach.step hs2' hR')
    refine ⟨l', _, hR, ?_, hB'⟩
    · rw [hc2]
      have hpow : M ^ k ≤ M ^ d := Nat.pow_le_pow_right (by omega) (by omega)
      exact cost_build (le_trans hc1 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hpow) 3)))) hc' hB1.lenHi

/-! ### Entering and leaving the building phase -/

/-- State before `r0`: the fixed tracks for horizon `G`. -/
structure Pre (x : List Bool) (G : ℕ) (l : L A) : Prop where
  lenM : base x G ≤ l.length
  lenHi : l.length ≤ base x G ^ (d + 1) + 1
  inp : ∀ i (h : i < l.length), l[i].inp = x[i]?
  fst : ∀ i (h : i < l.length), l[i].fst = decide (i = 0)
  cnt : ∀ i (h : i < l.length), l[i].cnt = decide (i < base x G)
  gm : ∀ i (h : i < l.length), l[i].gm = decide (i ≤ G)
  rp : ∀ i (h : i < l.length), l[i].rp = decide (i = 0)
  ptr : ∀ i (h : i < l.length), l[i].ptr = decide (i = 0)

theorem r0_inv (x : List Bool) (G : ℕ) (l : L A) (hP : Pre A x G l) : BInv A x G 0 0 0 (gR0 A l) := by
  have h3 := base_ge x G
  have hM := hP.lenM
  refine ⟨by simpa [gR0_length] using hP.lenM, by simp [gR0_length]; omega,
    by simpa [gR0_length] using hP.lenHi, by simp [gR0_length]; omega, by omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h; simp only [gR0, List.getElem_mapIdx, setR0]; exact hP.inp i _
  · intro i h; simp only [gR0, List.getElem_mapIdx, setR0]; exact hP.fst i _
  · intro i h; simp only [gR0, List.getElem_mapIdx, setR0]; exact hP.cnt i _
  · intro i h; simp only [gR0, List.getElem_mapIdx, setR0]; exact hP.gm i _
  · intro i h; simp only [gR0, List.getElem_mapIdx, setR0]; exact hP.rp i _
  · intro i h; simp only [gR0, List.getElem_mapIdx, setR0]; exact hP.ptr i _
  · intro i h; simp only [gR0, List.getElem_mapIdx, setR0]; exact hP.fst i _
  · intro i h j
    simp only [gR0, List.getElem_mapIdx, setR0]
    by_cases hj : j = 0
    · subst hj; simp
    · have : ¬ j.val ≤ 0 := fun h' => hj (Fin.ext (by rw [Fin.val_zero]; omega))
      simp [hj, this]

theorem cval_eq (x : List Bool) (N i : ℕ) (hi : i < N) (a : Cell A.S d) (hinp : a.inp = x[i]?)
    (hfst : a.fst = decide (i = 0)) : cval A a = A.cinit N x (i : ZMod N) := by
  unfold cval WCCD.cinit
  rw [ZMod.val_cast_of_lt hi, hfst, hinp]
  by_cases h0 : i = 0
  · subst h0
    simp [List.head?_eq_getElem?]
  · rw [if_neg (by simpa using h0), if_neg h0]
    by_cases hx : i < x.length
    · rw [if_pos hx, List.getElem?_eq_getElem hx, List.getD_eq_getElem _ _ hx]
    · rw [if_neg hx, List.getElem?_eq_none (by omega)]

/-- `xfin`: write the initial cyclic configuration; this establishes `Inv` at `t = 0`. -/
theorem xfin_inv (x : List Bool) (G : ℕ) (l : L A) (hB : BInv A x G (d + 1) 0 0 l) :
    Inv A x G 0 (l.map (gXfin A)) := by
  have hlen : l.length = base x G ^ (d + 1) + 1 := by have := hB.lenK; have := hB.lenHi; omega
  refine ⟨by simpa using hlen, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h; simp only [List.getElem_map, gXfin]; exact hB.inp i _
  · intro i h; simp only [List.getElem_map, gXfin]; exact hB.fst i _
  · intro i h; simp only [List.getElem_map, gXfin]; exact hB.cnt i _
  · intro i h; simp only [List.getElem_map, gXfin]; exact hB.gm i _
  · intro i h; simp only [List.getElem_map, gXfin]; exact hB.rp i _
  · intro i h; simp only [List.getElem_map, gXfin]; exact hB.ptr i _
  · intro i h; simp only [List.getElem_map, gXfin]; exact hB.mv i _
  · intro i h k
    simp only [List.getElem_map, gXfin]
    rw [hB.ref i _ k]
    simp [show k.val ≤ d + 1 by omega]
  · intro i h
    simp only [List.getElem_map, gXfin]
    exact cval_eq A x _ i h _ (hB.inp i _) (hB.fst i _)

end PVNP.Discrete.WCCDSweep
