import PVNP.WCCDSweepLoops

/-!
# D-1: one simulated round of the WCCD sweep program

After `spread`, the window track `u` of every cell holds the current cyclic
configuration; the axis loops rotate track `u` by `Σⱼ off(uⱼ) Mʲ`, so that
`app` computes exactly one step of the cyclic automaton `WCCD.cstep`.
-/

namespace PVNP.Discrete.WCCDSweep

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.Discrete.WCCD

variable {d : ℕ} (A : WCCD d)

/-- All fields of a cell except the window and the count-down marker. -/
def core (a : Cell A.S d) :
    Option Bool × Bool × Bool × Bool × Bool × Bool × Bool × (Fin (d + 2) → Bool) × A.S :=
  (a.inp, a.fst, a.cnt, a.gm, a.rp, a.ptr, a.mv, a.ref, a.cur)

theorem core_setWB (a : Cell A.S d) (w : Nb d → A.S) (b : Bool) : core A (setWB A a w b) = core A a := rfl
theorem core_gCopy (k : Fin (d + 1)) (a : Cell A.S d) : core A (gCopy A k a) = core A a := rfl
theorem core_gSpread (a : Cell A.S d) : core A (gSpread A a) = core A a := rfl

/-- Partial neighbourhood offset over the axes `< k`, in `ℤ/Nℤ`. -/
def offZ (N M : ℕ) (u : Nb d) (k : ℕ) : ZMod N :=
  ∑ j : Fin (d + 1), if j.val < k then ((off (u j) : ℤ) : ZMod N) * (M : ZMod N) ^ j.val else 0

theorem offZ_zero (N M : ℕ) (u : Nb d) : offZ N M u 0 = 0 := by simp [offZ]

theorem offZ_succ (N M : ℕ) (u : Nb d) (k : Fin (d + 1)) :
    offZ N M u (k.val + 1) = offZ N M u k.val + ((off (u k) : ℤ) : ZMod N) * (M : ZMod N) ^ k.val := by
  simp only [offZ]
  have hsplit : ∀ j : Fin (d + 1),
      (if j.val < k.val + 1 then ((off (u j) : ℤ) : ZMod N) * (M : ZMod N) ^ j.val else 0) =
        (if j.val < k.val then ((off (u j) : ℤ) : ZMod N) * (M : ZMod N) ^ j.val else 0) +
        (if k = j then ((off (u j) : ℤ) : ZMod N) * (M : ZMod N) ^ j.val else 0) := by
    intro j
    by_cases h1 : j.val < k.val
    · have h2 : k ≠ j := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      rw [if_pos (by omega), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : k = j
      · subst h2; rw [if_pos (by omega), if_neg h1, if_pos rfl, zero_add]
      · have h3 : j.val ≠ k.val := fun h => h2 (Fin.ext h.symm)
        rw [if_neg (by omega), if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

theorem offZ_full (N M : ℕ) (v : Fin 3 × (Fin d → Fin 3)) :
    offZ N M (Fin.cons v.1 v.2) (d + 1) = ((flat M (offv v) : ℤ) : ZMod N) := by
  simp only [offZ, Fin.is_lt, if_true, flat, offv]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.val_zero, pow_zero, mul_one, Fin.cons_succ, Fin.val_succ]
  push_cast
  congr 1

/-- Gather invariant after the axes `< k`. -/
def GW (N M : ℕ) (cz : ZMod N → A.S) (k : ℕ) (l : L A) : Prop :=
  ∀ i (h : i < l.length) (u : Nb d), l[i].win u = cz ((i : ZMod N) + offZ N M u k)

theorem natCast_mod_add (N i B : ℕ) : (((i + B) % N : ℕ) : ZMod N) = (i : ZMod N) + (B : ZMod N) := by
  rw [ZMod.natCast_mod]; push_cast; ring

theorem natCast_mod_sub (N i B : ℕ) (hN : 0 < N) :
    (((i + B * (N - 1)) % N : ℕ) : ZMod N) = (i : ZMod N) - (B : ZMod N) := by
  rw [ZMod.natCast_mod]
  push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
  rw [ZMod.natCast_self]
  ring

theorem loopLRes_get (k : Fin (d + 1)) (B : ℕ) (l : L A) (i : ℕ) (h : i < l.length) :
    (loopLRes A k B l)[i]'(by rw [loopLRes_length]; exact h) =
      setWB A l[i] (winSel A k 2 (l.getD ((i + B) % l.length) (dflt A)).win l[i].win) (decide (i = 0)) := by
  simp [loopLRes]

theorem loopRRes_get (k : Fin (d + 1)) (B : ℕ) (l : L A) (i : ℕ) (h : i < l.length) :
    (loopRRes A k B l)[i]'(by rw [loopRRes_length]; exact h) =
      setWB A l[i] (winSel A k 0 (l.getD ((i + B * (l.length - 1)) % l.length) (dflt A)).win l[i].win)
        (decide (i = 0)) := by
  simp [loopRRes]

/-- The list after the two count-down loops of one axis. -/
def axisRes (k : Fin (d + 1)) (B : ℕ) (l : L A) : L A :=
  loopRRes A k B ((loopLRes A k B (l.map (gCopy A k))).map (gCopy A k))

theorem axisRes_length (k : Fin (d + 1)) (B : ℕ) (l : L A) : (axisRes A k B l).length = l.length := by
  simp [axisRes, loopRRes_length, loopLRes_length]

/-- Window after the left loop (and the second copy). -/
theorem axis_mid_win (k : Fin (d + 1)) (B : ℕ) (l : L A) (j : ℕ) (hj : j < l.length) (u : Nb d) :
    (((loopLRes A k B (l.map (gCopy A k))).map (gCopy A k))[j]'(by
        simp only [List.length_map, loopLRes_length]; exact hj)).win u =
      if u k = 2 then (l.getD ((j + B) % l.length) (dflt A)).win u else l[j].win u := by
  rw [List.getElem_map, loopLRes_get A k B _ j (by simpa using hj)]
  simp only [gCopy, setWB, winSel, List.length_map]
  split_ifs with h2
  · have hm : (j + B) % l.length < l.length := Nat.mod_lt _ (by omega)
    rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getD_eq_getElem _ _ hm, List.getElem_map]
    rfl
  · rw [List.getElem_map]
    rfl

theorem axis_mid_core (k : Fin (d + 1)) (B : ℕ) (l : L A) (j : ℕ) (hj : j < l.length) :
    core A (((loopLRes A k B (l.map (gCopy A k))).map (gCopy A k))[j]'(by
        simp only [List.length_map, loopLRes_length]; exact hj)) = core A l[j] := by
  rw [List.getElem_map, loopLRes_get A k B _ j (by simpa using hj), core_gCopy, core_setWB,
    List.getElem_map, core_gCopy]

theorem axisRes_core (k : Fin (d + 1)) (B : ℕ) (l : L A) (i : ℕ) (h : i < l.length) :
    core A ((axisRes A k B l)[i]'(by rw [axisRes_length]; exact h)) = core A l[i] := by
  simp only [axisRes]
  rw [loopRRes_get A k B _ i (by simpa [loopLRes_length] using h), core_setWB, axis_mid_core A k B l i h]

theorem axisRes_win (k : Fin (d + 1)) (B : ℕ) (l : L A) (i : ℕ) (h : i < l.length) (u : Nb d) :
    ((axisRes A k B l)[i]'(by rw [axisRes_length]; exact h)).win u =
      if u k = 0 then (l.getD ((i + B * (l.length - 1)) % l.length) (dflt A)).win u
      else if u k = 2 then (l.getD ((i + B) % l.length) (dflt A)).win u
      else l[i].win u := by
  simp only [axisRes]
  rw [loopRRes_get A k B _ i (by simpa [loopLRes_length] using h)]
  simp only [setWB, winSel]
  have hlen : ((loopLRes A k B (l.map (gCopy A k))).map (gCopy A k)).length = l.length := by
    simp [loopLRes_length]
  split_ifs with h0 h2
  · have hm : (i + B * (l.length - 1)) % l.length < l.length := Nat.mod_lt _ (by omega)
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hm), List.getD_eq_getElem _ _ hm]
    simp only [hlen]
    rw [axis_mid_win A k B l _ hm u, if_neg (by rw [h0]; decide)]
  · rw [axis_mid_win A k B l i h u, if_pos h2]
  · rw [axis_mid_win A k B l i h u, if_neg h2]

theorem off_cast (N : ℕ) (c : Fin 3) :
    ((off c : ℤ) : ZMod N) = if c = 0 then -1 else if c = 2 then 1 else 0 := by
  have key : c = 0 ∨ c = 1 ∨ c = 2 := by revert c; decide
  rcases key with h | h | h <;> subst h <;> simp [off]

/-- **One axis**: the left and the right count-down loops of axis `k`. -/
theorem axis_step (k : Fin (d + 1)) (N M : ℕ) (l : L A) (hN : l.length = N) (hNpos : 0 < N)
    (hMk : M ^ k.val < N)
    (hfst : ∀ i (h : i < l.length), l[i].fst = decide (i = 0))
    (href : ∀ i (h : i < l.length), l[i].ref k.castSucc = decide (i = M ^ k.val))
    (cz : ZMod N → A.S) (hgw : GW A N M cz k.val l) :
    (prog A).Reach (.lcopy k, l)
        ((match nextAxis k with | some k' => .lcopy k' | none => .app), axisRes A k (M ^ k.val) l)
        ((4 * M ^ k.val + 4) * (2 * N + 2)) ∧
      GW A N M cz (k.val + 1) (axisRes A k (M ^ k.val) l) := by
  subst hN
  set B := M ^ k.val with hB
  -- lcopy
  obtain ⟨hs1, hc1⟩ := step_lcopy A k l
  have hl1len : (l.map (gCopy A k)).length = l.length := by simp
  have hfst1 : ∀ i (h : i < (l.map (gCopy A k)).length), (l.map (gCopy A k))[i].fst = decide (i = 0) := by
    intro i h; rw [List.getElem_map]; exact hfst i _
  have hbb1 : ∀ i (h : i < (l.map (gCopy A k)).length), (l.map (gCopy A k))[i].bb = decide (i = B) := by
    intro i h; rw [List.getElem_map]; exact href i _
  have hL := loopL A k B (l.map (gCopy A k)) (by rw [hl1len]; exact hNpos) (by rw [hl1len]; exact hMk)
    hfst1 hbb1
  -- rcopyR
  obtain ⟨hs3, hc3⟩ := step_rcopyR A k (loopLRes A k B (l.map (gCopy A k)))
  set l3 := (loopLRes A k B (l.map (gCopy A k))).map (gCopy A k) with hl3
  have hl3len : l3.length = l.length := by simp [hl3, loopLRes_length]
  have hfst3 : ∀ i (h : i < l3.length), l3[i].fst = decide (i = 0) := by
    intro i h
    have := axis_mid_core A k B l i (by rw [hl3len] at h; exact h)
    have hf : l3[i].fst = l[i].fst := congrArg (fun c => c.2.1) this
    rw [hf]; exact hfst i _
  have hbb3 : ∀ i (h : i < l3.length), l3[i].bb = decide (i = B) := by
    intro i h
    simp only [hl3, List.getElem_map, gCopy]
    rw [loopLRes_get A k B _ i (by simpa using (show i < l.length by rw [hl3len] at h; exact h))]
    simp only [setWB, List.getElem_map, gCopy]
    exact href i _
  have hR := loopR A k B l3 (by rw [hl3len]; exact hNpos) (by rw [hl3len]; exact hMk) hfst3 hbb3
  refine ⟨?_, ?_⟩
  · have h := Prog.Reach.step hs1 (Prog.Reach.trans (prog A) hL (Prog.Reach.step hs3 hR))
    convert h using 1
    simp only [hc1, hc3, hl1len, loopLRes_length, hl3len]
    ring
  · intro i h u
    have hi : i < l.length := by rw [axisRes_length] at h; exact h
    rw [axisRes_win A k B l i hi u, offZ_succ, off_cast]
    have hm1 : (i + B * (l.length - 1)) % l.length < l.length := Nat.mod_lt _ hNpos
    have hm2 : (i + B) % l.length < l.length := Nat.mod_lt _ hNpos
    by_cases h0 : u k = 0
    · rw [if_pos h0, if_pos h0, List.getD_eq_getElem _ _ hm1, hgw _ hm1 u, natCast_mod_sub _ _ _ hNpos]
      congr 1
      rw [hB]; push_cast; ring
    · rw [if_neg h0, if_neg h0]
      by_cases h2 : u k = 2
      · rw [if_pos h2, if_pos h2, List.getD_eq_getElem _ _ hm2, hgw _ hm2 u, natCast_mod_add]
        congr 1
        rw [hB]; push_cast; ring
      · rw [if_neg h2, if_neg h2, hgw i hi u]
        congr 1
        ring

/-! ### All axes, `app`, `rnd` -/

/-- Instruction at the start of axis `k` (`app` after the last axis). -/
def axisIns (k : ℕ) : Ins d := if h : k < d + 1 then .lcopy ⟨k, h⟩ else .app

theorem axisIns_zero : axisIns (d := d) 0 = .lcopy 0 := by
  simp only [axisIns, dif_pos (Nat.succ_pos d)]
  rfl

theorem axisIns_last : axisIns (d := d) (d + 1) = .app := by
  simp [axisIns]

theorem core_eq_iff (a b : Cell A.S d) :
    core A a = core A b ↔ a.inp = b.inp ∧ a.fst = b.fst ∧ a.cnt = b.cnt ∧ a.gm = b.gm ∧
      a.rp = b.rp ∧ a.ptr = b.ptr ∧ a.mv = b.mv ∧ a.ref = b.ref ∧ a.cur = b.cur := by
  simp only [core, Prod.mk.injEq]

/-- **The axes `k, …, d`.** -/
theorem axes_run (N M : ℕ) (hM : 1 ≤ M) (hNpos : 0 < N) (hMd : M ^ d < N) (cz : ZMod N → A.S) :
    ∀ (m k : ℕ), k + m = d + 1 → ∀ (l : L A) (hN : l.length = N),
    (∀ i (h : i < l.length), l[i].fst = decide (i = 0)) →
    (∀ i (h : i < l.length) (j : Fin (d + 1)), l[i].ref j.castSucc = decide (i = M ^ j.val)) →
    GW A N M cz k l →
    ∃ (l' : L A) (c : ℕ), (prog A).Reach (axisIns k, l) (.app, l') c ∧
      c ≤ m * ((4 * M ^ d + 4) * (2 * N + 2)) ∧
      ∃ hlen : l'.length = N, (∀ i (h : i < l.length), core A (l'[i]'(by rw [hlen, ← hN]; exact h)) = core A l[i]) ∧
        GW A N M cz (d + 1) l'
  | 0, k, hkm, l, hN, _, _, hgw => by
    have hk : k = d + 1 := by omega
    subst hk
    refine ⟨l, 0, ?_, by simp, hN, fun i h => rfl, hgw⟩
    rw [axisIns_last]
    exact Prog.Reach.refl _
  | m + 1, k, hkm, l, hN, hfst, href, hgw => by
    have hk : k < d + 1 := by omega
    have hMk : M ^ k < N := lt_of_le_of_lt (Nat.pow_le_pow_right hM (by omega)) hMd
    obtain ⟨hR1, hgw1⟩ := axis_step A ⟨k, hk⟩ N M l hN hNpos hMk hfst (fun i h => href i h ⟨k, hk⟩) cz hgw
    set l1 := axisRes A ⟨k, hk⟩ (M ^ k) l with hl1
    have hl1len : l1.length = l.length := axisRes_length A _ _ l
    have hcore1 : ∀ i (h : i < l.length), core A (l1[i]'(by omega)) = core A l[i] :=
      fun i h => axisRes_core A _ _ l i h
    have hfst1 : ∀ i (h : i < l1.length), l1[i].fst = decide (i = 0) := by
      intro i h
      rw [((core_eq_iff A _ _).1 (hcore1 i (by omega))).2.1]
      exact hfst i _
    have href1 : ∀ i (h : i < l1.length) (j : Fin (d + 1)), l1[i].ref j.castSucc = decide (i = M ^ j.val) := by
      intro i h j
      rw [((core_eq_iff A _ _).1 (hcore1 i (by omega))).2.2.2.2.2.2.2.1]
      exact href i _ j
    obtain ⟨l', c, hR2, hc2, hlen', hcore2, hgw2⟩ :=
      axes_run N M hM hNpos hMd cz m (k + 1) (by omega) l1 (by rw [hl1len]; exact hN) hfst1 href1 hgw1
    refine ⟨l', (4 * M ^ k + 4) * (2 * N + 2) + c, ?_, ?_, hlen', ?_, hgw2⟩
    · have hR1' : (prog A).Reach (axisIns k, l) (axisIns (k + 1), l1) ((4 * M ^ k + 4) * (2 * N + 2)) := by
        have hk' : axisIns (d := d) k = .lcopy ⟨k, hk⟩ := by simp [axisIns, hk]
        rw [hk']
        by_cases h1 : k + 1 < d + 1
        · have e1 : nextAxis (⟨k, hk⟩ : Fin (d + 1)) = some ⟨k + 1, h1⟩ := by simp [nextAxis, h1]
          have e2 : axisIns (d := d) (k + 1) = .lcopy ⟨k + 1, h1⟩ := by simp [axisIns, h1]
          rw [e1] at hR1
          rw [e2]
          exact hR1
        · have e1 : nextAxis (⟨k, hk⟩ : Fin (d + 1)) = none := by simp [nextAxis, h1]
          have e2 : axisIns (d := d) (k + 1) = .app := by simp [axisIns, h1]
          rw [e1] at hR1
          rw [e2]
          exact hR1
      exact Prog.Reach.trans (prog A) hR1' hR2
    · have : M ^ k ≤ M ^ d := Nat.pow_le_pow_right hM (by omega)
      have h2 : (4 * M ^ k + 4) * (2 * N + 2) ≤ (4 * M ^ d + 4) * (2 * N + 2) :=
        Nat.mul_le_mul_right _ (by omega)
      calc (4 * M ^ k + 4) * (2 * N + 2) + c
          ≤ (4 * M ^ d + 4) * (2 * N + 2) + m * ((4 * M ^ d + 4) * (2 * N + 2)) := Nat.add_le_add h2 hc2
        _ = (m + 1) * ((4 * M ^ d + 4) * (2 * N + 2)) := by ring
    · intro i h
      rw [hcore2 i (by omega), hcore1 i h]

theorem rpRight_get (l : L A) (i : ℕ) (h : i < l.length) :
    (rpRight A l)[i]'(by rw [rpRight_length]; exact h) =
      {l[i] with rp := if h' : 0 < i ∧ i - 1 < l.length then l[i - 1].rp else false} := by
  simp [rpRight]

/-! ### The invariant at `chk` -/

/-- **Invariant at `chk`** for horizon `G` after `t` simulated rounds. -/
structure Inv (x : List Bool) (G t : ℕ) (l : L A) : Prop where
  len : l.length = base x G ^ (d + 1) + 1
  ht : t ≤ G
  inp : ∀ i (h : i < l.length), l[i].inp = x[i]?
  fst : ∀ i (h : i < l.length), l[i].fst = decide (i = 0)
  cnt : ∀ i (h : i < l.length), l[i].cnt = decide (i < base x G)
  gm : ∀ i (h : i < l.length), l[i].gm = decide (i ≤ G)
  rp : ∀ i (h : i < l.length), l[i].rp = decide (i = t)
  ptr : ∀ i (h : i < l.length), l[i].ptr = decide (i = 0)
  mv : ∀ i (h : i < l.length), l[i].mv = decide (i = 0)
  ref : ∀ i (h : i < l.length) (k : Fin (d + 2)), l[i].ref k = decide (i = base x G ^ k.val)
  cur : ∀ i (h : i < l.length),
    l[i].cur = A.crun l.length (base x G) (A.cinit l.length x) t (i : ZMod l.length)

theorem base_ge (x : List Bool) (G : ℕ) : G + 3 ≤ base x G := by
  unfold base; omega

theorem pow_ge (M : ℕ) (hM : 1 ≤ M) (d : ℕ) : M ≤ M ^ (d + 1) := by
  calc M = M ^ 1 := (pow_one M).symm
    _ ≤ M ^ (d + 1) := Nat.pow_le_pow_right hM (by omega)

theorem Inv.len_gt {x : List Bool} {G t : ℕ} {l : L A} (hI : Inv A x G t l) : base x G < l.length := by
  have := pow_ge (base x G) (by have := base_ge x G; omega) d
  rw [hI.len]; omega

/-- **One simulated round**, `chk → spread → axes → app → rnd → chk`. -/
theorem round (x : List Bool) (G t : ℕ) (l : L A) (hI : Inv A x G t l) (htG : t < G)
    (hans : arrAns A l = none) :
    ∃ (l' : L A) (c : ℕ), (prog A).Reach (.chk, l) (.chk, l') c ∧
      c ≤ (d + 5) * ((4 * base x G ^ d + 4) * (2 * l.length + 2)) ∧ Inv A x G (t + 1) l' := by
  set M := base x G with hMdef
  set N := l.length with hNdef
  have hM3 : 3 ≤ M := by have := base_ge x G; omega
  have hMN : M < N := hI.len_gt
  have hNpos : 0 < N := by omega
  have hlenM : N = M ^ (d + 1) + 1 := hI.len
  have hMd : M ^ d < N := by
    have := Nat.pow_le_pow_right (show 1 ≤ M by omega) (show d ≤ d + 1 by omega)
    omega
  have hGN : G + 1 < N := by have := base_ge x G; omega
  -- chk
  have hs0 : (prog A).stepP (.chk, l) = .inl (.spread, l) := by
    rw [(step_chk A l G t hGN hI.ht hI.gm hI.rp).1, hans]
    simp [show t ≠ G by omega]
  have hc0 := (step_chk A l G t hGN hI.ht hI.gm hI.rp).2
  -- spread
  obtain ⟨hs1, hc1⟩ := step_spread A l
  set cz := A.crun N M (A.cinit N x) t with hcz
  set l0 := l.map (gSpread A) with hl0
  have hl0len : l0.length = N := by simp [hl0, hNdef]
  have hgw0 : GW A N M cz 0 l0 := by
    intro i h u
    simp only [hl0, List.getElem_map, gSpread, offZ_zero, add_zero]
    exact hI.cur i _
  have hfst0 : ∀ i (h : i < l0.length), l0[i].fst = decide (i = 0) := by
    intro i h; simp only [hl0, List.getElem_map, gSpread]; exact hI.fst i _
  have href0 : ∀ i (h : i < l0.length) (j : Fin (d + 1)), l0[i].ref j.castSucc = decide (i = M ^ j.val) := by
    intro i h j; simp only [hl0, List.getElem_map, gSpread]; exact hI.ref i _ j.castSucc
  obtain ⟨lAx, cAx, hRAx, hcAx, hlenAx, hcoreAx, hgwAx⟩ :=
    axes_run A N M (by omega) hNpos hMd cz (d + 1) 0 (by omega) l0 hl0len hfst0 href0 hgw0
  rw [axisIns_zero] at hRAx
  -- app, rnd
  obtain ⟨hs2, hc2⟩ := step_app A lAx
  obtain ⟨hs3, hc3⟩ := step_rnd A (lAx.map (gApp A))
  set l4 := rpRight A (lAx.map (gApp A)) with hl4
  have hl4len : l4.length = N := by simp [hl4, rpRight_length, hlenAx]
  refine ⟨l4, _, Prog.Reach.step hs0 (Prog.Reach.step hs1 (Prog.Reach.trans (prog A) hRAx
    (Prog.Reach.step hs2 (Prog.Reach.single (prog A) hs3)))), ?_, ?_⟩
  · simp only [hc0, hc1, hc2, hc3, hlenAx, List.length_map]
    have h1 : 1 ≤ 4 * M ^ d + 4 := by omega
    have h2 : 2 * N + 2 ≤ (4 * M ^ d + 4) * (2 * N + 2) := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  · -- field facts for `l4`
    have hget : ∀ i (h : i < N), ∃ h4 : i < l4.length, ∃ hA : i < lAx.length,
        l4[i]'h4 = {gApp A (lAx[i]'hA) with
          rp := if h' : 0 < i ∧ i - 1 < lAx.length then (lAx[i - 1]'h'.2).rp else false} := by
      intro i h
      refine ⟨by omega, by omega, ?_⟩
      simp only [hl4]
      rw [rpRight_get A _ i (by simp [hlenAx]; omega)]
      simp only [List.getElem_map, List.length_map]
      rfl
    have hcore : ∀ i (h : i < N), core A (lAx[i]'(by omega)) = core A l[i] := by
      intro i h
      rw [hcoreAx i (by simp [hl0]; omega)]
      simp only [hl0, List.getElem_map, core_gSpread]
    refine ⟨by rw [hl4len, hNdef, hI.len], by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i h
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he]
      simp only [gApp]
      rw [((core_eq_iff A _ _).1 (hcore i (by omega))).1]
      exact hI.inp i _
    · intro i h
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he]
      simp only [gApp]
      rw [((core_eq_iff A _ _).1 (hcore i (by omega))).2.1]
      exact hI.fst i _
    · intro i h
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he]
      simp only [gApp]
      rw [((core_eq_iff A _ _).1 (hcore i (by omega))).2.2.1]
      exact hI.cnt i _
    · intro i h
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he]
      simp only [gApp]
      rw [((core_eq_iff A _ _).1 (hcore i (by omega))).2.2.2.1]
      exact hI.gm i _
    · intro i h
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he]
      by_cases hi : 0 < i
      · rw [dif_pos ⟨hi, by omega⟩, ((core_eq_iff A _ _).1 (hcore (i - 1) (by omega))).2.2.2.2.1,
          hI.rp (i - 1) _]
        exact decide_iff_eq (by omega)
      · rw [dif_neg (fun h' => hi h'.1)]
        exact (decide_eq_false (by omega)).symm
    · intro i h
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he]
      simp only [gApp]
      rw [((core_eq_iff A _ _).1 (hcore i (by omega))).2.2.2.2.2.1]
      exact hI.ptr i _
    · intro i h
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he]
      simp only [gApp]
      rw [((core_eq_iff A _ _).1 (hcore i (by omega))).2.2.2.2.2.2.1]
      exact hI.mv i _
    · intro i h k
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he]
      simp only [gApp]
      rw [((core_eq_iff A _ _).1 (hcore i (by omega))).2.2.2.2.2.2.2.1]
      exact hI.ref i _ k
    · intro i h
      obtain ⟨h4, hA, he⟩ := hget i (by omega)
      rw [he, hl4len]
      simp only [gApp]
      rw [A.crun_succ, cstep]
      congr 1
      funext v
      rw [hgwAx i hA, offZ_full]

end PVNP.Discrete.WCCDSweep
