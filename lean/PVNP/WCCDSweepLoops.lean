import PVNP.WCCDSweepSteps

/-!
# D-1: count-down loops of the WCCD sweep program

`loopL`, `loopR`: starting with the count-down marker `bb` at cell `B`, the
`lchk/lmov` (resp. `rchkR/rmovR`) loop rotates the selected window tracks
cyclically left (resp. right) by exactly `B` cells, returns `bb` to cell `0`
and exits, at exact cost `(2B + 1)(2N + 2)`.
-/

namespace PVNP.Discrete.WCCDSweep

open PVNP.Discrete PVNP.Discrete.Sweep

variable {d : ℕ} (A : WCCD d)

theorem winSel_self (k : Fin (d + 1)) (c : Fin 3) (w : Nb d → A.S) : winSel A k c w w = w := by
  funext u; simp [winSel]

theorem winSel_winSel (k : Fin (d + 1)) (c : Fin 3) (X Y Z W : Nb d → A.S) :
    winSel A k c (winSel A k c X Y) (winSel A k c Z W) = winSel A k c X W := by
  funext u; simp only [winSel]; split_ifs <;> rfl

theorem rotL_get (k : Fin (d + 1)) (l : L A) (i : ℕ) (h : i < l.length) :
    (rotL A k l)[i]'(by rw [rotL_length]; exact h) =
      {l[i] with win := winSel A k 2 (l.getD ((i + 1) % l.length) (dflt A)).win l[i].win} := by
  simp [rotL]

theorem rotR_get (k : Fin (d + 1)) (l : L A) (i : ℕ) (h : i < l.length) :
    (rotR A k l)[i]'(by rw [rotR_length]; exact h) =
      {l[i] with win := winSel A k 0 (l.getD ((i + l.length - 1) % l.length) (dflt A)).win l[i].win} := by
  simp [rotR]

theorem bbLeft_get' (l : L A) (i : ℕ) (h : i < l.length) :
    (bbLeft A l)[i]'(by rw [bbLeft_length]; exact h) =
      {l[i] with bb := if h' : i + 1 < l.length then l[i + 1].bb else false} := by
  simp [bbLeft]

/-- Update the window and the count-down marker of a cell. -/
def setWB (a : Cell A.S d) (w : Nb d → A.S) (b : Bool) : Cell A.S d := {a with win := w, bb := b}

/-- Result of the left loop: selected tracks rotated left by `B`, `bb` at `0`. -/
def loopLRes (k : Fin (d + 1)) (B : ℕ) (l : L A) : L A :=
  l.mapIdx fun i a => setWB A a (winSel A k 2 (l.getD ((i + B) % l.length) (dflt A)).win a.win) (decide (i = 0))

/-- Result of the right loop: selected tracks rotated right by `B`, `bb` at `0`. -/
def loopRRes (k : Fin (d + 1)) (B : ℕ) (l : L A) : L A :=
  l.mapIdx fun i a =>
    setWB A a (winSel A k 0 (l.getD ((i + B * (l.length - 1)) % l.length) (dflt A)).win a.win) (decide (i = 0))

theorem loopLRes_length (k : Fin (d + 1)) (B : ℕ) (l : L A) : (loopLRes A k B l).length = l.length := by
  simp [loopLRes]

theorem loopRRes_length (k : Fin (d + 1)) (B : ℕ) (l : L A) : (loopRRes A k B l).length = l.length := by
  simp [loopRRes]

theorem cell_eq_of_bb (a : Cell A.S d) (b : Bool) (h : a.bb = b) : {a with bb := b} = a := by
  subst h; rfl

/-- **Left count-down loop.** -/
theorem loopL (k : Fin (d + 1)) : ∀ (B : ℕ) (l : L A), 0 < l.length → B < l.length →
    (∀ j (h : j < l.length), l[j].fst = decide (j = 0)) →
    (∀ j (h : j < l.length), l[j].bb = decide (j = B)) →
    (prog A).Reach (.lchk k, l) (.rcopyR k, loopLRes A k B l) ((2 * B + 1) * (2 * l.length + 2))
  | 0, l, hl, _, hfst, hbb => by
    have hbb0 : l[0].bb = true := by rw [hbb 0 hl]; simp
    obtain ⟨hs, hc⟩ := step_lchk_done A k l hl hfst hbb0
    have hres : loopLRes A k 0 l = l := by
      apply List.ext_getElem (by simp [loopLRes])
      intro i h1 h2
      simp only [loopLRes, List.getElem_mapIdx, Nat.add_zero, Nat.mod_eq_of_lt h2,
        List.getD_eq_getElem _ _ h2, winSel_self, setWB]
      rw [← hbb i h2]
    rw [hres]
    have h := Prog.Reach.single (prog A) hs
    simp only [hc] at h
    simpa using h
  | B + 1, l, hl, hB, hfst, hbb => by
    have hbb0 : l[0].bb = false := by rw [hbb 0 hl]; simp
    obtain ⟨hs1, hc1⟩ := step_lchk_rot A k l hl hfst hbb0
    obtain ⟨hs2, hc2⟩ := step_lmov A k (rotL A k l)
    have hlen' : (bbLeft A (rotL A k l)).length = l.length := by
      rw [bbLeft_length, rotL_length]
    have hget : ∀ i (h : i < l.length), (bbLeft A (rotL A k l))[i]'(by rw [hlen']; exact h) =
        setWB A l[i] (winSel A k 2 (l.getD ((i + 1) % l.length) (dflt A)).win l[i].win) (decide (i = B)) := by
      intro i h
      rw [bbLeft_get' A _ i (by rw [rotL_length]; exact h), rotL_get A k l i h]
      by_cases hi : i + 1 < l.length
      · rw [dif_pos (by rw [rotL_length]; exact hi), rotL_get A k l (i + 1) hi, hbb (i + 1) hi]
        simp [setWB]
      · rw [dif_neg (by rw [rotL_length]; exact hi)]
        simp only [show ¬ (i = B) by omega, decide_false, setWB]
    have hfst' : ∀ j (h : j < (bbLeft A (rotL A k l)).length),
        (bbLeft A (rotL A k l))[j].fst = decide (j = 0) := by
      intro j h
      rw [hget j (by omega)]
      exact hfst j (by omega)
    have hbb' : ∀ j (h : j < (bbLeft A (rotL A k l)).length),
        (bbLeft A (rotL A k l))[j].bb = decide (j = B) := by
      intro j h
      rw [hget j (by omega)]
      rfl
    have ih := loopL k B (bbLeft A (rotL A k l)) (by omega) (by omega) hfst' hbb'
    have hres : loopLRes A k B (bbLeft A (rotL A k l)) = loopLRes A k (B + 1) l := by
      apply List.ext_getElem (by simp [loopLRes, hlen'])
      intro i h1 h2
      have hi : i < l.length := by simpa [loopLRes] using h2
      simp only [loopLRes, List.getElem_mapIdx, hlen']
      have hj : (i + B) % l.length < l.length := Nat.mod_lt _ hl
      rw [List.getD_eq_getElem _ _ (by rw [hlen']; exact hj), hget _ hj, hget i hi]
      simp only [setWB]
      rw [winSel_winSel]
      have hmod : ((i + B) % l.length + 1) % l.length = (i + (B + 1)) % l.length := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
      rw [hmod]
    have h := Prog.Reach.step hs1 (Prog.Reach.step hs2 ih)
    rw [hres] at h
    convert h using 1
    simp only [hc1, hc2, hlen', rotL_length]
    ring

/-- **Right count-down loop.** -/
theorem loopR (k : Fin (d + 1)) : ∀ (B : ℕ) (l : L A), 0 < l.length → B < l.length →
    (∀ j (h : j < l.length), l[j].fst = decide (j = 0)) →
    (∀ j (h : j < l.length), l[j].bb = decide (j = B)) →
    (prog A).Reach (.rchkR k, l)
      ((match nextAxis k with | some k' => .lcopy k' | none => .app), loopRRes A k B l)
      ((2 * B + 1) * (2 * l.length + 2))
  | 0, l, hl, _, hfst, hbb => by
    have hbb0 : l[0].bb = true := by rw [hbb 0 hl]; simp
    obtain ⟨hs, hc⟩ := step_rchkR_done A k l hl hfst hbb0
    have hres : loopRRes A k 0 l = l := by
      apply List.ext_getElem (by simp [loopRRes])
      intro i h1 h2
      simp only [loopRRes, List.getElem_mapIdx, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt h2,
        List.getD_eq_getElem _ _ h2, winSel_self, setWB]
      rw [← hbb i h2]
    rw [hres]
    have h := Prog.Reach.single (prog A) hs
    simp only [hc] at h
    simpa using h
  | B + 1, l, hl, hB, hfst, hbb => by
    have hbb0 : l[0].bb = false := by rw [hbb 0 hl]; simp
    obtain ⟨hs1, hc1⟩ := step_rchkR_rot A k l hl hfst hbb0
    obtain ⟨hs2, hc2⟩ := step_rmovR A k (rotR A k l)
    have hlen' : (bbLeft A (rotR A k l)).length = l.length := by
      rw [bbLeft_length, rotR_length]
    have hget : ∀ i (h : i < l.length), (bbLeft A (rotR A k l))[i]'(by rw [hlen']; exact h) =
        setWB A l[i] (winSel A k 0 (l.getD ((i + l.length - 1) % l.length) (dflt A)).win l[i].win) (decide (i = B)) := by
      intro i h
      rw [bbLeft_get' A _ i (by rw [rotR_length]; exact h), rotR_get A k l i h]
      by_cases hi : i + 1 < l.length
      · rw [dif_pos (by rw [rotR_length]; exact hi), rotR_get A k l (i + 1) hi, hbb (i + 1) hi]
        simp [setWB]
      · rw [dif_neg (by rw [rotR_length]; exact hi)]
        simp only [show ¬ (i = B) by omega, decide_false, setWB]
    have hfst' : ∀ j (h : j < (bbLeft A (rotR A k l)).length),
        (bbLeft A (rotR A k l))[j].fst = decide (j = 0) := by
      intro j h
      rw [hget j (by omega)]
      exact hfst j (by omega)
    have hbb' : ∀ j (h : j < (bbLeft A (rotR A k l)).length),
        (bbLeft A (rotR A k l))[j].bb = decide (j = B) := by
      intro j h
      rw [hget j (by omega)]
      rfl
    have ih := loopR k B (bbLeft A (rotR A k l)) (by omega) (by omega) hfst' hbb'
    have hres : loopRRes A k B (bbLeft A (rotR A k l)) = loopRRes A k (B + 1) l := by
      apply List.ext_getElem (by simp [loopRRes, hlen'])
      intro i h1 h2
      have hi : i < l.length := by simpa [loopRRes] using h2
      simp only [loopRRes, List.getElem_mapIdx, hlen']
      have hj : (i + B * (l.length - 1)) % l.length < l.length := Nat.mod_lt _ hl
      rw [List.getD_eq_getElem _ _ (by rw [hlen']; exact hj), hget _ hj, hget i hi]
      simp only [setWB]
      rw [winSel_winSel]
      have hmod : ((i + B * (l.length - 1)) % l.length + l.length - 1) % l.length =
          (i + (B + 1) * (l.length - 1)) % l.length := by
        rw [show (i + B * (l.length - 1)) % l.length + l.length - 1 =
            (i + B * (l.length - 1)) % l.length + (l.length - 1) by omega,
          Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1
        ring
      rw [hmod]
    have h := Prog.Reach.step hs1 (Prog.Reach.step hs2 ih)
    rw [hres] at h
    convert h using 1
    simp only [hc1, hc2, hlen', rotR_length]
    ring

end PVNP.Discrete.WCCDSweep
