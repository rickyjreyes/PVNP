import PVNP.PartIIUniform
import PVNP.SweepTM

/-!
# Milestone 5, part 1: generic sweep lemmas and the folded Turing-machine step

Infrastructure for the simulation `P^{disc}_{WCC} ⊆ P_TM` of the uniform model
`PVNP.PartIIUniform.UWCC`.  Everything is phrased for the round-trip sweep programs of
`PVNP.Discrete.Sweep`, which `Prog.toTM` compiles to ordinary single-tape machines with exact step
accounting (`Prog.toTM_firstAnswer`).

* `fscan_getElem`, `fscan_take_succ`, `bscan_getElem`, `bscan_drop_snd`: a forward (backward)
  transduction is determined cell by cell by the buffer after the prefix (suffix).
* `RN`: reachability counting round trips; `RN.reach` bounds the exact cost by
  `k · (2ℓ + 3)` with `ℓ` the final length (round trips never shorten the list).
* `Lens`: a track of a data cell.
* `FCell`, `FRep`, `simF`, `simB`: the **folded** representation of a Turing-machine tape on a
  track (cell `j` holds the symbols at `j` and `−j−1`), and one machine step as one round trip.
  `simTrip_spec` proves that the round trip performs exactly `MTM.step` of the manuscript
  machine (`def:tm`), changes only the track, and extends the list by at most one cell.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring

/-! ## Cellwise characterization of scans -/

section Scan

variable {D B : Type}

theorem fscan_take_succ (f : B → D → D × B) :
    ∀ (b : B) (l : List D) (j : ℕ) (hj : j < l.length),
      (fscan f b (l.take (j + 1))).2 = (f (fscan f b (l.take j)).2 l[j]).2
  | b, a :: l, 0, _ => by simp [fscan]
  | b, a :: l, j + 1, hj => by
    simp only [List.take_succ_cons, fscan, List.getElem_cons_succ]
    exact fscan_take_succ f _ l j (by simp at hj; omega)

theorem fscan_getElem (f : B → D → D × B) :
    ∀ (b : B) (l : List D) (j : ℕ) (hj : j < l.length),
      (fscan f b l).1[j]'(by rw [fscan_length]; exact hj) = (f (fscan f b (l.take j)).2 l[j]).1
  | b, a :: l, 0, _ => by simp [fscan]
  | b, a :: l, j + 1, hj => by
    simp only [fscan, List.getElem_cons_succ, List.take_succ_cons]
    exact fscan_getElem f _ l j (by simp at hj; omega)

theorem fscan_snd_eq_take (f : B → D → D × B) (b : B) (l : List D) :
    (fscan f b l).2 = (fscan f b (l.take l.length)).2 := by rw [List.take_length]

theorem bscan_getElem (f : B → D → D × B) :
    ∀ (b : B) (l : List D) (j : ℕ) (hj : j < l.length),
      (bscan f b l).1[j]'(by rw [bscan_length]; exact hj) =
        (f (bscan f b (l.drop (j + 1))).2 l[j]).1
  | b, a :: l, 0, _ => by simp [bscan]
  | b, a :: l, j + 1, hj => by
    simp only [bscan, List.getElem_cons_succ, List.drop_succ_cons]
    exact bscan_getElem f b l j (by simp at hj; omega)

theorem bscan_drop_snd (f : B → D → D × B) :
    ∀ (b : B) (l : List D) (j : ℕ) (hj : j < l.length),
      (bscan f b (l.drop j)).2 = (f (bscan f b (l.drop (j + 1))).2 l[j]).2
  | b, a :: l, 0, _ => by simp [bscan]
  | b, a :: l, j + 1, hj => by
    simp only [List.drop_succ_cons, List.getElem_cons_succ]
    exact bscan_drop_snd f b l j (by simp at hj; omega)

theorem bscan_drop_length (f : B → D → D × B) (b : B) (l : List D) :
    (bscan f b (l.drop l.length)).2 = b := by simp [bscan]

end Scan

/-! ## Round trips counted -/

section Counted

variable (P : Prog)

/-- `RN P s s' k`: the program goes from `s` to `s'` in exactly `k` round trips. -/
inductive RN : P.I × List P.D → P.I × List P.D → ℕ → Prop
  | refl (s : P.I × List P.D) : RN s s 0
  | step {s s' s'' : P.I × List P.D} {k : ℕ} : P.stepP s = .inl s' → RN s' s'' k → RN s s'' (k + 1)

variable {P}

theorem RN.trans {s s' s'' : P.I × List P.D} {k k' : ℕ} (h : RN P s s' k) (h' : RN P s' s'' k') :
    RN P s s'' (k + k') := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => rw [Nat.add_right_comm]; exact .step hs (ih h')

theorem RN.single {s s' : P.I × List P.D} (h : P.stepP s = .inl s') : RN P s s' 1 :=
  .step h (.refl s')

theorem trip_fst_length (i : P.I) (l : List P.D) :
    (P.trip i l).1.length = l.length + (P.ext i (P.fpass i l).2).toList.length := by
  simp [Prog.trip, Prog.mid, bscan_length, Prog.fpass, fscan_length]

theorem stepP_inl {s s' : P.I × List P.D} (h : P.stepP s = .inl s') :
    s'.2 = (P.trip s.1 s.2).1 := by
  obtain ⟨i, l⟩ := s
  simp only [Prog.stepP] at h
  split at h
  · simp only [Sum.inl.injEq] at h; subst h; rfl
  · simp at h

theorem RN.length_le {s s' : P.I × List P.D} {k : ℕ} (h : RN P s s' k) :
    s.2.length ≤ s'.2.length := by
  induction h with
  | refl => exact le_rfl
  | step hs _ ih =>
    rw [stepP_inl hs] at ih
    exact le_trans (P.trip_length _ _) ih

theorem RN.length_le_add {s s' : P.I × List P.D} {k : ℕ} (h : RN P s s' k) :
    s'.2.length ≤ s.2.length + k := by
  induction h with
  | refl => simp
  | @step s s₁ s₂ k hs _ ih =>
    rw [stepP_inl hs, trip_fst_length] at ih
    have : (P.ext s.1 (P.fpass s.1 s.2).2).toList.length ≤ 1 := by
      cases P.ext s.1 (P.fpass s.1 s.2).2 <;> simp
    omega

/-- The exact cost of `k` round trips is at most `k · (2ℓ + 3)`, `ℓ` the final length. -/
theorem RN.reach {s s' : P.I × List P.D} {k : ℕ} (h : RN P s s' k) :
    ∃ c, P.Reach s s' c ∧ c ≤ k * (2 * s'.2.length + 3) := by
  induction h with
  | refl s => exact ⟨0, .refl s, by simp⟩
  | @step s s₁ s₂ k hs hr ih =>
    obtain ⟨c, hc, hle⟩ := ih
    refine ⟨P.tripCost s.1 s.2 + c, .step hs hc, ?_⟩
    have h1 := hr.length_le
    rw [stepP_inl hs, trip_fst_length] at h1
    have he : (P.ext s.1 (P.fpass s.1 s.2).2).toList.length ≤ 1 := by
      cases P.ext _ _ <;> simp
    have hcost : P.tripCost s.1 s.2 ≤ 2 * s₂.2.length + 3 := by
      unfold Prog.tripCost
      simp only [Prog.fpass] at he h1 ⊢
      omega
    calc P.tripCost s.1 s.2 + c ≤ (2 * s₂.2.length + 3) + k * (2 * s₂.2.length + 3) :=
          Nat.add_le_add hcost hle
      _ = (k + 1) * (2 * s₂.2.length + 3) := by ring

/-- A final halting round trip after `k` counted trips. -/
theorem RN.halts {s s' : P.I × List P.D} {k : ℕ} (h : RN P s s' k) {a : Bool} {l : List P.D}
    (hf : P.stepP s' = .inr (a, l)) :
    ∃ c, P.Halts s a c ∧ c ≤ (k + 1) * (2 * s'.2.length + 3) := by
  obtain ⟨c, hc, hle⟩ := h.reach
  refine ⟨c + P.tripCost s'.1 s'.2, ?_, ?_⟩
  · have h2 : P.Halts s' a (P.tripCost s'.1 s'.2) := .last hf
    exact Prog.Reach.halts P hc h2
  · have he : (P.ext s'.1 (P.fpass s'.1 s'.2).2).toList.length ≤ 1 := by
      cases P.ext _ _ <;> simp
    have hcost : P.tripCost s'.1 s'.2 ≤ 2 * s'.2.length + 3 := by
      unfold Prog.tripCost; simp only [Prog.fpass] at he ⊢; omega
    calc c + P.tripCost s'.1 s'.2 ≤ k * (2 * s'.2.length + 3) + (2 * s'.2.length + 3) :=
          Nat.add_le_add hle hcost
      _ = (k + 1) * (2 * s'.2.length + 3) := by ring

end Counted

/-! ## Tracks -/

/-- A track of a data cell. -/
structure Lens (C T : Type) where
  get : C → T
  set : T → C → C
  get_set : ∀ t c, get (set t c) = t
  set_get : ∀ c, set (get c) c = c
  set_set : ∀ t t' c, set t (set t' c) = set t c

/-! ## Folded Turing-machine tapes -/

/-- A folded tape cell: `r` is the symbol at position `j`, `l` the symbol at `−j−1`.  `hd` marks
the head (`some true`: at `j`; `some false`: at `−j−1`); `pl` marks a pending left move. -/
structure FCell (Γ : Type) where
  r : Γ
  l : Γ
  hd : Option Bool
  pl : Option Bool
  deriving DecidableEq

instance (Γ : Type) [Fintype Γ] : Fintype (FCell Γ) :=
  Fintype.ofEquiv (Γ × Γ × Option Bool × Option Bool)
    ⟨fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩, fun c => (c.r, c.l, c.hd, c.pl),
      fun _ => rfl, fun _ => rfl⟩

/-- The head marker of data cell `j` for head position `h`. -/
def headAt (h : ℤ) (j : ℕ) : Option Bool :=
  if h = j then some true else if h = -(j : ℤ) - 1 then some false else none

/-- `l` represents the tape `T` with head at `h` on the track `get`. -/
structure FRep {C Γ : Type} (get : C → FCell Γ) (blank : Γ) (l : List C) (T : ℤ → Γ) (h : ℤ) :
    Prop where
  cell : ∀ (j : ℕ) (hj : j < l.length), get l[j] = ⟨T j, T (-(j : ℤ) - 1), headAt h j, none⟩
  out : ∀ i : ℤ, ((l.length : ℤ) ≤ i ∨ i < -(l.length : ℤ)) → T i = blank
  hlo : -(l.length : ℤ) ≤ h
  hhi : h < l.length

/-- Data index of a head position. -/
def hidx (h : ℤ) : ℕ := if 0 ≤ h then h.toNat else (-h - 1).toNat

/-- Side of a head position (`true`: right half). -/
def hside (h : ℤ) : Bool := decide (0 ≤ h)

theorem headAt_eq (h : ℤ) (j : ℕ) :
    headAt h j = if j = hidx h then some (hside h) else none := by
  unfold headAt hidx hside
  by_cases h0 : 0 ≤ h
  · have : ¬ h = -(j : ℤ) - 1 := by omega
    by_cases hj : h = j
    · rw [if_pos hj, if_pos h0, if_pos (by omega), decide_eq_true h0]
    · rw [if_neg hj, if_neg this, if_pos h0, if_neg (by omega)]
  · have : ¬ h = (j : ℤ) := by omega
    rw [if_neg this, if_neg h0, decide_eq_false h0]
    by_cases hj : h = -(j : ℤ) - 1
    · rw [if_pos hj, if_pos (by omega)]
    · rw [if_neg hj, if_neg (by omega)]

theorem hidx_lt {h : ℤ} {ℓ : ℕ} (hlo : -(ℓ : ℤ) ≤ h) (hhi : h < ℓ) : hidx h < ℓ := by
  unfold hidx; split_ifs <;> omega

/-- Buffer of a simulated step. -/
structure SimBuf (Q : Type) where
  first : Bool
  pend : Option Bool
  nq : Option Q
  pendL : Option Bool
  deriving DecidableEq

instance (Q : Type) [Fintype Q] : Fintype (SimBuf Q) :=
  Fintype.ofEquiv (Bool × Option Bool × Option Q × Option Bool)
    ⟨fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩, fun c => (c.first, c.pend, c.nq, c.pendL),
      fun _ => rfl, fun _ => rfl⟩

/-- The initial buffer of a simulated step. -/
def SimBuf.start (Q : Type) : SimBuf Q := ⟨true, none, none, none⟩

/-- The head moves to the next data cell. -/
def fwdMove (s : Bool) (m : Mv) : Bool := (s && decide (m = .R)) || (!s && decide (m = .L))

/-- The symbol under a head on side `s`. -/
def FCell.read {Γ : Type} (fc : FCell Γ) (s : Bool) : Γ := if s then fc.r else fc.l

/-- Write `a` on side `s` and set the head and pending-left fields. -/
def FCell.wr {Γ : Type} (fc : FCell Γ) (s : Bool) (a : Γ) (hd pl : Option Bool) : FCell Γ :=
  if s then ⟨a, fc.l, hd, pl⟩ else ⟨fc.r, a, hd, pl⟩

/-- Forward transducer of a simulated step of `M` in state `q`. -/
def simF (M : MTM) (q : M.Q) (sb : SimBuf M.Q) (fc : FCell M.Γ) : FCell M.Γ × SimBuf M.Q :=
  match sb.pend with
  | some s => (⟨fc.r, fc.l, some s, fc.pl⟩, ⟨false, none, sb.nq, sb.pendL⟩)
  | none =>
    match fc.hd with
    | none => (fc, ⟨false, sb.pend, sb.nq, sb.pendL⟩)
    | some s =>
      if fwdMove s (M.δ q (fc.read s)).2.2 then
        (fc.wr s (M.δ q (fc.read s)).2.1 none fc.pl,
          ⟨false, some s, some (M.δ q (fc.read s)).1, sb.pendL⟩)
      else if sb.first then
        (fc.wr s (M.δ q (fc.read s)).2.1 (some (!s)) fc.pl,
          ⟨false, sb.pend, some (M.δ q (fc.read s)).1, sb.pendL⟩)
      else
        (fc.wr s (M.δ q (fc.read s)).2.1 none (some s),
          ⟨false, sb.pend, some (M.δ q (fc.read s)).1, sb.pendL⟩)

/-- Backward transducer of a simulated step: a pending left move lands on the next cell. -/
def simB {Γ Q : Type} (sb : SimBuf Q) (fc : FCell Γ) : FCell Γ × SimBuf Q :=
  match sb.pendL with
  | some s => (⟨fc.r, fc.l, some s, fc.pl⟩, ⟨sb.first, sb.pend, sb.nq, none⟩)
  | none =>
    match fc.pl with
    | some s => (⟨fc.r, fc.l, fc.hd, none⟩, ⟨sb.first, sb.pend, sb.nq, some s⟩)
    | none => (fc, sb)

section Lifted

variable {C Bf : Type} (M : MTM) (L : Lens C (FCell M.Γ)) (LB : Lens Bf (SimBuf M.Q))

/-- The forward transducer on whole cells and buffers. -/
def gF (q : M.Q) (b : Bf) (a : C) : C × Bf :=
  (L.set (simF M q (LB.get b) (L.get a)).1 a, LB.set (simF M q (LB.get b) (L.get a)).2 b)

/-- The backward transducer on whole cells and buffers. -/
def gB (b : Bf) (a : C) : C × Bf :=
  (L.set (simB (LB.get b) (L.get a)).1 a, LB.set (simB (LB.get b) (L.get a)).2 b)

/-- The extension: a fresh cell receiving the head. -/
def gE (dflt : C) (b : Bf) : Option C :=
  (LB.get b).pend.map fun s => L.set ⟨M.blank, M.blank, some s, none⟩ dflt

/-- One simulated step as a round trip. -/
def simTrip (dflt : C) (q : M.Q) (b0 : Bf) (l : List C) : List C × Bf :=
  bscan (gB M L LB) (fscan (gF M L LB q) b0 l).2
    ((fscan (gF M L LB q) b0 l).1 ++ (gE M L LB dflt (fscan (gF M L LB q) b0 l).2).toList)

end Lifted

/-! ## Correctness of one simulated step -/

section Spec

theorem fpos_hidx (h : ℤ) : (if hside h then (hidx h : ℤ) else -(hidx h : ℤ) - 1) = h := by
  unfold hside hidx
  by_cases h0 : 0 ≤ h
  · rw [decide_eq_true h0, if_pos rfl, if_pos h0]; omega
  · rw [decide_eq_false h0, if_neg (by simp), if_neg h0]; omega

/-- New data index of the head after move `m` from data cell `j`, side `s`. -/
def newIdx (j : ℕ) (s : Bool) (m : Mv) : ℕ :=
  if fwdMove s m then j + 1 else if j = 0 then 0 else j - 1

/-- New side of the head after move `m`. -/
def newSide (j : ℕ) (s : Bool) (m : Mv) : Bool :=
  if fwdMove s m then s else if j = 0 then !s else s

theorem hidx_nonneg {h : ℤ} (h0 : 0 ≤ h) : hidx h = h.toNat := by unfold hidx; rw [if_pos h0]
theorem hidx_neg {h : ℤ} (h0 : h < 0) : hidx h = (-h - 1).toNat := by
  unfold hidx; rw [if_neg (by omega)]
theorem hside_nonneg {h : ℤ} (h0 : 0 ≤ h) : hside h = true := decide_eq_true h0
theorem hside_neg {h : ℤ} (h0 : h < 0) : hside h = false := decide_eq_false (by omega)

theorem move_head (h : ℤ) (m : Mv) :
    hidx (h + m.shift) = newIdx (hidx h) (hside h) m ∧
      hside (h + m.shift) = newSide (hidx h) (hside h) m := by
  have fTL : fwdMove true .L = false := rfl
  have fTR : fwdMove true .R = true := rfl
  have fFL : fwdMove false .L = true := rfl
  have fFR : fwdMove false .R = false := rfl
  unfold newIdx newSide
  cases m with
  | L =>
    simp only [Mv.shift]
    by_cases h0 : 0 ≤ h
    · rw [hidx_nonneg h0, hside_nonneg h0]
      simp only [fTL, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : h = 0
      · subst h1; decide
      · have h2 : h.toNat ≠ 0 := by omega
        rw [hidx_nonneg (by omega), hside_nonneg (by omega), if_neg h2, if_neg h2]
        exact ⟨by omega, by simp⟩
    · rw [hidx_neg (by omega), hside_neg (by omega), hidx_neg (by omega), hside_neg (by omega)]
      simp only [fFL, ↓reduceIte]
      exact ⟨by omega, by simp⟩
  | R =>
    simp only [Mv.shift]
    by_cases h0 : 0 ≤ h
    · rw [hidx_nonneg h0, hside_nonneg h0, hidx_nonneg (by omega), hside_nonneg (by omega)]
      simp only [fTR, ↓reduceIte]
      exact ⟨by omega, by simp⟩
    · rw [hidx_neg (h := h) (by omega), hside_neg (h := h) (by omega)]
      simp only [fFR, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : h = -1
      · subst h1; decide
      · have h2 : (-h - 1).toNat ≠ 0 := by omega
        rw [hidx_neg (by omega), hside_neg (by omega), if_neg h2, if_neg h2]
        exact ⟨by omega, by simp⟩

theorem FCell.read_cell {Γ : Type} (T : ℤ → Γ) (h : ℤ) (hd pl : Option Bool) :
    (⟨T (hidx h), T (-(hidx h : ℤ) - 1), hd, pl⟩ : FCell Γ).read (hside h) = T h := by
  unfold FCell.read
  have := fpos_hidx h
  by_cases hs : hside h
  · rw [if_pos hs] at this ⊢; exact congrArg T this
  · rw [if_neg hs] at this ⊢; exact congrArg T this

variable {C Bf : Type} (M : MTM) (L : Lens C (FCell M.Γ)) (LB : Lens Bf (SimBuf M.Q)) (dflt : C)

/-- The forward buffer after a prefix of a represented tape. -/
theorem sim_fbuf (q : M.Q) (b0 : Bf) (hb0 : LB.get b0 = SimBuf.start M.Q)
    (l : List C) (T : ℤ → M.Γ) (h : ℤ) (hrep : FRep L.get M.blank l T h) :
    ∀ j ≤ l.length, LB.get (fscan (gF M L LB q) b0 (l.take j)).2 =
      ⟨decide (j = 0),
        if fwdMove (hside h) (M.δ q (T h)).2.2 ∧ j = hidx h + 1 then some (hside h) else none,
        if hidx h < j then some (M.δ q (T h)).1 else none, none⟩ := by
  intro j
  induction j with
  | zero => intro _; simpa [fscan, SimBuf.start] using hb0
  | succ j ih =>
    intro hj
    rw [fscan_take_succ _ _ _ j (by omega)]
    simp only [gF, LB.get_set]
    rw [ih (by omega), hrep.cell j (by omega), headAt_eq]
    by_cases hp : fwdMove (hside h) (M.δ q (T h)).2.2 ∧ j = hidx h + 1
    · rw [if_pos hp]
      simp only [simF]
      have h1 : ¬ (fwdMove (hside h) (M.δ q (T h)).2.2 ∧ j + 1 = hidx h + 1) := by omega
      have h3 : hidx h < j := by omega
      have h4 : hidx h < j + 1 := by omega
      rw [if_neg h1, if_pos h3, if_pos h4]
      simp
    · rw [if_neg hp]
      by_cases hJ : j = hidx h
      · rw [if_pos hJ]
        subst hJ
        have hr := FCell.read_cell T h (some (hside h)) none
        have h1 : ¬ hidx h < hidx h := lt_irrefl _
        have h2 : hidx h < hidx h + 1 := Nat.lt_succ_self _
        simp only [simF]
        rw [hr]
        by_cases hF : fwdMove (hside h) (M.δ q (T h)).2.2
        · simp [hF, h2]
        · by_cases h0 : hidx h = 0
          · simp [hF, h0]
          · simp [hF, h0, h2]
      · rw [if_neg hJ]
        simp only [simF]
        have h1 : ¬ (fwdMove (hside h) (M.δ q (T h)).2.2 ∧ j + 1 = hidx h + 1) := by omega
        rw [if_neg h1]
        have h2 : (hidx h < j + 1) ↔ (hidx h < j) := by omega
        simp [h2]

/-- The forward output cell, in closed form. -/
def fwdOut (q : M.Q) (T : ℤ → M.Γ) (h : ℤ) (j : ℕ) : FCell M.Γ :=
  if fwdMove (hside h) (M.δ q (T h)).2.2 ∧ j = hidx h + 1 then
    ⟨T j, T (-(j : ℤ) - 1), some (hside h), none⟩
  else if j = hidx h then
    (⟨T j, T (-(j : ℤ) - 1), none, none⟩ : FCell M.Γ).wr (hside h) (M.δ q (T h)).2.1
      (if fwdMove (hside h) (M.δ q (T h)).2.2 then none
        else if hidx h = 0 then some (!hside h) else none)
      (if fwdMove (hside h) (M.δ q (T h)).2.2 then none
        else if hidx h = 0 then none else some (hside h))
  else ⟨T j, T (-(j : ℤ) - 1), none, none⟩

theorem sim_fcell (q : M.Q) (b0 : Bf) (hb0 : LB.get b0 = SimBuf.start M.Q)
    (l : List C) (T : ℤ → M.Γ) (h : ℤ) (hrep : FRep L.get M.blank l T h) (j : ℕ)
    (hj : j < l.length) :
    (fscan (gF M L LB q) b0 l).1[j]'(by rw [fscan_length]; exact hj) =
      L.set (fwdOut M q T h j) l[j] := by
  rw [fscan_getElem _ _ _ j hj]
  simp only [gF]
  rw [sim_fbuf M L LB q b0 hb0 l T h hrep j hj.le, hrep.cell j hj, headAt_eq]
  unfold fwdOut
  by_cases hp : fwdMove (hside h) (M.δ q (T h)).2.2 ∧ j = hidx h + 1
  · have hj1 := hp.2
    have hne : ¬ j = hidx h := by omega
    simp only [if_pos hp, if_neg hne]
    simp [simF]
  · rw [if_neg hp, if_neg hp]
    by_cases hJ : j = hidx h
    · rw [if_pos hJ, if_pos hJ]
      subst hJ
      have hr := FCell.read_cell T h (some (hside h)) none
      simp only [simF]
      rw [hr]
      by_cases hF : fwdMove (hside h) (M.δ q (T h)).2.2
      · simp [hF, FCell.wr]
      · by_cases h0 : hidx h = 0
        · simp [hF, h0, FCell.wr]
        · simp [hF, h0, FCell.wr]
    · rw [if_neg hJ, if_neg hJ]
      simp [simF]

theorem fwdOut_pl (q : M.Q) (T : ℤ → M.Γ) (h : ℤ) (j : ℕ) :
    (fwdOut M q T h j).pl =
      if (!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧ j = hidx h then
        some (hside h) else none := by
  unfold fwdOut
  by_cases hF : fwdMove (hside h) (M.δ q (T h)).2.2 <;> by_cases h0 : hidx h = 0 <;>
    by_cases hJ : j = hidx h <;> simp [hF, h0, hJ, FCell.wr] <;> split_ifs <;> simp_all

/-- The backward buffer after a suffix. -/
theorem sim_bbuf (q : M.Q) (b0 : Bf) (hb0 : LB.get b0 = SimBuf.start M.Q)
    (l : List C) (T : ℤ → M.Γ) (h : ℤ) (hrep : FRep L.get M.blank l T h) :
    ∀ k ≤ ((fscan (gF M L LB q) b0 l).1 ++
        (gE M L LB dflt (fscan (gF M L LB q) b0 l).2).toList).length,
      LB.get (bscan (gB M L LB) (fscan (gF M L LB q) b0 l).2
        (((fscan (gF M L LB q) b0 l).1 ++
          (gE M L LB dflt (fscan (gF M L LB q) b0 l).2).toList).drop k)).2 =
      ⟨false,
        if fwdMove (hside h) (M.δ q (T h)).2.2 ∧ l.length = hidx h + 1 then some (hside h)
          else none,
        some (M.δ q (T h)).1,
        if (!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧ k = hidx h then
          some (hside h) else none⟩ := by
  set fs := fscan (gF M L LB q) b0 l with hfs
  set mid := fs.1 ++ (gE M L LB dflt fs.2).toList with hmid
  have hJ := hidx_lt hrep.hlo hrep.hhi
  have hlen : fs.1.length = l.length := fscan_length _ _ _
  have hfin : LB.get fs.2 = ⟨decide (l.length = 0),
      if fwdMove (hside h) (M.δ q (T h)).2.2 ∧ l.length = hidx h + 1 then some (hside h) else none,
      if hidx h < l.length then some (M.δ q (T h)).1 else none, none⟩ := by
    rw [hfs, fscan_snd_eq_take]
    exact sim_fbuf M L LB q b0 hb0 l T h hrep l.length le_rfl
  have hmidlen : l.length ≤ mid.length := by rw [hmid, List.length_append, hlen]; omega
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = mid.length - n := ⟨mid.length - k, by omega⟩
  induction n with
  | zero =>
    rw [Nat.sub_zero, bscan_drop_length, hfin]
    have h1 : ¬ ((!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧
        mid.length = hidx h) := by omega
    rw [if_neg h1, if_pos hJ, decide_eq_false (by omega)]
  | succ n ih =>
    by_cases hn : n < mid.length
    · have hk' : mid.length - (n + 1) < mid.length := by omega
      rw [bscan_drop_snd _ _ _ _ hk', show mid.length - (n + 1) + 1 = mid.length - n by omega]
      simp only [gB, LB.get_set]
      rw [ih (by omega)]
      set k := mid.length - (n + 1) with hk
      by_cases hkl : k < l.length
      · have hcell : mid[k]'hk' = L.set (fwdOut M q T h k) l[k] := by
          show (fs.1 ++ (gE M L LB dflt fs.2).toList)[k]'(by rw [← hmid]; exact hk') = _
          rw [List.getElem_append_left (by rw [hlen]; exact hkl)]
          exact sim_fcell M L LB q b0 hb0 l T h hrep k hkl
        rw [hcell, L.get_set]
        by_cases hb : (!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧
            mid.length - n = hidx h
        · have hb2 := hb.2
          have hne : ¬ ((!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧
              k = hidx h) := by
            intro hc; have := hc.2; omega
          rw [if_pos hb, if_neg hne]
          rfl
        · rw [if_neg hb]
          simp only [simB]
          rw [fwdOut_pl]
          by_cases hc : (!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧
              k = hidx h
          · rw [if_pos hc]
          · rw [if_neg hc]
      · -- the extension cell
        have hml : mid.length ≤ l.length + 1 := by
          rw [hmid, List.length_append, hlen]
          cases gE M L LB dflt fs.2 <;> simp
        have hkm : k = l.length := by omega
        have hext : (gE M L LB dflt fs.2).isSome := by
          by_contra hno
          simp only [Option.not_isSome_iff_eq_none] at hno
          have : mid.length = l.length := by rw [hmid, hno]; simp [hlen]
          omega
        obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hext
        have hcell : mid[k]'hk' = e := by
          show (fs.1 ++ (gE M L LB dflt fs.2).toList)[k]'(by rw [← hmid]; exact hk') = _
          simp only [he, Option.toList_some]
          rw [List.getElem_append_right (by rw [hlen]; omega)]
          simp [hlen, hkm]
        have hepl : (L.get e).pl = none := by
          unfold gE at he
          cases hp : (LB.get fs.2).pend with
          | none => rw [hp] at he; simp at he
          | some s => rw [hp] at he; simp at he; rw [← he, L.get_set]
        rw [hcell]
        simp only [simB]
        have h1 : ¬ ((!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧
            mid.length - n = hidx h) := by omega
        have h2 : ¬ ((!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧
            k = hidx h) := by omega
        rw [if_neg h1, if_neg h2, hepl]
    · have : mid.length - (n + 1) = mid.length - n := by omega
      rw [this]; exact ih (by omega)

theorem bound_of_hidx {h : ℤ} {n : ℕ} (hb : hidx h < n) : -(n : ℤ) ≤ h ∧ h < n := by
  unfold hidx at hb; split_ifs at hb <;> omega

theorem pos_facts (h : ℤ) (j : ℕ) (hj : j ≠ hidx h) : (j : ℤ) ≠ h ∧ -(j : ℤ) - 1 ≠ h := by
  have hfp := fpos_hidx h
  by_cases hs : hside h
  · rw [if_pos hs] at hfp; constructor <;> omega
  · rw [if_neg hs] at hfp; constructor <;> omega

theorem headAt_new (h : ℤ) (m : Mv) (j : ℕ) :
    headAt (h + m.shift) j =
      if j = newIdx (hidx h) (hside h) m then some (newSide (hidx h) (hside h) m) else none := by
  rw [headAt_eq, (move_head h m).1, (move_head h m).2]

/-- The final value of an old data cell after the round trip. -/
theorem final_cell (q : M.Q) (T : ℤ → M.Γ) (h : ℤ) (j : ℕ) (P : Option Bool) :
    (simB (⟨false, P, some (M.δ q (T h)).1,
        if (!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧ j + 1 = hidx h then
          some (hside h) else none⟩ : SimBuf M.Q) (fwdOut M q T h j)).1 =
      ⟨Function.update T h (M.δ q (T h)).2.1 j, Function.update T h (M.δ q (T h)).2.1 (-(j : ℤ) - 1),
        headAt (h + (M.δ q (T h)).2.2.shift) j, none⟩ := by
  rw [headAt_new]
  have hfp := fpos_hidx h
  set J := hidx h with hJdef
  set s := hside h with hsdef
  set F := fwdMove s (M.δ q (T h)).2.2 with hF
  unfold newIdx newSide
  rw [← hF]
  by_cases hA : F ∧ j = J + 1
  · -- the head arrives from the left
    have hjJ : j ≠ J := by omega
    obtain ⟨h1, h2⟩ := pos_facts h j hjJ
    have hb : ¬ ((!F && decide (J ≠ 0)) ∧ j + 1 = J) := by omega
    rw [if_neg hb]
    unfold fwdOut
    rw [← hsdef, ← hJdef, ← hF, if_pos hA]
    simp only [simB, Function.update_of_ne h1, Function.update_of_ne h2]
    simp [hA.1, hA.2]
  · by_cases hB : j = J
    · -- the old head cell
      subst hB
      have hb : ¬ ((!F && decide (J ≠ 0)) ∧ J + 1 = J) := by omega
      rw [if_neg hb]
      unfold fwdOut
      rw [← hsdef, ← hJdef, ← hF, if_neg hA, if_pos rfl]
      by_cases hFF : F
      · have hn : ¬ J = J + 1 := by omega
        simp only [hFF, if_true, if_neg hn, simB]
        unfold FCell.wr
        by_cases hs : s
        · rw [if_pos hs] at hfp ⊢
          rw [← hfp]
          simp [Function.update_apply]
          omega
        · rw [if_neg hs] at hfp ⊢
          rw [← hfp]
          simp [Function.update_apply]
          omega
      · by_cases h0 : J = 0
        · simp only [hFF, h0, if_true, Bool.false_eq_true, if_false, simB]
          unfold FCell.wr
          rw [h0] at hfp
          by_cases hs : s
          · rw [if_pos hs] at hfp ⊢
            rw [← hfp]
            simp [Function.update_apply, hs, h0]
          · rw [if_neg hs] at hfp ⊢
            rw [← hfp]
            simp [Function.update_apply, hs, h0]
        · have hn : ¬ J = J - 1 := by omega
          simp only [hFF, h0, Bool.false_eq_true, if_false, if_neg hn, simB]
          unfold FCell.wr
          by_cases hs : s
          · rw [if_pos hs] at hfp ⊢
            rw [← hfp]
            simp [Function.update_apply]
            omega
          · rw [if_neg hs] at hfp ⊢
            rw [← hfp]
            simp [Function.update_apply]
            omega
    · obtain ⟨h1, h2⟩ := pos_facts h j hB
      unfold fwdOut
      rw [← hsdef, ← hJdef, ← hF, if_neg hA, if_neg hB]
      by_cases hC : (!F && decide (J ≠ 0)) ∧ j + 1 = J
      · -- the head arrives from the right
        rw [if_pos hC]
        have hFF : F = false := by
          have := hC.1; revert this; cases F <;> simp
        have h0 : J ≠ 0 := by
          have := hC.1; revert this; simp
        have hj : j = J - 1 := by omega
        simp only [simB, Function.update_of_ne h1, Function.update_of_ne h2, hFF,
          Bool.false_eq_true, if_false, if_neg h0, if_pos hj]
      · rw [if_neg hC]
        simp only [simB, Function.update_of_ne h1, Function.update_of_ne h2]
        by_cases hFF : F
        · have hn : ¬ j = J + 1 := fun e => hA ⟨hFF, e⟩
          simp [hFF, hn]
        · by_cases h0 : J = 0
          · have hj0 : ¬ j = 0 := by omega
            simp [hFF, h0, hj0]
          · have hn : ¬ j = J - 1 := by
              intro e
              apply hC
              refine ⟨?_, by omega⟩
              simp [hFF, h0]
            simp [hFF, h0, hn]

/-- **One simulated step.**  The round trip performs exactly one step of the manuscript machine
on the folded track, changes no other track, and adds at most one (fresh) cell. -/
theorem simTrip_spec (q : M.Q) (b0 : Bf) (hb0 : LB.get b0 = SimBuf.start M.Q)
    (l : List C) (T : ℤ → M.Γ) (h : ℤ) (hrep : FRep L.get M.blank l T h) :
    FRep L.get M.blank (simTrip M L LB dflt q b0 l).1 (M.step ⟨T, h, q⟩).tape
        (M.step ⟨T, h, q⟩).head ∧
      (LB.get (simTrip M L LB dflt q b0 l).2).nq = some (M.step ⟨T, h, q⟩).q ∧
      l.length ≤ (simTrip M L LB dflt q b0 l).1.length ∧
      (simTrip M L LB dflt q b0 l).1.length ≤ l.length + 1 ∧
      ∀ (j : ℕ) (hj : j < (simTrip M L LB dflt q b0 l).1.length),
        (simTrip M L LB dflt q b0 l).1[j] =
          L.set (L.get (simTrip M L LB dflt q b0 l).1[j]) (l.getD j dflt) := by
  have hJ := hidx_lt hrep.hlo hrep.hhi
  have hstep : M.step ⟨T, h, q⟩ = ⟨Function.update T h (M.δ q (T h)).2.1,
      h + (M.δ q (T h)).2.2.shift, (M.δ q (T h)).1⟩ := rfl
  rw [hstep]
  unfold simTrip
  set fs := fscan (gF M L LB q) b0 l with hfs
  set mid := fs.1 ++ (gE M L LB dflt fs.2).toList with hmid
  have hlen : fs.1.length = l.length := fscan_length _ _ _
  have hfin : LB.get fs.2 = ⟨decide (l.length = 0),
      if fwdMove (hside h) (M.δ q (T h)).2.2 ∧ l.length = hidx h + 1 then some (hside h) else none,
      if hidx h < l.length then some (M.δ q (T h)).1 else none, none⟩ := by
    rw [hfs, fscan_snd_eq_take]
    exact sim_fbuf M L LB q b0 hb0 l T h hrep l.length le_rfl
  -- the extension
  have hext : gE M L LB dflt fs.2 =
      if fwdMove (hside h) (M.δ q (T h)).2.2 ∧ l.length = hidx h + 1 then
        some (L.set ⟨M.blank, M.blank, some (hside h), none⟩ dflt) else none := by
    unfold gE; rw [hfin]; split_ifs <;> rfl
  have hmidlen : mid.length = l.length +
      (if fwdMove (hside h) (M.δ q (T h)).2.2 ∧ l.length = hidx h + 1 then 1 else 0) := by
    rw [hmid, List.length_append, hlen, hext]; split_ifs <;> simp
  have houtlen : (bscan (gB M L LB) fs.2 mid).1.length = mid.length := bscan_length _ _ _
  have hbb := sim_bbuf M L LB dflt q b0 hb0 l T h hrep
  -- each output cell
  have hcell : ∀ (j : ℕ) (hj : j < mid.length),
      (bscan (gB M L LB) fs.2 mid).1[j]'(by rw [houtlen]; exact hj) =
        L.set (simB (LB.get (bscan (gB M L LB) fs.2 (mid.drop (j + 1))).2)
          (L.get (mid[j]'hj))).1 (l.getD j dflt) := by
    intro j hj
    rw [bscan_getElem _ _ _ j hj]
    simp only [gB]
    by_cases hjl : j < l.length
    · have hm : mid[j]'hj = L.set (fwdOut M q T h j) l[j] := by
        show (fs.1 ++ (gE M L LB dflt fs.2).toList)[j]'(by rw [← hmid]; exact hj) = _
        rw [List.getElem_append_left (by rw [hlen]; exact hjl)]
        exact sim_fcell M L LB q b0 hb0 l T h hrep j hjl
      rw [hm, L.set_set, L.get_set, List.getD_eq_getElem _ _ hjl]
    · have hjm : j = l.length := by
        rw [hmidlen] at hj; split_ifs at hj <;> omega
      have hA : fwdMove (hside h) (M.δ q (T h)).2.2 ∧ l.length = hidx h + 1 := by
        by_contra hno; rw [hmidlen, if_neg hno] at hj; omega
      have hm : mid[j]'hj = L.set ⟨M.blank, M.blank, some (hside h), none⟩ dflt := by
        show (fs.1 ++ (gE M L LB dflt fs.2).toList)[j]'(by rw [← hmid]; exact hj) = _
        simp only [hext, if_pos hA, Option.toList_some]
        rw [List.getElem_append_right (by rw [hlen]; omega)]
        simp [hlen, hjm]
      rw [hm, L.set_set, L.get_set, List.getD_eq_default _ _ (by omega)]
  have hnew : hidx (h + (M.δ q (T h)).2.2.shift) < mid.length := by
    rw [(move_head h _).1, hmidlen]
    unfold newIdx
    by_cases hF : fwdMove (hside h) (M.δ q (T h)).2.2
    · rw [if_pos hF]
      by_cases he : l.length = hidx h + 1
      · rw [if_pos ⟨hF, he⟩]; omega
      · rw [if_neg (fun hc => he hc.2)]; omega
    · have hn : ¬ (fwdMove (hside h) (M.δ q (T h)).2.2 = true ∧ l.length = hidx h + 1) :=
        fun hc => hF hc.1
      rw [if_neg hF, if_neg hn]
      split_ifs <;> omega
  refine ⟨⟨fun j hj => ?_, fun i hi => ?_, ?_, ?_⟩, ?_, ?_, ?_, fun j hj => ?_⟩
  · -- cells of the new representation
    replace hj : j < mid.length := by rw [← houtlen]; exact hj
    show L.get ((bscan (gB M L LB) fs.2 mid).1[j]'(by rw [houtlen]; exact hj)) =
      ⟨Function.update T h (M.δ q (T h)).2.1 j,
        Function.update T h (M.δ q (T h)).2.1 (-(j : ℤ) - 1),
        headAt (h + (M.δ q (T h)).2.2.shift) j, none⟩
    rw [hcell j hj, L.get_set, hbb (j + 1) (by show j + 1 ≤ mid.length; omega)]
    by_cases hjl : j < l.length
    · have hm : L.get (mid[j]'hj) = fwdOut M q T h j := by
        have : mid[j]'hj = L.set (fwdOut M q T h j) l[j] := by
          show (fs.1 ++ (gE M L LB dflt fs.2).toList)[j]'(by rw [← hmid]; exact hj) = _
          rw [List.getElem_append_left (by rw [hlen]; exact hjl)]
          exact sim_fcell M L LB q b0 hb0 l T h hrep j hjl
        rw [this, L.get_set]
      rw [hm]
      exact final_cell M q T h j _
    · have hjm : j = l.length := by
        rw [hmidlen] at hj; split_ifs at hj <;> omega
      have hA : fwdMove (hside h) (M.δ q (T h)).2.2 ∧ l.length = hidx h + 1 := by
        by_contra hno; rw [hmidlen, if_neg hno] at hj; omega
      have hm : L.get (mid[j]'hj) = ⟨M.blank, M.blank, some (hside h), none⟩ := by
        have : mid[j]'hj = L.set ⟨M.blank, M.blank, some (hside h), none⟩ dflt := by
          show (fs.1 ++ (gE M L LB dflt fs.2).toList)[j]'(by rw [← hmid]; exact hj) = _
          simp only [hext, if_pos hA, Option.toList_some]
          rw [List.getElem_append_right (by rw [hlen]; omega)]
          simp [hlen, hjm]
        rw [this, L.get_set]
      rw [hm]
      have hb : ¬ ((!fwdMove (hside h) (M.δ q (T h)).2.2 && decide (hidx h ≠ 0)) ∧
          j + 1 = hidx h) := by omega
      rw [if_neg hb]
      have hne1 : (j : ℤ) ≠ h := by have := hrep.hhi; omega
      have hne2 : -(j : ℤ) - 1 ≠ h := by have := hrep.hlo; omega
      rw [headAt_new]
      simp only [simB, Function.update_of_ne hne1, Function.update_of_ne hne2]
      rw [hrep.out j (Or.inl (by omega)), hrep.out _ (Or.inr (by omega))]
      unfold newIdx newSide
      rw [if_pos hA.1, if_pos hA.1, if_pos (by omega)]
  · -- outside the represented range the tape is blank
    replace hi : ((mid.length : ℕ) : ℤ) ≤ i ∨ i < -((mid.length : ℕ) : ℤ) := by
      rw [← houtlen]; exact hi
    rw [hmidlen] at hi
    show Function.update T h (M.δ q (T h)).2.1 i = M.blank
    have hne : i ≠ h := by
      have := hrep.hlo; have := hrep.hhi; split_ifs at hi <;> omega
    rw [Function.update_of_ne hne]
    exact hrep.out i (by split_ifs at hi <;> omega)
  · show -(((bscan (gB M L LB) fs.2 mid).1.length : ℕ) : ℤ) ≤ h + (M.δ q (T h)).2.2.shift
    rw [houtlen]; exact (bound_of_hidx hnew).1
  · show h + (M.δ q (T h)).2.2.shift < (((bscan (gB M L LB) fs.2 mid).1.length : ℕ) : ℤ)
    rw [houtlen]; exact (bound_of_hidx hnew).2
  · show (LB.get (bscan (gB M L LB) fs.2 mid).2).nq = some (M.δ q (T h)).1
    have := hbb 0 (Nat.zero_le _)
    simp only [List.drop_zero] at this
    rw [this]
  · show l.length ≤ (bscan (gB M L LB) fs.2 mid).1.length
    rw [houtlen, hmidlen]; omega
  · show (bscan (gB M L LB) fs.2 mid).1.length ≤ l.length + 1
    rw [houtlen, hmidlen]; split_ifs <;> omega
  · replace hj : j < mid.length := by rw [← houtlen]; exact hj
    show (bscan (gB M L LB) fs.2 mid).1[j]'(by rw [houtlen]; exact hj) =
      L.set (L.get ((bscan (gB M L LB) fs.2 mid).1[j]'(by rw [houtlen]; exact hj))) (l.getD j dflt)
    rw [hcell j hj, L.get_set]

end Spec

end PVNP.UniformSim
