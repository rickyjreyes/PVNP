import PVNP.DiscreteMachines

/-!
# Discrete WCC → ordinary TM, explicit quadratic simulation (issue #11, direction 2)

For every finite quiescent radius-one WCC `A` we construct an ordinary
single-tape Turing machine `A.toTM` with

* tape alphabet `Option (Bool ⊕ A.S)` (`none` = TM blank, `inl b` = raw input
  bit, `inr s` = simulated cell);
* finite control `SimPhase (Option (Bool ⊕ A.S))`: a preprocessing state,
  left-to-right and right-to-left sweep states remembering the two previously
  read symbols and two answer flags, and the halting states `yes`, `no`.

The machine alternates *shifted sweeps*.  A left-to-right sweep writes the new
value of cell `j-1` onto tape cell `j` (frame shift `+1`), a right-to-left sweep
writes the new value of cell `j+1` onto tape cell `j` (frame shift `-1`); each
simulated cell costs exactly one TM step and no return sweep is needed.  During
a sweep the machine also accumulates whether the configuration being read
contains an accepting / rejecting cell and halts accordingly at the sweep end.

Main results:

* `rsweep_run`, `lsweep_run`: exact intermediate configurations of a sweep.
* `phase_step`: one full sweep simulates exactly one synchronous WCC update.
* `toTM_decides`: if `A` decides `L` within `T`, then `A.toTM` decides `L`
  within `1 + (T n + 1) * (n + 2 T n + 5)` ordinary TM steps.
* `P_WCC_subset_P_TM`.
-/

namespace PVNP.Discrete

/-- Control states of the simulating Turing machine. -/
inductive SimPhase (Γ : Type) where
  | pre
  | rs (x y : Γ) (fa fr : Bool)
  | ls (x y : Γ) (fa fr : Bool)
  | yes
  | no
  deriving DecidableEq, Fintype

namespace WCC

variable (A : WCC)

/-- Tape alphabet of the simulator. -/
abbrev Sym := Option (Bool ⊕ A.S)

/-- Simulated cell value of a tape symbol (TM blank reads as WCC blank). -/
def val : A.Sym → A.S
  | none => A.blank
  | some (Sum.inl b) => A.inp b
  | some (Sum.inr s) => s

/-- Tape symbol storing a simulated cell. -/
def cellOf (s : A.S) : A.Sym := some (Sum.inr s)

/-- Origin bit recovered during preprocessing. -/
def preBit : A.Sym → Option Bool
  | some (Sum.inl b) => some b
  | _ => none

/-- Transition function of the simulator. -/
def simδ : SimPhase A.Sym → A.Sym → Option (SimPhase A.Sym × A.Sym × Dir)
  | .pre, z => some (.rs none none (A.acc A.blank) (A.rej A.blank),
      A.cellOf (A.origin (A.preBit z)), Dir.S)
  | .rs x y fa fr, z =>
    if y = none ∧ z = none then
      (if fa then some (.yes, z, Dir.S)
       else if fr then some (.no, z, Dir.S)
       else some (.ls none none (A.acc A.blank) (A.rej A.blank),
          A.cellOf (A.rule (A.val x) (A.val y) (A.val z)), Dir.S))
    else some (.rs y z (fa || A.acc (A.val z)) (fr || A.rej (A.val z)),
          A.cellOf (A.rule (A.val x) (A.val y) (A.val z)), Dir.R)
  | .ls x y fa fr, z =>
    if y = none ∧ z = none then
      (if fa then some (.yes, z, Dir.S)
       else if fr then some (.no, z, Dir.S)
       else some (.rs none none (A.acc A.blank) (A.rej A.blank),
          A.cellOf (A.rule (A.val z) (A.val y) (A.val x)), Dir.S))
    else some (.ls y z (fa || A.acc (A.val z)) (fr || A.rej (A.val z)),
          A.cellOf (A.rule (A.val z) (A.val y) (A.val x)), Dir.L)
  | .yes, _ => none
  | .no, _ => none

/-- The simulating ordinary Turing machine. -/
abbrev toTM : TM where
  Λ := SimPhase A.Sym
  Γ := A.Sym
  blank := none
  inp b := some (Sum.inl b)
  start := .pre
  δ := A.simδ
  acc q := decide (q = .yes)
  rej q := decide (q = .no)

/-- `T` represents the WCC configuration `c` with frame shift `s` on the
nonempty contiguous tape region `[L, R]`. -/
def Represents (c : ℤ → A.S) (T : ℤ → A.Sym) (s L R : ℤ) : Prop :=
  (∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) ∧ ∀ j, A.val (T j) = c (j - s)

theorem none_of_outside {T : ℤ → A.Sym} {L R : ℤ}
    (h : ∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) {j : ℤ} (hj : ¬ (L ≤ j ∧ j ≤ R)) :
    T j = none := by
  by_contra hc; exact hj ((h j).1 hc)

theorem next_eq {c : A.toTM.Cfg} {q' : SimPhase A.Sym} {a : A.Sym} {d : Dir}
    (h : A.simδ c.q (c.tape c.head) = some (q', a, d)) :
    A.toTM.next c = ⟨q', Function.update c.tape c.head a, c.head + d.shift⟩ := by
  simp [TM.next, TM.step, h]

/-! ### Left-to-right sweep -/

/-- Values written by a left-to-right sweep. -/
def newR (T : ℤ → A.Sym) (j : ℤ) : A.S :=
  A.rule (A.val (T (j - 2))) (A.val (T (j - 1))) (A.val (T j))

/-- Tape after `m` steps of a left-to-right sweep started at `L`. -/
def wrR (T : ℤ → A.Sym) (L : ℤ) (m : ℕ) (j : ℤ) : A.Sym :=
  if L ≤ j ∧ j < L + m then A.cellOf (A.newR T j) else T j

/-- Accept flag accumulated over the first `m` cells read. -/
def accR (T : ℤ → A.Sym) (L : ℤ) (m : ℕ) : Bool :=
  (List.range m).any fun k => A.acc (A.val (T (L + k)))

/-- Reject flag accumulated over the first `m` cells read. -/
def rejR (T : ℤ → A.Sym) (L : ℤ) (m : ℕ) : Bool :=
  (List.range m).any fun k => A.rej (A.val (T (L + k)))

theorem rsweep_run (T : ℤ → A.Sym) (L R : ℤ) (fa fr : Bool)
    (hreg : ∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) (hLR : L ≤ R) (m : ℕ)
    (hm : (m : ℤ) ≤ R - L + 2) :
    A.toTM.run ⟨.rs none none fa fr, T, L⟩ m =
      ⟨.rs (T (L + m - 2)) (T (L + m - 1)) (fa || A.accR T L m) (fr || A.rejR T L m),
        A.wrR T L m, L + m⟩ := by
  induction m with
  | zero =>
    have h2 : T (L - 2) = none := A.none_of_outside hreg (by omega)
    have h1 : T (L - 1) = none := A.none_of_outside hreg (by omega)
    have hw : A.wrR T L 0 = T := funext fun j => by simp [wrR]
    simp [TM.run, h1, h2, hw, accR, rejR]
  | succ m ih =>
    rw [TM.run_succ, ih (by omega)]
    have hz : A.wrR T L m (L + m) = T (L + m) := by simp [wrR]
    have hcont : ¬ (T (L + m - 1) = none ∧ T (L + m) = none) := by
      rintro ⟨h1, h2⟩
      by_cases hle : L + m ≤ R
      · exact ((hreg (L + m)).2 ⟨by omega, hle⟩) h2
      · exact ((hreg (L + m - 1)).2 ⟨by omega, by omega⟩) h1
    rw [A.next_eq (q' := .rs (T (L + m - 1)) (T (L + m))
        ((fa || A.accR T L m) || A.acc (A.val (T (L + m))))
        ((fr || A.rejR T L m) || A.rej (A.val (T (L + m)))))
        (a := A.cellOf (A.newR T (L + m))) (d := Dir.R)]
    · have e1 : L + ((m + 1 : ℕ) : ℤ) - 2 = L + m - 1 := by push_cast; ring
      have e2 : L + ((m + 1 : ℕ) : ℤ) - 1 = L + m := by push_cast; ring
      have e3 : L + ((m + 1 : ℕ) : ℤ) = L + m + Dir.R.shift := by simp only [Dir.shift]; push_cast; ring
      rw [e1, e2, e3]
      have hw : Function.update (A.wrR T L m) (L + m) (A.cellOf (A.newR T (L + m))) =
          A.wrR T L (m + 1) := by
        funext j
        by_cases hj : j = L + m
        · subst hj; simp [wrR]
        · simp only [Function.update, hj, dite_false, wrR]
          push_cast
          by_cases h3 : L ≤ j ∧ j < L + m
          · rw [if_pos h3, if_pos ⟨h3.1, by omega⟩]
          · rw [if_neg h3, if_neg (by omega)]
      rw [hw]
      simp [accR, rejR, List.range_succ, List.any_append, Bool.or_assoc]
    · simp only [hz]
      simp only [simδ, if_neg hcont, newR]

/-! ### Right-to-left sweep -/

/-- Values written by a right-to-left sweep. -/
def newL (T : ℤ → A.Sym) (j : ℤ) : A.S :=
  A.rule (A.val (T j)) (A.val (T (j + 1))) (A.val (T (j + 2)))

/-- Tape after `m` steps of a right-to-left sweep started at `R`. -/
def wrL (T : ℤ → A.Sym) (R : ℤ) (m : ℕ) (j : ℤ) : A.Sym :=
  if R - m < j ∧ j ≤ R then A.cellOf (A.newL T j) else T j

def accL (T : ℤ → A.Sym) (R : ℤ) (m : ℕ) : Bool :=
  (List.range m).any fun k => A.acc (A.val (T (R - k)))

def rejL (T : ℤ → A.Sym) (R : ℤ) (m : ℕ) : Bool :=
  (List.range m).any fun k => A.rej (A.val (T (R - k)))

theorem lsweep_run (T : ℤ → A.Sym) (L R : ℤ) (fa fr : Bool)
    (hreg : ∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) (hLR : L ≤ R) (m : ℕ)
    (hm : (m : ℤ) ≤ R - L + 2) :
    A.toTM.run ⟨.ls none none fa fr, T, R⟩ m =
      ⟨.ls (T (R - m + 2)) (T (R - m + 1)) (fa || A.accL T R m) (fr || A.rejL T R m),
        A.wrL T R m, R - m⟩ := by
  induction m with
  | zero =>
    have h2 : T (R + 2) = none := A.none_of_outside hreg (by omega)
    have h1 : T (R + 1) = none := A.none_of_outside hreg (by omega)
    have hw : A.wrL T R 0 = T := funext fun j => by
      simp only [wrL, CharP.cast_eq_zero, sub_zero]
      rw [if_neg (by omega)]
    simp [TM.run, h1, h2, hw, accL, rejL]
  | succ m ih =>
    rw [TM.run_succ, ih (by omega)]
    have hz : A.wrL T R m (R - m) = T (R - m) := by simp [wrL]
    have hcont : ¬ (T (R - m + 1) = none ∧ T (R - m) = none) := by
      rintro ⟨h1, h2⟩
      by_cases hle : L ≤ R - m
      · exact ((hreg (R - m)).2 ⟨hle, by omega⟩) h2
      · exact ((hreg (R - m + 1)).2 ⟨by omega, by omega⟩) h1
    rw [A.next_eq (q' := .ls (T (R - m + 1)) (T (R - m))
        ((fa || A.accL T R m) || A.acc (A.val (T (R - m))))
        ((fr || A.rejL T R m) || A.rej (A.val (T (R - m)))))
        (a := A.cellOf (A.newL T (R - m))) (d := Dir.L)]
    · have e1 : R - ((m + 1 : ℕ) : ℤ) + 2 = R - m + 1 := by push_cast; ring
      have e2 : R - ((m + 1 : ℕ) : ℤ) + 1 = R - m := by push_cast; ring
      have e3 : R - ((m + 1 : ℕ) : ℤ) = R - m + Dir.L.shift := by simp only [Dir.shift]; push_cast; ring
      rw [e1, e2, e3]
      have hw : Function.update (A.wrL T R m) (R - m) (A.cellOf (A.newL T (R - m))) =
          A.wrL T R (m + 1) := by
        funext j
        by_cases hj : j = R - m
        · subst hj; simp only [Function.update_self, wrL]; push_cast
          rw [if_pos ⟨by omega, by omega⟩]
        · simp only [Function.update, hj, dite_false, wrL]
          push_cast
          by_cases h3 : R - m < j ∧ j ≤ R
          · rw [if_pos h3, if_pos ⟨by omega, h3.2⟩]
          · rw [if_neg h3, if_neg (by omega)]
      rw [hw]
      simp [accL, rejL, List.range_succ, List.any_append, Bool.or_assoc]
    · simp only [hz]
      simp only [simδ, if_neg (by tauto : ¬ (T (R - m + 1) = none ∧ T (R - m) = none)), newL]

/-! ### One sweep simulates one synchronous update -/

theorem represents_wrR {c : ℤ → A.S} {T : ℤ → A.Sym} {s L R : ℤ}
    (h : A.Represents c T s L R) (hLR : L ≤ R) :
    A.Represents (A.step c) (A.wrR T L (R - L + 3).toNat) (s + 1) L (R + 2) := by
  obtain ⟨hreg, hval⟩ := h
  have hn : (((R - L + 3).toNat : ℕ) : ℤ) = R - L + 3 := by omega
  constructor
  · intro j
    simp only [wrR, hn]
    by_cases hj : L ≤ j ∧ j < L + (R - L + 3)
    · rw [if_pos hj]; simp [cellOf]; omega
    · rw [if_neg hj, hreg j]; omega
  · intro j
    simp only [wrR, hn]
    by_cases hj : L ≤ j ∧ j < L + (R - L + 3)
    · rw [if_pos hj]
      show A.rule (A.val (T (j - 2))) (A.val (T (j - 1))) (A.val (T j)) = A.step c (j - (s + 1))
      rw [hval, hval, hval]
      simp only [step]
      rw [show j - (s + 1) - 1 = j - 2 - s by ring, show j - (s + 1) = j - 1 - s by ring,
        show j - 1 - s + 1 = j - s by ring]
    · rw [if_neg hj]
      have h0 : T j = none := A.none_of_outside hreg (by omega)
      have h1 : T (j - 1) = none := A.none_of_outside hreg (by omega)
      have h2 : T (j - 2) = none := A.none_of_outside hreg (by omega)
      have v0 := hval j; have v1 := hval (j - 1); have v2 := hval (j - 2)
      rw [h0] at v0; rw [h1] at v1; rw [h2] at v2
      simp only [val] at v0 v1 v2
      simp only [h0, val, step]
      rw [show j - (s + 1) - 1 = j - 2 - s by ring, show j - (s + 1) = j - 1 - s by ring,
        show j - 1 - s + 1 = j - s by ring, ← v0, ← v1, ← v2, A.quiescent]

theorem represents_wrL {c : ℤ → A.S} {T : ℤ → A.Sym} {s L R : ℤ}
    (h : A.Represents c T s L R) (hLR : L ≤ R) :
    A.Represents (A.step c) (A.wrL T R (R - L + 3).toNat) (s - 1) (L - 2) R := by
  obtain ⟨hreg, hval⟩ := h
  have hn : (((R - L + 3).toNat : ℕ) : ℤ) = R - L + 3 := by omega
  constructor
  · intro j
    simp only [wrL, hn]
    by_cases hj : R - (R - L + 3) < j ∧ j ≤ R
    · rw [if_pos hj]; simp [cellOf]; omega
    · rw [if_neg hj, hreg j]; omega
  · intro j
    simp only [wrL, hn]
    by_cases hj : R - (R - L + 3) < j ∧ j ≤ R
    · rw [if_pos hj]
      show A.rule (A.val (T j)) (A.val (T (j + 1))) (A.val (T (j + 2))) = A.step c (j - (s - 1))
      rw [hval, hval, hval]
      simp only [step]
      rw [show j - (s - 1) - 1 = j - s by ring, show j - (s - 1) = j + 1 - s by ring,
        show j + 1 - s + 1 = j + 2 - s by ring]
    · rw [if_neg hj]
      have h0 : T j = none := A.none_of_outside hreg (by omega)
      have h1 : T (j + 1) = none := A.none_of_outside hreg (by omega)
      have h2 : T (j + 2) = none := A.none_of_outside hreg (by omega)
      have v0 := hval j; have v1 := hval (j + 1); have v2 := hval (j + 2)
      rw [h0] at v0; rw [h1] at v1; rw [h2] at v2
      simp only [val] at v0 v1 v2
      simp only [h0, val, step]
      rw [show j - (s - 1) - 1 = j - s by ring, show j - (s - 1) = j + 1 - s by ring,
        show j + 1 - s + 1 = j + 2 - s by ring, ← v0, ← v1, ← v2, A.quiescent]

/-- The accumulated accept flag at the end of a left-to-right sweep is exactly
"some cell of the represented configuration accepts". -/
theorem accR_iff {c : ℤ → A.S} {T : ℤ → A.Sym} {s L R : ℤ}
    (h : A.Represents c T s L R) (hLR : L ≤ R) (P : A.S → Bool) :
    (P A.blank || (List.range (R - L + 2).toNat).any fun k => P (A.val (T (L + k)))) = true ↔
      ∃ i, P (c i) = true := by
  obtain ⟨hreg, hval⟩ := h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
  constructor
  · rintro (hb | ⟨k, -, hk⟩)
    · refine ⟨R + 1 - s, ?_⟩
      have := hval (R + 1)
      rw [A.none_of_outside hreg (by omega)] at this
      simp only [val] at this
      rw [← show R + 1 - s = R + 1 - s from rfl, ← this]; exact hb
    · exact ⟨L + k - s, by rw [← hval]; exact hk⟩
  · rintro ⟨i, hi⟩
    rw [← show i + s - s = i by ring, ← hval] at hi
    by_cases hj : L ≤ i + s ∧ i + s ≤ R
    · right
      refine ⟨(i + s - L).toNat, by omega, ?_⟩
      rw [show L + (((i + s - L).toNat : ℕ) : ℤ) = i + s by omega]; exact hi
    · left
      rw [A.none_of_outside hreg hj] at hi; simpa [val] using hi

theorem accL_iff {c : ℤ → A.S} {T : ℤ → A.Sym} {s L R : ℤ}
    (h : A.Represents c T s L R) (hLR : L ≤ R) (P : A.S → Bool) :
    (P A.blank || (List.range (R - L + 2).toNat).any fun k => P (A.val (T (R - k)))) = true ↔
      ∃ i, P (c i) = true := by
  obtain ⟨hreg, hval⟩ := h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
  constructor
  · rintro (hb | ⟨k, -, hk⟩)
    · refine ⟨L - 1 - s, ?_⟩
      have := hval (L - 1)
      rw [A.none_of_outside hreg (by omega)] at this
      simp only [val] at this
      rw [← this]; exact hb
    · exact ⟨R - k - s, by rw [← hval]; exact hk⟩
  · rintro ⟨i, hi⟩
    rw [← show i + s - s = i by ring, ← hval] at hi
    by_cases hj : L ≤ i + s ∧ i + s ≤ R
    · right
      refine ⟨(R - (i + s)).toNat, by omega, ?_⟩
      rw [show R - (((R - (i + s)).toNat : ℕ) : ℤ) = i + s by omega]; exact hi
    · left
      rw [A.none_of_outside hreg hj] at hi; simpa [val] using hi

open Classical in
theorem outCfg_eq (c : ℤ → A.S) (fa fr : Bool)
    (ha : fa = true ↔ ∃ i, A.acc (c i) = true) (hr : fr = true ↔ ∃ i, A.rej (c i) = true) :
    A.outCfg c = answerOf fa fr := by
  unfold outCfg
  congr 1
  · exact Bool.eq_iff_iff.2 (by simpa using ha.symm)
  · exact Bool.eq_iff_iff.2 (by simpa using hr.symm)

/-! ### Phases -/

/-- Simulator configuration at the start of the sweep for WCC step `k`. -/
def PhaseCfg (c : ℤ → A.S) (w k : ℕ) (cfg : A.toTM.Cfg) : Prop :=
  ∃ T L R s, A.Represents c T s L R ∧ R - L = (w : ℤ) + 2 * k ∧
    ((k % 2 = 0 ∧ cfg = ⟨.rs none none (A.acc A.blank) (A.rej A.blank), T, L⟩) ∨
     (k % 2 = 1 ∧ cfg = ⟨.ls none none (A.acc A.blank) (A.rej A.blank), T, R⟩))

/-- Length of the `k`-th sweep, including its turn-around step. -/
def sweepLen (w k : ℕ) : ℕ := w + 2 * k + 3

theorem answerOf_false : answerOf false false = none := rfl

theorem ans_rs (T : ℤ → A.Sym) (h : ℤ) (x y : A.Sym) (fa fr : Bool) :
    A.toTM.ans ⟨.rs x y fa fr, T, h⟩ = none := by
  simp [TM.ans, answerOf]

theorem ans_ls (T : ℤ → A.Sym) (h : ℤ) (x y : A.Sym) (fa fr : Bool) :
    A.toTM.ans ⟨.ls x y fa fr, T, h⟩ = none := by
  simp [TM.ans, answerOf]

theorem answerOf_none {a r : Bool} (h : answerOf a r = none) : a = false ∧ r = false := by
  cases a <;> cases r <;> simp_all [answerOf]

theorem answerOf_true {a r : Bool} (h : answerOf a r = some true) : a = true := by
  cases a <;> cases r <;> simp_all [answerOf]

theorem answerOf_false' {a r : Bool} (h : answerOf a r = some false) : a = false ∧ r = true := by
  cases a <;> cases r <;> simp_all [answerOf]

/-- One sweep: no answer is displayed during it; at its end the simulator
either displays exactly the WCC output of `c`, or (if that output is `none`)
is in the phase configuration for `A.step c`. -/
theorem phase_step (c : ℤ → A.S) (w k : ℕ) (cfg : A.toTM.Cfg)
    (hp : A.PhaseCfg c w k cfg) :
    (∀ m < sweepLen w k, A.toTM.ans (A.toTM.run cfg m) = none) ∧
    (A.outCfg c = none → A.PhaseCfg (A.step c) w (k + 1) (A.toTM.run cfg (sweepLen w k))) ∧
    (∀ b, A.outCfg c = some b → A.toTM.ans (A.toTM.run cfg (sweepLen w k)) = some b) := by
  obtain ⟨T, L, R, s, hrep, hw, hcfg⟩ := hp
  have hLR : L ≤ R := by omega
  have hm0 : ((R - L + 2).toNat : ℤ) = R - L + 2 := by omega
  have hlen : sweepLen w k = (R - L + 2).toNat + 1 := by
    simp only [sweepLen]; omega
  rcases hcfg with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
  · -- left-to-right sweep
    have hrun := A.rsweep_run T L R (A.acc A.blank) (A.rej A.blank) hrep.1 hLR
    have hmid : ∀ m < sweepLen w k, A.toTM.ans (A.toTM.run
        ⟨.rs none none (A.acc A.blank) (A.rej A.blank), T, L⟩ m) = none := by
      intro m hm
      rw [hrun m (by omega)]; exact A.ans_rs _ _ _ _ _ _
    set m0 := (R - L + 2).toNat with hm0def
    have hend := hrun m0 (by omega)
    have eR : L + (m0 : ℤ) - 2 = R := by omega
    have eR1 : L + (m0 : ℤ) - 1 = R + 1 := by omega
    have eR2 : L + (m0 : ℤ) = R + 2 := by omega
    rw [eR, eR1, eR2] at hend
    have hT1 : T (R + 1) = none := A.none_of_outside hrep.1 (by omega)
    have hW2 : A.wrR T L m0 (R + 2) = none := by
      simp only [wrR]; rw [if_neg (by omega)]; exact A.none_of_outside hrep.1 (by omega)
    have hfa : (A.acc A.blank || A.accR T L m0) = true ↔ ∃ i, A.acc (c i) = true :=
      A.accR_iff hrep hLR A.acc
    have hfr : (A.rej A.blank || A.rejR T L m0) = true ↔ ∃ i, A.rej (c i) = true :=
      A.accR_iff hrep hLR A.rej
    have hout := A.outCfg_eq c _ _ hfa hfr
    have hlast : A.toTM.run ⟨.rs none none (A.acc A.blank) (A.rej A.blank), T, L⟩
        (sweepLen w k) = A.toTM.next ⟨.rs (T R) (T (R + 1))
          (A.acc A.blank || A.accR T L m0) (A.rej A.blank || A.rejR T L m0),
          A.wrR T L m0, R + 2⟩ := by
      rw [hlen, TM.run_succ, hend]
    refine ⟨hmid, ?_, ?_⟩
    · intro hnone
      rw [hout] at hnone
      obtain ⟨hfa0, hfr0⟩ := answerOf_none hnone
      rw [hlast, hfa0, hfr0, hT1]
      rw [A.next_eq (q' := .ls none none (A.acc A.blank) (A.rej A.blank))
        (a := A.cellOf (A.newR T (R + 2))) (d := Dir.S)]
      · refine ⟨A.wrR T L (R - L + 3).toNat, L, R + 2, s + 1,
          A.represents_wrR hrep hLR, by push_cast; omega, Or.inr ⟨by omega, ?_⟩⟩
        have hw' : Function.update (A.wrR T L m0) (R + 2) (A.cellOf (A.newR T (R + 2))) =
            A.wrR T L (R - L + 3).toNat := by
          funext j
          by_cases hj : j = R + 2
          · subst hj; simp only [Function.update_self, wrR]
            rw [if_pos ⟨by omega, by omega⟩]
          · simp only [Function.update, hj, dite_false, wrR]
            by_cases h3 : L ≤ j ∧ j < L + (m0 : ℤ)
            · rw [if_pos h3, if_pos ⟨h3.1, by omega⟩]
            · rw [if_neg h3, if_neg (by omega)]
        simp [hw', Dir.shift]
      · simp only [hW2, simδ, and_self, if_true, Bool.false_eq_true, if_false, newR]
        have hT2 : T (R + 2) = none := A.none_of_outside hrep.1 (by omega)
        rw [show R + 2 - 2 = R by ring, show R + 2 - 1 = R + 1 by ring, hT1, hT2]
    · intro b hb
      rw [hout] at hb
      rw [hlast]
      cases b
      · obtain ⟨hfa0, hfr0⟩ := answerOf_false' hb
        rw [hfa0, hfr0, hT1, A.next_eq (q' := .no) (a := none) (d := Dir.S)]
        · simp [TM.ans, answerOf]
        · simp [hW2, simδ]
      · have hfa0 := answerOf_true hb
        rw [hfa0, hT1, A.next_eq (q' := .yes) (a := none) (d := Dir.S)]
        · simp [TM.ans, answerOf]
        · simp [hW2, simδ]
  · -- right-to-left sweep
    have hrun := A.lsweep_run T L R (A.acc A.blank) (A.rej A.blank) hrep.1 hLR
    have hmid : ∀ m < sweepLen w k, A.toTM.ans (A.toTM.run
        ⟨.ls none none (A.acc A.blank) (A.rej A.blank), T, R⟩ m) = none := by
      intro m hm
      rw [hrun m (by omega)]; exact A.ans_ls _ _ _ _ _ _
    set m0 := (R - L + 2).toNat with hm0def
    have hend := hrun m0 (by omega)
    have eR : R - (m0 : ℤ) + 2 = L := by omega
    have eR1 : R - (m0 : ℤ) + 1 = L - 1 := by omega
    have eR2 : R - (m0 : ℤ) = L - 2 := by omega
    rw [eR, eR1, eR2] at hend
    have hT1 : T (L - 1) = none := A.none_of_outside hrep.1 (by omega)
    have hW2 : A.wrL T R m0 (L - 2) = none := by
      simp only [wrL]; rw [if_neg (by omega)]; exact A.none_of_outside hrep.1 (by omega)
    have hfa : (A.acc A.blank || A.accL T R m0) = true ↔ ∃ i, A.acc (c i) = true :=
      A.accL_iff hrep hLR A.acc
    have hfr : (A.rej A.blank || A.rejL T R m0) = true ↔ ∃ i, A.rej (c i) = true :=
      A.accL_iff hrep hLR A.rej
    have hout := A.outCfg_eq c _ _ hfa hfr
    have hlast : A.toTM.run ⟨.ls none none (A.acc A.blank) (A.rej A.blank), T, R⟩
        (sweepLen w k) = A.toTM.next ⟨.ls (T L) (T (L - 1))
          (A.acc A.blank || A.accL T R m0) (A.rej A.blank || A.rejL T R m0),
          A.wrL T R m0, L - 2⟩ := by
      rw [hlen, TM.run_succ, hend]
    refine ⟨hmid, ?_, ?_⟩
    · intro hnone
      rw [hout] at hnone
      obtain ⟨hfa0, hfr0⟩ := answerOf_none hnone
      rw [hlast, hfa0, hfr0, hT1]
      rw [A.next_eq (q' := .rs none none (A.acc A.blank) (A.rej A.blank))
        (a := A.cellOf (A.newL T (L - 2))) (d := Dir.S)]
      · refine ⟨A.wrL T R (R - L + 3).toNat, L - 2, R, s - 1,
          A.represents_wrL hrep hLR, by push_cast; omega, Or.inl ⟨by omega, ?_⟩⟩
        have hw' : Function.update (A.wrL T R m0) (L - 2) (A.cellOf (A.newL T (L - 2))) =
            A.wrL T R (R - L + 3).toNat := by
          funext j
          by_cases hj : j = L - 2
          · subst hj; simp only [Function.update_self, wrL]
            rw [if_pos ⟨by omega, by omega⟩]
          · simp only [Function.update, hj, dite_false, wrL]
            by_cases h3 : R - (m0 : ℤ) < j ∧ j ≤ R
            · rw [if_pos h3, if_pos ⟨by omega, h3.2⟩]
            · rw [if_neg h3, if_neg (by omega)]
        simp [hw', Dir.shift]
      · simp only [hW2, simδ, and_self, if_true, Bool.false_eq_true, if_false, newL]
        have hT2 : T (L - 2) = none := A.none_of_outside hrep.1 (by omega)
        rw [show L - 2 + 2 = L by ring, show L - 2 + 1 = L - 1 by ring, hT1, hT2]
    · intro b hb
      rw [hout] at hb
      rw [hlast]
      cases b
      · obtain ⟨hfa0, hfr0⟩ := answerOf_false' hb
        rw [hfa0, hfr0, hT1, A.next_eq (q' := .no) (a := none) (d := Dir.S)]
        · simp [TM.ans, answerOf]
        · simp [hW2, simδ]
      · have hfa0 := answerOf_true hb
        rw [hfa0, hT1, A.next_eq (q' := .yes) (a := none) (d := Dir.S)]
        · simp [TM.ans, answerOf]
        · simp [hW2, simδ]

/-! ### Preprocessing and the global simulation -/

/-- Width parameter of the initial tape region `[0, |x| - 1]` (at least one cell). -/
def w0 (x : List Bool) : ℕ := x.length - 1

/-- Tape after the preprocessing step. -/
def tape0 (x : List Bool) : ℤ → A.Sym :=
  Function.update (A.toTM.inputTape x) 0 (A.cellOf (A.origin x.head?))

theorem pre_step (x : List Bool) :
    A.toTM.run (A.toTM.init x) 1 =
      ⟨.rs none none (A.acc A.blank) (A.rej A.blank), A.tape0 x, 0⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, TM.run_succ]
  simp only [TM.run, Function.iterate_zero, id]
  rw [A.next_eq (q' := .rs none none (A.acc A.blank) (A.rej A.blank))
    (a := A.cellOf (A.origin x.head?)) (d := Dir.S)]
  · simp [tape0, TM.init, Dir.shift]
  · simp only [TM.init, simδ, TM.inputTape]
    cases x with
    | nil => simp [preBit]
    | cons b xs => simp [preBit]

theorem represents_tape0 (x : List Bool) :
    A.Represents (A.init x) (A.tape0 x) 0 0 (w0 x) := by
  constructor
  · intro j
    by_cases hj : j = 0
    · subst hj; simp [tape0, cellOf]
    · simp only [tape0, Function.update, hj, dite_false, TM.inputTape, w0]
      by_cases h : 0 ≤ j ∧ j < (x.length : ℤ)
      · rw [if_pos h]; simp; omega
      · rw [if_neg h]; simp; omega
  · intro j
    by_cases hj : j = 0
    · subst hj; simp [tape0, val, cellOf, init]
    · simp only [tape0, Function.update, hj, dite_false, TM.inputTape, init, if_false, sub_zero]
      by_cases h : 0 ≤ j ∧ j < (x.length : ℤ)
      · rw [if_pos h, if_pos ⟨by omega, h.2⟩]; rfl
      · rw [if_neg h, if_neg (by omega)]; rfl

/-- TM time at which the sweep for WCC step `k` starts. -/
def tau (w : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => tau w k + sweepLen w k

theorem tau_le (w k : ℕ) : tau w k ≤ 1 + k * (w + 2 * k + 3) := by
  induction k with
  | zero => simp [tau]
  | succ k ih =>
    simp only [tau, sweepLen]
    nlinarith

theorem global (x : List Bool) (k : ℕ)
    (hk : ∀ j < k, A.outCfg (A.run (A.init x) j) = none) :
    A.PhaseCfg (A.run (A.init x) k) (w0 x) k (A.toTM.run (A.toTM.init x) (tau (w0 x) k)) ∧
    ∀ m < tau (w0 x) k, A.toTM.ans (A.toTM.run (A.toTM.init x) m) = none := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [tau]
      rw [A.pre_step]
      exact ⟨A.tape0 x, 0, w0 x, 0, A.represents_tape0 x, by simp,
        Or.inl ⟨rfl, rfl⟩⟩
    · intro m hm
      simp only [tau] at hm
      obtain rfl : m = 0 := by omega
      simp [TM.run, TM.init, TM.ans, answerOf]
  | succ k ih =>
    obtain ⟨hp, hans⟩ := ih (fun j hj => hk j (by omega))
    have hs := A.phase_step _ _ _ _ hp
    refine ⟨?_, ?_⟩
    · simp only [tau]
      rw [TM.run_add, WCC.run_succ]
      exact hs.2.1 (hk k (by omega))
    · intro m hm
      simp only [tau] at hm
      by_cases hlt : m < tau (w0 x) k
      · exact hans m hlt
      · obtain ⟨m', rfl⟩ : ∃ m', m = tau (w0 x) k + m' := ⟨m - tau (w0 x) k, by omega⟩
        rw [TM.run_add]
        exact hs.1 m' (by omega)

/-- **WCC → TM simulation theorem.**  If the WCC `A` decides `L` within `T`
steps, the ordinary TM `A.toTM` decides `L` within
`1 + (T n + 1) * (n + 2 * T n + 5)` steps. -/
theorem toTM_decides {L : Set (List Bool)} {T : ℕ → ℕ} (h : A.Decides L T) :
    A.toTM.Decides L (fun n => 1 + (T n + 1) * (n + 2 * T n + 5)) := by
  intro x
  obtain ⟨b, ⟨s, hs, hout, hfirst⟩, hb⟩ := h x
  have hg := A.global x s (fun j hj => hfirst j hj)
  have hstep := A.phase_step _ _ _ _ hg.1
  refine ⟨b, ⟨tau (w0 x) (s + 1), ?_, ?_, ?_⟩, hb⟩
  · have h1 := tau_le (w0 x) (s + 1)
    have h2 : w0 x ≤ x.length := Nat.sub_le _ _
    have h3 : (s + 1) * (w0 x + 2 * (s + 1) + 3) ≤
        (T x.length + 1) * (x.length + 2 * T x.length + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    show tau (w0 x) (s + 1) ≤ 1 + (T x.length + 1) * (x.length + 2 * T x.length + 5)
    omega
  · simp only [TM.out, tau]
    rw [TM.run_add]
    exact hstep.2.2 b hout
  · intro m hm
    simp only [tau] at hm
    simp only [TM.out]
    by_cases hlt : m < tau (w0 x) s
    · exact hg.2 m hlt
    · obtain ⟨m', rfl⟩ : ∃ m', m = tau (w0 x) s + m' := ⟨m - tau (w0 x) s, by omega⟩
      rw [TM.run_add]
      exact hstep.1 m' (by omega)

end WCC

/-- `P_WCC ⊆ P_TM`, with explicit polynomial `1 + (p + 1) * (X + 2 p + 5)`. -/
theorem P_WCC_subset_P_TM : P_WCC ⊆ P_TM := by
  rintro L ⟨A, p, h⟩
  refine ⟨A.toTM, 1 + (p + 1) * (Polynomial.X + 2 * p + 5), ?_⟩
  have := A.toTM_decides h
  have heq : (fun n : ℕ => (1 + (p + 1) * (Polynomial.X + 2 * p + 5)).eval n) =
      (fun n => 1 + (p.eval n + 1) * (n + 2 * p.eval n + 5)) := by
    funext n; simp
  rw [heq]; exact this

end PVNP.Discrete
