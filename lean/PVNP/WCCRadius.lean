import PVNP.ComplexityEquivalence

/-!
# Radius-`r` discrete WCC ⇄ ordinary TM (Part II, arbitrary fixed finite radius)

`WCCR`: a finite-alphabet quiescent cellular automaton on `ℤ` whose rule reads
the window of radius `r ≥ 1` (`2r + 1` cells), with the same origin-marked input
convention and first-answer semantics as `PVNP.Discrete.WCC`.

* `WCC.toR`, `WCC.toR_decides`: every radius-one WCC is a radius-`r` WCC with
  the identical run (the rule ignores the outer cells), so `P_WCC ⊆ P_WCCR r`.
* `WCCR.toTM`: an explicit ordinary single-tape TM simulating a radius-`r` WCC
  by alternating shifted sweeps; the control state carries the last `2r` tape
  symbols, each sweep shifts the simulated frame by `r` and grows the tape
  region by `2r`; one TM step per simulated cell.
* `WCCR.rsweep_run`, `lsweep_run`, `phase_step`, `global`: exact invariants.
* `WCCR.toTM_decides`: time `1 + (T + 1)(n + 2r(T + 1) + 2r + 1)`.
* `P_WCCR_eq_P_TM`, `NP_WCCR_eq_NP_TM`: for **every** fixed radius `r ≥ 1`.
-/

namespace PVNP.Discrete

/-- A discrete WCC of fixed radius `r ≥ 1`. -/
structure WCCR where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  r : ℕ
  hr : 1 ≤ r
  blank : S
  rule : (Fin (2 * r + 1) → S) → S
  quiescent : rule (fun _ => blank) = blank
  inp : Bool → S
  origin : Option Bool → S
  acc : S → Bool
  rej : S → Bool

/-- Control states of the radius-`r` simulator (buffer of `N = 2r` symbols). -/
inductive RPhase (Γ : Type) (N : ℕ) where
  | pre
  | rs (buf : Fin N → Γ) (fa fr : Bool)
  | ls (buf : Fin N → Γ) (fa fr : Bool)
  | yes
  | no
  deriving DecidableEq, Fintype

namespace WCCR

attribute [instance] WCCR.finS WCCR.decS

variable (A : WCCR)

/-- The radius-`r` window of `c` around cell `i` (index `k` ↦ offset `k - r`). -/
def window (c : ℤ → A.S) (i : ℤ) : Fin (2 * A.r + 1) → A.S := fun k => c (i + k - A.r)

def step (c : ℤ → A.S) : ℤ → A.S := fun i => A.rule (A.window c i)

def run (c : ℤ → A.S) (t : ℕ) : ℤ → A.S := (A.step)^[t] c

def init (x : List Bool) (i : ℤ) : A.S :=
  if i = 0 then A.origin x.head?
  else if 0 < i ∧ i < x.length then A.inp (x.getD i.toNat false) else A.blank

open Classical in
noncomputable def outCfg (c : ℤ → A.S) : Option Bool :=
  answerOf (decide (∃ i, A.acc (c i) = true)) (decide (∃ i, A.rej (c i) = true))

noncomputable def out (x : List Bool) (s : ℕ) : Option Bool := A.outCfg (A.run (A.init x) s)

def Decides (L : Set (List Bool)) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, DecidesAt (A.out x) (T x.length) x L

theorem run_succ (c : ℤ → A.S) (t : ℕ) : A.run c (t + 1) = A.step (A.run c t) := by
  simp [run, Function.iterate_succ_apply']

/-! ### Buffers -/

section Buffers

variable {Γ : Type} {N : ℕ}

/-- Window for a left-to-right sweep: buffer (oldest first) followed by `z`. -/
def winR (buf : Fin N → Γ) (z : Γ) : Fin (N + 1) → Γ :=
  fun k => if h : k.val < N then buf ⟨k.val, h⟩ else z

/-- Shift a left-to-right buffer, appending `z`. -/
def shiftR (buf : Fin N → Γ) (z : Γ) : Fin N → Γ :=
  fun k => if h : k.val + 1 < N then buf ⟨k.val + 1, h⟩ else z

/-- Window for a right-to-left sweep: `z` followed by the buffer (nearest first). -/
def winL (z : Γ) (buf : Fin N → Γ) : Fin (N + 1) → Γ :=
  fun k => if h : k.val = 0 then z else buf ⟨k.val - 1, by omega⟩

/-- Shift a right-to-left buffer, prepending `z`. -/
def shiftL (z : Γ) (buf : Fin N → Γ) : Fin N → Γ :=
  fun k => if h : k.val = 0 then z else buf ⟨k.val - 1, by omega⟩

end Buffers

/-! ### The machine -/

abbrev Sym := Option (Bool ⊕ A.S)

def val : A.Sym → A.S
  | none => A.blank
  | some (Sum.inl b) => A.inp b
  | some (Sum.inr s) => s

def cellOf (s : A.S) : A.Sym := some (Sum.inr s)

def preBit : A.Sym → Option Bool
  | some (Sum.inl b) => some b
  | _ => none

/-- End-of-sweep test for a left-to-right sweep. -/
def stopR (buf : Fin (2 * A.r) → A.Sym) (z : A.Sym) : Prop :=
  (∀ k : Fin (2 * A.r), 1 ≤ k.val → buf k = none) ∧ z = none

/-- End-of-sweep test for a right-to-left sweep. -/
def stopL (z : A.Sym) (buf : Fin (2 * A.r) → A.Sym) : Prop :=
  z = none ∧ ∀ k : Fin (2 * A.r), k.val + 1 < 2 * A.r → buf k = none

instance (buf : Fin (2 * A.r) → A.Sym) (z : A.Sym) : Decidable (A.stopR buf z) := by
  unfold stopR; infer_instance

instance (z : A.Sym) (buf : Fin (2 * A.r) → A.Sym) : Decidable (A.stopL z buf) := by
  unfold stopL; infer_instance

/-- Transition function of the radius-`r` simulator. -/
def simδ : RPhase A.Sym (2 * A.r) → A.Sym → Option (RPhase A.Sym (2 * A.r) × A.Sym × Dir)
  | .pre, z => some (.rs (fun _ => none) (A.acc A.blank) (A.rej A.blank),
      A.cellOf (A.origin (A.preBit z)), Dir.S)
  | .rs buf fa fr, z =>
    if A.stopR buf z then
      (if fa then some (.yes, z, Dir.S)
       else if fr then some (.no, z, Dir.S)
       else some (.ls (fun _ => none) (A.acc A.blank) (A.rej A.blank),
          A.cellOf (A.rule fun k => A.val (winR buf z k)), Dir.S))
    else some (.rs (shiftR buf z) (fa || A.acc (A.val z)) (fr || A.rej (A.val z)),
          A.cellOf (A.rule fun k => A.val (winR buf z k)), Dir.R)
  | .ls buf fa fr, z =>
    if A.stopL z buf then
      (if fa then some (.yes, z, Dir.S)
       else if fr then some (.no, z, Dir.S)
       else some (.rs (fun _ => none) (A.acc A.blank) (A.rej A.blank),
          A.cellOf (A.rule fun k => A.val (winL z buf k)), Dir.S))
    else some (.ls (shiftL z buf) (fa || A.acc (A.val z)) (fr || A.rej (A.val z)),
          A.cellOf (A.rule fun k => A.val (winL z buf k)), Dir.L)
  | .yes, _ => none
  | .no, _ => none

/-- The simulating ordinary Turing machine. -/
abbrev toTM : TM where
  Λ := RPhase A.Sym (2 * A.r)
  Γ := A.Sym
  blank := none
  inp b := some (Sum.inl b)
  start := .pre
  δ := A.simδ
  acc q := decide (q = .yes)
  rej q := decide (q = .no)

def Represents (c : ℤ → A.S) (T : ℤ → A.Sym) (s L R : ℤ) : Prop :=
  (∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) ∧ ∀ j, A.val (T j) = c (j - s)

theorem none_of_outside {T : ℤ → A.Sym} {L R : ℤ}
    (h : ∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) {j : ℤ} (hj : ¬ (L ≤ j ∧ j ≤ R)) : T j = none := by
  by_contra hc; exact hj ((h j).1 hc)

theorem next_eq {c : A.toTM.Cfg} {q' : RPhase A.Sym (2 * A.r)} {a : A.Sym} {d : Dir}
    (h : A.simδ c.q (c.tape c.head) = some (q', a, d)) :
    A.toTM.next c = ⟨q', Function.update c.tape c.head a, c.head + d.shift⟩ := by
  simp [TM.next, TM.step, h]

/-! ### Left-to-right sweep -/

/-- Buffer content when the head is at `p` during a left-to-right sweep. -/
def bufAt (T : ℤ → A.Sym) (p : ℤ) : Fin (2 * A.r) → A.Sym := fun k => T (p - 2 * A.r + k)

def newR (T : ℤ → A.Sym) (j : ℤ) : A.S := A.rule fun k => A.val (T (j - 2 * A.r + k))

def wrR (T : ℤ → A.Sym) (L : ℤ) (m : ℕ) (j : ℤ) : A.Sym :=
  if L ≤ j ∧ j < L + m then A.cellOf (A.newR T j) else T j

def accR (T : ℤ → A.Sym) (L : ℤ) (m : ℕ) : Bool :=
  (List.range m).any fun k => A.acc (A.val (T (L + k)))

def rejR (T : ℤ → A.Sym) (L : ℤ) (m : ℕ) : Bool :=
  (List.range m).any fun k => A.rej (A.val (T (L + k)))

theorem winR_bufAt (T : ℤ → A.Sym) (p : ℤ) (k : Fin (2 * A.r + 1)) :
    winR (A.bufAt T p) (T p) k = T (p - 2 * A.r + (k : ℕ)) := by
  simp only [winR, bufAt, Fin.val_mk]
  split_ifs with h
  all_goals (try rfl)
  all_goals (congr 1; have := k.2; omega)

theorem shiftR_bufAt (T : ℤ → A.Sym) (p : ℤ) :
    shiftR (A.bufAt T p) (T p) = A.bufAt T (p + 1) := by
  funext k
  simp only [shiftR, bufAt]
  split_ifs with h
  · congr 1; push_cast; ring
  · congr 1; have := k.2; push_cast; omega

theorem bufAt_start (T : ℤ → A.Sym) {L R : ℤ} (hreg : ∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) :
    A.bufAt T L = fun _ => none := by
  funext k
  have := k.2
  exact A.none_of_outside hreg (by omega)

theorem rsweep_run (T : ℤ → A.Sym) (L R : ℤ) (fa fr : Bool)
    (hreg : ∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) (hLR : L ≤ R) (m : ℕ)
    (hm : (m : ℤ) ≤ R - L + 2 * A.r) :
    A.toTM.run ⟨.rs (fun _ => none) fa fr, T, L⟩ m =
      ⟨.rs (A.bufAt T (L + m)) (fa || A.accR T L m) (fr || A.rejR T L m), A.wrR T L m, L + m⟩ := by
  have hr := A.hr
  induction m with
  | zero =>
    have hw : A.wrR T L 0 = T := funext fun j => by simp [wrR]
    simp [TM.run, hw, accR, rejR, A.bufAt_start T hreg]
  | succ m ih =>
    rw [TM.run_succ, ih (by omega)]
    have hz : A.wrR T L m (L + m) = T (L + m) := by simp [wrR]
    have hcont : ¬ A.stopR (A.bufAt T (L + m)) (T (L + m)) := by
      rintro ⟨h1, h2⟩
      by_cases hle : L + m ≤ R
      · exact ((hreg (L + m)).2 ⟨by omega, hle⟩) h2
      · have hk : ((R - (L + m - 2 * A.r)).toNat) < 2 * A.r := by omega
        have := h1 ⟨_, hk⟩ (by simp; omega)
        simp only [bufAt] at this
        rw [show (L + m - 2 * A.r : ℤ) + ((R - (L + m - 2 * A.r)).toNat : ℕ) = R by omega] at this
        exact ((hreg R).2 ⟨hLR, le_rfl⟩) this
    rw [A.next_eq (q' := .rs (A.bufAt T (L + m + 1))
        ((fa || A.accR T L m) || A.acc (A.val (T (L + m))))
        ((fr || A.rejR T L m) || A.rej (A.val (T (L + m)))))
        (a := A.cellOf (A.newR T (L + m))) (d := Dir.R)]
    · have e3 : L + ((m + 1 : ℕ) : ℤ) = L + m + Dir.R.shift := by
        simp only [Dir.shift]; push_cast; ring
      rw [e3]
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
      simp only [Dir.shift]
      simp [accR, rejR, List.range_succ, List.any_append, Bool.or_assoc]
    · simp only [hz]
      simp only [simδ, if_neg hcont, A.shiftR_bufAt, A.winR_bufAt, newR]

/-! ### Right-to-left sweep -/

/-- Buffer content when the head is at `p` during a right-to-left sweep. -/
def bufAtL (T : ℤ → A.Sym) (p : ℤ) : Fin (2 * A.r) → A.Sym := fun k => T (p + 1 + k)

def newL (T : ℤ → A.Sym) (j : ℤ) : A.S := A.rule fun k => A.val (T (j + k))

def wrL (T : ℤ → A.Sym) (R : ℤ) (m : ℕ) (j : ℤ) : A.Sym :=
  if R - m < j ∧ j ≤ R then A.cellOf (A.newL T j) else T j

def accL (T : ℤ → A.Sym) (R : ℤ) (m : ℕ) : Bool :=
  (List.range m).any fun k => A.acc (A.val (T (R - k)))

def rejL (T : ℤ → A.Sym) (R : ℤ) (m : ℕ) : Bool :=
  (List.range m).any fun k => A.rej (A.val (T (R - k)))

theorem winL_bufAtL (T : ℤ → A.Sym) (p : ℤ) (k : Fin (2 * A.r + 1)) :
    winL (T p) (A.bufAtL T p) k = T (p + (k : ℕ)) := by
  simp only [winL, bufAtL, Fin.val_mk]
  split_ifs with h
  all_goals (try rfl)
  all_goals (congr 1; omega)

theorem shiftL_bufAtL (T : ℤ → A.Sym) (p : ℤ) :
    shiftL (T p) (A.bufAtL T p) = A.bufAtL T (p - 1) := by
  funext k
  simp only [shiftL, bufAtL]
  split_ifs with h
  · congr 1; simp [h]
  · congr 1; push_cast; omega

theorem bufAtL_start (T : ℤ → A.Sym) {L R : ℤ} (hreg : ∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) :
    A.bufAtL T R = fun _ => none := by
  funext k
  exact A.none_of_outside hreg (by omega)

theorem lsweep_run (T : ℤ → A.Sym) (L R : ℤ) (fa fr : Bool)
    (hreg : ∀ j, T j ≠ none ↔ L ≤ j ∧ j ≤ R) (hLR : L ≤ R) (m : ℕ)
    (hm : (m : ℤ) ≤ R - L + 2 * A.r) :
    A.toTM.run ⟨.ls (fun _ => none) fa fr, T, R⟩ m =
      ⟨.ls (A.bufAtL T (R - m)) (fa || A.accL T R m) (fr || A.rejL T R m), A.wrL T R m, R - m⟩ := by
  have hr := A.hr
  induction m with
  | zero =>
    have hw : A.wrL T R 0 = T := funext fun j => by
      simp only [wrL, CharP.cast_eq_zero, sub_zero]
      rw [if_neg (by omega)]
    simp [TM.run, hw, accL, rejL, A.bufAtL_start T hreg]
  | succ m ih =>
    rw [TM.run_succ, ih (by omega)]
    have hz : A.wrL T R m (R - m) = T (R - m) := by simp [wrL]
    have hcont : ¬ A.stopL (T (R - m)) (A.bufAtL T (R - m)) := by
      rintro ⟨h2, h1⟩
      by_cases hle : L ≤ R - m
      · exact ((hreg (R - m)).2 ⟨hle, by omega⟩) h2
      · have hk : ((L - (R - m + 1)).toNat) < 2 * A.r := by omega
        have := h1 ⟨_, hk⟩ (by simp; omega)
        simp only [bufAtL] at this
        rw [show (R - m + 1 : ℤ) + ((L - (R - m + 1)).toNat : ℕ) = L by omega] at this
        exact ((hreg L).2 ⟨le_rfl, hLR⟩) this
    rw [A.next_eq (q' := .ls (A.bufAtL T (R - m - 1))
        ((fa || A.accL T R m) || A.acc (A.val (T (R - m))))
        ((fr || A.rejL T R m) || A.rej (A.val (T (R - m)))))
        (a := A.cellOf (A.newL T (R - m))) (d := Dir.L)]
    · have e3 : R - ((m + 1 : ℕ) : ℤ) = R - m + Dir.L.shift := by
        simp only [Dir.shift]; push_cast; ring
      rw [e3]
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
      simp only [Dir.shift, show R - (m : ℤ) + -1 = R - m - 1 by ring]
      simp [accL, rejL, List.range_succ, List.any_append, Bool.or_assoc]
    · simp only [hz]
      simp only [simδ, if_neg hcont, A.shiftL_bufAtL, A.winL_bufAtL, newL]

/-! ### One sweep simulates one synchronous update -/

theorem represents_wrR {c : ℤ → A.S} {T : ℤ → A.Sym} {s L R : ℤ}
    (h : A.Represents c T s L R) (hLR : L ≤ R) :
    A.Represents (A.step c) (A.wrR T L (R - L + 2 * A.r + 1).toNat) (s + A.r) L (R + 2 * A.r) := by
  obtain ⟨hreg, hval⟩ := h
  have hr := A.hr
  have hn : (((R - L + 2 * A.r + 1).toNat : ℕ) : ℤ) = R - L + 2 * A.r + 1 := by omega
  constructor
  · intro j
    simp only [wrR, hn]
    by_cases hj : L ≤ j ∧ j < L + (R - L + 2 * A.r + 1)
    · rw [if_pos hj]; simp [cellOf]; omega
    · rw [if_neg hj, hreg j]; omega
  · intro j
    simp only [wrR, hn]
    by_cases hj : L ≤ j ∧ j < L + (R - L + 2 * A.r + 1)
    · rw [if_pos hj]
      show A.rule (fun k => A.val (T (j - 2 * A.r + k))) = A.step c (j - (s + A.r))
      simp only [step, window, hval]
      congr 1; funext k; congr 1; ring
    · rw [if_neg hj]
      have h0 : T j = none := A.none_of_outside hreg (by omega)
      have hb : A.window c (j - (s + A.r)) = fun _ => A.blank := by
        funext k
        have hk := k.2
        have := hval (j - 2 * A.r + k)
        rw [A.none_of_outside hreg (by omega)] at this
        simp only [val] at this
        simp only [window]
        rw [this]; congr 1; ring
      rw [h0]
      simp only [val, step]
      rw [hb, A.quiescent]

theorem represents_wrL {c : ℤ → A.S} {T : ℤ → A.Sym} {s L R : ℤ}
    (h : A.Represents c T s L R) (hLR : L ≤ R) :
    A.Represents (A.step c) (A.wrL T R (R - L + 2 * A.r + 1).toNat) (s - A.r) (L - 2 * A.r) R := by
  obtain ⟨hreg, hval⟩ := h
  have hr := A.hr
  have hn : (((R - L + 2 * A.r + 1).toNat : ℕ) : ℤ) = R - L + 2 * A.r + 1 := by omega
  constructor
  · intro j
    simp only [wrL, hn]
    by_cases hj : R - (R - L + 2 * A.r + 1) < j ∧ j ≤ R
    · rw [if_pos hj]; simp [cellOf]; omega
    · rw [if_neg hj, hreg j]; omega
  · intro j
    simp only [wrL, hn]
    by_cases hj : R - (R - L + 2 * A.r + 1) < j ∧ j ≤ R
    · rw [if_pos hj]
      show A.rule (fun k => A.val (T (j + k))) = A.step c (j - (s - A.r))
      simp only [step, window, hval]
      congr 1; funext k; congr 1; ring
    · rw [if_neg hj]
      have h0 : T j = none := A.none_of_outside hreg (by omega)
      have hb : A.window c (j - (s - A.r)) = fun _ => A.blank := by
        funext k
        have hk := k.2
        have := hval (j + k)
        rw [A.none_of_outside hreg (by omega)] at this
        simp only [val] at this
        simp only [window]
        rw [this]; congr 1; ring
      rw [h0]
      simp only [val, step]
      rw [hb, A.quiescent]

theorem accR_iff {c : ℤ → A.S} {T : ℤ → A.Sym} {s L R : ℤ}
    (h : A.Represents c T s L R) (hLR : L ≤ R) (P : A.S → Bool) :
    (P A.blank || (List.range (R - L + 2 * A.r).toNat).any fun k => P (A.val (T (L + k)))) = true ↔
      ∃ i, P (c i) = true := by
  obtain ⟨hreg, hval⟩ := h
  have hr := A.hr
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
  constructor
  · rintro (hb | ⟨k, -, hk⟩)
    · refine ⟨R + 1 - s, ?_⟩
      have := hval (R + 1)
      rw [A.none_of_outside hreg (by omega)] at this
      simp only [val] at this
      rw [← this]; exact hb
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
    (P A.blank || (List.range (R - L + 2 * A.r).toNat).any fun k => P (A.val (T (R - k)))) = true ↔
      ∃ i, P (c i) = true := by
  obtain ⟨hreg, hval⟩ := h
  have hr := A.hr
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

theorem answerOf_none {a b : Bool} (h : answerOf a b = none) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all [answerOf]

theorem answerOf_true {a b : Bool} (h : answerOf a b = some true) : a = true := by
  cases a <;> cases b <;> simp_all [answerOf]

theorem answerOf_false' {a b : Bool} (h : answerOf a b = some false) : a = false ∧ b = true := by
  cases a <;> cases b <;> simp_all [answerOf]

/-- Width `R - L` of the represented region at the start of sweep `k`. -/
def wid (w k : ℕ) : ℕ := w + 2 * A.r * k

theorem wid_succ (w k : ℕ) : A.wid w (k + 1) = A.wid w k + 2 * A.r := by
  simp only [wid]; ring

/-- Simulator configuration at the start of the sweep for WCC step `k`. -/
def PhaseCfg (c : ℤ → A.S) (w k : ℕ) (cfg : A.toTM.Cfg) : Prop :=
  ∃ T L R s, A.Represents c T s L R ∧ R - L = (A.wid w k : ℤ) ∧
    ((k % 2 = 0 ∧ cfg = ⟨.rs (fun _ => none) (A.acc A.blank) (A.rej A.blank), T, L⟩) ∨
     (k % 2 = 1 ∧ cfg = ⟨.ls (fun _ => none) (A.acc A.blank) (A.rej A.blank), T, R⟩))

/-- Length of the `k`-th sweep, including its turn-around step. -/
def sweepLen (w k : ℕ) : ℕ := A.wid w k + 2 * A.r + 1

theorem ans_rs (T : ℤ → A.Sym) (h : ℤ) (buf : Fin (2 * A.r) → A.Sym) (fa fr : Bool) :
    A.toTM.ans ⟨.rs buf fa fr, T, h⟩ = none := by
  simp [TM.ans, answerOf]

theorem ans_ls (T : ℤ → A.Sym) (h : ℤ) (buf : Fin (2 * A.r) → A.Sym) (fa fr : Bool) :
    A.toTM.ans ⟨.ls buf fa fr, T, h⟩ = none := by
  simp [TM.ans, answerOf]

/-- One sweep: no answer is displayed during it; at its end the simulator
either displays exactly the WCC output of `c`, or (if that output is `none`)
is in the phase configuration for `A.step c`. -/
theorem phase_step (c : ℤ → A.S) (w k : ℕ) (cfg : A.toTM.Cfg)
    (hp : A.PhaseCfg c w k cfg) :
    (∀ m < A.sweepLen w k, A.toTM.ans (A.toTM.run cfg m) = none) ∧
    (A.outCfg c = none → A.PhaseCfg (A.step c) w (k + 1) (A.toTM.run cfg (A.sweepLen w k))) ∧
    (∀ b, A.outCfg c = some b → A.toTM.ans (A.toTM.run cfg (A.sweepLen w k)) = some b) := by
  obtain ⟨T, L, R, s, hrep, hw, hcfg⟩ := hp
  have hr := A.hr
  have hLR : L ≤ R := by omega
  have hlen : A.sweepLen w k = (R - L + 2 * A.r).toNat + 1 := by
    simp only [sweepLen]; omega
  rcases hcfg with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
  · -- left-to-right sweep
    have hrun := A.rsweep_run T L R (A.acc A.blank) (A.rej A.blank) hrep.1 hLR
    have hmid : ∀ m < A.sweepLen w k, A.toTM.ans (A.toTM.run
        ⟨.rs (fun _ => none) (A.acc A.blank) (A.rej A.blank), T, L⟩ m) = none := by
      intro m hm
      rw [hrun m (by omega)]; exact A.ans_rs _ _ _ _ _
    set m0 := (R - L + 2 * A.r).toNat with hm0def
    have hend := hrun m0 (by omega)
    have eR : L + (m0 : ℤ) = R + 2 * A.r := by omega
    rw [eR] at hend
    have hz : A.wrR T L m0 (R + 2 * A.r) = T (R + 2 * A.r) := by
      simp only [wrR]; rw [if_neg (by omega)]
    have hstop : A.stopR (A.bufAt T (R + 2 * A.r)) (T (R + 2 * A.r)) := by
      refine ⟨fun k hk => ?_, A.none_of_outside hrep.1 (by omega)⟩
      simp only [bufAt]
      exact A.none_of_outside hrep.1 (by omega)
    have hfa : (A.acc A.blank || A.accR T L m0) = true ↔ ∃ i, A.acc (c i) = true :=
      A.accR_iff hrep hLR A.acc
    have hfr : (A.rej A.blank || A.rejR T L m0) = true ↔ ∃ i, A.rej (c i) = true :=
      A.accR_iff hrep hLR A.rej
    have hout := A.outCfg_eq c _ _ hfa hfr
    have hlast : A.toTM.run ⟨.rs (fun _ => none) (A.acc A.blank) (A.rej A.blank), T, L⟩
        (A.sweepLen w k) = A.toTM.next ⟨.rs (A.bufAt T (R + 2 * A.r))
          (A.acc A.blank || A.accR T L m0) (A.rej A.blank || A.rejR T L m0),
          A.wrR T L m0, R + 2 * A.r⟩ := by
      rw [hlen, TM.run_succ, hend]
    refine ⟨hmid, ?_, ?_⟩
    · intro hnone
      rw [hout] at hnone
      obtain ⟨hfa0, hfr0⟩ := answerOf_none hnone
      rw [hlast, hfa0, hfr0]
      rw [A.next_eq (q' := .ls (fun _ => none) (A.acc A.blank) (A.rej A.blank))
        (a := A.cellOf (A.newR T (R + 2 * A.r))) (d := Dir.S)]
      · refine ⟨A.wrR T L (R - L + 2 * A.r + 1).toNat, L, R + 2 * A.r, s + A.r,
          A.represents_wrR hrep hLR, ?_, Or.inr ⟨by omega, ?_⟩⟩
        · rw [A.wid_succ]; push_cast; omega
        have hw' : Function.update (A.wrR T L m0) (R + 2 * A.r)
            (A.cellOf (A.newR T (R + 2 * A.r))) = A.wrR T L (R - L + 2 * A.r + 1).toNat := by
          funext j
          by_cases hj : j = R + 2 * A.r
          · subst hj; simp only [Function.update_self, wrR]
            rw [if_pos ⟨by omega, by omega⟩]
          · simp only [Function.update, hj, dite_false, wrR]
            by_cases h3 : L ≤ j ∧ j < L + (m0 : ℤ)
            · rw [if_pos h3, if_pos ⟨h3.1, by omega⟩]
            · rw [if_neg h3, if_neg (by omega)]
        simp [hw', Dir.shift]
      · simp only [hz, simδ, if_pos hstop, Bool.false_eq_true, if_false, A.winR_bufAt, newR]
    · intro b hb
      rw [hout] at hb
      rw [hlast]
      cases b
      · obtain ⟨hfa0, hfr0⟩ := answerOf_false' hb
        rw [hfa0, hfr0, A.next_eq (q' := .no) (a := T (R + 2 * A.r)) (d := Dir.S)]
        · simp [TM.ans, answerOf]
        · simp only [hz, simδ, if_pos hstop, Bool.false_eq_true, if_false, if_true]
      · have hfa0 := answerOf_true hb
        rw [hfa0, A.next_eq (q' := .yes) (a := T (R + 2 * A.r)) (d := Dir.S)]
        · simp [TM.ans, answerOf]
        · simp only [hz, simδ, if_pos hstop, if_true]
  · -- right-to-left sweep
    have hrun := A.lsweep_run T L R (A.acc A.blank) (A.rej A.blank) hrep.1 hLR
    have hmid : ∀ m < A.sweepLen w k, A.toTM.ans (A.toTM.run
        ⟨.ls (fun _ => none) (A.acc A.blank) (A.rej A.blank), T, R⟩ m) = none := by
      intro m hm
      rw [hrun m (by omega)]; exact A.ans_ls _ _ _ _ _
    set m0 := (R - L + 2 * A.r).toNat with hm0def
    have hend := hrun m0 (by omega)
    have eR : R - (m0 : ℤ) = L - 2 * A.r := by omega
    rw [eR] at hend
    have hz : A.wrL T R m0 (L - 2 * A.r) = T (L - 2 * A.r) := by
      simp only [wrL]; rw [if_neg (by omega)]
    have hstop : A.stopL (T (L - 2 * A.r)) (A.bufAtL T (L - 2 * A.r)) := by
      refine ⟨A.none_of_outside hrep.1 (by omega), fun k hk => ?_⟩
      simp only [bufAtL]
      exact A.none_of_outside hrep.1 (by omega)
    have hfa : (A.acc A.blank || A.accL T R m0) = true ↔ ∃ i, A.acc (c i) = true :=
      A.accL_iff hrep hLR A.acc
    have hfr : (A.rej A.blank || A.rejL T R m0) = true ↔ ∃ i, A.rej (c i) = true :=
      A.accL_iff hrep hLR A.rej
    have hout := A.outCfg_eq c _ _ hfa hfr
    have hlast : A.toTM.run ⟨.ls (fun _ => none) (A.acc A.blank) (A.rej A.blank), T, R⟩
        (A.sweepLen w k) = A.toTM.next ⟨.ls (A.bufAtL T (L - 2 * A.r))
          (A.acc A.blank || A.accL T R m0) (A.rej A.blank || A.rejL T R m0),
          A.wrL T R m0, L - 2 * A.r⟩ := by
      rw [hlen, TM.run_succ, hend]
    refine ⟨hmid, ?_, ?_⟩
    · intro hnone
      rw [hout] at hnone
      obtain ⟨hfa0, hfr0⟩ := answerOf_none hnone
      rw [hlast, hfa0, hfr0]
      rw [A.next_eq (q' := .rs (fun _ => none) (A.acc A.blank) (A.rej A.blank))
        (a := A.cellOf (A.newL T (L - 2 * A.r))) (d := Dir.S)]
      · refine ⟨A.wrL T R (R - L + 2 * A.r + 1).toNat, L - 2 * A.r, R, s - A.r,
          A.represents_wrL hrep hLR, ?_, Or.inl ⟨by omega, ?_⟩⟩
        · rw [A.wid_succ]; push_cast; omega
        have hw' : Function.update (A.wrL T R m0) (L - 2 * A.r)
            (A.cellOf (A.newL T (L - 2 * A.r))) = A.wrL T R (R - L + 2 * A.r + 1).toNat := by
          funext j
          by_cases hj : j = L - 2 * A.r
          · subst hj; simp only [Function.update_self, wrL]
            rw [if_pos ⟨by omega, by omega⟩]
          · simp only [Function.update, hj, dite_false, wrL]
            by_cases h3 : R - (m0 : ℤ) < j ∧ j ≤ R
            · rw [if_pos h3, if_pos ⟨by omega, h3.2⟩]
            · rw [if_neg h3, if_neg (by omega)]
        simp [hw', Dir.shift]
      · simp only [hz, simδ, if_pos hstop, Bool.false_eq_true, if_false, A.winL_bufAtL, newL]
    · intro b hb
      rw [hout] at hb
      rw [hlast]
      cases b
      · obtain ⟨hfa0, hfr0⟩ := answerOf_false' hb
        rw [hfa0, hfr0, A.next_eq (q' := .no) (a := T (L - 2 * A.r)) (d := Dir.S)]
        · simp [TM.ans, answerOf]
        · simp only [hz, simδ, if_pos hstop, Bool.false_eq_true, if_false, if_true]
      · have hfa0 := answerOf_true hb
        rw [hfa0, A.next_eq (q' := .yes) (a := T (L - 2 * A.r)) (d := Dir.S)]
        · simp [TM.ans, answerOf]
        · simp only [hz, simδ, if_pos hstop, if_true]

/-! ### Preprocessing and the global simulation -/

/-- Width parameter of the initial tape region `[0, |x| - 1]` (at least one cell). -/
def w0 (x : List Bool) : ℕ := x.length - 1

/-- Tape after the preprocessing step. -/
def tape0 (x : List Bool) : ℤ → A.Sym :=
  Function.update (A.toTM.inputTape x) 0 (A.cellOf (A.origin x.head?))

theorem pre_step (x : List Bool) :
    A.toTM.run (A.toTM.init x) 1 =
      ⟨.rs (fun _ => none) (A.acc A.blank) (A.rej A.blank), A.tape0 x, 0⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, TM.run_succ]
  simp only [TM.run, Function.iterate_zero, id]
  rw [A.next_eq (q' := .rs (fun _ => none) (A.acc A.blank) (A.rej A.blank))
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

/-- TM time at which the sweep for WCC step `k` starts (radius `r`, width `w`). -/
def tauR (r w : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => tauR r w k + (w + 2 * r * k + 2 * r + 1)

theorem tauR_succ (w k : ℕ) : tauR A.r w (k + 1) = tauR A.r w k + A.sweepLen w k := rfl

theorem tauR_le (r w k : ℕ) : tauR r w k ≤ 1 + k * (w + 2 * r * k + 2 * r + 1) := by
  induction k with
  | zero => simp [tauR]
  | succ k ih =>
    simp only [tauR]
    nlinarith [ih, Nat.zero_le (r * k), Nat.zero_le r]

theorem global (x : List Bool) (k : ℕ)
    (hk : ∀ j < k, A.outCfg (A.run (A.init x) j) = none) :
    A.PhaseCfg (A.run (A.init x) k) (w0 x) k (A.toTM.run (A.toTM.init x) (tauR A.r (w0 x) k)) ∧
    ∀ m < tauR A.r (w0 x) k, A.toTM.ans (A.toTM.run (A.toTM.init x) m) = none := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [tauR]
      rw [A.pre_step]
      exact ⟨A.tape0 x, 0, w0 x, 0, A.represents_tape0 x, by simp [wid],
        Or.inl ⟨rfl, rfl⟩⟩
    · intro m hm
      simp only [tauR] at hm
      obtain rfl : m = 0 := by omega
      simp [TM.run, TM.init, TM.ans, answerOf]
  | succ k ih =>
    obtain ⟨hp, hans⟩ := ih (fun j hj => hk j (by omega))
    have hs := A.phase_step _ _ _ _ hp
    refine ⟨?_, ?_⟩
    · rw [A.tauR_succ, TM.run_add, WCCR.run_succ]
      exact hs.2.1 (hk k (by omega))
    · intro m hm
      rw [A.tauR_succ] at hm
      by_cases hlt : m < tauR A.r (w0 x) k
      · exact hans m hlt
      · obtain ⟨m', rfl⟩ : ∃ m', m = tauR A.r (w0 x) k + m' :=
          ⟨m - tauR A.r (w0 x) k, by omega⟩
        rw [TM.run_add]
        exact hs.1 m' (by omega)

/-- **Radius-`r` WCC → TM simulation theorem.**  If the radius-`r` WCC `A`
decides `L` within `T` steps, the ordinary TM `A.toTM` decides `L` within
`1 + (T n + 1)(n + 2r(T n + 1) + 2r + 1)` steps (for `r = 1` this is the
radius-one bound `1 + (T n + 1)(n + 2 T n + 5)`). -/
theorem toTM_decides {L : Set (List Bool)} {T : ℕ → ℕ} (h : A.Decides L T) :
    A.toTM.Decides L (fun n => 1 + (T n + 1) * (n + 2 * A.r * (T n + 1) + 2 * A.r + 1)) := by
  intro x
  obtain ⟨b, ⟨s, hs, hout, hfirst⟩, hb⟩ := h x
  have hg := A.global x s (fun j hj => hfirst j hj)
  have hstep := A.phase_step _ _ _ _ hg.1
  refine ⟨b, ⟨tauR A.r (w0 x) (s + 1), ?_, ?_, ?_⟩, hb⟩
  · have h1 := tauR_le A.r (w0 x) (s + 1)
    have h2 : w0 x ≤ x.length := Nat.sub_le _ _
    have h4 : 2 * A.r * (s + 1) ≤ 2 * A.r * (T x.length + 1) :=
      Nat.mul_le_mul le_rfl (by omega)
    have h3 : (s + 1) * (w0 x + 2 * A.r * (s + 1) + 2 * A.r + 1) ≤
        (T x.length + 1) * (x.length + 2 * A.r * (T x.length + 1) + 2 * A.r + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    show tauR A.r (w0 x) (s + 1) ≤
      1 + (T x.length + 1) * (x.length + 2 * A.r * (T x.length + 1) + 2 * A.r + 1)
    omega
  · simp only [TM.out]
    rw [A.tauR_succ, TM.run_add]
    exact hstep.2.2 b hout
  · intro m hm
    rw [A.tauR_succ] at hm
    simp only [TM.out]
    by_cases hlt : m < tauR A.r (w0 x) s
    · exact hg.2 m hlt
    · obtain ⟨m', rfl⟩ : ∃ m', m = tauR A.r (w0 x) s + m' :=
        ⟨m - tauR A.r (w0 x) s, by omega⟩
      rw [TM.run_add]
      exact hstep.1 m' (by omega)

end WCCR

/-! ### Radius-one WCCs are radius-`r` WCCs -/

namespace WCC

variable (B : WCC)

/-- A radius-one WCC viewed as a radius-`r` WCC whose rule ignores all cells
of the window except the centre and its two neighbours. -/
def toR (r : ℕ) (hr : 1 ≤ r) : WCCR where
  S := B.S
  r := r
  hr := hr
  blank := B.blank
  rule w := B.rule (w ⟨r - 1, by omega⟩) (w ⟨r, by omega⟩) (w ⟨r + 1, by omega⟩)
  quiescent := B.quiescent
  inp := B.inp
  origin := B.origin
  acc := B.acc
  rej := B.rej

theorem toR_step (r : ℕ) (hr : 1 ≤ r) (c : ℤ → B.S) : (B.toR r hr).step c = B.step c := by
  funext i
  show B.rule (c (i + ((r - 1 : ℕ) : ℤ) - r)) (c (i + (r : ℤ) - r))
      (c (i + ((r + 1 : ℕ) : ℤ) - r)) = B.rule (c (i - 1)) (c i) (c (i + 1))
  rw [show i + ((r - 1 : ℕ) : ℤ) - r = i - 1 by omega, show i + (r : ℤ) - r = i by omega,
    show i + ((r + 1 : ℕ) : ℤ) - r = i + 1 by omega]

theorem toR_run (r : ℕ) (hr : 1 ≤ r) (c : ℤ → B.S) (t : ℕ) :
    (B.toR r hr).run c t = B.run c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [WCCR.run_succ, WCC.run_succ, ih]
    exact B.toR_step r hr _

theorem toR_out (r : ℕ) (hr : 1 ≤ r) (x : List Bool) (s : ℕ) :
    (B.toR r hr).out x s = B.out x s :=
  congrArg B.outCfg (B.toR_run r hr (B.init x) s)

/-- The embedding preserves the decision run step for step. -/
theorem toR_decides (r : ℕ) (hr : 1 ≤ r) {L : Set (List Bool)} {T : ℕ → ℕ}
    (h : B.Decides L T) : (B.toR r hr).Decides L T := by
  intro x
  rw [show (B.toR r hr).out x = B.out x from funext (B.toR_out r hr x)]
  exact h x

end WCC

/-! ### Radius-`r` complexity classes -/

/-- Languages decided in polynomial time by a radius-`r` WCC. -/
def P_WCCR (r : ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (A : WCCR) (p : Polynomial ℕ), A.r = r ∧ A.Decides L (fun n => p.eval n)}

/-- Verifier NP over radius-`r` WCC verifiers. -/
def NP_WCCR (r : ℕ) : Set (Set (List Bool)) := NPOf (P_WCCR r)

/-- Every radius-`r` polynomial-time language is in `P_TM`, with explicit
polynomial `1 + (p + 1)(X + 2r(p + 1) + 2r + 1)`. -/
theorem P_WCCR_subset_P_TM (r : ℕ) : P_WCCR r ⊆ P_TM := by
  rintro L ⟨A, p, -, h⟩
  refine ⟨A.toTM, 1 + (p + 1) * (Polynomial.X + 2 * (A.r : Polynomial ℕ) * (p + 1) +
    2 * (A.r : Polynomial ℕ) + 1), ?_⟩
  have := A.toTM_decides h
  have heq : (fun n : ℕ => (1 + (p + 1) * (Polynomial.X + 2 * (A.r : Polynomial ℕ) * (p + 1) +
      2 * (A.r : Polynomial ℕ) + 1)).eval n) =
      (fun n => 1 + (p.eval n + 1) * (n + 2 * A.r * (p.eval n + 1) + 2 * A.r + 1)) := by
    funext n; simp
  rw [heq]; exact this

theorem P_WCC_subset_P_WCCR {r : ℕ} (hr : 1 ≤ r) : P_WCC ⊆ P_WCCR r := by
  rintro L ⟨B, p, h⟩
  exact ⟨B.toR r hr, p, rfl, B.toR_decides r hr h⟩

/-- **Radius-`r` class equivalence**: for every fixed radius `r ≥ 1`,
`P_WCCR r = P_TM`. -/
theorem P_WCCR_eq_P_TM {r : ℕ} (hr : 1 ≤ r) : P_WCCR r = P_TM :=
  Set.Subset.antisymm (P_WCCR_subset_P_TM r)
    (P_TM_subset_P_WCC.trans (P_WCC_subset_P_WCCR hr))

/-- **Radius-`r` verifier-class equivalence.** -/
theorem NP_WCCR_eq_NP_TM {r : ℕ} (hr : 1 ≤ r) : NP_WCCR r = NP_TM := by
  simp only [NP_WCCR, NP_TM, P_WCCR_eq_P_TM hr]

/-- The radius does not matter: all fixed radii give the same class. -/
theorem P_WCCR_radius_invariant {r r' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r') :
    P_WCCR r = P_WCCR r' := by
  rw [P_WCCR_eq_P_TM hr, P_WCCR_eq_P_TM hr']

/-- Radius `0` is excluded by definition (a radius-`0` automaton has no
communication between cells); the class is empty. -/
theorem P_WCCR_zero : P_WCCR 0 = ∅ := by
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, p, h0, -⟩
  have := A.hr
  omega

/-- Transfer: the radius-`r` P-vs-NP question is the classical one. -/
theorem p_vs_np_radius_transfer {r : ℕ} (hr : 1 ≤ r) :
    (P_WCCR r = NP_WCCR r) ↔ (P_TM = NP_TM) := by
  rw [P_WCCR_eq_P_TM hr, NP_WCCR_eq_NP_TM hr]

/-- Explicit polynomial overheads in both directions for radius `r`. -/
theorem explicit_radius_simulations :
    (∀ (B : WCC) (r : ℕ) (hr : 1 ≤ r) (L : Set (List Bool)) (T : ℕ → ℕ),
      B.Decides L T → (B.toR r hr).Decides L T) ∧
    (∀ (A : WCCR) (L : Set (List Bool)) (T : ℕ → ℕ), A.Decides L T →
      A.toTM.Decides L (fun n => 1 + (T n + 1) * (n + 2 * A.r * (T n + 1) + 2 * A.r + 1))) :=
  ⟨fun B r hr _ _ h => B.toR_decides r hr h, fun A _ _ h => A.toTM_decides h⟩

end PVNP.Discrete
