import PVNP.TMtoWCC
import PVNP.SATVerifier

/-!
# CL-1, part 1: the Cook–Levin tableau formula

For a single-tape verifier `M` (an ordinary `PVNP.Discrete.TM`), an input `x`, a witness bound
`Q` and a time bound `T`, `phi M x Q T` is an explicit CNF formula whose satisfying assignments
are exactly the space-time diagrams of `M` on the inputs `pair x w`, `|w| ≤ Q`, that accept at
time `T`.  The diagram is the run of the radius-one cellular automaton `M.toWCC`
(`PVNP.Discrete.TM.toWCC_step_encode`) on the window `[−T−1, T+1]`.

**Layout.**  Columns `c < W = 2T+3` stand for positions `j = c − (T+1)`, rows `t ≤ T` for times.
Group `k = t·W + c` carries one variable per cell symbol (`var M k σ`) and one acceptance-chain
variable (`accv M k`).  For every group `k < K = (T+1)·W` the formula lists one clause per
template (`Tpl`): at-least-one and at-most-one symbol, one window clause per symbol triple, the
boundary/initial-row unit clause, two witness clauses, and the acceptance chain.  A template
that does not apply to group `k` contributes a tautology.  Every clause mentions only groups
`k − 1`, `k`, `k + 1` and `k + W`.

**Verifier normalization.**  `Nrm.nrm V` reads fresh input symbols `inr b` as `V.inp b` (so its
input alphabet is injective and avoids the blank) and halts at its first answer.  `nrm_answer`:
if `V` decides `VL` within `P`, then `nrm V` shows the answer `[y ∈ VL]` at every time
`T ≥ P(|y|)`.

**Main results.**
* `phi_sat_iff`: `phi M x Q T` is satisfiable iff some `w` with `|w| ≤ Q` makes `M` accept
  `pair x w` at time `T`, provided `2|x| + 1 + Q ≤ T` and `M.inp` is injective and avoids the
  blank.
* `phi_bounded`: every variable is below `numVars M T = K·(|cells| + 1)`.
-/

namespace PVNP.CookLevin

open PVNP.Discrete PVNP.PartI PVNP.Discrete.SATV

/-! ## Generic run facts -/

section RunFacts

variable (M : TM)

theorem shift_abs_le (d : Dir) : |d.shift| ≤ 1 := by cases d <;> simp [Dir.shift]

/-- The head moves at most one cell per step. -/
theorem head_le (y : List Bool) : ∀ t, |(M.run (M.init y) t).head| ≤ t
  | 0 => by simp [TM.run, TM.init]
  | t + 1 => by
    rw [TM.run_succ]
    have ih := head_le y t
    simp only [TM.next, TM.step]
    rcases M.δ (M.run (M.init y) t).q ((M.run (M.init y) t).tape (M.run (M.init y) t).head) with
      _ | ⟨q', a, d⟩
    · simp only [Option.map_none, Option.getD_none]; push_cast; linarith
    · simp only [Option.map_some, Option.getD_some]
      have := shift_abs_le d
      push_cast
      calc |(M.run (M.init y) t).head + d.shift| ≤ |(M.run (M.init y) t).head| + |d.shift| :=
            abs_add_le _ _
        _ ≤ t + 1 := by linarith

/-- Cells farther than `t` from the origin still hold the input tape at time `t`. -/
theorem tape_far (y : List Bool) :
    ∀ (t : ℕ) (i : ℤ), (t : ℤ) < |i| → (M.run (M.init y) t).tape i = M.inputTape y i
  | 0, i, _ => by simp [TM.run, TM.init]
  | t + 1, i, hi => by
    rw [TM.run_succ]
    have hh := head_le M y t
    have ih := tape_far y t i (by push_cast at hi; linarith)
    simp only [TM.next, TM.step]
    rcases M.δ (M.run (M.init y) t).q ((M.run (M.init y) t).tape (M.run (M.init y) t).head) with
      _ | ⟨q', a, d⟩
    · simpa using ih
    · simp only [Option.map_some, Option.getD_some]
      rw [Function.update_of_ne]
      · exact ih
      · intro h
        rw [h] at hi
        push_cast at hi
        linarith

end RunFacts

/-! ## Verifier normalization -/

namespace Nrm

variable (V : TM)

/-- Reading map: the fresh input symbol `inr b` is read as `V.inp b`. -/
def rd : V.Γ ⊕ Bool → V.Γ := Sum.elim id V.inp

/-- **Normalized verifier**: fresh input alphabet and halting at the first answer. -/
def nrm : TM where
  Λ := V.Λ
  Γ := V.Γ ⊕ Bool
  blank := .inl V.blank
  inp := .inr
  start := V.start
  δ q g := if answerOf (V.acc q) (V.rej q) = none then
      (V.δ q (rd V g)).map fun t => (t.1, .inl t.2.1, t.2.2)
    else none
  acc := V.acc
  rej := V.rej

theorem nrm_inp_inj : Function.Injective (nrm V).inp := Sum.inr_injective

theorem nrm_inp_ne_blank (b : Bool) : (nrm V).inp b ≠ (nrm V).blank := Sum.inr_ne_inl

/-- Simulation relation. -/
def Rel (c : (nrm V).Cfg) (d : V.Cfg) : Prop :=
  c.q = d.q ∧ c.head = d.head ∧ ∀ i, rd V (c.tape i) = d.tape i

theorem rel_init (y : List Bool) : Rel V ((nrm V).init y) (V.init y) := by
  refine ⟨rfl, rfl, fun i => ?_⟩
  show rd V ((nrm V).inputTape y i) = V.inputTape y i
  unfold TM.inputTape
  split_ifs <;> rfl

theorem rel_next {c : (nrm V).Cfg} {d : V.Cfg} (h : Rel V c d) (hans : V.ans d = none) :
    Rel V ((nrm V).next c) (V.next d) := by
  obtain ⟨hq, hh, ht⟩ := h
  have hread : rd V (c.tape c.head) = d.tape d.head := by rw [hh, ht]
  have hδ : (nrm V).δ c.q (c.tape c.head) =
      (V.δ d.q (d.tape d.head)).map fun t => (t.1, .inl t.2.1, t.2.2) := by
    show (if answerOf (V.acc c.q) (V.rej c.q) = none then _ else none) = _
    rw [hq]
    simp only [TM.ans] at hans
    rw [if_pos hans, hread]
  simp only [TM.next, TM.step]
  rw [hδ]
  rcases hv : V.δ d.q (d.tape d.head) with _ | ⟨q', a, m⟩
  · simpa using ⟨hq, hh, ht⟩
  · simp only [Option.map_some, Option.getD_some]
    refine ⟨rfl, by rw [hh], fun i => ?_⟩
    by_cases hi : i = c.head
    · subst hi
      rw [hh]
      simp [rd]
    · show rd V (Function.update c.tape c.head (Sum.inl a) i) = Function.update d.tape d.head a i
      rw [Function.update_of_ne hi, Function.update_of_ne (by rwa [← hh])]
      exact ht i

theorem next_of_ans {c : (nrm V).Cfg} (h : (nrm V).ans c ≠ none) : (nrm V).next c = c := by
  have : (nrm V).δ c.q (c.tape c.head) = none := by
    have h' : answerOf (V.acc c.q) (V.rej c.q) ≠ none := h
    show (if answerOf (V.acc c.q) (V.rej c.q) = none then _ else none) = none
    rw [if_neg h']
  simp [TM.next, TM.step, this]

theorem run_fixed {c : (nrm V).Cfg} (h : (nrm V).ans c ≠ none) : ∀ m, (nrm V).run c m = c
  | 0 => rfl
  | m + 1 => by rw [TM.run_succ, run_fixed h m, next_of_ans V h]

/-- **The normalized verifier shows its answer at every time `T ≥ P(|y|)`.** -/
theorem nrm_answer {VL : Set (List Bool)} {P : ℕ → ℕ} (hV : V.Decides VL P) (y : List Bool)
    {T : ℕ} (hT : P y.length ≤ T) :
    ∃ b, (nrm V).ans ((nrm V).run ((nrm V).init y) T) = some b ∧ (b = true ↔ y ∈ VL) := by
  obtain ⟨b, ⟨s, hs, hout, hbefore⟩, hb⟩ := hV y
  have hrel : ∀ s' ≤ s, Rel V ((nrm V).run ((nrm V).init y) s') (V.run (V.init y) s') := by
    intro s' hs'
    induction s' with
    | zero => exact rel_init V y
    | succ s' ih =>
      rw [TM.run_succ, TM.run_succ]
      exact rel_next V (ih (by omega)) (hbefore s' (by omega))
  have hans : (nrm V).ans ((nrm V).run ((nrm V).init y) s) = some b := by
    obtain ⟨hq, -, -⟩ := hrel s le_rfl
    simp only [TM.out] at hout
    simp only [TM.ans] at hout ⊢
    rw [hq]
    exact hout
  have hfix := run_fixed V (c := (nrm V).run ((nrm V).init y) s) (by rw [hans]; simp)
  exact ⟨b, by rw [show T = s + (T - s) by omega, TM.run_add, hfix, hans], hb⟩

end Nrm

/-! ## Cells, variables and templates -/

section Tableau

variable (M : TM)

/-- Cell symbols of the compiled automaton `M.toWCC`. -/
abbrev Cell := M.Γ × Option M.Λ

/-- Number of cell symbols. -/
abbrev ns : ℕ := Fintype.card (Cell M)

/-- Variables per group: one per cell symbol and one acceptance-chain variable. -/
abbrev G : ℕ := ns M + 1

/-- A fixed enumeration of the cell symbols. -/
noncomputable def eqv : Cell M ≃ Fin (ns M) := Fintype.equivFin _

/-- All cell symbols, as a list. -/
noncomputable def univL (C : Type) [Fintype C] : List C := (Finset.univ : Finset C).toList

theorem mem_univL {C : Type} [Fintype C] (a : C) : a ∈ univL C := by simp [univL]

/-- The blank cell. -/
def blankC : Cell M := (M.blank, none)

/-- Symbol variable of group `k`. -/
noncomputable def var (k : ℕ) (σ : Cell M) : ℕ := k * G M + (eqv M σ : ℕ)

/-- Acceptance-chain variable of group `k`. -/
def accv (k : ℕ) : ℕ := k * G M + ns M

/-- Number of columns. -/
def W (T : ℕ) : ℕ := 2 * T + 3

/-- Number of groups. -/
def K (T : ℕ) : ℕ := (T + 1) * W T

/-- Number of variables. -/
def numVars (T : ℕ) : ℕ := K T * G M

/-- Row, column and position of group `k`. -/
def row (T k : ℕ) : ℕ := k / W T
def col (T k : ℕ) : ℕ := k % W T
def pos (T k : ℕ) : ℤ := (col T k : ℤ) - (T + 1)

theorem W_pos (T : ℕ) : 0 < W T := by unfold W; omega

/-- Clause templates. -/
inductive Tpl (C : Type) where
  | alo
  | amo (a b : C)
  | win (a b c : C)
  | unit
  | wit1
  | wit2
  | accC
  | accS
  deriving DecidableEq, Fintype

/-- The template order. -/
noncomputable def tpls (C : Type) [Fintype C] [DecidableEq C] : List (Tpl C) := univL (Tpl C)

/-- The fixed prefix of every pair: `pair x w = pre x ++ w`. -/
def pre (x : List Bool) : List Bool := x.flatMap (fun b => [true, b]) ++ [false]

theorem pair_eq (x w : List Bool) : pair x w = pre x ++ w := by simp [pair, pre]

theorem pre_length (x : List Bool) : (pre x).length = 2 * x.length + 1 := by
  simp [pre, List.length_flatMap]
  omega

/-- Witness columns: positions `2|x| < j ≤ 2|x| + Q`. -/
def isWit (n Q : ℕ) (j : ℤ) : Prop := 2 * (n : ℤ) < j ∧ j ≤ 2 * n + Q

instance (n Q : ℕ) (j : ℤ) : Decidable (isWit n Q j) := by unfold isWit; infer_instance

/-- Initial-row content of a non-witness position (independent of the witness). -/
def fixCell (x : List Bool) (j : ℤ) : Cell M :=
  (if 0 ≤ j ∧ j < (pre x).length then M.inp ((pre x).getD j.toNat false) else M.blank,
    if j = 0 then some M.start else none)

/-- A tautology on group `k`. -/
noncomputable def taut (k : ℕ) : Clause := [(var M k (blankC M), true), (var M k (blankC M), false)]

/-- Positive literals of the accepting symbols of group `k`. -/
noncomputable def accLits (k : ℕ) : Clause :=
  (univL (Cell M)).filterMap fun σ => if M.cellAcc σ then some (var M k σ, true) else none

/-- The clause of template `τ` at group `k`. -/
noncomputable def clause (x : List Bool) (Q T : ℕ) : Tpl (Cell M) → ℕ → Clause
  | .alo, k => (univL (Cell M)).map fun σ => (var M k σ, true)
  | .amo a b, k => if a ≠ b then [(var M k a, false), (var M k b, false)] else taut M k
  | .win a b c, k =>
      if row T k < T ∧ 1 ≤ col T k ∧ col T k + 1 < W T then
        [(var M (k - 1) a, false), (var M k b, false), (var M (k + 1) c, false),
          (var M (k + W T) (M.cellRule a b c), true)]
      else taut M k
  | .unit, k =>
      if col T k = 0 ∨ col T k + 1 = W T then [(var M k (blankC M), true)]
      else if row T k = 0 ∧ ¬ isWit x.length Q (pos T k) then
        [(var M k (fixCell M x (pos T k)), true)]
      else taut M k
  | .wit1, k =>
      if row T k = 0 ∧ isWit x.length Q (pos T k) then
        [(var M k (M.inp false, none), true), (var M k (M.inp true, none), true),
          (var M k (blankC M), true)]
      else taut M k
  | .wit2, k =>
      if row T k = 0 ∧ isWit x.length Q (pos T k) ∧ col T k + 1 < W T then
        [(var M k (blankC M), false), (var M (k + 1) (blankC M), true)]
      else taut M k
  | .accC, k =>
      if row T k = T then
        (accv M k, false) ::
          ((if col T k + 1 < W T then [(accv M (k + 1), true)] else []) ++ accLits M k)
      else taut M k
  | .accS, k => if row T k = T ∧ col T k = 0 then [(accv M k, true)] else taut M k

/-- **The tableau formula.** -/
noncomputable def phi (x : List Bool) (Q T : ℕ) : Formula :=
  (List.range (K T)).flatMap fun k => (tpls (Cell M)).map fun τ => clause M x Q T τ k

/-! ### Index arithmetic -/

theorem eqv_lt (σ : Cell M) : (eqv M σ : ℕ) < G M := by
  have := (eqv M σ).isLt; show (eqv M σ : ℕ) < ns M + 1; omega

theorem ns_lt_G : ns M < G M := Nat.lt_succ_self _

theorem var_div (k : ℕ) (σ : Cell M) : var M k σ / G M = k := by
  unfold var
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _ : 0 < G M),
    Nat.div_eq_of_lt (eqv_lt M σ), zero_add]

theorem var_mod (k : ℕ) (σ : Cell M) : var M k σ % G M = eqv M σ := by
  unfold var
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (eqv_lt M σ)]

theorem accv_div (k : ℕ) : accv M k / G M = k := by
  unfold accv
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _ : 0 < G M),
    Nat.div_eq_of_lt (ns_lt_G M), zero_add]

theorem accv_mod (k : ℕ) : accv M k % G M = ns M := by
  unfold accv
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (ns_lt_G M)]

theorem var_inj {k k' : ℕ} {σ σ' : Cell M} (h : var M k σ = var M k' σ') : k = k' ∧ σ = σ' := by
  refine ⟨by rw [← var_div M k σ, h, var_div], ?_⟩
  have := var_mod M k σ
  rw [h, var_mod] at this
  exact (eqv M).injective (Fin.ext this.symm)

theorem var_ne_accv (k k' : ℕ) (σ : Cell M) : var M k σ ≠ accv M k' := by
  intro h
  have h1 := var_mod M k σ
  rw [h, accv_mod] at h1
  have := (eqv M σ).isLt
  omega

theorem accv_inj {k k' : ℕ} (h : accv M k = accv M k') : k = k' := by
  rw [← accv_div M k, h, accv_div]

theorem var_lt {T k : ℕ} (hk : k < K T) (σ : Cell M) : var M k σ < numVars M T := by
  unfold var numVars
  have := eqv_lt M σ
  calc k * G M + (eqv M σ : ℕ) < k * G M + G M := by omega
    _ = (k + 1) * G M := by ring
    _ ≤ K T * G M := Nat.mul_le_mul_right _ hk

theorem accv_lt {T k : ℕ} (hk : k < K T) : accv M k < numVars M T := by
  unfold accv numVars
  calc k * G M + ns M < k * G M + G M := by have := ns_lt_G M; omega
    _ = (k + 1) * G M := by ring
    _ ≤ K T * G M := Nat.mul_le_mul_right _ hk

theorem group_eq (T k : ℕ) : k = row T k * W T + col T k := by
  unfold row col; rw [mul_comm]; exact (Nat.div_add_mod k (W T)).symm

theorem col_lt (T k : ℕ) : col T k < W T := Nat.mod_lt _ (W_pos T)

theorem row_lt {T k : ℕ} (hk : k < K T) : row T k < T + 1 := by
  unfold row K at *; exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hk)

theorem row_mk (T t c : ℕ) (hc : c < W T) : row T (t * W T + c) = t := by
  unfold row; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (W_pos T), Nat.div_eq_of_lt hc, zero_add]

theorem col_mk (T t c : ℕ) (hc : c < W T) : col T (t * W T + c) = c := by
  unfold col; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem mk_lt {T t c : ℕ} (ht : t ≤ T) (hc : c < W T) : t * W T + c < K T := by
  unfold K
  calc t * W T + c < t * W T + W T := by omega
    _ = (t + 1) * W T := by ring
    _ ≤ (T + 1) * W T := Nat.mul_le_mul_right _ (by omega)

/-! ### Every variable is in range -/

theorem taut_bounded {T k : ℕ} (hk : k < K T) : ∀ l ∈ taut M k, l.1 < numVars M T := by
  intro l hl
  simp only [taut, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> exact var_lt M hk _

theorem clause_bounded (x : List Bool) (Q T : ℕ) (τ : Tpl (Cell M)) {k : ℕ} (hk : k < K T) :
    ∀ l ∈ clause M x Q T τ k, l.1 < numVars M T := by
  have hW := W_pos T
  have hrc := group_eq T k
  intro l hl
  cases τ with
  | alo =>
    simp only [clause, List.mem_map] at hl
    obtain ⟨σ, -, rfl⟩ := hl
    exact var_lt M hk σ
  | amo a b =>
    simp only [clause] at hl
    split_ifs at hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> exact var_lt M hk _
    · exact taut_bounded M hk l hl
  | win a b c =>
    simp only [clause] at hl
    split_ifs at hl with h
    · obtain ⟨hr, hc1, hc2⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      have hcl := col_lt T k
      rcases hl with rfl | rfl | rfl | rfl
      · exact var_lt M (by omega) _
      · exact var_lt M hk _
      · exact var_lt M (by rw [hrc]; exact (by
          have := mk_lt (T := T) (t := row T k) (c := col T k + 1) (by omega) hc2
          omega)) _
      · refine var_lt M ?_ _
        have := mk_lt (T := T) (t := row T k + 1) (c := col T k) (by omega) hcl
        rw [hrc]
        calc row T k * W T + col T k + W T = (row T k + 1) * W T + col T k := by ring
          _ < K T := this
    · exact taut_bounded M hk l hl
  | unit =>
    simp only [clause] at hl
    split_ifs at hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; subst hl; exact var_lt M hk _
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; subst hl; exact var_lt M hk _
    · exact taut_bounded M hk l hl
  | wit1 =>
    simp only [clause] at hl
    split_ifs at hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> exact var_lt M hk _
    · exact taut_bounded M hk l hl
  | wit2 =>
    simp only [clause] at hl
    split_ifs at hl with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact var_lt M hk _
      · refine var_lt M ?_ _
        obtain ⟨hr0, -, hc⟩ := h
        have := mk_lt (T := T) (t := row T k) (c := col T k + 1) (by omega) hc
        rw [hrc]; omega
    · exact taut_bounded M hk l hl
  | accC =>
    simp only [clause] at hl
    split_ifs at hl with h1 h2
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | hl
      · exact accv_lt M hk
      · refine accv_lt M ?_
        have := mk_lt (T := T) (t := row T k) (c := col T k + 1) (by omega) h2
        rw [hrc]; omega
      · simp only [accLits, List.mem_filterMap] at hl
        obtain ⟨σ, -, hσ⟩ := hl
        split_ifs at hσ
        cases hσ
        exact var_lt M hk σ
    · simp only [List.nil_append, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact accv_lt M hk
      · simp only [accLits, List.mem_filterMap] at hl
        obtain ⟨σ, -, hσ⟩ := hl
        split_ifs at hσ
        cases hσ
        exact var_lt M hk σ
    · exact taut_bounded M hk l hl
  | accS =>
    simp only [clause] at hl
    split_ifs at hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; subst hl; exact accv_lt M hk
    · exact taut_bounded M hk l hl

theorem phi_bounded (x : List Bool) (Q T : ℕ) :
    ∀ c ∈ phi M x Q T, ∀ l ∈ c, l.1 < numVars M T := by
  intro c hc
  simp only [phi, List.mem_flatMap, List.mem_range, List.mem_map] at hc
  obtain ⟨k, hk, τ, -, rfl⟩ := hc
  exact clause_bounded M x Q T τ hk

/-! ### Clause evaluation -/

theorem evalFormula_iff (α : ℕ → Bool) (F : Formula) :
    evalFormula α F = true ↔ ∀ c ∈ F, evalClause α c = true := by
  induction F with
  | nil => simp [evalFormula]
  | cons c F ih => simp [evalFormula, ih]

theorem evalClause_iff (α : ℕ → Bool) (c : Clause) :
    evalClause α c = true ↔ ∃ l ∈ c, evalLiteral α l = true := by
  induction c with
  | nil => simp [evalClause]
  | cons l c ih => simp [evalClause, ih]

@[simp] theorem evalLiteral_pos (α : ℕ → Bool) (v : ℕ) : evalLiteral α (v, true) = α v := by
  cases h : α v <;> simp [evalLiteral, literalTrue, h]

@[simp] theorem evalLiteral_neg (α : ℕ → Bool) (v : ℕ) : evalLiteral α (v, false) = !α v := by
  cases h : α v <;> simp [evalLiteral, literalTrue, h]

theorem clause_mem_phi (x : List Bool) (Q T : ℕ) (τ : Tpl (Cell M)) {k : ℕ} (hk : k < K T) :
    clause M x Q T τ k ∈ phi M x Q T := by
  simp only [phi, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨k, hk, τ, mem_univL τ, rfl⟩

/-! ### The true diagram -/

/-- The true space-time diagram of `M` on input `y`, on the window. -/
def truth (y : List Bool) (T t c : ℕ) : Cell M :=
  M.encode (M.run (M.init y) t) ((c : ℤ) - (T + 1))

theorem truth_zero (y : List Bool) (T c : ℕ) :
    truth M y T 0 c = (M.inputTape y ((c : ℤ) - (T + 1)),
      if (c : ℤ) - (T + 1) = 0 then some M.start else none) := by
  simp only [truth, TM.encode, TM.run, Function.iterate_zero, id, TM.init]

/-- Boundary columns stay blank up to time `T`. -/
theorem truth_bnd {y : List Bool} {T t c : ℕ} (hy : y.length ≤ T) (ht : t ≤ T)
    (hc : c = 0 ∨ c = 2 * T + 2) : truth M y T t c = blankC M := by
  have hj : (t : ℤ) < |(c : ℤ) - (T + 1)| := by
    rcases hc with rfl | rfl
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; push_cast; omega
  have htape := tape_far M y t _ hj
  have hhead := head_le M y t
  simp only [truth, TM.encode, blankC]
  rw [htape]
  have hne : (c : ℤ) - (T + 1) ≠ (M.run (M.init y) t).head := by
    intro h; rw [← h] at hhead; omega
  rw [if_neg hne]
  simp only [TM.inputTape, Prod.mk.injEq, and_true]
  rw [if_neg]
  rcases hc with rfl | rfl
  · omega
  · omega

/-- Inner columns follow the compiled local rule (`toWCC_step_encode`). -/
theorem truth_step (y : List Bool) (T t c : ℕ) (hc : 1 ≤ c) :
    truth M y T (t + 1) c =
      M.cellRule (truth M y T t (c - 1)) (truth M y T t c) (truth M y T t (c + 1)) := by
  simp only [truth]
  rw [TM.run_succ, ← M.toWCC_step_encode]
  simp only [WCC.step, TM.toWCC]
  congr 2 <;> push_cast [Nat.cast_sub hc] <;> ring

/-- Only the head cell can be accepting. -/
theorem acc_of_cellAcc {c : M.Cfg} {j : ℤ} (h : M.cellAcc (M.encode c j) = true) :
    M.acc c.q = true := by
  simp only [TM.encode, TM.cellAcc] at h
  split_ifs at h <;> simp_all

theorem cellAcc_head (c : M.Cfg) : M.cellAcc (M.encode c c.head) = M.acc c.q := by
  simp [TM.encode, TM.cellAcc]

/-! ## Soundness -/

section Sound

variable {M} {x : List Bool} {Q T : ℕ} {α : ℕ → Bool}

theorem holds (hα : evalFormula α (phi M x Q T) = true) {k : ℕ} (hk : k < K T)
    (τ : Tpl (Cell M)) : ∃ l ∈ clause M x Q T τ k, evalLiteral α l = true :=
  (evalClause_iff α _).1 ((evalFormula_iff α _).1 hα _ (clause_mem_phi M x Q T τ hk))

theorem alo_holds (hα : evalFormula α (phi M x Q T) = true) {k : ℕ} (hk : k < K T) :
    ∃ σ, α (var M k σ) = true := by
  obtain ⟨l, hl, hv⟩ := holds hα hk .alo
  simp only [clause, List.mem_map] at hl
  obtain ⟨σ, -, rfl⟩ := hl
  exact ⟨σ, by simpa using hv⟩

theorem amo_holds (hα : evalFormula α (phi M x Q T) = true) {k : ℕ} (hk : k < K T)
    {a b : Cell M} (ha : α (var M k a) = true) (hb : α (var M k b) = true) : a = b := by
  by_contra hne
  obtain ⟨l, hl, hv⟩ := holds hα hk (.amo a b)
  simp only [clause, if_pos hne, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> simp_all

open Classical in
/-- The symbol an assignment puts on group `k`. -/
noncomputable def sym (α : ℕ → Bool) (k : ℕ) : Cell M :=
  if h : ∃ σ, α (var M k σ) = true then h.choose else blankC M

theorem sym_iff (hα : evalFormula α (phi M x Q T) = true) {k : ℕ} (hk : k < K T) (σ : Cell M) :
    α (var M k σ) = true ↔ sym (M := M) α k = σ := by
  have hex := alo_holds hα hk
  have hs : α (var M k (sym (M := M) α k)) = true := by
    simp only [sym, dif_pos hex]; exact hex.choose_spec
  constructor
  · intro h; exact amo_holds hα hk hs h
  · rintro rfl; exact hs

theorem sym_true (hα : evalFormula α (phi M x Q T) = true) {k : ℕ} (hk : k < K T) :
    α (var M k (sym (M := M) α k)) = true := (sym_iff hα hk _).2 rfl

/-- Unit clauses force the boundary columns blank. -/
theorem sym_bnd (hα : evalFormula α (phi M x Q T) = true) {t c : ℕ} (ht : t ≤ T)
    (hc : c = 0 ∨ c + 1 = W T) : sym (M := M) α (t * W T + c) = blankC M := by
  have hcW : c < W T := by rcases hc with rfl | h <;> [exact W_pos T; omega]
  have hk := mk_lt ht hcW
  obtain ⟨l, hl, hv⟩ := holds hα hk .unit
  simp only [clause, col_mk T t c hcW, if_pos hc, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  subst hl
  exact (sym_iff hα hk _).1 (by simpa using hv)

theorem sym_fix (hα : evalFormula α (phi M x Q T) = true) {c : ℕ} (hc0 : c ≠ 0)
    (hcW : c + 1 < W T) (hw : ¬ isWit x.length Q ((c : ℤ) - (T + 1))) :
    sym (M := M) α (0 * W T + c) = fixCell M x ((c : ℤ) - (T + 1)) := by
  have hk := mk_lt (Nat.zero_le T) (by omega : c < W T)
  obtain ⟨l, hl, hv⟩ := holds hα hk .unit
  have hn : ¬ (c = 0 ∨ c + 1 = W T) := by omega
  simp only [clause, col_mk T 0 c (by omega), row_mk T 0 c (by omega), if_neg hn, pos,
    true_and, if_pos hw, List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl
  exact (sym_iff hα hk _).1 (by simpa using hv)

theorem sym_wit (hα : evalFormula α (phi M x Q T) = true) {c : ℕ} (hcW : c < W T)
    (hw : isWit x.length Q ((c : ℤ) - (T + 1))) :
    sym (M := M) α (0 * W T + c) = (M.inp false, none) ∨
      sym (M := M) α (0 * W T + c) = (M.inp true, none) ∨
      sym (M := M) α (0 * W T + c) = blankC M := by
  have hk := mk_lt (Nat.zero_le T) hcW
  obtain ⟨l, hl, hv⟩ := holds hα hk .wit1
  simp only [clause, col_mk T 0 c hcW, row_mk T 0 c hcW, pos, true_and, if_pos hw,
    List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact Or.inl ((sym_iff hα hk _).1 (by simpa using hv))
  · exact Or.inr (Or.inl ((sym_iff hα hk _).1 (by simpa using hv)))
  · exact Or.inr (Or.inr ((sym_iff hα hk _).1 (by simpa using hv)))

theorem sym_wit2 (hα : evalFormula α (phi M x Q T) = true) {c : ℕ} (hcW : c + 1 < W T)
    (hw : isWit x.length Q ((c : ℤ) - (T + 1)))
    (hb : sym (M := M) α (0 * W T + c) = blankC M) :
    sym (M := M) α (0 * W T + (c + 1)) = blankC M := by
  have hk := mk_lt (Nat.zero_le T) (by omega : c < W T)
  have hk' := mk_lt (Nat.zero_le T) hcW
  obtain ⟨l, hl, hv⟩ := holds hα hk .wit2
  simp only [clause, col_mk T 0 c (by omega), row_mk T 0 c (by omega), pos, true_and,
    if_pos (And.intro hw hcW), List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · rw [← sym_iff hα hk] at hb; simp_all
  · rw [show 0 * W T + c + 1 = 0 * W T + (c + 1) by ring] at hv
    exact (sym_iff hα hk' _).1 (by simpa using hv)

theorem sym_win (hα : evalFormula α (phi M x Q T) = true) {t c : ℕ} (ht : t < T) (hc : 1 ≤ c)
    (hcW : c + 1 < W T) :
    sym (M := M) α ((t + 1) * W T + c) =
      M.cellRule (sym (M := M) α (t * W T + (c - 1))) (sym (M := M) α (t * W T + c))
        (sym (M := M) α (t * W T + (c + 1))) := by
  have hk := mk_lt (le_of_lt ht) (by omega : c < W T)
  have hkm := mk_lt (le_of_lt ht) (by omega : c - 1 < W T)
  have hkp := mk_lt (le_of_lt ht) hcW
  have hkW := mk_lt (Nat.succ_le_of_lt ht) (by omega : c < W T)
  obtain ⟨l, hl, hv⟩ := holds hα hk (.win (sym (M := M) α (t * W T + (c - 1)))
    (sym (M := M) α (t * W T + c)) (sym (M := M) α (t * W T + (c + 1))))
  simp only [clause, col_mk T t c (by omega), row_mk T t c (by omega),
    if_pos (And.intro ht (And.intro hc hcW)), List.mem_cons, List.not_mem_nil, or_false] at hl
  have e1 : t * W T + c - 1 = t * W T + (c - 1) := by omega
  have e2 : t * W T + c + W T = (t + 1) * W T + c := by ring
  have e3 : t * W T + c + 1 = t * W T + (c + 1) := by ring
  have h1 := sym_true hα hkm
  have h2 := sym_true hα hk
  have h3 := sym_true hα hkp
  rcases hl with rfl | rfl | rfl | rfl
  · rw [e1] at hv; simp [h1] at hv
  · simp [h2] at hv
  · rw [e3] at hv; simp [h3] at hv
  · rw [e2] at hv; exact ((sym_iff hα hkW _).1 (by simpa using hv))

/-! ### Decoding the witness and the rows -/

/-- Column of witness cell `i` (position `2|x| + 1 + i`). -/
def wcol (x : List Bool) (T i : ℕ) : ℕ := T + 1 + (2 * x.length + 1 + i)

theorem wcol_pos (x : List Bool) (T i : ℕ) :
    ((wcol x T i : ℕ) : ℤ) - (T + 1) = 2 * x.length + 1 + i := by
  unfold wcol; push_cast; ring

theorem isWit_wcol {x : List Bool} {Q T i : ℕ} (hi : i < Q) :
    isWit x.length Q ((wcol x T i : ℤ) - (T + 1)) := by
  rw [wcol_pos]; unfold isWit; constructor <;> push_cast <;> omega

open Classical in
/-- Number of leading non-blank witness cells. -/
noncomputable def wlen (α : ℕ → Bool) (x : List Bool) (Q T : ℕ) : ℕ :=
  Nat.find (⟨Q, Or.inl rfl⟩ :
    ∃ i, i = Q ∨ sym (M := M) α (0 * W T + wcol x T i) = blankC M)

/-- The decoded witness. -/
noncomputable def wit (α : ℕ → Bool) (x : List Bool) (Q T : ℕ) : List Bool :=
  (List.range (wlen (M := M) α x Q T)).map fun i =>
    decide (sym (M := M) α (0 * W T + wcol x T i) = (M.inp true, none))

theorem wlen_le : wlen (M := M) α x Q T ≤ Q := by
  classical
  unfold wlen
  exact Nat.find_min' _ (Or.inl rfl)

theorem wlen_spec : wlen (M := M) α x Q T = Q ∨
    sym (M := M) α (0 * W T + wcol x T (wlen (M := M) α x Q T)) = blankC M := by
  classical
  unfold wlen
  convert Nat.find_spec (⟨Q, Or.inl rfl⟩ :
    ∃ i, i = Q ∨ sym (M := M) α (0 * W T + wcol x T i) = blankC M)

theorem wlen_min {i : ℕ} (h : i < wlen (M := M) α x Q T) :
    sym (M := M) α (0 * W T + wcol x T i) ≠ blankC M := by
  classical
  intro hb
  have hle : wlen (M := M) α x Q T ≤ i := by
    unfold wlen
    exact Nat.find_min' _ (Or.inr hb)
  omega

theorem wit_blank_after (hT : 2 * x.length + 1 + Q ≤ T)
    (hα : evalFormula α (phi M x Q T) = true) :
    ∀ d, wlen (M := M) α x Q T + d < Q →
      sym (M := M) α (0 * W T + wcol x T (wlen (M := M) α x Q T + d)) = blankC M
  | 0, h => by
    rcases wlen_spec (M := M) (α := α) (x := x) (Q := Q) (T := T) with h' | h'
    · omega
    · simpa using h'
  | d + 1, h => by
    have ih := wit_blank_after hT hα d (by omega)
    have := sym_wit2 hα (c := wcol x T (wlen (M := M) α x Q T + d))
      (by unfold wcol W; omega) (isWit_wcol (by omega)) ih
    rwa [show wcol x T (wlen (M := M) α x Q T + d) + 1 =
      wcol x T (wlen (M := M) α x Q T + (d + 1)) by unfold wcol; ring] at this

theorem wit_length : (wit (M := M) α x Q T).length ≤ Q := by
  simpa [wit] using wlen_le (M := M) (α := α) (x := x) (Q := Q) (T := T)

theorem pair_getD (x w : List Bool) (i : ℕ) :
    (pair x w).getD (2 * x.length + 1 + i) false = w.getD i false := by
  rw [pair_eq, ← pre_length, List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

theorem pair_length' (x w : List Bool) : (pair x w).length = 2 * x.length + 1 + w.length := by
  rw [pair_eq, List.length_append, pre_length]

theorem fix_eq_truth (M : TM) {w : List Bool} (hwQ : w.length ≤ Q) {c : ℕ}
    (hw : ¬ isWit x.length Q ((c : ℤ) - (T + 1))) :
    fixCell M x ((c : ℤ) - (T + 1)) = truth M (pair x w) T 0 c := by
  rw [truth_zero]
  unfold fixCell
  congr 1
  simp only [TM.inputTape]
  set j : ℤ := (c : ℤ) - (T + 1)
  by_cases hj : 0 ≤ j ∧ j < (pre x).length
  · rw [if_pos hj, if_pos (by rw [pair_eq, List.length_append]; push_cast; omega)]
    rw [pair_eq, List.getD_append _ _ _ _ (by omega)]
  · rw [if_neg hj, if_neg]
    rw [pre_length] at hj
    unfold isWit at hw
    rw [pair_length']
    push_cast at hj ⊢
    omega

theorem row0_wit (hinj : Function.Injective M.inp) (hT : 2 * x.length + 1 + Q ≤ T)
    (hα : evalFormula α (phi M x Q T) = true) {i : ℕ} (hi : i < Q) :
    sym (M := M) α (0 * W T + wcol x T i) =
      truth M (pair x (wit (M := M) α x Q T)) T 0 (wcol x T i) := by
  classical
  have hcW : wcol x T i < W T := by unfold wcol W; omega
  rw [truth_zero, wcol_pos]
  have hj0 : (2 * (x.length : ℤ) + 1 + i) ≠ 0 := by omega
  simp only [hj0, if_false]
  set w := wit (M := M) α x Q T with hw
  have hlen : w.length = wlen (M := M) α x Q T := by simp [hw, wit]
  by_cases hil : i < wlen (M := M) α x Q T
  · -- a witness bit
    have hnb : sym (M := M) α (0 * W T + wcol x T i) ≠ blankC M := wlen_min hil
    have hwi : w.getD i false =
        decide (sym (M := M) α (0 * W T + wcol x T i) = (M.inp true, none)) := by
      simp [hw, wit, List.getD_eq_getElem?_getD, hil]
    have hin : (0 : ℤ) ≤ 2 * x.length + 1 + i ∧ 2 * (x.length : ℤ) + 1 + i < (pair x w).length := by
      rw [pair_length']; constructor <;> push_cast <;> omega
    simp only [TM.inputTape, if_pos hin]
    rw [show (2 * (x.length : ℤ) + 1 + i).toNat = 2 * x.length + 1 + i by omega, pair_getD, hwi]
    rcases sym_wit hα hcW (isWit_wcol hi) with h | h | h
    · rw [h]
      have : (M.inp false, (none : Option M.Λ)) ≠ (M.inp true, none) := by
        intro he; exact absurd (hinj (Prod.ext_iff.1 he).1) (by decide)
      simp [this]
    · rw [h]; simp
    · exact absurd h hnb
  · -- past the witness: blank
    push_neg at hil
    have hb : sym (M := M) α (0 * W T + wcol x T i) = blankC M := by
      obtain ⟨d, rfl⟩ : ∃ d, i = wlen (M := M) α x Q T + d :=
        ⟨i - wlen (M := M) α x Q T, by omega⟩
      exact wit_blank_after hT hα d hi
    rw [hb]
    have hout : ¬ ((0 : ℤ) ≤ 2 * x.length + 1 + i ∧ 2 * (x.length : ℤ) + 1 + i < (pair x w).length) := by
      rw [pair_length', hlen]; push_cast; omega
    simp [TM.inputTape, if_neg hout, blankC]

theorem row0 (hinj : Function.Injective M.inp) (hT : 2 * x.length + 1 + Q ≤ T)
    (hα : evalFormula α (phi M x Q T) = true) {c : ℕ} (hc : c < W T) :
    sym (M := M) α (0 * W T + c) = truth M (pair x (wit (M := M) α x Q T)) T 0 c := by
  have hpl : (pair x (wit (M := M) α x Q T)).length ≤ T := by
    rw [pair_length']; have := wit_length (M := M) (α := α) (x := x) (Q := Q) (T := T); omega
  by_cases hb : c = 0 ∨ c + 1 = W T
  · rw [sym_bnd hα (Nat.zero_le T) hb, truth_bnd M hpl (Nat.zero_le T)
      (by unfold W at hb; omega)]
  · push_neg at hb
    by_cases hw : isWit x.length Q ((c : ℤ) - (T + 1))
    · obtain ⟨i, rfl⟩ : ∃ i, c = wcol x T i := by
        refine ⟨c - (T + 1) - (2 * x.length + 1), ?_⟩
        unfold isWit at hw; unfold wcol; omega
      exact row0_wit hinj hT hα (by
        have := hw.2; rw [wcol_pos] at this; push_cast at this; omega)
    · rw [sym_fix hα hb.1 (by omega) hw]
      exact fix_eq_truth M wit_length hw

/-- **Every row of a satisfying assignment is the true diagram.** -/
theorem rows (hinj : Function.Injective M.inp) (hT : 2 * x.length + 1 + Q ≤ T)
    (hα : evalFormula α (phi M x Q T) = true) :
    ∀ t ≤ T, ∀ c < W T,
      sym (M := M) α (t * W T + c) = truth M (pair x (wit (M := M) α x Q T)) T t c := by
  have hpl : (pair x (wit (M := M) α x Q T)).length ≤ T := by
    rw [pair_length']; have := wit_length (M := M) (α := α) (x := x) (Q := Q) (T := T); omega
  intro t
  induction t with
  | zero => intro _ c hc; exact row0 hinj hT hα hc
  | succ t ih =>
    intro ht c hc
    by_cases hb : c = 0 ∨ c + 1 = W T
    · rw [sym_bnd hα ht hb, truth_bnd M hpl ht (by unfold W at hb; omega)]
    · push_neg at hb
      have hc1 : 1 ≤ c := by omega
      rw [sym_win hα (by omega) hc1 (by omega), truth_step M _ T t c hc1,
        ih (by omega) (c - 1) (by omega), ih (by omega) c hc, ih (by omega) (c + 1) (by omega)]

/-- The acceptance chain finds an accepting cell in the last row. -/
theorem acc_chain (hα : evalFormula α (phi M x Q T) = true) :
    ∀ d c, c + d + 1 = W T → α (accv M (T * W T + c)) = true →
      ∃ c' < W T, M.cellAcc (sym (M := M) α (T * W T + c')) = true := by
  intro d
  induction d with
  | zero =>
    intro c hc ha
    have hcW : c < W T := by omega
    have hk := mk_lt le_rfl hcW
    obtain ⟨l, hl, hv⟩ := holds hα hk .accC
    simp only [clause, row_mk T T c hcW, col_mk T T c hcW, if_true,
      show ¬ (c + 1 < W T) by omega, if_false, List.nil_append, List.mem_cons] at hl
    rcases hl with rfl | hl
    · simp [ha] at hv
    · simp only [accLits, List.mem_filterMap] at hl
      obtain ⟨σ, -, hσ⟩ := hl
      split_ifs at hσ with hacc
      cases hσ
      rw [evalLiteral_pos, sym_iff hα hk] at hv
      exact ⟨c, hcW, by rw [hv]; exact hacc⟩
  | succ d ih =>
    intro c hc ha
    have hcW : c + 1 < W T := by omega
    have hk := mk_lt le_rfl (by omega : c < W T)
    obtain ⟨l, hl, hv⟩ := holds hα hk .accC
    simp only [clause, row_mk T T c (by omega), col_mk T T c (by omega), if_true, if_pos hcW,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | hl
    · simp [ha] at hv
    · rw [evalLiteral_pos, show T * W T + c + 1 = T * W T + (c + 1) by ring] at hv
      exact ih (c + 1) (by omega) hv
    · simp only [accLits, List.mem_filterMap] at hl
      obtain ⟨σ, -, hσ⟩ := hl
      split_ifs at hσ with hacc
      cases hσ
      rw [evalLiteral_pos, sym_iff hα hk] at hv
      exact ⟨c, by omega, by rw [hv]; exact hacc⟩

/-- **Soundness.** -/
theorem sound (hinj : Function.Injective M.inp) (hT : 2 * x.length + 1 + Q ≤ T)
    (hα : evalFormula α (phi M x Q T) = true) :
    ∃ w : List Bool, w.length ≤ Q ∧ M.acc (M.run (M.init (pair x w)) T).q = true := by
  refine ⟨wit (M := M) α x Q T, wit_length, ?_⟩
  have hk0 := mk_lt le_rfl (W_pos T)
  obtain ⟨l, hl, hv⟩ := holds hα (k := T * W T + 0) hk0 .accS
  simp only [clause, row_mk T T 0 (W_pos T), col_mk T T 0 (W_pos T), and_self, if_true,
    List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl
  rw [evalLiteral_pos] at hv
  obtain ⟨c, hc, hacc⟩ := acc_chain hα (W T - 1) 0 (by have := W_pos T; omega) hv
  rw [rows hinj hT hα T le_rfl c hc] at hacc
  exact acc_of_cellAcc M hacc

end Sound

/-! ## Completeness -/

section Complete

variable {M}

/-- Acceptance-chain value: an accepting cell at some column `≥ c` of the last row. -/
def accFrom (y : List Bool) (T c : ℕ) : Prop :=
  ∃ c', c ≤ c' ∧ c' < W T ∧ M.cellAcc (truth M y T T c') = true

open Classical in
/-- The assignment read off the true diagram. -/
noncomputable def asg (y : List Bool) (T : ℕ) (v : ℕ) : Bool :=
  if h : v % G M < ns M then
    decide (truth M y T (row T (v / G M)) (col T (v / G M)) = (eqv M).symm ⟨v % G M, h⟩)
  else decide (accFrom (M := M) y T (col T (v / G M)))

theorem asg_var (y : List Bool) (T k : ℕ) (σ : Cell M) :
    asg (M := M) y T (var M k σ) = decide (truth M y T (row T k) (col T k) = σ) := by
  classical
  have h : var M k σ % G M < ns M := by rw [var_mod]; exact (eqv M σ).isLt
  unfold asg
  rw [dif_pos h]
  simp only [var_div]
  congr 2
  rw [show (⟨var M k σ % G M, h⟩ : Fin (ns M)) = eqv M σ from Fin.ext (var_mod M k σ),
    Equiv.symm_apply_apply]

open Classical in
theorem asg_accv (y : List Bool) (T k : ℕ) :
    asg (M := M) y T (accv M k) = decide (accFrom (M := M) y T (col T k)) := by
  classical
  have h : ¬ accv M k % G M < ns M := by rw [accv_mod]; omega
  unfold asg
  rw [dif_neg h, accv_div]

theorem taut_eval (α : ℕ → Bool) (k : ℕ) : evalClause α (taut M k) = true := by
  rw [evalClause_iff]
  cases h : α (var M k (blankC M))
  · exact ⟨(var M k (blankC M), false), by simp [taut], by simp [h]⟩
  · exact ⟨(var M k (blankC M), true), by simp [taut], by simp [h]⟩

theorem truth_wit {x w : List Bool} {T : ℕ} (hnb : ∀ b, M.inp b ≠ M.blank) {c : ℕ}
    (hc : 2 * (x.length : ℤ) < (c : ℤ) - (T + 1)) :
    (truth M (pair x w) T 0 c = blankC M ↔ ¬ ((c : ℤ) - (T + 1) < (pair x w).length)) ∧
    (truth M (pair x w) T 0 c = (M.inp false, none) ∨
      truth M (pair x w) T 0 c = (M.inp true, none) ∨ truth M (pair x w) T 0 c = blankC M) := by
  rw [truth_zero]
  have hj0 : (c : ℤ) - (T + 1) ≠ 0 := by omega
  simp only [hj0, if_false, TM.inputTape, blankC]
  by_cases hin : 0 ≤ (c : ℤ) - (T + 1) ∧ (c : ℤ) - (T + 1) < (pair x w).length
  · rw [if_pos hin]
    refine ⟨⟨fun h => absurd (Prod.ext_iff.1 h).1 (hnb _), fun h => absurd hin.2 h⟩, ?_⟩
    cases (pair x w).getD ((c : ℤ) - (T + 1)).toNat false <;> simp
  · rw [if_neg hin]
    exact ⟨⟨fun _ h => hin ⟨by omega, h⟩, fun _ => rfl⟩, Or.inr (Or.inr rfl)⟩

/-- **Completeness**: every clause holds under the diagram assignment. -/
theorem complete (hnb : ∀ b, M.inp b ≠ M.blank) {x w : List Bool} {Q T : ℕ}
    (hT : 2 * x.length + 1 + Q ≤ T) (hw : w.length ≤ Q)
    (hacc : M.acc (M.run (M.init (pair x w)) T).q = true) :
    evalFormula (asg (M := M) (pair x w) T) (phi M x Q T) = true := by
  classical
  set y := pair x w with hy
  have hyl : y.length ≤ T := by rw [hy, pair_length']; omega
  rw [evalFormula_iff]
  intro cl hcl
  simp only [phi, List.mem_flatMap, List.mem_range, List.mem_map] at hcl
  obtain ⟨k, hk, τ, -, rfl⟩ := hcl
  have hkt := group_eq T k
  have hcW := col_lt T k
  have hrT := row_lt hk
  set t := row T k with ht
  set c := col T k with hc
  have hvar : ∀ σ, asg (M := M) y T (var M k σ) = decide (truth M y T t c = σ) := fun σ => asg_var y T k σ
  rw [evalClause_iff]
  cases τ with
  | alo =>
    refine ⟨(var M k (truth M y T t c), true), ?_, by simp [hvar]⟩
    simp only [clause, List.mem_map]
    exact ⟨_, mem_univL _, rfl⟩
  | amo a b =>
    simp only [clause]
    split_ifs with hab
    · by_cases ha : truth M y T t c = a
      · refine ⟨(var M k b, false), by simp, ?_⟩
        simp only [evalLiteral_neg, hvar, ha]
        simpa using hab
      · exact ⟨(var M k a, false), by simp, by simp [hvar, ha]⟩
    · exact (evalClause_iff (asg (M := M) y T) _).1 (taut_eval (asg (M := M) y T) k)
  | win a b d =>
    simp only [clause]
    split_ifs with hwin
    · obtain ⟨hrt, hc1, hc2⟩ := hwin
      have ek1 : k - 1 = t * W T + (c - 1) := by omega
      have ek2 : k + 1 = t * W T + (c + 1) := by omega
      have ek3 : k + W T = (t + 1) * W T + c := by rw [hkt]; ring
      have v1 : ∀ σ, asg (M := M) y T (var M (k - 1) σ) = decide (truth M y T t (c - 1) = σ) := by
        intro σ; rw [ek1, asg_var, row_mk T t (c - 1) (by omega), col_mk T t (c - 1) (by omega)]
      have v2 : ∀ σ, asg (M := M) y T (var M (k + 1) σ) = decide (truth M y T t (c + 1) = σ) := by
        intro σ; rw [ek2, asg_var, row_mk T t (c + 1) hc2, col_mk T t (c + 1) hc2]
      have v3 : ∀ σ, asg (M := M) y T (var M (k + W T) σ) = decide (truth M y T (t + 1) c = σ) := by
        intro σ; rw [ek3, asg_var, row_mk T (t + 1) c hcW, col_mk T (t + 1) c hcW]
      by_cases h1 : truth M y T t (c - 1) = a
      · by_cases h2 : truth M y T t c = b
        · by_cases h3 : truth M y T t (c + 1) = d
          · refine ⟨(var M (k + W T) (M.cellRule a b d), true), by simp, ?_⟩
            rw [evalLiteral_pos, v3, truth_step M y T t c hc1, h1, h2, h3]; simp
          · exact ⟨(var M (k + 1) d, false), by simp, by simp [v2, h3]⟩
        · exact ⟨(var M k b, false), by simp, by simp [hvar, h2]⟩
      · exact ⟨(var M (k - 1) a, false), by simp, by simp [v1, h1]⟩
    · exact (evalClause_iff (asg (M := M) y T) _).1 (taut_eval (asg (M := M) y T) k)
  | unit =>
    simp only [clause]
    split_ifs with hb hf
    · refine ⟨(var M k (blankC M), true), by simp, ?_⟩
      rw [evalLiteral_pos, hvar, truth_bnd M hyl (by omega) (by unfold W at hb; omega)]
      simp
    · refine ⟨(var M k (fixCell M x (pos T k)), true), by simp, ?_⟩
      rw [← ht] at hf
      rw [evalLiteral_pos, hvar, hf.1]
      unfold pos
      rw [← hc, fix_eq_truth M hw hf.2]
      simp only [decide_eq_true_eq]
      rfl
    · exact (evalClause_iff (asg (M := M) y T) _).1 (taut_eval (asg (M := M) y T) k)
  | wit1 =>
    simp only [clause]
    split_ifs with hwt
    · obtain ⟨hr0, hwc⟩ := hwt
      unfold pos at hwc
      rw [← hc] at hwc
      rw [← ht] at hr0
      rcases (truth_wit (x := x) (w := w) (T := T) hnb hwc.1).2 with h | h | h
      · exact ⟨(var M k (M.inp false, none), true), by simp,
          by rw [evalLiteral_pos, hvar, hr0, h]; simp⟩
      · exact ⟨(var M k (M.inp true, none), true), by simp,
          by rw [evalLiteral_pos, hvar, hr0, h]; simp⟩
      · exact ⟨(var M k (blankC M), true), by simp, by rw [evalLiteral_pos, hvar, hr0, h]; simp⟩
    · exact (evalClause_iff (asg (M := M) y T) _).1 (taut_eval (asg (M := M) y T) k)
  | wit2 =>
    simp only [clause]
    split_ifs with hwt
    · obtain ⟨hr0, hwc, hc2⟩ := hwt
      unfold pos at hwc
      rw [← hc] at hwc hc2
      rw [← ht] at hr0
      have ek2 : k + 1 = 0 * W T + (c + 1) := by rw [hkt, hr0]; ring
      by_cases hbl : truth M y T 0 c = blankC M
      · refine ⟨(var M (k + 1) (blankC M), true), by simp, ?_⟩
        rw [evalLiteral_pos, ek2, asg_var, row_mk T 0 (c + 1) hc2, col_mk T 0 (c + 1) hc2]
        have h1 := (truth_wit (x := x) (w := w) (T := T) hnb hwc.1).1.1 hbl
        have hw1 := hwc.1
        have h2 := (truth_wit (x := x) (w := w) (T := T) (c := c + 1) hnb
          (by push_cast; omega)).1.2
        rw [h2 (by push_cast; omega)]
        simp
      · exact ⟨(var M k (blankC M), false), by simp, by rw [evalLiteral_neg, hvar, hr0]; simp [hbl]⟩
    · exact (evalClause_iff (asg (M := M) y T) _).1 (taut_eval (asg (M := M) y T) k)
  | accC =>
    simp only [clause]
    split_ifs with hrT' hc2
    · rw [← ht] at hrT'
      rw [← hc] at hc2
      by_cases hf : accFrom (M := M) y T c
      · obtain ⟨c', hcc', hc'W, hacc'⟩ := hf
        rcases Nat.lt_or_ge c c' with hlt | hge
        · refine ⟨(accv M (k + 1), true), by simp, ?_⟩
          rw [evalLiteral_pos, show k + 1 = t * W T + (c + 1) by omega, asg_accv,
            col_mk T t (c + 1) hc2]
          exact decide_eq_true ⟨c', by omega, hc'W, hacc'⟩
        · have hcc : c' = c := by omega
          rw [hcc] at hacc'
          refine ⟨(var M k (truth M y T t c), true), ?_, by simp [hvar]⟩
          refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
          simp only [accLits, List.mem_filterMap]
          refine ⟨truth M y T t c, mem_univL _, ?_⟩
          rw [if_pos (by rw [hrT']; exact hacc')]
      · exact ⟨(accv M k, false), by simp, by rw [evalLiteral_neg, asg_accv]; simp [← hc, hf]⟩
    · rw [← ht] at hrT'
      rw [← hc] at hc2
      by_cases hf : accFrom (M := M) y T c
      · obtain ⟨c', hcc', hc'W, hacc'⟩ := hf
        have hcc : c' = c := by omega
        rw [hcc] at hacc'
        refine ⟨(var M k (truth M y T t c), true), ?_, by simp [hvar]⟩
        refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
        simp only [accLits, List.mem_filterMap]
        refine ⟨truth M y T t c, mem_univL _, ?_⟩
        rw [if_pos (by rw [hrT']; exact hacc')]
      · exact ⟨(accv M k, false), by simp, by rw [evalLiteral_neg, asg_accv]; simp [← hc, hf]⟩
    · exact (evalClause_iff (asg (M := M) y T) _).1 (taut_eval (asg (M := M) y T) k)
  | accS =>
    simp only [clause]
    split_ifs with hs
    · refine ⟨(accv M k, true), by simp, ?_⟩
      rw [← ht, ← hc] at hs
      rw [evalLiteral_pos, asg_accv, ← hc, hs.2]
      apply decide_eq_true
      obtain ⟨h1, h2⟩ := abs_le.mp (head_le M y T)
      refine ⟨((M.run (M.init y) T).head + (T + 1)).toNat, Nat.zero_le _, by unfold W; omega, ?_⟩
      have e : (((M.run (M.init y) T).head + (T + 1)).toNat : ℤ) - (T + 1) =
          (M.run (M.init y) T).head := by omega
      simp only [truth]
      rw [e, cellAcc_head]
      exact hacc
    · exact (evalClause_iff (asg (M := M) y T) _).1 (taut_eval (asg (M := M) y T) k)

end Complete

/-! ## The tableau theorem -/

/-- **Cook–Levin tableau.**  For a machine whose input symbols are injective and non-blank,
`phi M x Q T` is satisfiable iff `M` accepts some `pair x w` with `|w| ≤ Q` at time `T`. -/
theorem phi_sat_iff (hinj : Function.Injective M.inp) (hnb : ∀ b, M.inp b ≠ M.blank)
    (x : List Bool) (Q T : ℕ) (hT : 2 * x.length + 1 + Q ≤ T) :
    satisfiable (phi M x Q T) ↔
      ∃ w : List Bool, w.length ≤ Q ∧ M.acc (M.run (M.init (pair x w)) T).q = true :=
  ⟨fun ⟨α, hα⟩ => sound hinj hT hα,
    fun ⟨w, hw, hacc⟩ => ⟨_, complete hnb hT hw hacc⟩⟩

end Tableau

/-! ## Every NP language reduces to dense SAT through the tableau -/

/-- Polynomials with natural coefficients are monotone on `ℕ`. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-- Acceptance at time `T` of the normalized verifier, as a decision. -/
theorem nrm_acc_iff (V : TM) {VL : Set (List Bool)} {P : ℕ → ℕ} (hV : V.Decides VL P)
    (y : List Bool) {T : ℕ} (hT : P y.length ≤ T) :
    (Nrm.nrm V).acc ((Nrm.nrm V).run ((Nrm.nrm V).init y) T).q = true ↔ y ∈ VL := by
  obtain ⟨b, hb, hiff⟩ := Nrm.nrm_answer V hV y hT
  simp only [TM.ans, answerOf] at hb
  split_ifs at hb with ha hr
  · cases hb; simpa [ha] using hiff
  · cases hb; simp only [ha, Bool.false_eq_true, false_iff]; simpa using hiff

/-- The reduction data of an NP language: normalized verifier `M`, witness bound `q`, time
bound `t`. -/
structure Data where
  M : TM
  q : Polynomial ℕ
  t : Polynomial ℕ

namespace Data

variable (d : Data)

/-- **The Cook–Levin instance of `x`.** -/
noncomputable def inst (x : List Bool) : List Bool :=
  encDense (numVars d.M (d.t.eval x.length))
    (phi d.M x (d.q.eval x.length) (d.t.eval x.length))

end Data

/-- **Cook–Levin, mathematical form.**  For every `L ∈ NP_TM` there are a single-tape machine
`M` with injective, non-blank input symbols and polynomials `q`, `t` such that, for every `x`,
`x ∈ L ↔ encDense (numVars M T) (phi M x Q T) ∈ SAT_dense` with `Q = q(|x|)`, `T = t(|x|)`, and
`2|x| + 1 + Q ≤ T`.  The instance has `3·numVars·|phi|` bits, polynomial in `|x|`. -/
theorem cookLevin {L : Set (List Bool)} (hL : L ∈ NP_TM) :
    ∃ d : Data, Function.Injective d.M.inp ∧ (∀ b, d.M.inp b ≠ d.M.blank) ∧
      ∀ x : List Bool, 2 * x.length + 1 + d.q.eval x.length ≤ d.t.eval x.length ∧
        (x ∈ L ↔ d.inst x ∈ SAT_dense) := by
  obtain ⟨VL, ⟨V, p, hV⟩, q, hq⟩ := hL
  let s : Polynomial ℕ := 2 * Polynomial.X + 1 + q
  refine ⟨⟨Nrm.nrm V, q, p.comp s + s⟩, Nrm.nrm_inp_inj V, Nrm.nrm_inp_ne_blank V,
    fun x => ?_⟩
  have hs : s.eval x.length = 2 * x.length + 1 + q.eval x.length := by
    simp [s]
  have hT : 2 * x.length + 1 + q.eval x.length ≤ (p.comp s + s).eval x.length := by
    simp only [Polynomial.eval_add, hs]; omega
  refine ⟨hT, ?_⟩
  have hN : 1 ≤ numVars (Nrm.nrm V) ((p.comp s + s).eval x.length) := by
    unfold numVars K W G
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  show x ∈ L ↔ encDense _ (phi (Nrm.nrm V) x _ _) ∈ SAT_dense
  rw [encDense_mem_SAT_iff _ hN _ (phi_bounded _ _ _ _),
    phi_sat_iff _ (Nrm.nrm_inp_inj V) (Nrm.nrm_inp_ne_blank V) x _ _ hT, hq x]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  refine (nrm_acc_iff V hV (pair x w) ?_).symm
  have hpl : (pair x w).length ≤ s.eval x.length := by
    rw [pair_length', hs]; omega
  calc p.eval (pair x w).length ≤ p.eval (s.eval x.length) := eval_mono p hpl
    _ = (p.comp s).eval x.length := by rw [Polynomial.eval_comp]
    _ ≤ (p.comp s + s).eval x.length := by rw [Polynomial.eval_add]; omega

end PVNP.CookLevin
