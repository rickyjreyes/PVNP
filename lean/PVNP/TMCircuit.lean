import PVNP.Circuits

/-!
# Phase X: tableau circuits for single-tape Turing machines (`P_TM ⊆ Ppoly`)

For every ordinary single-tape machine `M` (`PVNP.Discrete.TM`), every time bound `T` and every
input length `N`, `tableau M T N src` is an explicit Boolean circuit that computes whether the
first answer of `M` within `T` steps is `true` (`tableau_eval`). Its size is at most
`(T+1)(2T+3)·c_M`, where `c_M` depends only on the state set and tape alphabet of `M`
(`size_tableau`). The input bits of the machine are taken from an arbitrary source map
`src : ℕ → Src` (constant bits or circuit inputs), so the same construction serves verifiers run
on `pair x w`.

The construction is the standard tableau.
* `content M c j` is the symbol of cell `j` together with the state, if the head is there.
* `content_next` proves that one step of `TM.next` acts on contents by the cell-local rule
  `rule M` (radius one). This is derived from the definition of `TM.step`, including halted
  configurations.
* The circuit holds a one-hot copy of the contents of the cells `|j| ≤ T` at every time `s ≤ T`,
  and computes the next row by evaluating `rule` on all `|Sym|³` neighbour patterns.
* `abs_head_run`: the head never leaves `[-s, s]` before time `s`, so the window `[-T, T]` with
  blank edges at `±(T+1)` is exact (`rule_congr_left`, `rule_congr_right`).
* The first-answer semantics (`FirstAnswer`, acceptance precedence of `answerOf`) is computed by
  a chain "no answer before `s`" and an OR over `s ≤ T`.

**Main results.**
* `P_TM_subset_Ppoly`: every language in `P_TM` has polynomial-size circuits.
* `satLowerBound_of_not_Ppoly`: if `SAT_dense` has no polynomial-size circuits, then
  `SATLowerBound` holds, and hence `P_TM ≠ NP_TM` (`P_ne_NP_of_not_Ppoly`).
-/

namespace PVNP.TMCircuit

open PVNP.Discrete PVNP.Discrete.TM PVNP.Circuits

/-! ### The local rule of a single-tape machine -/

section Rule

variable (M : TM)

/-- The local content of a tape cell: its symbol and, if the head is on it, the state. -/
abbrev Sym := M.Γ × Option M.Λ

/-- The local content of cell `j` in the configuration `c`. -/
def content (c : M.Cfg) (j : ℤ) : Sym M := (c.tape j, if c.head = j then some c.q else none)

/-- The symbol of a cell after one step, computed from its own content. -/
def newSym (c : Sym M) : M.Γ :=
  match c.2 with
  | some q =>
    match M.δ q c.1 with
    | some t => t.2.1
    | none => c.1
  | none => c.1

/-- The state of a head entering from a neighbour that moves in direction `d`. -/
def enter (n : Sym M) (d : Dir) : Option M.Λ :=
  match n.2 with
  | some q =>
    match M.δ q n.1 with
    | some t => if t.2.2 = d then some t.1 else none
    | none => none
  | none => none

/-- The head marker of a cell after one step. -/
def newMark (l c r : Sym M) : Option M.Λ :=
  match c.2 with
  | some q =>
    match M.δ q c.1 with
    | none => some q
    | some t => if t.2.2 = Dir.S then some t.1 else none
  | none =>
    match enter M l Dir.R with
    | some q => some q
    | none => enter M r Dir.L

/-- **The local rule**: the content of a cell after one step, from the contents of the cell and
its two neighbours. -/
def rule (l c r : Sym M) : Sym M := (newSym M c, newMark M l c r)

theorem enter_of_none {n : Sym M} (h : n.2 = none) (d : Dir) : enter M n d = none := by
  simp [enter, h]

/-- A neighbour without the head does not influence the rule. -/
theorem rule_congr_left {l l' c r : Sym M} (hl : l.2 = none) (hl' : l'.2 = none) :
    rule M l c r = rule M l' c r := by
  simp only [rule, newMark, enter_of_none M hl, enter_of_none M hl']

theorem rule_congr_right {l c r r' : Sym M} (hr : r.2 = none) (hr' : r'.2 = none) :
    rule M l c r = rule M l c r' := by
  simp only [rule, newMark, enter_of_none M hr, enter_of_none M hr']

theorem newSym_of_none {c : Sym M} (h : c.2 = none) : newSym M c = c.1 := by
  simp [newSym, h]

theorem newMark_of_none {l c r : Sym M} (h : c.2 = none)
    (hl : enter M l Dir.R = none) (hr : enter M r Dir.L = none) : newMark M l c r = none := by
  simp only [newMark, h, hl, hr]

theorem newMark_of_none_left {l c r : Sym M} (h : c.2 = none) {q : M.Λ}
    (hl : enter M l Dir.R = some q) : newMark M l c r = some q := by
  simp only [newMark, h, hl]

theorem newMark_of_none_right {l c r : Sym M} (h : c.2 = none)
    (hl : enter M l Dir.R = none) : newMark M l c r = enter M r Dir.L := by
  simp only [newMark, h, hl]

/-- **One step of the machine is the local rule on contents.** -/
theorem content_next (c : M.Cfg) (j : ℤ) :
    content M (M.next c) j = rule M (content M c (j - 1)) (content M c j) (content M c (j + 1)) := by
  rcases hδ : M.δ c.q (c.tape c.head) with _ | ⟨q', a', d⟩
  · have hn : M.next c = c := by simp [TM.next, TM.step, hδ]
    rw [hn]
    by_cases h0 : c.head = j
    · subst h0
      simp [rule, newSym, newMark, content, hδ]
    · have hc : (content M c j).2 = none := by simp [content, h0]
      have hl : enter M (content M c (j - 1)) Dir.R = none := by
        by_cases h1 : c.head = j - 1
        · have ht : c.tape (j - 1) = c.tape c.head := by rw [h1]
          simp [enter, content, h1, ht, hδ]
        · simp [enter, content, h1]
      have hr : enter M (content M c (j + 1)) Dir.L = none := by
        by_cases h1 : c.head = j + 1
        · have ht : c.tape (j + 1) = c.tape c.head := by rw [h1]
          simp [enter, content, h1, ht, hδ]
        · simp [enter, content, h1]
      refine Prod.ext ?_ ?_
      · exact (newSym_of_none M hc).symm
      · show (if c.head = j then some c.q else none) = _
        rw [if_neg h0]
        exact (newMark_of_none M hc hl hr).symm
  · have hn : M.next c = ⟨q', Function.update c.tape c.head a', c.head + d.shift⟩ := by
      simp [TM.next, TM.step, hδ]
    rw [hn]
    by_cases h0 : c.head = j
    · subst h0
      cases d <;> simp [rule, newSym, newMark, content, hδ, Dir.shift]
    · have hc : (content M c j).2 = none := by simp [content, h0]
      refine Prod.ext ?_ ?_
      · show Function.update c.tape c.head a' j = newSym M (content M c j)
        rw [newSym_of_none M hc, Function.update_of_ne (Ne.symm h0)]
        rfl
      · show (if c.head + d.shift = j then some q' else none) =
          newMark M (content M c (j - 1)) (content M c j) (content M c (j + 1))
        by_cases h1 : c.head = j - 1
        · have ht : c.tape (j - 1) = c.tape c.head := by rw [h1]
          have hl : enter M (content M c (j - 1)) Dir.R = if d = Dir.R then some q' else none := by
            simp [enter, content, h1, ht, hδ]
          have key : (c.head + d.shift = j) ↔ d = Dir.R := by
            cases d <;> simp [Dir.shift] <;> omega
          by_cases hd : d = Dir.R
          · rw [if_pos (key.2 hd)]
            rw [if_pos hd] at hl
            exact (newMark_of_none_left M hc hl).symm
          · rw [if_neg (fun h => hd (key.1 h))]
            rw [if_neg hd] at hl
            have hr : enter M (content M c (j + 1)) Dir.L = none := by
              have : c.head ≠ j + 1 := by omega
              simp [enter, content, this]
            exact (newMark_of_none M hc hl hr).symm
        · have hl : enter M (content M c (j - 1)) Dir.R = none := by simp [enter, content, h1]
          rw [newMark_of_none_right M hc hl]
          by_cases h2 : c.head = j + 1
          · have ht : c.tape (j + 1) = c.tape c.head := by rw [h2]
            have hr : enter M (content M c (j + 1)) Dir.L = if d = Dir.L then some q' else none := by
              simp [enter, content, h2, ht, hδ]
            have key : (c.head + d.shift = j) ↔ d = Dir.L := by
              cases d <;> simp [Dir.shift] <;> omega
            rw [hr]
            by_cases hd : d = Dir.L
            · rw [if_pos (key.2 hd), if_pos hd]
            · rw [if_neg (fun h => hd (key.1 h)), if_neg hd]
          · have hr : enter M (content M c (j + 1)) Dir.L = none := by simp [enter, content, h2]
            rw [hr]
            have key : ¬ (c.head + d.shift = j) := by
              cases d <;> simp [Dir.shift] <;> omega
            rw [if_neg key]

/-- The configuration at time `s` on input `y`. -/
def cfg (y : List Bool) (s : ℕ) : M.Cfg := M.run (M.init y) s

theorem content_succ (y : List Bool) (s : ℕ) (j : ℤ) :
    content M (cfg M y (s + 1)) j =
      rule M (content M (cfg M y s) (j - 1)) (content M (cfg M y s) j)
        (content M (cfg M y s) (j + 1)) := by
  unfold cfg; rw [TM.run_succ]; exact content_next M _ j

theorem cfg_zero (y : List Bool) : cfg M y 0 = M.init y := by simp [cfg, TM.run]

theorem head_next (c : M.Cfg) : |(M.next c).head - c.head| ≤ 1 := by
  rcases hδ : M.δ c.q (c.tape c.head) with _ | ⟨q', a', d⟩
  · have hn : M.next c = c := by simp [TM.next, TM.step, hδ]
    rw [hn]; simp
  · have hn : M.next c = ⟨q', Function.update c.tape c.head a', c.head + d.shift⟩ := by
      simp [TM.next, TM.step, hδ]
    rw [hn]
    cases d <;> simp [Dir.shift]

/-- The head stays in `[-s, s]` up to time `s`. -/
theorem abs_head_run (y : List Bool) : ∀ s : ℕ, |(cfg M y s).head| ≤ s
  | 0 => by simp [cfg_zero, TM.init]
  | s + 1 => by
    have h1 := abs_head_run y s
    have h2 := head_next M (cfg M y s)
    have he : cfg M y (s + 1) = M.next (cfg M y s) := by unfold cfg; rw [TM.run_succ]
    rw [he]
    have := abs_sub_abs_le_abs_sub (M.next (cfg M y s)).head (cfg M y s).head
    push_cast
    linarith

/-- Accepting marker. -/
def isAcc (a : Sym M) : Bool :=
  match a.2 with
  | some q => M.acc q
  | none => false

/-- Answering marker. -/
def isAns (a : Sym M) : Bool :=
  match a.2 with
  | some q => M.acc q || M.rej q
  | none => false

theorem isAcc_content (c : M.Cfg) (j : ℤ) :
    isAcc M (content M c j) = (decide (c.head = j) && M.acc c.q) := by
  by_cases h : c.head = j <;> simp [isAcc, content, h]

theorem isAns_content (c : M.Cfg) (j : ℤ) :
    isAns M (content M c j) = (decide (c.head = j) && (M.acc c.q || M.rej c.q)) := by
  by_cases h : c.head = j <;> simp [isAns, content, h]

end Rule

/-! ### The tableau circuit -/

/-- A source for an input cell of the simulated machine: a constant bit or a circuit input. -/
inductive Src
  | const (b : Bool)
  | inp (i : ℕ)

/-- The bit supplied by a source. -/
def Src.eval (x : ℕ → Bool) : Src → Bool
  | .const b => b
  | .inp i => x i

/-- The gate reading a source. -/
def Src.gate {α : Type} : Src → Gate α
  | .const b => .const b
  | .inp i => .inp i

theorem Src.gate_eval {α : Type} (v : α → Bool) (x : ℕ → Bool) (s : Src) :
    (s.gate : Gate α).eval v x = s.eval x := by
  cases s <;> rfl

/-- Register names of the tableau circuit. -/
inductive WN (M : TM) : Type
  | inb (j : ℤ)
  | ninb (j : ℤ)
  | cell (s : ℕ) (j : ℤ) (a : Sym M)
  | tl (s : ℕ) (j : ℤ) (k : ℕ)
  | tr (s : ℕ) (j : ℤ) (k : ℕ)
  | ch (s : ℕ) (j : ℤ) (a : Sym M) (k : ℕ)
  | wa (s : ℕ) (k : ℕ)
  | wn (s : ℕ) (k : ℕ)
  | nany (s : ℕ)
  | nb (s : ℕ)
  | first (s : ℕ)
  | res (s : ℕ)
  deriving DecidableEq

section Tableau

variable (M : TM)

/-- All contents. -/
noncomputable def syms : List (Sym M) := (Finset.univ : Finset (Sym M)).toList

/-- All neighbour patterns. -/
noncomputable def triples : List (Sym M × Sym M × Sym M) :=
  (Finset.univ : Finset (Sym M × Sym M × Sym M)).toList

/-- The content of a blank cell without the head. -/
def blankSym : Sym M := (M.blank, none)

/-- The `k`-th neighbour pattern. -/
noncomputable def tri (k : ℕ) : Sym M × Sym M × Sym M :=
  (triples M).getD k (blankSym M, blankSym M, blankSym M)

/-- The number of neighbour patterns, `|Sym|³`. -/
noncomputable def K : ℕ := (triples M).length

/-- The window `[-T, T]`. -/
def win (T : ℕ) : List ℤ := (List.range (2 * T + 1)).map fun i : ℕ => (i : ℤ) - (T : ℤ)

/-- The window with its edges, `[-(T+1), T+1]`. -/
def win1 (T : ℕ) : List ℤ := (List.range (2 * T + 3)).map fun i : ℕ => (i : ℤ) - ((T : ℤ) + 1)

/-- The (cell, content) pairs of the window. -/
noncomputable def pairs (T : ℕ) : List (ℤ × Sym M) :=
  (win T).flatMap fun j => (syms M).map fun a => (j, a)

/-- The `k`-th pair. -/
noncomputable def pr (T k : ℕ) : ℤ × Sym M := (pairs M T).getD k (0, blankSym M)

/-- The number of pairs. -/
noncomputable def P (T : ℕ) : ℕ := (pairs M T).length

/-- The initial head marker of cell `j`. -/
def mk0 (j : ℤ) : Option M.Λ := if (0 : ℤ) = j then some M.start else none

theorem mem_win {T : ℕ} {j : ℤ} : j ∈ win T ↔ |j| ≤ T := by
  simp only [win, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [abs_le]; constructor <;> omega
  · intro h
    rw [abs_le] at h
    exact ⟨(j + T).toNat, by omega, by omega⟩

theorem mem_win1 {T : ℕ} {j : ℤ} : j ∈ win1 T ↔ |j| ≤ T + 1 := by
  simp only [win1, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [abs_le]; constructor <;> omega
  · intro h
    rw [abs_le] at h
    exact ⟨(j + (T + 1)).toNat, by omega, by omega⟩

theorem length_win (T : ℕ) : (win T).length = 2 * T + 1 := by simp [win]

theorem length_win1 (T : ℕ) : (win1 T).length = 2 * T + 3 := by simp [win1]

theorem mem_syms (a : Sym M) : a ∈ syms M := Finset.mem_toList.2 (Finset.mem_univ a)

theorem length_syms : (syms M).length = Fintype.card (Sym M) := by
  simp [syms, Finset.length_toList]

theorem tri_mem {k : ℕ} (hk : k < K M) : tri M k ∈ triples M := by
  unfold tri; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

theorem exists_tri (t : Sym M × Sym M × Sym M) : ∃ k < K M, tri M k = t := by
  have ht : t ∈ triples M := Finset.mem_toList.2 (Finset.mem_univ t)
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem ht
  exact ⟨k, hk, by unfold tri; rw [List.getD_eq_getElem _ _ hk, he]⟩

theorem pr_mem {T k : ℕ} (hk : k < P M T) : pr M T k ∈ pairs M T := by
  unfold pr; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

theorem exists_pr {T : ℕ} {q : ℤ × Sym M} (hq : q ∈ pairs M T) : ∃ k < P M T, pr M T k = q := by
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem hq
  exact ⟨k, hk, by unfold pr; rw [List.getD_eq_getElem _ _ hk, he]⟩

theorem mem_pairs {T : ℕ} {q : ℤ × Sym M} : q ∈ pairs M T ↔ |q.1| ≤ T := by
  simp only [pairs, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨j, hj, a, -, rfl⟩; exact mem_win.1 hj
  · intro h; exact ⟨q.1, mem_win.2 h, q.2, mem_syms M q.2, rfl⟩

variable (T N : ℕ) (src : ℕ → Src)

/-- The gates of the tableau circuit. -/
noncomputable def gate : WN M → Gate (WN M)
  | .inb j => if 0 ≤ j ∧ j < N ∧ |j| ≤ T + 1 then (src j.toNat).gate else .const false
  | .ninb j => if 0 ≤ j ∧ j < N ∧ |j| ≤ T + 1 then .not (.inb j) else .const false
  | .cell 0 j a =>
    if |j| ≤ T then
      if 0 ≤ j ∧ j < N then
        if a = (M.inp true, mk0 M j) then
          (if a = (M.inp false, mk0 M j) then .const true else .or (.inb j) (.inb j))
        else if a = (M.inp false, mk0 M j) then .or (.ninb j) (.ninb j) else .const false
      else .const (decide (a = (M.blank, mk0 M j)))
    else if |j| = T + 1 then .const (decide (a = blankSym M)) else .const false
  | .cell (s + 1) j a =>
    if s + 1 ≤ T then
      if |j| ≤ T then .or (.ch (s + 1) j a (K M)) (.ch (s + 1) j a (K M))
      else if |j| = T + 1 then .const (decide (a = blankSym M)) else .const false
    else .const false
  | .tl s j k =>
    if 1 ≤ s ∧ s ≤ T ∧ |j| ≤ T ∧ k < K M then
      .and (.cell (s - 1) (j - 1) (tri M k).1) (.cell (s - 1) j (tri M k).2.1)
    else .const false
  | .tr s j k =>
    if 1 ≤ s ∧ s ≤ T ∧ |j| ≤ T ∧ k < K M then
      .and (.tl s j k) (.cell (s - 1) (j + 1) (tri M k).2.2)
    else .const false
  | .ch _ _ _ 0 => .const false
  | .ch s j a (k + 1) =>
    if 1 ≤ s ∧ s ≤ T ∧ |j| ≤ T ∧ k < K M then
      if rule M (tri M k).1 (tri M k).2.1 (tri M k).2.2 = a then .or (.ch s j a k) (.tr s j k)
      else .or (.ch s j a k) (.ch s j a k)
    else .const false
  | .wa _ 0 => .const false
  | .wa s (k + 1) =>
    if s ≤ T ∧ k < P M T then
      if isAcc M (pr M T k).2 then .or (.wa s k) (.cell s (pr M T k).1 (pr M T k).2)
      else .or (.wa s k) (.wa s k)
    else .const false
  | .wn _ 0 => .const false
  | .wn s (k + 1) =>
    if s ≤ T ∧ k < P M T then
      if isAns M (pr M T k).2 then .or (.wn s k) (.cell s (pr M T k).1 (pr M T k).2)
      else .or (.wn s k) (.wn s k)
    else .const false
  | .nany s => if s ≤ T then .not (.wn s (P M T)) else .const false
  | .nb 0 => .const true
  | .nb (s + 1) => if s + 1 ≤ T then .and (.nb s) (.nany s) else .const false
  | .first s => if s ≤ T then .and (.nb s) (.wa s (P M T)) else .const false
  | .res 0 => .const false
  | .res (s + 1) => if s ≤ T then .or (.res s) (.first s) else .const false

/-- Rank budget of one row. -/
noncomputable def D : ℕ := 3 * K M + 3

/-- Base rank of row `s ≥ 1`. -/
noncomputable def ob (s : ℕ) : ℕ := 3 + (s - 1) * D M

/-- Base rank of the answer logic. -/
noncomputable def A0 : ℕ := 3 + T * D M

/-- Ranks: every gate reads registers of strictly smaller rank. -/
noncomputable def rank : WN M → ℕ
  | .inb _ => 0
  | .ninb _ => 1
  | .cell 0 _ _ => 2
  | .cell (s + 1) _ _ => ob M (s + 1) + 3 * K M + 1
  | .tl s _ k => ob M s + 3 * k + 1
  | .tr s _ k => ob M s + 3 * k + 2
  | .ch s _ _ k => ob M s + 3 * k
  | .wa _ k => A0 M T + k
  | .wn _ k => A0 M T + k
  | .nany _ => A0 M T + P M T + 1
  | .nb s => A0 M T + P M T + 2 + s
  | .first s => A0 M T + P M T + 3 + T + s
  | .res s => A0 M T + P M T + 4 + 2 * T + s

/-- The rank of a row-`s` cell. -/
theorem rank_cell (s : ℕ) (j : ℤ) (a : Sym M) :
    rank M T (.cell s j a) = if s = 0 then 2 else ob M s + 3 * K M + 1 := by
  cases s <;> simp [rank]

theorem rank_cell_lt_ob {s : ℕ} (hs : 1 ≤ s) (j : ℤ) (a : Sym M) (k : ℕ) :
    rank M T (.cell (s - 1) j a) < ob M s + 3 * k + 1 := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  cases s' with
  | zero => simp only [rank, ob, Nat.sub_self, zero_mul, add_zero]; omega
  | succ s'' =>
    simp only [rank, ob, D, Nat.add_sub_cancel]
    nlinarith [Nat.zero_le (s'' * K M)]

theorem rank_cell_lt_A0 {s : ℕ} (hs : s ≤ T) (j : ℤ) (a : Sym M) :
    rank M T (.cell s j a) < A0 M T := by
  cases s with
  | zero =>
    simp only [rank, A0]
    exact Nat.lt_of_lt_of_le (by norm_num) (Nat.le_add_right 3 _)
  | succ s' =>
    simp only [rank, ob, A0, D, Nat.add_sub_cancel]
    have hT : s' + 1 ≤ T := hs
    obtain ⟨u, rfl⟩ : ∃ u, T = s' + 1 + u := ⟨T - (s' + 1), by omega⟩
    nlinarith [Nat.zero_le (s' * K M), Nat.zero_le (u * K M)]

theorem gate_wf : ∀ a, ∀ b ∈ (gate M T N src a).args, rank M T b < rank M T a := by
  intro a b hb
  cases a with
  | inb j =>
    simp only [gate] at hb
    split_ifs at hb
    · cases h : src j.toNat <;> simp [h, Src.gate, Gate.args] at hb
    · simp [Gate.args] at hb
  | ninb j =>
    simp only [gate] at hb
    split_ifs at hb <;> simp_all [Gate.args, rank]
  | cell s j a =>
    cases s with
    | zero =>
      simp only [gate] at hb
      split_ifs at hb <;> simp_all [Gate.args, rank]
    | succ s =>
      simp only [gate] at hb
      split_ifs at hb <;> simp_all [Gate.args, rank]
  | tl s j k =>
    simp only [gate] at hb
    split_ifs at hb with h
    · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> exact rank_cell_lt_ob M T h.1 _ _ k
    · simp [Gate.args] at hb
  | tr s j k =>
    simp only [gate] at hb
    split_ifs at hb with h
    · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · simp [rank]
      · have := rank_cell_lt_ob M T h.1 (j + 1) (tri M k).2.2 k
        have h2 : rank M T (WN.tr s j k) = ob M s + 3 * k + 2 := rfl
        rw [h2]; omega
    · simp [Gate.args] at hb
  | ch s j a k =>
    cases k with
    | zero => simp [gate, Gate.args] at hb
    | succ k =>
      simp only [gate] at hb
      split_ifs at hb with h1 h2
      · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · show ob M s + 3 * k < ob M s + 3 * (k + 1); omega
        · show ob M s + 3 * k + 2 < ob M s + 3 * (k + 1); omega
      · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false, or_self] at hb
        subst hb
        show ob M s + 3 * k < ob M s + 3 * (k + 1); omega
      · simp [Gate.args] at hb
  | wa s k =>
    cases k with
    | zero => simp [gate, Gate.args] at hb
    | succ k =>
      simp only [gate] at hb
      split_ifs at hb with h1 h2
      · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · simp [rank]
        · have := rank_cell_lt_A0 M T h1.1 (pr M T k).1 (pr M T k).2
          have h3 : rank M T (WN.wa s (k + 1)) = A0 M T + (k + 1) := rfl
          rw [h3]; omega
      · simp_all [Gate.args, rank]
      · simp [Gate.args] at hb
  | wn s k =>
    cases k with
    | zero => simp [gate, Gate.args] at hb
    | succ k =>
      simp only [gate] at hb
      split_ifs at hb with h1 h2
      · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · simp [rank]
        · have := rank_cell_lt_A0 M T h1.1 (pr M T k).1 (pr M T k).2
          have h3 : rank M T (WN.wn s (k + 1)) = A0 M T + (k + 1) := rfl
          rw [h3]; omega
      · simp_all [Gate.args, rank]
      · simp [Gate.args] at hb
  | nany s =>
    simp only [gate] at hb
    split_ifs at hb <;> simp_all [Gate.args, rank]
  | nb s =>
    cases s with
    | zero => simp [gate, Gate.args] at hb
    | succ s =>
      simp only [gate] at hb
      split_ifs at hb with h1
      · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · show A0 M T + P M T + 2 + s < A0 M T + P M T + 2 + (s + 1); omega
        · show A0 M T + P M T + 1 < A0 M T + P M T + 2 + (s + 1); omega
      · simp [Gate.args] at hb
  | first s =>
    simp only [gate] at hb
    split_ifs at hb with h1
    · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · show A0 M T + P M T + 2 + s < A0 M T + P M T + 3 + T + s; omega
      · show A0 M T + P M T < A0 M T + P M T + 3 + T + s; omega
    · simp [Gate.args] at hb
  | res s =>
    cases s with
    | zero => simp [gate, Gate.args] at hb
    | succ s =>
      simp only [gate] at hb
      split_ifs at hb with h1
      · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · show A0 M T + P M T + 4 + 2 * T + s < A0 M T + P M T + 4 + 2 * T + (s + 1); omega
        · show A0 M T + P M T + 3 + T + s < A0 M T + P M T + 4 + 2 * T + (s + 1); omega
      · simp [Gate.args] at hb

/-- The listed registers. -/
noncomputable def regs : List (WN M) :=
  (win1 T).map WN.inb ++ (win1 T).map WN.ninb ++
  (List.range (T + 1)).flatMap (fun s => (win1 T).flatMap fun j => (syms M).map (WN.cell s j)) ++
  (List.range T).flatMap (fun s => (win T).flatMap fun j =>
    (List.range (K M)).flatMap fun k => [WN.tl (s + 1) j k, WN.tr (s + 1) j k]) ++
  (List.range T).flatMap (fun s => (win T).flatMap fun j => (syms M).flatMap fun a =>
    (List.range (K M + 1)).map (WN.ch (s + 1) j a)) ++
  (List.range (T + 1)).flatMap (fun s => (List.range (P M T + 1)).flatMap fun k =>
    [WN.wa s k, WN.wn s k]) ++
  (List.range (T + 1)).flatMap (fun s => [WN.nany s, WN.nb s, WN.first s]) ++
  (List.range (T + 2)).map WN.res

theorem gate_triv : ∀ a, a ∉ regs M T → gate M T N src a = .const false := by
  intro a ha
  simp only [regs, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_exists, not_and] at ha
  obtain ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩, hH⟩ := ha
  cases a with
  | inb j =>
    have : ¬ |j| ≤ T + 1 := fun h => hA j (mem_win1.2 h) rfl
    simp [gate, this]
  | ninb j =>
    have : ¬ |j| ≤ T + 1 := fun h => hB j (mem_win1.2 h) rfl
    simp [gate, this]
  | cell s j a =>
    have hn : ¬ (s ≤ T ∧ |j| ≤ T + 1) := fun h =>
      hC s (by omega) j (mem_win1.2 h.2) a (mem_syms M a) rfl
    cases s with
    | zero =>
      have : ¬ |j| ≤ T + 1 := fun h => hn ⟨Nat.zero_le _, h⟩
      have h1 : ¬ |j| ≤ T := fun h => this (by omega)
      have h2 : ¬ |j| = T + 1 := fun h => this (by omega)
      simp [gate, h1, h2]
    | succ s =>
      by_cases hs : s + 1 ≤ T
      · have : ¬ |j| ≤ T + 1 := fun h => hn ⟨hs, h⟩
        have h1 : ¬ |j| ≤ T := fun h => this (by omega)
        have h2 : ¬ |j| = T + 1 := fun h => this (by omega)
        simp [gate, hs, h1, h2]
      · simp [gate, hs]
  | tl s j k =>
    have : ¬ (1 ≤ s ∧ s ≤ T ∧ |j| ≤ T ∧ k < K M) := by
      rintro ⟨h1, h2, h3, h4⟩
      exact (hD (s - 1) (by omega) j (mem_win.2 h3) k h4).1 (by congr 1; omega)
    simp [gate, this]
  | tr s j k =>
    have : ¬ (1 ≤ s ∧ s ≤ T ∧ |j| ≤ T ∧ k < K M) := by
      rintro ⟨h1, h2, h3, h4⟩
      exact (hD (s - 1) (by omega) j (mem_win.2 h3) k h4).2 (by congr 1; omega)
    simp [gate, this]
  | ch s j a k =>
    cases k with
    | zero => simp [gate]
    | succ k =>
      have : ¬ (1 ≤ s ∧ s ≤ T ∧ |j| ≤ T ∧ k < K M) := by
        rintro ⟨h1, h2, h3, h4⟩
        exact hE (s - 1) (by omega) j (mem_win.2 h3) a (mem_syms M a) (k + 1) (by omega)
          (by congr 1; omega)
      simp [gate, this]
  | wa s k =>
    cases k with
    | zero => simp [gate]
    | succ k =>
      have : ¬ (s ≤ T ∧ k < P M T) := by
        rintro ⟨h1, h2⟩
        exact (hF s (by omega) (k + 1) (by omega)).1 rfl
      simp [gate, this]
  | wn s k =>
    cases k with
    | zero => simp [gate]
    | succ k =>
      have : ¬ (s ≤ T ∧ k < P M T) := by
        rintro ⟨h1, h2⟩
        exact (hF s (by omega) (k + 1) (by omega)).2 rfl
      simp [gate, this]
  | nany s =>
    have : ¬ s ≤ T := fun h => (hG s (by omega)).1 rfl
    simp [gate, this]
  | nb s =>
    have : ¬ s ≤ T := fun h => (hG s (by omega)).2.1 rfl
    cases s with
    | zero => exact absurd (Nat.zero_le T) this
    | succ s => simp [gate, this]
  | first s =>
    have : ¬ s ≤ T := fun h => (hG s (by omega)).2.2 rfl
    simp [gate, this]
  | res s =>
    cases s with
    | zero => simp [gate]
    | succ s =>
      have : ¬ s ≤ T := fun h => hH (s + 1) (by omega) rfl
      simp [gate, this]

/-- **The tableau circuit** of `M` for time bound `T`, input length `N` and input sources `src`. -/
noncomputable def tableau : Circuit (WN M) where
  gate := gate M T N src
  rank := rank M T
  wf := gate_wf M T N src
  regs := regs M T
  triv := gate_triv M T N src
  out := .res (T + 1)

/-- Only the input-bit registers read circuit inputs, and they read them through the sources of
input cells. -/
theorem gate_eq_inp {a : WN M} {i : ℕ} (h : gate M T N src a = .inp i) :
    ∃ j : ℤ, 0 ≤ j ∧ j < N ∧ src j.toNat = .inp i := by
  cases a with
  | inb j =>
    simp only [gate] at h
    split_ifs at h with hc
    cases hs : src j.toNat with
    | const b => rw [hs] at h; cases h
    | inp i' => rw [hs] at h; cases h; exact ⟨j, hc.1, hc.2.1, hs⟩
  | ninb j => simp only [gate] at h; split_ifs at h <;> cases h
  | cell s j a => cases s <;> simp only [gate] at h <;> split_ifs at h <;> cases h
  | tl s j k => simp only [gate] at h; split_ifs at h <;> cases h
  | tr s j k => simp only [gate] at h; split_ifs at h <;> cases h
  | ch s j a k => cases k <;> simp only [gate] at h <;> (try split_ifs at h) <;> cases h
  | wa s k => cases k <;> simp only [gate] at h <;> (try split_ifs at h) <;> cases h
  | wn s k => cases k <;> simp only [gate] at h <;> (try split_ifs at h) <;> cases h
  | nany s => simp only [gate] at h; split_ifs at h <;> cases h
  | nb s => cases s <;> simp only [gate] at h <;> (try split_ifs at h) <;> cases h
  | first s => simp only [gate] at h; split_ifs at h <;> cases h
  | res s => cases s <;> simp only [gate] at h <;> (try split_ifs at h) <;> cases h

/-! ### Correctness of the tableau circuit -/

/-- The machine input supplied by the sources. -/
def inputOf (x : ℕ → Bool) : List Bool := (List.range N).map fun j => (src j).eval x

theorem length_inputOf (x : ℕ → Bool) : (inputOf N src x).length = N := by simp [inputOf]

theorem getD_inputOf (x : ℕ → Bool) {j : ℕ} (hj : j < N) :
    (inputOf N src x).getD j false = (src j).eval x := by
  rw [List.getD_eq_getElem _ _ (by rw [length_inputOf]; exact hj)]
  simp [inputOf]

variable (x : ℕ → Bool)

theorem tgate : (tableau M T N src).gate = gate M T N src := rfl

theorem val_inb {j : ℤ} (h : 0 ≤ j ∧ j < N ∧ |j| ≤ T + 1) :
    (tableau M T N src).val x (.inb j) = (src j.toNat).eval x := by
  rw [Circuit.val_eq, tgate]
  simp only [gate, if_pos h]
  exact Src.gate_eval _ _ _

theorem val_ninb {j : ℤ} (h : 0 ≤ j ∧ j < N ∧ |j| ≤ T + 1) :
    (tableau M T N src).val x (.ninb j) = !(src j.toNat).eval x := by
  rw [Circuit.val_eq, tgate]
  simp only [gate, if_pos h, Gate.eval]
  rw [val_inb M T N src x h]

theorem content_cfg_zero (y : List Bool) (j : ℤ) :
    content M (cfg M y 0) j = (M.inputTape y j, mk0 M j) := by
  rw [cfg_zero]; rfl

theorem val_cell_zero {j : ℤ} (hj : |j| ≤ T) (a : Sym M) :
    (tableau M T N src).val x (.cell 0 j a) =
      decide (content M (cfg M (inputOf N src x) 0) j = a) := by
  rw [content_cfg_zero, Circuit.val_eq, tgate]
  by_cases hin : 0 ≤ j ∧ j < N
  · have hT : 0 ≤ j ∧ j < N ∧ |j| ≤ T + 1 := ⟨hin.1, hin.2, by omega⟩
    have htape : M.inputTape (inputOf N src x) j = M.inp ((src j.toNat).eval x) := by
      simp only [TM.inputTape, length_inputOf]
      rw [if_pos ⟨hin.1, by exact_mod_cast hin.2⟩, getD_inputOf N src x (by omega)]
    rw [htape]
    simp only [gate, if_pos hj, if_pos hin]
    by_cases h1 : a = (M.inp true, mk0 M j)
    · by_cases h2 : a = (M.inp false, mk0 M j)
      · simp only [if_pos h1, if_pos h2, Gate.eval]
        cases (src j.toNat).eval x
        · exact (decide_eq_true h2.symm).symm
        · exact (decide_eq_true h1.symm).symm
      · simp only [if_pos h1, if_neg h2, Gate.eval, val_inb M T N src x hT, Bool.or_self]
        cases (src j.toNat).eval x
        · exact (decide_eq_false (Ne.symm h2)).symm
        · exact (decide_eq_true h1.symm).symm
    · by_cases h2 : a = (M.inp false, mk0 M j)
      · simp only [if_neg h1, if_pos h2, Gate.eval, val_ninb M T N src x hT, Bool.or_self]
        cases (src j.toNat).eval x
        · exact (decide_eq_true h2.symm).symm
        · exact (decide_eq_false (Ne.symm h1)).symm
      · simp only [if_neg h1, if_neg h2, Gate.eval]
        cases (src j.toNat).eval x
        · exact (decide_eq_false (Ne.symm h2)).symm
        · exact (decide_eq_false (Ne.symm h1)).symm
  · have htape : M.inputTape (inputOf N src x) j = M.blank := by
      simp only [TM.inputTape, length_inputOf]
      rw [if_neg (fun h => hin ⟨h.1, by exact_mod_cast h.2⟩)]
    rw [htape]
    simp only [gate, if_pos hj, if_neg hin, Gate.eval]
    exact decide_eq_decide.2 eq_comm

theorem val_cell_edge {s : ℕ} (hs : s ≤ T) {j : ℤ} (hj : |j| = T + 1) (a : Sym M) :
    (tableau M T N src).val x (.cell s j a) = decide (a = blankSym M) := by
  rw [Circuit.val_eq, tgate]
  have h1 : ¬ |j| ≤ T := by omega
  cases s with
  | zero => simp only [gate, if_neg h1, if_pos hj, Gate.eval]
  | succ s => simp only [gate, if_pos hs, if_neg h1, if_pos hj, Gate.eval]

theorem val_tr {s : ℕ} (h1 : 1 ≤ s) (hs : s ≤ T) {j : ℤ} (hj : |j| ≤ T) {k : ℕ} (hk : k < K M) :
    (tableau M T N src).val x (.tr s j k) =
      ((tableau M T N src).val x (.cell (s - 1) (j - 1) (tri M k).1) &&
        (tableau M T N src).val x (.cell (s - 1) j (tri M k).2.1) &&
        (tableau M T N src).val x (.cell (s - 1) (j + 1) (tri M k).2.2)) := by
  have hc : 1 ≤ s ∧ s ≤ T ∧ |j| ≤ T ∧ k < K M := ⟨h1, hs, hj, hk⟩
  rw [Circuit.val_eq, tgate]
  simp only [gate, if_pos hc, Gate.eval]
  rw [Circuit.val_eq, tgate]
  simp only [gate, if_pos hc, Gate.eval]

theorem val_ch {s : ℕ} (h1 : 1 ≤ s) (hs : s ≤ T) {j : ℤ} (hj : |j| ≤ T) (a : Sym M) :
    ∀ k ≤ K M, (tableau M T N src).val x (.ch s j a k) =
      decide (∃ k' < k, rule M (tri M k').1 (tri M k').2.1 (tri M k').2.2 = a ∧
        (tableau M T N src).val x (.tr s j k') = true)
  | 0, _ => by
    rw [Circuit.val_eq, tgate]
    simp [gate, Gate.eval]
  | k + 1, hk => by
    have hc : 1 ≤ s ∧ s ≤ T ∧ |j| ≤ T ∧ k < K M := ⟨h1, hs, hj, by omega⟩
    have ih := val_ch h1 hs hj a k (by omega)
    rw [Circuit.val_eq, tgate]
    simp only [gate, if_pos hc]
    by_cases hr : rule M (tri M k).1 (tri M k).2.1 (tri M k).2.2 = a
    · simp only [if_pos hr, Gate.eval, ih]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨k', hk', h⟩ | h)
        · exact ⟨k', by omega, h⟩
        · exact ⟨k, by omega, hr, h⟩
      · rintro ⟨k', hk', h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
        · exact Or.inl ⟨k', hlt, h⟩
        · exact Or.inr h.2
    · simp only [if_neg hr, Gate.eval, ih, Bool.or_self]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨k', hk', h⟩; exact ⟨k', by omega, h⟩
      · rintro ⟨k', hk', h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
        · exact ⟨k', hlt, h⟩
        · exact absurd h.1 hr

/-- The content seen by the circuit: the true content in the window, a blank at the edges. -/
def ext (y : List Bool) (s : ℕ) (j : ℤ) : Sym M :=
  if |j| ≤ T then content M (cfg M y s) j else blankSym M

theorem content_snd_of_ne {c : M.Cfg} {j : ℤ} (h : c.head ≠ j) : (content M c j).2 = none := by
  simp [content, h]

/-- **Row invariant**: the one-hot wires of row `s` hold the true contents of the window. -/
theorem val_cell : ∀ s ≤ T, ∀ j : ℤ, |j| ≤ T → ∀ a : Sym M,
    (tableau M T N src).val x (.cell s j a) =
      decide (content M (cfg M (inputOf N src x) s) j = a)
  | 0, _, j, hj, a => val_cell_zero M T N src x hj a
  | s + 1, hs, j, hj, a => by
    have ih := val_cell s (by omega)
    have hc : s + 1 ≤ T := hs
    have hnb : ∀ j' : ℤ, |j'| ≤ T + 1 → ∀ t : Sym M,
        (tableau M T N src).val x (.cell s j' t) = decide (ext M T (inputOf N src x) s j' = t) := by
      intro j' hj' t
      by_cases hw : |j'| ≤ T
      · rw [ih j' hw t]; simp only [ext, if_pos hw]
      · rw [val_cell_edge M T N src x (by omega) (by omega) t]
        simp only [ext, if_neg hw]
        exact decide_eq_decide.2 eq_comm
    have hl1 : |j - 1| ≤ T + 1 := by rw [abs_le] at hj ⊢; constructor <;> omega
    have hr1 : |j + 1| ≤ T + 1 := by rw [abs_le] at hj ⊢; constructor <;> omega
    have htr : ∀ k < K M, (tableau M T N src).val x (.tr (s + 1) j k) =
        decide (tri M k = (ext M T (inputOf N src x) s (j - 1), ext M T (inputOf N src x) s j,
          ext M T (inputOf N src x) s (j + 1))) := by
      intro k hk
      rw [val_tr M T N src x (by omega) hc hj hk]
      simp only [show s + 1 - 1 = s by omega]
      rw [hnb (j - 1) hl1, hnb j (by omega), hnb (j + 1) hr1]
      apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rw [h1, h2, h3]
      · intro h
        rw [h]
        exact ⟨⟨rfl, rfl⟩, rfl⟩
    rw [Circuit.val_eq, tgate]
    simp only [gate, if_pos hc, if_pos hj, Gate.eval, Bool.or_self]
    rw [val_ch M T N src x (by omega) hc hj a (K M) le_rfl]
    have hall : decide (∃ k' < K M, rule M (tri M k').1 (tri M k').2.1 (tri M k').2.2 = a ∧
        (tableau M T N src).val x (.tr (s + 1) j k') = true) =
        decide (rule M (ext M T (inputOf N src x) s (j - 1)) (ext M T (inputOf N src x) s j)
          (ext M T (inputOf N src x) s (j + 1)) = a) := by
      apply decide_eq_decide.2
      constructor
      · rintro ⟨k', hk', hr, ht⟩
        rw [htr k' hk', decide_eq_true_eq] at ht
        rw [ht] at hr; exact hr
      · intro h
        obtain ⟨k', hk', hke⟩ := exists_tri M (ext M T (inputOf N src x) s (j - 1),
          ext M T (inputOf N src x) s j, ext M T (inputOf N src x) s (j + 1))
        refine ⟨k', hk', by rw [hke]; exact h, ?_⟩
        rw [htr k' hk', decide_eq_true_eq]; exact hke
    rw [hall]
    have hhead := abs_head_run M (inputOf N src x) s
    have hmid : ext M T (inputOf N src x) s j = content M (cfg M (inputOf N src x) s) j := by
      simp only [ext, if_pos hj]
    have hL : ∀ C R : Sym M, rule M (ext M T (inputOf N src x) s (j - 1)) C R =
        rule M (content M (cfg M (inputOf N src x) s) (j - 1)) C R := by
      intro C R
      by_cases hw : |j - 1| ≤ T
      · simp only [ext, if_pos hw]
      · simp only [ext, if_neg hw]
        refine rule_congr_left M rfl (content_snd_of_ne M ?_)
        intro he; rw [he] at hhead; omega
    have hR : ∀ L C : Sym M, rule M L C (ext M T (inputOf N src x) s (j + 1)) =
        rule M L C (content M (cfg M (inputOf N src x) s) (j + 1)) := by
      intro L C
      by_cases hw : |j + 1| ≤ T
      · simp only [ext, if_pos hw]
      · simp only [ext, if_neg hw]
        refine rule_congr_right M rfl (content_snd_of_ne M ?_)
        intro he; rw [he] at hhead; omega
    rw [hL, hR, hmid, ← content_succ]

theorem val_wa {s : ℕ} (hs : s ≤ T) : ∀ k ≤ P M T, (tableau M T N src).val x (.wa s k) =
    decide (∃ k' < k, isAcc M (pr M T k').2 = true ∧
      (tableau M T N src).val x (.cell s (pr M T k').1 (pr M T k').2) = true)
  | 0, _ => by
    rw [Circuit.val_eq, tgate]
    simp [gate, Gate.eval]
  | k + 1, hk => by
    have hc : s ≤ T ∧ k < P M T := ⟨hs, by omega⟩
    have ih := val_wa hs k (by omega)
    rw [Circuit.val_eq, tgate]
    simp only [gate, if_pos hc]
    by_cases hr : isAcc M (pr M T k).2 = true
    · simp only [if_pos hr, Gate.eval, ih]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨k', hk', h⟩ | h)
        · exact ⟨k', by omega, h⟩
        · exact ⟨k, by omega, hr, h⟩
      · rintro ⟨k', hk', h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
        · exact Or.inl ⟨k', hlt, h⟩
        · exact Or.inr h.2
    · simp only [if_neg hr, Gate.eval, ih, Bool.or_self]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨k', hk', h⟩; exact ⟨k', by omega, h⟩
      · rintro ⟨k', hk', h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
        · exact ⟨k', hlt, h⟩
        · exact absurd h.1 hr

theorem val_wn {s : ℕ} (hs : s ≤ T) : ∀ k ≤ P M T, (tableau M T N src).val x (.wn s k) =
    decide (∃ k' < k, isAns M (pr M T k').2 = true ∧
      (tableau M T N src).val x (.cell s (pr M T k').1 (pr M T k').2) = true)
  | 0, _ => by
    rw [Circuit.val_eq, tgate]
    simp [gate, Gate.eval]
  | k + 1, hk => by
    have hc : s ≤ T ∧ k < P M T := ⟨hs, by omega⟩
    have ih := val_wn hs k (by omega)
    rw [Circuit.val_eq, tgate]
    simp only [gate, if_pos hc]
    by_cases hr : isAns M (pr M T k).2 = true
    · simp only [if_pos hr, Gate.eval, ih]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨k', hk', h⟩ | h)
        · exact ⟨k', by omega, h⟩
        · exact ⟨k, by omega, hr, h⟩
      · rintro ⟨k', hk', h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
        · exact Or.inl ⟨k', hlt, h⟩
        · exact Or.inr h.2
    · simp only [if_neg hr, Gate.eval, ih, Bool.or_self]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨k', hk', h⟩; exact ⟨k', by omega, h⟩
      · rintro ⟨k', hk', h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
        · exact ⟨k', hlt, h⟩
        · exact absurd h.1 hr

/-- Some cell of the window satisfies a marker predicate iff the head's state does. -/
theorem exists_marker {s : ℕ} (hs : s ≤ T) (f : Sym M → Bool) (g : M.Λ → Bool)
    (hf : ∀ (c : M.Cfg) (j : ℤ), f (content M c j) = (decide (c.head = j) && g c.q)) :
    decide (∃ k' < P M T, f (pr M T k').2 = true ∧
      (tableau M T N src).val x (.cell s (pr M T k').1 (pr M T k').2) = true) =
      g (cfg M (inputOf N src x) s).q := by
  have hhead := abs_head_run M (inputOf N src x) s
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨k', hk', hacc, hv⟩
    have hmem := (mem_pairs M).1 (pr_mem M hk')
    rw [val_cell M T N src x s hs _ hmem _, decide_eq_true_eq] at hv
    rw [← hv, hf] at hacc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
    exact hacc.2
  · intro hq
    have hmem : ((cfg M (inputOf N src x) s).head,
        content M (cfg M (inputOf N src x) s) (cfg M (inputOf N src x) s).head) ∈ pairs M T :=
      (mem_pairs M).2 (by simp only; omega)
    obtain ⟨k', hk', hke⟩ := exists_pr M hmem
    refine ⟨k', hk', ?_, ?_⟩
    · rw [hke, hf]; simp [hq]
    · rw [hke, val_cell M T N src x s hs _ (by simp only; omega) _]; simp

theorem val_wa_P {s : ℕ} (hs : s ≤ T) :
    (tableau M T N src).val x (.wa s (P M T)) = M.acc (cfg M (inputOf N src x) s).q := by
  rw [val_wa M T N src x hs (P M T) le_rfl]
  exact exists_marker M T N src x hs (isAcc M) M.acc (isAcc_content M)

theorem val_wn_P {s : ℕ} (hs : s ≤ T) :
    (tableau M T N src).val x (.wn s (P M T)) =
      (M.acc (cfg M (inputOf N src x) s).q || M.rej (cfg M (inputOf N src x) s).q) := by
  rw [val_wn M T N src x hs (P M T) le_rfl]
  exact exists_marker M T N src x hs (isAns M) (fun q => M.acc q || M.rej q) (isAns_content M)

theorem val_nb : ∀ s ≤ T, (tableau M T N src).val x (.nb s) =
    decide (∀ s' < s, (M.acc (cfg M (inputOf N src x) s').q ||
      M.rej (cfg M (inputOf N src x) s').q) = false)
  | 0, _ => by
    rw [Circuit.val_eq, tgate]
    simp [gate, Gate.eval]
  | s + 1, hs => by
    have hc : s + 1 ≤ T := hs
    rw [Circuit.val_eq, tgate]
    simp only [gate, if_pos hc, Gate.eval]
    rw [val_nb s (by omega)]
    rw [Circuit.val_eq, tgate]
    simp only [gate, if_pos (show s ≤ T by omega), Gate.eval]
    rw [val_wn_P M T N src x (by omega)]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    constructor
    · rintro ⟨h1, h2⟩ s' hs'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs' with hlt | rfl
      · exact h1 s' hlt
      · exact h2
    · intro h
      exact ⟨fun s' hs' => h s' (by omega), h s (by omega)⟩

theorem val_first {s : ℕ} (hs : s ≤ T) :
    (tableau M T N src).val x (.first s) =
      ((tableau M T N src).val x (.nb s) && M.acc (cfg M (inputOf N src x) s).q) := by
  rw [Circuit.val_eq, tgate]
  simp only [gate, if_pos hs, Gate.eval]
  rw [val_wa_P M T N src x hs]

theorem val_res : ∀ s ≤ T + 1, (tableau M T N src).val x (.res s) =
    decide (∃ s' < s, (tableau M T N src).val x (.first s') = true)
  | 0, _ => by
    rw [Circuit.val_eq, tgate]
    simp [gate, Gate.eval]
  | s + 1, hs => by
    have hc : s ≤ T := by omega
    rw [Circuit.val_eq, tgate]
    simp only [gate, if_pos hc, Gate.eval]
    rw [val_res s (by omega)]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨s', hs', h⟩ | h)
      · exact ⟨s', by omega, h⟩
      · exact ⟨s, by omega, h⟩
    · rintro ⟨s', hs', h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs' with hlt | rfl
      · exact Or.inl ⟨s', hlt, h⟩
      · exact Or.inr h

theorem out_eq (y : List Bool) (s : ℕ) :
    M.out y s = answerOf (M.acc (cfg M y s).q) (M.rej (cfg M y s).q) := rfl

theorem answerOf_eq_some_true (a r : Bool) : answerOf a r = some true ↔ a = true := by
  cases a <;> cases r <;> simp [answerOf]

theorem answerOf_eq_none (a r : Bool) : answerOf a r = none ↔ (a || r) = false := by
  cases a <;> cases r <;> simp [answerOf]

/-- **Tableau correctness.** The circuit outputs `true` exactly when the first answer of `M`
within `T` steps on the supplied input is `true`. -/
theorem tableau_eval :
    (tableau M T N src).eval x = true ↔ FirstAnswer (M.out (inputOf N src x)) T true := by
  show (tableau M T N src).val x (.res (T + 1)) = true ↔ _
  rw [val_res M T N src x (T + 1) le_rfl, decide_eq_true_eq]
  unfold FirstAnswer
  constructor
  · rintro ⟨s, hs, hf⟩
    rw [val_first M T N src x (by omega), Bool.and_eq_true, val_nb M T N src x s (by omega),
      decide_eq_true_eq] at hf
    refine ⟨s, by omega, ?_, fun s' hs' => ?_⟩
    · rw [out_eq, answerOf_eq_some_true]; exact hf.2
    · rw [out_eq, answerOf_eq_none]; exact hf.1 s' hs'
  · rintro ⟨s, hs, hst, hs0⟩
    refine ⟨s, by omega, ?_⟩
    rw [val_first M T N src x hs, Bool.and_eq_true, val_nb M T N src x s hs, decide_eq_true_eq]
    refine ⟨fun s' hs' => ?_, ?_⟩
    · have := hs0 s' hs'; rwa [out_eq, answerOf_eq_none] at this
    · rwa [out_eq, answerOf_eq_some_true] at hst

end Tableau




section Size

variable (M : TM)

theorem length_regs (T : ℕ) :
    (regs M T).length = (2 * T + 3) + (2 * T + 3) + (T + 1) * ((2 * T + 3) * Fintype.card (Sym M)) +
      T * ((2 * T + 1) * (K M * 2)) + T * ((2 * T + 1) * (Fintype.card (Sym M) * (K M + 1))) +
      (T + 1) * ((P M T + 1) * 2) + (T + 1) * 3 + (T + 2) := by
  simp [regs, List.length_flatMap, length_win, length_win1, length_syms]
  ring

theorem P_eq (T : ℕ) : P M T = (2 * T + 1) * Fintype.card (Sym M) := by
  simp [P, pairs, List.length_flatMap, length_win, length_syms]

theorem card_sym_pos : 0 < Fintype.card (Sym M) := Fintype.card_pos_iff.2 ⟨blankSym M⟩

/-- The constant of the size bound; it depends only on the state set and tape alphabet. -/
noncomputable def cM : ℕ := 6 * Fintype.card (Sym M) * (K M + 1) + 12

/-- **Size of the tableau circuit**: at most `(T+1)(2T+3)·c_M`. -/
theorem size_tableau (T N : ℕ) (src : ℕ → Src) :
    (tableau M T N src).size ≤ (T + 1) * (2 * T + 3) * cM M := by
  show (regs M T).length ≤ _
  rw [length_regs, P_eq, cM]
  have ha := card_sym_pos M
  set a := Fintype.card (Sym M)
  set k := K M
  have h1 : T * (2 * T + 1) ≤ (T + 1) * (2 * T + 3) := by nlinarith
  have h2 : (T + 1) * (2 * T + 1) ≤ (T + 1) * (2 * T + 3) := by nlinarith
  have h3 : T + 1 ≤ (T + 1) * (2 * T + 3) := by nlinarith
  have hk : k ≤ a * k := Nat.le_mul_of_pos_left k ha
  nlinarith [Nat.mul_le_mul_right (a * k) h1, Nat.mul_le_mul_right (a * (k + 1)) h1,
    Nat.mul_le_mul_right a h2, Nat.mul_le_mul_right k h1,
    Nat.mul_le_mul_left ((T + 1) * (2 * T + 3)) hk, Nat.zero_le (a * k)]

end Size

/-! ### `P_TM ⊆ Ppoly` and the circuit route to `SATLowerBound` -/

section Classes

/-- With identity sources, the supplied machine input is the circuit input. -/
theorem inputOf_inp (y : List Bool) :
    inputOf y.length Src.inp (fun i => y.getD i false) = y := by
  apply List.ext_getElem (by simp [length_inputOf])
  intro i h1 h2
  simp [inputOf, Src.eval, List.getElem?_eq_getElem h2]

/-- A decider within `T` has first answer `true` within `T(|y|)` exactly on members. -/
theorem firstAnswer_true_iff {M : TM} {L : Set (List Bool)} {Tf : ℕ → ℕ} (hM : M.Decides L Tf)
    (y : List Bool) : FirstAnswer (M.out y) (Tf y.length) true ↔ y ∈ L := by
  obtain ⟨b, hfa, hb⟩ := hM y
  constructor
  · intro h
    obtain ⟨s, -, hs, hs0⟩ := h
    obtain ⟨s', -, hs', hs0'⟩ := hfa
    have hbt : b = true := by
      rcases lt_trichotomy s s' with hlt | rfl | hgt
      · rw [hs0' s hlt] at hs; cases hs
      · rw [hs] at hs'; exact (Option.some.inj hs').symm
      · rw [hs0 s' hgt] at hs'; cases hs'
    exact hb.1 hbt
  · intro hy
    have hbt : b = true := hb.2 hy
    subst hbt; exact hfa

/-- **Every polynomial-time single-tape machine has polynomial-size circuits**: `P_TM ⊆ Ppoly`.
The circuit for inputs of length `n` is `tableau M (p n) n Src.inp`, of size at most
`(p(n)+1)(2p(n)+3)·c_M`. -/
theorem P_TM_subset_Ppoly : P_TM ⊆ Ppoly := by
  rintro L ⟨M, p, hM⟩
  refine ⟨(p + 1) * (2 * p + 3) * Polynomial.C (cM M), fun n =>
    ⟨WN M, tableau M (p.eval n) n Src.inp, ?_, ?_⟩⟩
  · have h := size_tableau M (p.eval n) n Src.inp
    simpa using h
  · intro y hy
    subst hy
    have key := tableau_eval M (p.eval y.length) y.length Src.inp (fun i => y.getD i false)
    rw [inputOf_inp] at key
    rw [key]
    exact firstAnswer_true_iff hM y

/-- If `SAT_dense` has polynomial-time deciders, it has polynomial-size circuits. -/
theorem SAT_dense_mem_Ppoly_of_mem_P_TM (h : SATV.SAT_dense ∈ P_TM) : SATV.SAT_dense ∈ Ppoly :=
  P_TM_subset_Ppoly h

/-- **Circuit route to the decisive premise.** A superpolynomial circuit lower bound for
`SAT_dense` (that is, `SAT_dense ∉ Ppoly`) implies `SATLowerBound`. -/
theorem satLowerBound_of_not_Ppoly (h : SATV.SAT_dense ∉ Ppoly) : CrossingSAT.SATLowerBound :=
  fun hP => h (P_TM_subset_Ppoly hP)

/-- ... and hence the classical-model separation. -/
theorem P_ne_NP_of_not_Ppoly (h : SATV.SAT_dense ∉ Ppoly) : P_TM ≠ NP_TM :=
  CrossingSAT.P_ne_NP_of_satLowerBound (satLowerBound_of_not_Ppoly h)

end Classes

end PVNP.TMCircuit
