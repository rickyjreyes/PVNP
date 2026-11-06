import PVNP.CookLevinKit

/-!
# CL-1, part 2c: every bit of the tableau instance is a finite function of local data

Every clause of `phi M x Q T` mentions only the groups `k − 1, k, k + 1, k + W` of its own group
`k`.  `absClause τ kc` is the same clause written with *relative* group positions (`R5`) and
in-group slots (`Slot`), where `kc` is the finite class of group `k`: its column label (`CLab`),
whether it is in the first row and whether it is in the last row.

* `clause_eq`: `clause M x Q T τ k = (absClause τ (kcOf k)).map (conc T k)`.
* `mem_conc_iff`: for a slot variable `k'·G + r` of the window, membership of `(k'·G + r, pol)`
  in the concrete clause holds iff an abstract literal with polarity `pol`, relative position
  `relOf k k'` and slot index `r` is present.  Hence each bit of `inst x` is computed from
  `(τ, kcOf k, relOf k k', r)` alone, which the generator reads with a constant number of passes.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.PartI PVNP.CookLevin PVNP.Discrete.SATV

section Bits

variable (M : TM)

/-- Relative position of a slot's group with respect to the clause group. -/
inductive R5 where
  | self | left | right | below | none
  deriving DecidableEq, Fintype

/-- Class of the clause group: column label, first row, last row. -/
structure KC where
  lab : CLab
  r0 : Bool
  rT : Bool
  deriving DecidableEq, Fintype

/-- A variable inside a group. -/
inductive Slot where
  | sym (σ : PVNP.CookLevin.Cell M)
  | acc

/-- An abstract literal: relative group, slot, polarity. -/
structure ALit where
  ρ : R5
  s : Slot M
  pol : Bool

/-- Slot index inside a group. -/
noncomputable def Slot.idx {M : TM} : Slot M → ℕ
  | .sym σ => (eqv M σ : ℕ)
  | .acc => ns M

/-- Group reached from `k` by a relative position. -/
def R5.go (T k : ℕ) : R5 → ℕ
  | .self => k
  | .left => k - 1
  | .right => k + 1
  | .below => k + W T
  | .none => k

/-- The concrete literal of an abstract literal at group `k`. -/
noncomputable def conc (T k : ℕ) (a : ALit M) : Literal :=
  (a.ρ.go T k * G M + a.s.idx, a.pol)

/-- Initial-row symbol from a column label. -/
def fixOf (lab : CLab) : PVNP.CookLevin.Cell M :=
  (if lab.inPre then M.inp lab.preBit else M.blank, if lab.origin then some M.start else none)

/-- Abstract tautology. -/
def tautA : List (ALit M) := [⟨.self, .sym (blankC M), true⟩, ⟨.self, .sym (blankC M), false⟩]

/-- Abstract accepting literals. -/
noncomputable def accA : List (ALit M) :=
  (univL (PVNP.CookLevin.Cell M)).filterMap fun σ => if M.cellAcc σ then some ⟨.self, .sym σ, true⟩ else none

/-- **The abstract clause** of template `τ` for a group of class `kc`. -/
noncomputable def absClause : Tpl (PVNP.CookLevin.Cell M) → KC → List (ALit M)
  | .alo, _ => (univL (PVNP.CookLevin.Cell M)).map fun σ => ⟨.self, .sym σ, true⟩
  | .amo a b, _ => if a ≠ b then [⟨.self, .sym a, false⟩, ⟨.self, .sym b, false⟩] else tautA M
  | .win a b c, kc =>
      if kc.rT = false ∧ kc.lab.first = false ∧ kc.lab.last = false then
        [⟨.left, .sym a, false⟩, ⟨.self, .sym b, false⟩, ⟨.right, .sym c, false⟩,
          ⟨.below, .sym (M.cellRule a b c), true⟩]
      else tautA M
  | .unit, kc =>
      if kc.lab.first = true ∨ kc.lab.last = true then [⟨.self, .sym (blankC M), true⟩]
      else if kc.r0 = true ∧ kc.lab.wit = false then [⟨.self, .sym (fixOf M kc.lab), true⟩]
      else tautA M
  | .wit1, kc =>
      if kc.r0 = true ∧ kc.lab.wit = true then
        [⟨.self, .sym (M.inp false, none), true⟩, ⟨.self, .sym (M.inp true, none), true⟩,
          ⟨.self, .sym (blankC M), true⟩]
      else tautA M
  | .wit2, kc =>
      if kc.r0 = true ∧ kc.lab.wit = true ∧ kc.lab.last = false then
        [⟨.self, .sym (blankC M), false⟩, ⟨.right, .sym (blankC M), true⟩]
      else tautA M
  | .accC, kc =>
      if kc.rT = true then
        ⟨.self, .acc, false⟩ :: ((if kc.lab.last = false then [⟨.right, .acc, true⟩] else []) ++
          accA M)
      else tautA M
  | .accS, kc => if kc.rT = true ∧ kc.lab.first = true then [⟨.self, .acc, true⟩] else tautA M

/-- The column label of column `c` (position `j = c − (T+1)`). -/
def labOf (x : List Bool) (Q T c : ℕ) : CLab :=
  ⟨decide (c = 0), decide (c + 1 = W T),
    decide (0 ≤ (c : ℤ) - (T + 1) ∧ (c : ℤ) - (T + 1) < (pre x).length),
    (pre x).getD ((c : ℤ) - (T + 1)).toNat false,
    decide ((c : ℤ) - (T + 1) = 0), decide (isWit x.length Q ((c : ℤ) - (T + 1)))⟩

/-- The class of group `k`. -/
def kcOf (x : List Bool) (Q T k : ℕ) : KC :=
  ⟨labOf x Q T (col T k), decide (row T k = 0), decide (row T k = T)⟩

/-- Relative position of group `k'` with respect to group `k`. -/
def relOf (T k k' : ℕ) : R5 :=
  if k' = k then .self
  else if row T k' = row T k ∧ col T k' + 1 = col T k then .left
  else if row T k' = row T k ∧ col T k' = col T k + 1 then .right
  else if row T k' = row T k + 1 ∧ col T k' = col T k then .below
  else .none

/-! ### Concretization reproduces the clauses -/

theorem fixOf_eq (x : List Bool) (Q T k : ℕ) :
    fixOf M (kcOf x Q T k).lab = fixCell M x (pos T k) := by
  simp only [fixOf, kcOf, labOf, fixCell, pos, decide_eq_true_eq]

theorem conc_self (T k : ℕ) (σ : PVNP.CookLevin.Cell M) (p : Bool) :
    conc M T k ⟨.self, .sym σ, p⟩ = (var M k σ, p) := rfl

theorem tautA_map (T k : ℕ) : (tautA M).map (conc M T k) = taut M k := rfl

theorem clause_eq (x : List Bool) (Q T : ℕ) (τ : Tpl (PVNP.CookLevin.Cell M)) {k : ℕ} (hk : k < K T) :
    clause M x Q T τ k = (absClause M τ (kcOf x Q T k)).map (conc M T k) := by
  have hcW := col_lt T k
  have hrT := row_lt hk
  cases τ with
  | alo => simp [clause, absClause, conc, Slot.idx, var, R5.go]
  | amo a b =>
    simp only [clause, absClause]
    split_ifs <;> rfl
  | win a b c =>
    simp only [clause, absClause, kcOf, labOf, decide_eq_false_iff_not]
    have e : (row T k < T ∧ 1 ≤ col T k ∧ col T k + 1 < W T) ↔
        (¬ row T k = T ∧ ¬ col T k = 0 ∧ ¬ col T k + 1 = W T) := by omega
    by_cases h : row T k < T ∧ 1 ≤ col T k ∧ col T k + 1 < W T
    · rw [if_pos h, if_pos (e.1 h)]; rfl
    · rw [if_neg h, if_neg (fun h' => h (e.2 h'))]; rfl
  | unit =>
    simp only [clause, absClause, kcOf, labOf, decide_eq_true_eq, decide_eq_false_iff_not]
    by_cases h1 : col T k = 0 ∨ col T k + 1 = W T
    · rw [if_pos h1, if_pos h1]; rfl
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : row T k = 0 ∧ ¬ isWit x.length Q (pos T k)
      · rw [if_pos h2, if_pos (by unfold pos at h2; exact h2)]
        simp only [List.map_cons, List.map_nil, conc_self]
        congr 3
        exact (fixOf_eq M x Q T k).symm
      · rw [if_neg h2, if_neg (by unfold pos at h2; exact h2)]; rfl
  | wit1 =>
    simp only [clause, absClause, kcOf, labOf, decide_eq_true_eq]
    by_cases h : row T k = 0 ∧ isWit x.length Q (pos T k)
    · rw [if_pos h, if_pos (by unfold pos at h; exact h)]; rfl
    · rw [if_neg h, if_neg (by unfold pos at h; exact h)]; rfl
  | wit2 =>
    simp only [clause, absClause, kcOf, labOf, decide_eq_true_eq, decide_eq_false_iff_not]
    by_cases h : row T k = 0 ∧ isWit x.length Q (pos T k) ∧ col T k + 1 < W T
    · rw [if_pos h, if_pos (by unfold pos at h; exact ⟨h.1, h.2.1, by omega⟩)]; rfl
    · rw [if_neg h, if_neg (by unfold pos at h; intro h'; exact h ⟨h'.1, h'.2.1, by omega⟩)]; rfl
  | accC =>
    simp only [clause, absClause, kcOf, labOf, decide_eq_true_eq, decide_eq_false_iff_not]
    by_cases h : row T k = T
    · rw [if_pos h, if_pos h]
      simp only [List.map_cons, List.map_append]
      congr 2
      · by_cases h2 : col T k + 1 < W T
        · rw [if_pos h2, if_pos (by omega)]; rfl
        · rw [if_neg h2, if_neg (by omega)]; rfl
      · simp only [accLits, accA, List.map_filterMap]
        congr 1
        funext σ
        split_ifs <;> rfl
    · rw [if_neg h, if_neg h]; rfl
  | accS =>
    simp only [clause, absClause, kcOf, labOf, decide_eq_true_eq]
    by_cases h : row T k = T ∧ col T k = 0
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl

/-! ### Relative positions -/

/-- `ρ` names an actual neighbour of group `k` in the window. -/
def Valid (T k : ℕ) : R5 → Prop
  | .self => True
  | .left => 1 ≤ col T k
  | .right => col T k + 1 < W T
  | .below => row T k < T
  | .none => False

theorem slot_idx_lt (s : Slot M) : s.idx < G M := by
  cases s with
  | sym σ => exact eqv_lt M σ
  | acc => exact ns_lt_G M

theorem go_iff {T k k' : ℕ} (hk : k < K T) (hk' : k' < K T) {ρ : R5} (hv : Valid T k ρ) :
    ρ.go T k = k' ↔ relOf T k k' = ρ := by
  have hW := W_pos T
  have ek := group_eq T k
  have ek' := group_eq T k'
  have hc := col_lt T k
  have hc' := col_lt T k'
  have hr := row_lt hk
  have hr' := row_lt hk'
  -- equality of groups is equality of row and column
  have geq : ∀ t c, c < W T → (k' = t * W T + c ↔ row T k' = t ∧ col T k' = c) := by
    intro t c hcW
    constructor
    · rintro rfl; exact ⟨row_mk T t c hcW, col_mk T t c hcW⟩
    · rintro ⟨h1, h2⟩; rw [ek', h1, h2]
  cases ρ with
  | self =>
    simp only [R5.go]
    unfold relOf
    by_cases h : k' = k
    · simp [h]
    · rw [if_neg h]
      constructor
      · intro h'; exact absurd h'.symm h
      · intro h'; split_ifs at h' <;> cases h'
  | left =>
    simp only [Valid] at hv
    simp only [R5.go, relOf]
    have e : k - 1 = row T k * W T + (col T k - 1) := by omega
    rw [e, eq_comm, geq _ _ (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      rw [if_neg (by intro h; rw [h] at h2; omega), if_pos ⟨h1, by omega⟩]
    · intro h
      split_ifs at h with h1 h2 <;> first | exact ⟨h2.1, by omega⟩ | simp at h
  | right =>
    simp only [Valid] at hv
    simp only [R5.go, relOf]
    have e : k + 1 = row T k * W T + (col T k + 1) := by omega
    rw [e, eq_comm, geq _ _ hv]
    constructor
    · rintro ⟨h1, h2⟩
      rw [if_neg (by intro h; rw [h] at h2; omega), if_neg (by omega), if_pos ⟨h1, h2⟩]
    · intro h
      split_ifs at h with h1 h2 h3 <;> first | exact h3 | simp at h
  | below =>
    simp only [Valid] at hv
    simp only [R5.go, relOf]
    have e : k + W T = (row T k + 1) * W T + col T k := by rw [add_mul, one_mul]; linarith
    rw [e, eq_comm, geq _ _ hc]
    constructor
    · rintro ⟨h1, h2⟩
      rw [if_neg (by intro h; rw [h] at h1; omega), if_neg (by omega), if_neg (by omega),
        if_pos ⟨h1, h2⟩]
    · intro h
      split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | simp at h
  | none => exact absurd hv id

theorem absClause_valid (x : List Bool) (Q T : ℕ) (τ : Tpl (PVNP.CookLevin.Cell M)) {k : ℕ}
    (hk : k < K T) : ∀ a ∈ absClause M τ (kcOf x Q T k), Valid T k a.ρ := by
  have hc := col_lt T k
  have hr := row_lt hk
  intro a ha
  cases τ with
  | alo => simp only [absClause, List.mem_map] at ha; obtain ⟨σ, -, rfl⟩ := ha; trivial
  | amo a b =>
    simp only [absClause] at ha
    split_ifs at ha <;> simp [tautA] at ha <;> rcases ha with rfl | rfl <;> trivial
  | win a b c =>
    simp only [absClause, kcOf, labOf] at ha
    split_ifs at ha with h
    · simp only [decide_eq_false_iff_not] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · show 1 ≤ col T k; omega
      · trivial
      · show col T k + 1 < W T; omega
      · show row T k < T; omega
    · simp [tautA] at ha; rcases ha with rfl | rfl <;> trivial
  | unit =>
    simp only [absClause] at ha
    split_ifs at ha <;> simp [tautA] at ha <;> (try rcases ha with rfl | rfl) <;>
      (try subst ha) <;> trivial
  | wit1 =>
    simp only [absClause] at ha
    split_ifs at ha <;> simp [tautA] at ha <;> (try rcases ha with rfl | rfl | rfl) <;> trivial
  | wit2 =>
    simp only [absClause, kcOf, labOf] at ha
    split_ifs at ha with h
    · simp only [decide_eq_false_iff_not] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · trivial
      · show col T k + 1 < W T; omega
    · simp [tautA] at ha; rcases ha with rfl | rfl <;> trivial
  | accC =>
    simp only [absClause, kcOf, labOf] at ha
    split_ifs at ha with h h2
    · simp only [decide_eq_false_iff_not] at h2
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | ha
      · trivial
      · show col T k + 1 < W T; omega
      · simp only [accA, List.mem_filterMap] at ha
        obtain ⟨σ, -, hσ⟩ := ha; split_ifs at hσ; cases hσ; trivial
    · simp only [List.nil_append, List.mem_cons] at ha
      rcases ha with rfl | ha
      · trivial
      · simp only [accA, List.mem_filterMap] at ha
        obtain ⟨σ, -, hσ⟩ := ha; split_ifs at hσ; cases hσ; trivial
    · simp [tautA] at ha; rcases ha with rfl | rfl <;> trivial
  | accS =>
    simp only [absClause] at ha
    split_ifs at ha <;> simp [tautA] at ha <;> (try rcases ha with rfl | rfl) <;>
      (try subst ha) <;> trivial

/-- **Membership is local.** -/
theorem mem_clause_iff (x : List Bool) (Q T : ℕ) (τ : Tpl (PVNP.CookLevin.Cell M)) {k k' r : ℕ}
    (hk : k < K T) (hk' : k' < K T) (hr : r < G M) (pol : Bool) :
    (k' * G M + r, pol) ∈ clause M x Q T τ k ↔
      ∃ a ∈ absClause M τ (kcOf x Q T k), a.pol = pol ∧ a.ρ = relOf T k k' ∧ a.s.idx = r := by
  rw [clause_eq M x Q T τ hk, List.mem_map]
  have hdec : ∀ a : ALit M, a ∈ absClause M τ (kcOf x Q T k) →
      (conc M T k a = (k' * G M + r, pol) ↔ (a.pol = pol ∧ a.ρ = relOf T k k' ∧ a.s.idx = r)) := by
    intro a ha
    have hv := absClause_valid M x Q T τ hk a ha
    have hi := slot_idx_lt M a.s
    simp only [conc, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      have hq : a.ρ.go T k = k' := by
        have := congrArg (· / G M) h1
        simp only at this
        rwa [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt hi,
          zero_add, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
          Nat.div_eq_of_lt hr, zero_add] at this
      refine ⟨h2, ((go_iff hk hk' hv).1 hq).symm, ?_⟩
      rw [hq] at h1; omega
    · rintro ⟨h1, h2, h3⟩
      have hq : a.ρ.go T k = k' := (go_iff hk hk' hv).2 h2.symm
      rw [hq, h3]; exact ⟨rfl, h1⟩
  constructor
  · rintro ⟨a, ha, he⟩; exact ⟨a, ha, (hdec a ha).1 he⟩
  · rintro ⟨a, ha, he⟩; exact ⟨a, ha, (hdec a ha).2 he⟩

/-! ### The bit function -/

/-- Positive-literal bit of slot `r` at relative position `ρ`. -/
noncomputable def posBit (τ : Tpl (PVNP.CookLevin.Cell M)) (kc : KC) (ρ : R5) (r : ℕ) : Bool :=
  decide (∃ a ∈ absClause M τ kc, a.pol = true ∧ a.ρ = ρ ∧ a.s.idx = r)

/-- Negative-literal bit of slot `r` at relative position `ρ`. -/
noncomputable def negBit (τ : Tpl (PVNP.CookLevin.Cell M)) (kc : KC) (ρ : R5) (r : ℕ) : Bool :=
  decide (∃ a ∈ absClause M τ kc, a.pol = false ∧ a.ρ = ρ ∧ a.s.idx = r)

theorem slot_last_iff {T k' r : ℕ} (hk' : k' < K T) (hr : r < G M) :
    k' * G M + r + 1 = numVars M T ↔ (k' + 1 = K T ∧ r + 1 = G M) := by
  unfold numVars
  constructor
  · intro h
    by_contra hne
    rcases Nat.lt_or_ge (k' + 1) (K T) with h1 | h1
    · have : k' * G M + r + 1 ≤ (k' + 1) * G M := by rw [add_mul, one_mul]; omega
      have : (k' + 1) * G M < K T * G M := Nat.mul_lt_mul_of_pos_right h1 (by omega)
      omega
    · have hk1 : k' + 1 = K T := by omega
      have : r + 1 ≠ G M := fun h' => hne ⟨hk1, h'⟩
      rw [← hk1, add_mul, one_mul] at h
      omega
  · rintro ⟨h1, h2⟩; rw [← h1, add_mul, one_mul]; omega

/-- **Every slot's three bits are local.** -/
theorem slotBits_eq (x : List Bool) (Q T : ℕ) (τ : Tpl (PVNP.CookLevin.Cell M)) {k k' r : ℕ}
    (hk : k < K T) (hk' : k' < K T) (hr : r < G M) :
    slotBits (numVars M T) (clause M x Q T τ k) (k' * G M + r) =
      [posBit M τ (kcOf x Q T k) (relOf T k k') r, negBit M τ (kcOf x Q T k) (relOf T k k') r,
        decide (k' + 1 = K T ∧ r + 1 = G M)] := by
  simp only [slotBits, posBit, negBit, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · exact decide_eq_decide.2 (mem_clause_iff M x Q T τ hk hk' hr true)
  · exact decide_eq_decide.2 (mem_clause_iff M x Q T τ hk hk' hr false)
  · exact decide_eq_decide.2 (slot_last_iff M hk' hr)

/-! ### Position of a bit in the instance -/

theorem getElem_flatMap_uniform {α β : Type} (f : α → List β) (b : ℕ) :
    ∀ (l : List α) (hl : ∀ a ∈ l, (f a).length = b) (i j : ℕ) (hi : i < l.length) (hj : j < b),
      (l.flatMap f)[i * b + j]'(by
        rw [List.length_flatMap]
        have : (l.map fun a => (f a).length) = l.map fun _ => b :=
          List.map_congr_left (fun a ha => hl a ha)
        rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
        calc i * b + j < i * b + b := by omega
          _ = (i + 1) * b := by ring
          _ ≤ l.length * b := Nat.mul_le_mul_right _ hi) = (f l[i])[j]'(by rw [hl _ (List.getElem_mem _)]; exact hj)
  | a :: l, hl, 0, j, _, hj => by
    simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
    rw [List.getElem_append_left]
  | a :: l, hl, i + 1, j, hi, hj => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    have ha : (f a).length = b := hl a (by simp)
    rw [List.getElem_append_right (by rw [ha]; nlinarith)]
    have e : (i + 1) * b + j - (f a).length = i * b + j := by rw [ha]; ring_nf; omega
    simp only [e]
    exact getElem_flatMap_uniform f b l (fun a' ha' => hl a' (by simp [ha'])) i j
      (by simp at hi; omega) hj

/-- Number of templates. -/
noncomputable abbrev nT : ℕ := (tpls (PVNP.CookLevin.Cell M)).length

theorem encClause_length (N : ℕ) (c : Clause) : (encClause N c).length = N * 3 := by
  simp [encClause, List.length_flatMap, slotBits]

/-- The instance as a triple flatMap. -/
theorem inst_flat (x : List Bool) (Q T : ℕ) :
    encDense (numVars M T) (phi M x Q T) =
      (List.range (K T)).flatMap fun k => (tpls (PVNP.CookLevin.Cell M)).flatMap fun τ =>
        encClause (numVars M T) (clause M x Q T τ k) := by
  simp only [encDense, phi, List.flatMap_assoc, List.flatMap_map]

theorem inst_length (x : List Bool) (Q T : ℕ) :
    (encDense (numVars M T) (phi M x Q T)).length = K T * (nT M * (numVars M T * 3)) := by
  rw [inst_flat]
  simp only [List.length_flatMap, encClause_length, List.map_const', List.sum_replicate,
    List.length_range, smul_eq_mul]

/-- **The bit at position `((k·nT + τ)·N + v)·3 + i`.** -/
theorem inst_getElem (x : List Bool) (Q T : ℕ) {k τ v i : ℕ} (hk : k < K T) (hτ : τ < nT M)
    (hv : v < numVars M T) (hi : i < 3) :
    (encDense (numVars M T) (phi M x Q T))[((k * nT M + τ) * numVars M T + v) * 3 + i]'(by
        rw [inst_length]
        have h1 : (k * nT M + τ) * numVars M T + v < (k + 1) * nT M * numVars M T := by
          have : (k * nT M + τ) * numVars M T + v < (k * nT M + τ + 1) * numVars M T := by
            rw [show (k * nT M + τ + 1) * numVars M T = (k * nT M + τ) * numVars M T +
              numVars M T by ring]; omega
          calc _ < (k * nT M + τ + 1) * numVars M T := this
            _ ≤ (k * nT M + nT M) * numVars M T := Nat.mul_le_mul_right _ (by omega)
            _ = (k + 1) * nT M * numVars M T := by ring
        have h2 : (k + 1) * nT M * numVars M T ≤ K T * nT M * numVars M T :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk)
        calc ((k * nT M + τ) * numVars M T + v) * 3 + i
            < ((k * nT M + τ) * numVars M T + v + 1) * 3 := by omega
          _ ≤ (K T * nT M * numVars M T) * 3 := Nat.mul_le_mul_right _ (by omega)
          _ = K T * (nT M * (numVars M T * 3)) := by ring) =
      (slotBits (numVars M T) (clause M x Q T (tpls (PVNP.CookLevin.Cell M))[τ] k) v)[i]'(by
        simpa [slotBits] using hi) := by
  have e1 : ((k * nT M + τ) * numVars M T + v) * 3 + i =
      k * (nT M * (numVars M T * 3)) + (τ * (numVars M T * 3) + (v * 3 + i)) := by ring
  simp only [inst_flat]
  simp only [e1]
  rw [getElem_flatMap_uniform _ (nT M * (numVars M T * 3)) (List.range (K T))
    (fun k _ => by simp [List.length_flatMap, encClause_length, List.map_const', List.sum_replicate])
    k _ (by simpa using hk) (by
      have : v * 3 + i < numVars M T * 3 := by omega
      calc τ * (numVars M T * 3) + (v * 3 + i) < τ * (numVars M T * 3) + numVars M T * 3 := by omega
        _ = (τ + 1) * (numVars M T * 3) := by ring
        _ ≤ nT M * (numVars M T * 3) := Nat.mul_le_mul_right _ hτ)]
  simp only [List.getElem_range]
  rw [getElem_flatMap_uniform _ (numVars M T * 3) _ (fun τ _ => encClause_length _ _) τ _ hτ
    (by omega)]
  simp only [encClause]
  rw [getElem_flatMap_uniform _ 3 (List.range (numVars M T)) (fun _ _ => rfl) v i
    (by simpa using hv) hi]
  simp only [List.getElem_range]

end Bits

end PVNP.CookLevin.Gen
