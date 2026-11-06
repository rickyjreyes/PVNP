import PVNP.TMCircuit

/-!
# Phase X: non-uniform Cook–Levin for `SAT_dense`

**Theorem (`NP_TM_subset_Ppoly_of_SAT`).** If `SAT_dense` has polynomial-size circuits, then every
language in `NP_TM` has polynomial-size circuits. Consequently (`satLowerBound_of_NP_not_Ppoly`):
if **any** language in `NP_TM` requires superpolynomial circuits, then `SATLowerBound`, and hence
`P_TM ≠ NP_TM`.

**Proof.**
1. *Verifier circuits* (`verCirc`). For `L ∈ NP_TM` with a polynomial-time verifier machine `M_V`
   (time `p`) and witness bound `q`, fix `n` and `Q = q(n)`. For each witness length `ℓ ≤ Q`, the
   tableau circuit of `M_V` on `pair x w` (`TMCircuit.tableau`) reads `x` from inputs `0, …, n−1`
   and `w` from a private block of inputs. The OR of these `Q+1` circuits (`orComb`) accepts some
   extension of `x` exactly when `x ∈ L` (`verCirc_iff`). This is the statement that Part I §11.1
   attributes to Cook–Levin (`x ∈ L ⟺ ∃ w, C(x, w) = 1` with `C` of polynomial size), here proved
   for the repository's machines.
2. *Tseitin transformation* (`Circuit.tseitin`). One CNF variable per register and per input
   bit. Each gate becomes at most three clauses forcing its register to the gate's value. The
   input bits of `x` are fixed by unit clauses (`Circuit.units`). The CNF is satisfiable iff some
   extension of `x` makes the circuit output `true` (`tseitin_sat_iff`).
3. *Projection.* In the dense encoding (`SATV.encDense`), only the unit clauses depend on `x`, and
   every bit of their encoding is a constant, `xᵢ` or `¬xᵢ` (`encDense_units`). Polynomial-size
   circuits are closed under such projections (`Ppoly_of_projection`).

All constructions are explicit, and every size bound is an explicit polynomial.
-/

namespace PVNP.CircuitCookLevin

open PVNP.Discrete PVNP.Discrete.TM PVNP.Discrete.SATV PVNP.PartI PVNP.Circuits PVNP.TMCircuit

/-! ### OR-combination of finitely many circuits -/

section OrComb

variable {α : Type} (C : ℕ → Circuit α) (Q R : ℕ)

/-- Gates of the OR-combination of the circuits `C 0, …, C Q`. -/
def orGate : (ℕ × α) ⊕ ℕ → Gate ((ℕ × α) ⊕ ℕ)
  | .inl (ℓ, a) => if ℓ ≤ Q then ((C ℓ).gate a).map (fun b => .inl (ℓ, b)) else .const false
  | .inr 0 => .const false
  | .inr (k + 1) => if k ≤ Q then .or (.inr k) (.inl (k, (C k).out)) else .const false

/-- Ranks of the OR-combination. -/
def orRank : (ℕ × α) ⊕ ℕ → ℕ
  | .inl (ℓ, a) => (C ℓ).rank a
  | .inr k => R + k

theorem orGate_wf (hR : ∀ ℓ ≤ Q, (C ℓ).rank (C ℓ).out < R) : ∀ a, ∀ b ∈ (orGate C Q a).args, orRank C R b < orRank C R a := by
  intro a b hb
  rcases a with ⟨ℓ, a⟩ | k
  · simp only [orGate] at hb
    split_ifs at hb with h
    · rw [Gate.args_map, List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      exact (C ℓ).wf a b' hb'
    · simp [Gate.args] at hb
  · cases k with
    | zero => simp [orGate, Gate.args] at hb
    | succ k =>
      simp only [orGate] at hb
      split_ifs at hb with h
      · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · show R + k < R + (k + 1); omega
        · have := hR k h
          show (C k).rank (C k).out < R + (k + 1); omega
      · simp [Gate.args] at hb

/-- Registers of the OR-combination. -/
def orRegs : List ((ℕ × α) ⊕ ℕ) :=
  (List.range (Q + 1)).flatMap (fun ℓ => (C ℓ).regs.map fun a => .inl (ℓ, a)) ++
    (List.range (Q + 2)).map .inr

theorem orGate_triv : ∀ a, a ∉ orRegs C Q → orGate C Q a = .const false := by
  intro a ha
  simp only [orRegs, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map,
    not_or, not_exists, not_and] at ha
  rcases a with ⟨ℓ, a⟩ | k
  · by_cases hℓ : ℓ ≤ Q
    · have : a ∉ (C ℓ).regs := fun h => ha.1 ℓ (by omega) a h rfl
      simp only [orGate, if_pos hℓ, (C ℓ).triv a this]
      rfl
    · simp [orGate, hℓ]
  · cases k with
    | zero => rfl
    | succ k =>
      have : ¬ k ≤ Q := fun h => ha.2 (k + 1) (by omega) rfl
      simp [orGate, this]

variable (hR : ∀ ℓ ≤ Q, (C ℓ).rank (C ℓ).out < R)

/-- **OR-combination** of `C 0, …, C Q`: outputs `true` iff some `C ℓ` does. -/
def orComb : Circuit ((ℕ × α) ⊕ ℕ) where
  gate := orGate C Q
  rank := orRank C R
  wf := orGate_wf C Q R hR
  regs := orRegs C Q
  triv := orGate_triv C Q
  out := .inr (Q + 1)

theorem orComb_val_inl {ℓ : ℕ} (hℓ : ℓ ≤ Q) (x : ℕ → Bool) (a : α) :
    (orComb C Q R hR).val x (.inl (ℓ, a)) = (C ℓ).val x a :=
  Circuit.val_embed (C ℓ) (orComb C Q R hR) (fun b => .inl (ℓ, b))
    (fun b => by simp only [orComb, orGate, if_pos hℓ]) x a

theorem orComb_val_inr (x : ℕ → Bool) : ∀ k ≤ Q + 1,
    (orComb C Q R hR).val x (.inr k) = decide (∃ ℓ < k, (C ℓ).eval x = true)
  | 0, _ => by
    rw [Circuit.val_eq]
    show (orGate C Q (.inr 0)).eval _ x = _
    simp [orGate, Gate.eval]
  | k + 1, hk => by
    rw [Circuit.val_eq]
    show (orGate C Q (.inr (k + 1))).eval _ x = _
    simp only [orGate, if_pos (show k ≤ Q by omega), Gate.eval]
    rw [orComb_val_inr x k (by omega), orComb_val_inl C Q R hR (by omega)]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨ℓ, hℓ, h⟩ | h)
      · exact ⟨ℓ, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨ℓ, hℓ, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hℓ with hlt | rfl
      · exact Or.inl ⟨ℓ, hlt, h⟩
      · exact Or.inr h

theorem orComb_eval (x : ℕ → Bool) :
    (orComb C Q R hR).eval x = true ↔ ∃ ℓ ≤ Q, (C ℓ).eval x = true := by
  show (orComb C Q R hR).val x (.inr (Q + 1)) = true ↔ _
  rw [orComb_val_inr C Q R hR x (Q + 1) le_rfl, decide_eq_true_eq]
  constructor
  · rintro ⟨ℓ, hℓ, h⟩; exact ⟨ℓ, by omega, h⟩
  · rintro ⟨ℓ, hℓ, h⟩; exact ⟨ℓ, by omega, h⟩

theorem orComb_size :
    (orComb C Q R hR).size = ((List.range (Q + 1)).map fun ℓ => (C ℓ).size).sum + (Q + 2) := by
  simp [orComb, Circuit.size, orRegs, List.length_flatMap]

end OrComb


/-! ### The Tseitin transformation -/

section Tseitin

variable {α : Type} [DecidableEq α] (C : Circuit α)

/-- CNF variable of a register: its position in `regs` (the dummy variable `|regs|` for registers
outside the list, whose gates are the constant `false`). -/
def ix (a : α) : ℕ := C.regs.idxOf a

/-- CNF variable of input bit `i`. -/
def inV (i : ℕ) : ℕ := C.regs.length + 1 + i

/-- The clauses of one gate: they force the register's variable to the gate's value. -/
def gateCl (a : α) : Formula :=
  match C.gate a with
  | .const b => [[(ix C a, b)]]
  | .inp i => [[(ix C a, false), (inV C i, true)], [(ix C a, true), (inV C i, false)]]
  | .not b => [[(ix C a, true), (ix C b, true)], [(ix C a, false), (ix C b, false)]]
  | .and b c => [[(ix C a, false), (ix C b, true)], [(ix C a, false), (ix C c, true)],
      [(ix C a, true), (ix C b, false), (ix C c, false)]]
  | .or b c => [[(ix C a, true), (ix C b, false)], [(ix C a, true), (ix C c, false)],
      [(ix C a, false), (ix C b, true), (ix C c, true)]]

/-- **The Tseitin CNF** (input-independent part): the dummy variable is false, every listed
register equals its gate, and the output is true. -/
def tseitin : Formula :=
  [[(C.regs.length, false)]] ++ C.regs.flatMap (gateCl C) ++ [[(ix C C.out, true)]]

/-- Unit clauses fixing the input bits `0, …, n−1` to `x`. -/
def units (n : ℕ) (x : List Bool) : Formula :=
  (List.range n).map fun i => [(inV C i, x.getD i false)]

theorem gateCl_sat (σ : ℕ → Bool) (a : α) :
    (∀ cl ∈ gateCl C a, evalClause σ cl = true) ↔
      σ (ix C a) = (C.gate a).eval (fun b => σ (ix C b)) (fun i => σ (inV C i)) := by
  unfold gateCl
  rcases C.gate a with b | i | b | ⟨b, c⟩ | ⟨b, c⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      evalClause, evalLiteral, literalTrue, Gate.eval] <;>
    cases σ (ix C a) <;> try cases b
  all_goals first
    | (cases σ (inV C i) <;> simp)
    | (cases σ (ix C b) <;> cases σ (ix C c) <;> simp)
    | (cases σ (ix C b) <;> simp)
    | simp

theorem ix_lt {a : α} (ha : a ∈ C.regs) : ix C a < C.regs.length := List.idxOf_lt_length_iff.2 ha

theorem ix_of_not_mem {a : α} (ha : a ∉ C.regs) : ix C a = C.regs.length :=
  List.idxOf_eq_length_iff.2 ha

theorem ix_le (a : α) : ix C a ≤ C.regs.length := List.idxOf_le_length

omit [DecidableEq α] in
theorem val_of_not_mem (X : ℕ → Bool) {a : α} (ha : a ∉ C.regs) : C.val X a = false :=
  C.val_const X (C.triv a ha)

/-- The input assignment extending `x` by `W`. -/
def merge (n : ℕ) (x : List Bool) (W : ℕ → Bool) : ℕ → Bool :=
  fun i => if i < n then x.getD i false else W i

/-- **Tseitin correctness.** The CNF with the input bits `0, …, n−1` fixed to `x` is satisfiable
iff some extension of `x` makes the circuit output `true`. -/
theorem tseitin_sat_iff (n : ℕ) (x : List Bool) :
    satisfiable (tseitin C ++ units C n x) ↔ ∃ W : ℕ → Bool, C.eval (merge n x W) = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [CrossingSAT.evalFormula_iff] at hσ
    have hall : ∀ c ∈ tseitin C ++ units C n x, evalClause σ c = true := hσ
    have hdummy : σ C.regs.length = false := by
      have := hall [(C.regs.length, false)] (by simp [tseitin])
      simpa [evalClause, evalLiteral, literalTrue] using this
    have hgate : ∀ a ∈ C.regs, ∀ cl ∈ gateCl C a, evalClause σ cl = true := fun a ha cl hcl =>
      hall cl (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, hcl⟩))))
    have hout : σ (ix C C.out) = true := by
      have := hall [(ix C C.out, true)] (by simp [tseitin])
      simpa [evalClause, evalLiteral, literalTrue] using this
    have hunit : ∀ i < n, σ (inV C i) = x.getD i false := by
      intro i hi
      have := hall [(inV C i, x.getD i false)]
        (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
      simp only [evalClause, evalLiteral, literalTrue, Bool.or_false, beq_iff_eq] at this
      exact this
    set X : ℕ → Bool := fun i => σ (inV C i)
    have key : ∀ a, σ (ix C a) = C.val X a := by
      intro a
      induction h : C.rank a using Nat.strong_induction_on generalizing a with
      | _ r ih =>
        by_cases ha : a ∈ C.regs
        · rw [(gateCl_sat C σ a).1 (hgate a ha), C.val_eq]
          apply Gate.eval_congr
          intro b hb
          exact ih (C.rank b) (h ▸ C.wf a b hb) b rfl
        · rw [ix_of_not_mem C ha, hdummy, val_of_not_mem C X ha]
    refine ⟨X, ?_⟩
    have hX : merge n x X = X := by
      funext i
      simp only [merge]
      split_ifs with hi
      · exact (hunit i hi).symm
      · rfl
    rw [hX]
    show C.val X C.out = true
    rw [← key]; exact hout
  · rintro ⟨W, hW⟩
    set X := merge n x W
    let σ : ℕ → Bool := fun v =>
      if h : v < C.regs.length then C.val X (C.regs[v]) else if v = C.regs.length then false
      else X (v - (C.regs.length + 1))
    have hσix : ∀ a, σ (ix C a) = C.val X a := by
      intro a
      by_cases ha : a ∈ C.regs
      · have hlt := ix_lt C ha
        simp only [σ, dif_pos hlt]
        congr 1
        exact List.getElem_idxOf hlt
      · simp only [σ, ix_of_not_mem C ha, lt_irrefl, dif_neg (not_false), if_true]
        exact (val_of_not_mem C X ha).symm
    have hσin : ∀ i, σ (inV C i) = X i := by
      intro i
      simp only [σ, inV]
      rw [dif_neg (by omega), if_neg (by omega)]
      congr 1; omega
    refine ⟨σ, (CrossingSAT.evalFormula_iff σ _).2 ?_⟩
    intro c hc
    simp only [tseitin, units, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_map, List.mem_range] at hc
    rcases hc with ((rfl | ⟨a, ha, hcl⟩) | rfl) | ⟨i, hi, rfl⟩
    · have : σ C.regs.length = false := by simp [σ]
      simp [evalClause, evalLiteral, literalTrue, this]
    · refine (gateCl_sat C σ a).2 ?_ c hcl
      have h1 : (fun b => σ (ix C b)) = C.val X := funext hσix
      have h2 : (fun i => σ (inV C i)) = X := funext hσin
      rw [h1, h2, hσix, C.val_eq]
    · have : σ (ix C C.out) = true := by rw [hσix]; exact hW
      simp [evalClause, evalLiteral, literalTrue, this]
    · have hv : σ (inV C i) = x.getD i false := by
        rw [hσin]; simp only [X, merge, if_pos hi]
      simp only [evalClause, evalLiteral, literalTrue, Bool.or_false, hv, beq_self_eq_true]

/-- Every variable of a gate's clauses is a register variable or, for an input gate, the input's
variable. -/
theorem gateCl_vars (a : α) : ∀ cl ∈ gateCl C a, ∀ l ∈ cl,
    (∃ b, l.1 = ix C b) ∨ (∃ i, C.gate a = .inp i ∧ l.1 = inV C i) := by
  intro cl hcl l hl
  unfold gateCl at hcl
  rcases hg : C.gate a with b | i | b | ⟨b, c⟩ | ⟨b, c⟩ <;> rw [hg] at hcl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  · subst hcl; simp only [List.mem_singleton] at hl; subst hl; exact Or.inl ⟨a, rfl⟩
  · rcases hcl with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
      rcases hl with rfl | rfl
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨i, rfl, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨i, rfl, rfl⟩
  · rcases hcl with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
      rcases hl with rfl | rfl
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inl ⟨b, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inl ⟨b, rfl⟩
  · rcases hcl with rfl | rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    · rcases hl with rfl | rfl
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inl ⟨b, rfl⟩
    · rcases hl with rfl | rfl
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inl ⟨c, rfl⟩
    · rcases hl with rfl | rfl | rfl
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inl ⟨b, rfl⟩
      · exact Or.inl ⟨c, rfl⟩
  · rcases hcl with rfl | rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    · rcases hl with rfl | rfl
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inl ⟨b, rfl⟩
    · rcases hl with rfl | rfl
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inl ⟨c, rfl⟩
    · rcases hl with rfl | rfl | rfl
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inl ⟨b, rfl⟩
      · exact Or.inl ⟨c, rfl⟩

/-- All variables of the Tseitin CNF are below `|regs| + 1 + Imax` when every input read by a
listed register, and every fixed input, is below `Imax`. -/
theorem tseitin_vars (Imax n : ℕ) (hn : n ≤ Imax)
    (hinp : ∀ a ∈ C.regs, ∀ i, C.gate a = .inp i → i < Imax) (x : List Bool) :
    ∀ c ∈ tseitin C ++ units C n x, ∀ l ∈ c, l.1 < C.regs.length + 1 + Imax := by
  have hix : ∀ a, ix C a < C.regs.length + 1 + Imax := fun a => by have := ix_le C a; omega
  intro c hc l hl
  simp only [tseitin, units, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_map, List.mem_range] at hc
  rcases hc with ((rfl | ⟨a, ha, hcl⟩) | rfl) | ⟨i, hi, rfl⟩
  · simp only [List.mem_singleton] at hl; subst hl; simp only; omega
  · rcases gateCl_vars C a c hcl l hl with ⟨b, hb⟩ | ⟨i, hg, hi⟩
    · rw [hb]; exact hix b
    · rw [hi]; have := hinp a ha i hg; simp only [inV]; omega
  · simp only [List.mem_singleton] at hl; subst hl; exact hix _
  · simp only [List.mem_singleton] at hl; subst hl; simp only [inV]; omega

theorem length_tseitin : (tseitin C).length ≤ 3 * C.regs.length + 2 := by
  have h : ∀ a, (gateCl C a).length ≤ 3 := by
    intro a; unfold gateCl; rcases C.gate a with b | i | b | ⟨b, c⟩ | ⟨b, c⟩ <;> simp
  simp only [tseitin, List.length_append, List.length_cons, List.length_nil, List.length_flatMap]
  have : (C.regs.map fun a => (gateCl C a).length).sum ≤ (C.regs.map fun _ => 3).sum :=
    List.sum_le_sum (fun a _ => h a)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  omega

end Tseitin

/-! ### Projections and the closure of `Ppoly` -/

/-- A projection bit: a constant, an input bit or the negation of an input bit. -/
inductive Proj
  | c (b : Bool)
  | pos (i : ℕ)
  | neg (i : ℕ)

namespace Proj

/-- The value of a projection bit. -/
def eval (x : ℕ → Bool) : Proj → Bool
  | c b => b
  | pos i => x i
  | neg i => !(x i)

/-- The input index of a projection bit is below `n`. -/
def ok (n : ℕ) : Proj → Prop
  | c _ => True
  | pos i => i < n
  | neg i => i < n

end Proj

/-- Projection form of the dense encoding of the unit clause `[(v, xᵢ)]`. -/
def unitProj (V v i : ℕ) : List Proj :=
  (List.range V).flatMap fun j =>
    [if j = v then .pos i else .c false, if j = v then .neg i else .c false, .c (decide (j + 1 = V))]

theorem encClause_unit (V v i : ℕ) (xf : ℕ → Bool) :
    encClause V [(v, xf i)] = (unitProj V v i).map (Proj.eval xf) := by
  simp only [encClause, unitProj, List.map_flatMap]
  congr 1
  funext j
  simp only [slotBits, List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq]
  by_cases hj : j = v
  · subst hj; cases xf j <;> cases h : xf i <;> simp [Proj.eval, h]
  · simp [hj, Proj.eval]

/-- Projection form of the unit clauses of the input bits `0, …, n−1`. -/
def unitsProj (n V : ℕ) (v : ℕ → ℕ) : List Proj :=
  (List.range n).flatMap fun i => unitProj V (v i) i

theorem unitsProj_ok (n V : ℕ) (v : ℕ → ℕ) : ∀ p ∈ unitsProj n V v, p.ok n := by
  intro p hp
  simp only [unitsProj, unitProj, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  obtain ⟨i, hi, j, -, hp⟩ := hp
  rcases hp with rfl | rfl | rfl
  · split_ifs <;> simp [Proj.ok, hi]
  · split_ifs <;> simp [Proj.ok, hi]
  · simp [Proj.ok]

theorem length_unitsProj (n V : ℕ) (v : ℕ → ℕ) : (unitsProj n V v).length = n * (3 * V) := by
  simp only [unitsProj, unitProj, List.length_flatMap, List.length_cons, List.length_nil,
    List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

section Proj

variable {α : Type} [DecidableEq α] (C : Circuit α)

omit [DecidableEq α] in
theorem encDense_units (n V : ℕ) (x : List Bool) :
    encDense V (units C n x) = (unitsProj n V (inV C)).map (Proj.eval fun i => x.getD i false) := by
  simp only [encDense, units, unitsProj, List.flatMap_map, List.map_flatMap]
  congr 1
  funext i
  exact encClause_unit V (inV C i) i (fun i => x.getD i false)

/-- The full projection: constants for the input-independent part, then the unit clauses. -/
def fullProj (n V : ℕ) : List Proj :=
  (encDense V (tseitin C)).map Proj.c ++ unitsProj n V (inV C)

theorem encDense_full (n V : ℕ) (x : List Bool) :
    encDense V (tseitin C ++ units C n x) =
      (fullProj C n V).map (Proj.eval fun i => x.getD i false) := by
  rw [CrossingSAT.encDense_append, encDense_units, fullProj, List.map_append, List.map_map]
  congr 1
  simp [Function.comp_def, Proj.eval]

theorem fullProj_ok (n V : ℕ) : ∀ p ∈ fullProj C n V, p.ok n := by
  intro p hp
  simp only [fullProj, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨b, -, rfl⟩ | hp
  · trivial
  · exact unitsProj_ok n V _ p hp

theorem length_fullProj (n V : ℕ) :
    (fullProj C n V).length = 3 * V * (tseitin C).length + n * (3 * V) := by
  rw [fullProj, List.length_append, List.length_map, CrossingSAT.length_encDense,
    length_unitsProj]

end Proj

/-! ### `Ppoly` is closed under projection reductions -/

section ProjCirc

variable {β : Type} (D : Circuit β) (πn : List Proj) (n : ℕ)

/-- The gate reading a projection bit. -/
def projGate : Proj → Gate (β ⊕ ℕ)
  | .c b => .const b
  | .pos i => .inp i
  | .neg i => .not (.inr i)

/-- Gates of `D` composed with the projection `πn`. -/
def pcGate : β ⊕ ℕ → Gate (β ⊕ ℕ)
  | .inl b =>
    match D.gate b with
    | .inp k => projGate (πn.getD k (.c false))
    | .const b0 => .const b0
    | .not a => .not (.inl a)
    | .and a a' => .and (.inl a) (.inl a')
    | .or a a' => .or (.inl a) (.inl a')
  | .inr i => if i < n then .inp i else .const false

/-- Ranks: inputs `inr i` at rank `0`, the registers of `D` one above their rank in `D`. -/
def pcRank : β ⊕ ℕ → ℕ
  | .inl b => D.rank b + 1
  | .inr _ => 0

theorem pcGate_wf : ∀ a, ∀ b ∈ (pcGate D πn n a).args, pcRank D b < pcRank D a := by
  intro a b hb
  rcases a with a | i
  · simp only [pcGate] at hb
    have hwf := D.wf a
    rcases hg : D.gate a with b0 | k | a1 | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [hg] at hb hwf <;>
      dsimp only at hb
    · simp [Gate.args] at hb
    · cases hp : πn.getD k (.c false) <;> rw [hp] at hb <;>
        simp_all [projGate, Gate.args, pcRank]
    · simp only [Gate.args, List.mem_singleton] at hb hwf
      subst hb; simp only [pcRank]; have := hwf a1 rfl; omega
    · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb hwf
      rcases hb with rfl | rfl
      · have := hwf a1 (Or.inl rfl); simp only [pcRank]; omega
      · have := hwf a2 (Or.inr rfl); simp only [pcRank]; omega
    · simp only [Gate.args, List.mem_cons, List.not_mem_nil, or_false] at hb hwf
      rcases hb with rfl | rfl
      · have := hwf a1 (Or.inl rfl); simp only [pcRank]; omega
      · have := hwf a2 (Or.inr rfl); simp only [pcRank]; omega
  · simp only [pcGate] at hb
    split_ifs at hb <;> simp [Gate.args] at hb

/-- Registers of the composed circuit. -/
def pcRegs : List (β ⊕ ℕ) := D.regs.map .inl ++ (List.range n).map .inr

theorem pcGate_triv : ∀ a, a ∉ pcRegs D n → pcGate D πn n a = .const false := by
  intro a ha
  simp only [pcRegs, List.mem_append, List.mem_map, List.mem_range, not_or, not_exists,
    not_and] at ha
  rcases a with a | i
  · have : a ∉ D.regs := fun h => ha.1 a h rfl
    simp only [pcGate, D.triv a this]
  · have : ¬ i < n := fun h => ha.2 i h rfl
    simp [pcGate, this]

/-- **`D` composed with the projection `πn`** on inputs of length `n`. -/
def projCirc : Circuit (β ⊕ ℕ) where
  gate := pcGate D πn n
  rank := pcRank D
  wf := pcGate_wf D πn n
  regs := pcRegs D n
  triv := pcGate_triv D πn n
  out := .inl D.out

theorem projCirc_size : (projCirc D πn n).size = D.size + n := by
  simp [projCirc, Circuit.size, pcRegs]

theorem projCirc_val (hok : ∀ p ∈ πn, p.ok n) (X : ℕ → Bool) :
    ∀ b, (projCirc D πn n).val X (.inl b) = D.val (fun k => (πn.getD k (.c false)).eval X) b := by
  intro b
  induction h : D.rank b using Nat.strong_induction_on generalizing b with
  | _ r ih =>
    have hwf := D.wf b
    rw [Circuit.val_eq, D.val_eq]
    show (pcGate D πn n (.inl b)).eval _ X = _
    simp only [pcGate]
    rcases hg : D.gate b with b0 | k | a1 | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [hg] at hwf <;> dsimp only
    · rfl
    · simp only [Gate.eval]
      have hpok : (πn.getD k (.c false)).ok n := by
        by_cases hk : k < πn.length
        · rw [List.getD_eq_getElem _ _ hk]; exact hok _ (List.getElem_mem hk)
        · rw [List.getD_eq_default _ _ (by omega)]; trivial
      cases hp : πn.getD k (.c false) with
      | c b0 => rfl
      | pos i => rfl
      | neg i =>
        rw [hp] at hpok
        simp only [projGate, Proj.eval]
        rw [Circuit.val_eq]
        congr 1
        show (pcGate D πn n (.inr i)).eval _ X = X i
        have hi : i < n := hpok
        simp only [pcGate, if_pos hi]
        rfl
    · simp only [Gate.eval]
      rw [ih (D.rank a1) (h ▸ hwf a1 (by simp [Gate.args])) a1 rfl]
    · simp only [Gate.eval]
      rw [ih (D.rank a1) (h ▸ hwf a1 (by simp [Gate.args])) a1 rfl,
        ih (D.rank a2) (h ▸ hwf a2 (by simp [Gate.args])) a2 rfl]
    · simp only [Gate.eval]
      rw [ih (D.rank a1) (h ▸ hwf a1 (by simp [Gate.args])) a1 rfl,
        ih (D.rank a2) (h ▸ hwf a2 (by simp [Gate.args])) a2 rfl]

theorem projCirc_eval (hok : ∀ p ∈ πn, p.ok n) (x : List Bool) :
    (projCirc D πn n).eval (fun i => x.getD i false) =
      D.eval (fun k => (πn.map (Proj.eval fun i => x.getD i false)).getD k false) := by
  show (projCirc D πn n).val _ (.inl D.out) = _
  rw [projCirc_val D πn n hok]
  congr 1
  funext k
  exact (List.getD_map πn (Proj.c false) (Proj.eval fun i => x.getD i false)).symm

end ProjCirc

/-- **Closure of `Ppoly` under projection reductions.** If `L'` has polynomial-size circuits and
membership of `x` in `L` is membership in `L'` of a projection of `x` of polynomial length, then
`L` has polynomial-size circuits. -/
theorem Ppoly_of_projection {L L' : Set (List Bool)} (hL' : L' ∈ Ppoly) (π : ℕ → List Proj)
    (hok : ∀ n, ∀ p ∈ π n, p.ok n) (Mp : Polynomial ℕ) (hM : ∀ n, (π n).length ≤ Mp.eval n)
    (hred : ∀ x : List Bool, x ∈ L ↔ (π x.length).map (Proj.eval fun i => x.getD i false) ∈ L') :
    L ∈ Ppoly := by
  obtain ⟨s, hs⟩ := hL'
  refine ⟨s.comp Mp + Polynomial.X, fun n => ?_⟩
  obtain ⟨β, D, hDs, hD⟩ := hs (π n).length
  refine ⟨β ⊕ ℕ, projCirc D (π n) n, ?_, ?_⟩
  · rw [projCirc_size]
    simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X]
    have := poly_eval_mono s (hM n)
    omega
  · intro x hx
    rw [projCirc_eval D (π n) n (hok n), hD _ (by simp), hred, hx]

/-! ### Verifier circuits: the Cook–Levin embedding of `NP_TM` -/

theorem list_eq_of_getD {l l' : List Bool} (hl : l.length = l'.length)
    (h : ∀ j < l.length, l.getD j false = l'.getD j false) : l = l' := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem Gate.map_eq_inp {α β : Type} {f : α → β} {g : Gate α} {i : ℕ} (h : g.map f = .inp i) :
    g = .inp i := by
  cases g <;> simp_all [Gate.map]

section Verifier

variable (MV : TM) (p : Polynomial ℕ) (n Q : ℕ)

/-- Sources of the verifier input `pair x w` with `|x| = n`: tags, `x` from the inputs
`0, …, n−1`, the terminator, and the witness from the inputs `n, n+1, …`. -/
def vsrc (j : ℕ) : Src :=
  if j < 2 * n then (if j % 2 = 0 then .const true else .inp (j / 2))
  else if j = 2 * n then .const false
  else .inp (n + (j - (2 * n + 1)))

/-- The tableau circuit of the verifier for witness length `ℓ`. -/
noncomputable def vcirc (ℓ : ℕ) : Circuit (WN MV) :=
  tableau MV (p.eval (2 * n + 1 + ℓ)) (2 * n + 1 + ℓ) (vsrc n)

/-- A rank above every output rank. -/
noncomputable def vR : ℕ :=
  (Finset.range (Q + 1)).sup (fun ℓ => (vcirc MV p n ℓ).rank (vcirc MV p n ℓ).out) + 1

theorem vR_spec : ∀ ℓ ≤ Q, (vcirc MV p n ℓ).rank (vcirc MV p n ℓ).out < vR MV p n Q := by
  intro ℓ hℓ
  unfold vR
  exact Nat.lt_succ_of_le (Finset.le_sup (s := Finset.range (Q + 1))
    (f := fun ℓ => (vcirc MV p n ℓ).rank (vcirc MV p n ℓ).out)
    (Finset.mem_range.2 (by omega : ℓ < Q + 1)))

/-- **The verifier circuit**: the OR over witness lengths `ℓ ≤ Q` of the verifier tableaux. -/
noncomputable def verCirc : Circuit ((ℕ × WN MV) ⊕ ℕ) :=
  orComb (vcirc MV p n) Q (vR MV p n Q) (vR_spec MV p n Q)

/-- The string read from the inputs `0, …, n−1`. -/
def xsOf (X : ℕ → Bool) : List Bool := (List.range n).map X

/-- The witness of length `ℓ` read from the inputs `n, …, n+ℓ−1`. -/
def witOf (X : ℕ → Bool) (ℓ : ℕ) : List Bool := (List.range ℓ).map fun j => X (n + j)

theorem inputOf_vsrc (X : ℕ → Bool) (ℓ : ℕ) :
    inputOf (2 * n + 1 + ℓ) (vsrc n) X = pair (xsOf n X) (witOf n X ℓ) := by
  apply list_eq_of_getD
  · simp [length_inputOf, pair_length, xsOf, witOf]
  · intro j hj
    rw [length_inputOf] at hj
    rw [getD_inputOf _ _ X hj]
    simp only [vsrc]
    split_ifs with h1 h2 h3
    · obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i := ⟨j / 2, by omega⟩
      rw [TM.getD_pair_even _ _ i (by simp [xsOf]; omega)]; rfl
    · obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + 1 := ⟨j / 2, by omega⟩
      rw [TM.getD_pair_odd _ _ i (by simp [xsOf]; omega)]
      have hi : i < n := by omega
      simp [Src.eval, xsOf, hi, show (2 * i + 1) / 2 = i by omega]
    · subst h3
      have := SATV.getD_pair_term (xsOf n X) (witOf n X ℓ)
      rw [show (xsOf n X).length = n by simp [xsOf]] at this
      rw [this]; rfl
    · obtain ⟨t, rfl⟩ : ∃ t, j = 2 * n + 1 + t := ⟨j - (2 * n + 1), by omega⟩
      have := TM.getD_pair_witness (xsOf n X) (witOf n X ℓ) t
      rw [show (xsOf n X).length = n by simp [xsOf]] at this
      rw [this]
      have ht : t < ℓ := by omega
      simp [Src.eval, witOf, ht, show 2 * n + 1 + t - (2 * n + 1) = t by omega]

theorem verCirc_eval {V : Set (List Bool)} (hV : MV.Decides V fun m => p.eval m) (X : ℕ → Bool) :
    (verCirc MV p n Q).eval X = true ↔ ∃ ℓ ≤ Q, pair (xsOf n X) (witOf n X ℓ) ∈ V := by
  rw [verCirc, orComb_eval]
  apply exists_congr; intro ℓ; apply and_congr_right; intro _
  rw [vcirc, tableau_eval, inputOf_vsrc]
  have hlen : (pair (xsOf n X) (witOf n X ℓ)).length = 2 * n + 1 + ℓ := by
    simp [pair_length, xsOf, witOf]
  rw [← hlen]
  exact firstAnswer_true_iff hV _

/-- **Cook–Levin embedding (non-uniform).** `x ∈ L` iff some extension of `x` makes the
verifier circuit output `true`. -/
theorem mem_iff_verCirc {L V : Set (List Bool)} {q : Polynomial ℕ}
    (hV : MV.Decides V fun m => p.eval m)
    (hL : ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ pair x w ∈ V)
    (x : List Bool) (hx : x.length = n) :
    x ∈ L ↔ ∃ W : ℕ → Bool, (verCirc MV p n (q.eval n)).eval (merge n x W) = true := by
  have hxs : ∀ W, xsOf n (merge n x W) = x := by
    intro W
    apply list_eq_of_getD (by simp [xsOf, hx])
    intro i hi
    simp only [xsOf, List.length_map, List.length_range] at hi
    simp [xsOf, merge, hi]
  rw [hL]
  constructor
  · rintro ⟨w, hw, hwV⟩
    refine ⟨fun i => w.getD (i - n) false, ?_⟩
    rw [verCirc_eval MV p n _ hV]
    refine ⟨w.length, by rw [← hx]; exact hw, ?_⟩
    have hwit : witOf n (merge n x (fun i => w.getD (i - n) false)) w.length = w := by
      apply list_eq_of_getD (by simp [witOf])
      intro j hj
      simp only [witOf, List.length_map, List.length_range] at hj
      simp [witOf, merge, hj]
    rw [hxs, hwit]; exact hwV
  · rintro ⟨W, hW⟩
    rw [verCirc_eval MV p n _ hV] at hW
    obtain ⟨ℓ, hℓ, hV'⟩ := hW
    rw [hxs] at hV'
    exact ⟨witOf n (merge n x W) ℓ, by simp [witOf]; rw [hx]; exact hℓ, hV'⟩

/-- Every input read by the verifier circuit is below `n + Q`. -/
theorem verCirc_inp : ∀ a, ∀ i, (verCirc MV p n Q).gate a = .inp i → i < n + Q := by
  intro a i h
  rcases a with ⟨ℓ, b⟩ | k
  · change orGate (vcirc MV p n) Q (.inl (ℓ, b)) = _ at h
    simp only [orGate] at h
    split_ifs at h with hℓ
    have h' := Gate.map_eq_inp h
    obtain ⟨j, hj0, hjN, hs⟩ := gate_eq_inp MV _ _ _ h'
    simp only [vsrc] at hs
    split_ifs at hs with h1 h2 h3 <;> cases hs <;> omega
  · change orGate (vcirc MV p n) Q (.inr k) = _ at h
    cases k with
    | zero => cases h
    | succ k => simp only [orGate] at h; split_ifs at h

theorem vcirc_size_le {ℓ : ℕ} (hℓ : ℓ ≤ Q) :
    (vcirc MV p n ℓ).size ≤
      (p.eval (2 * n + 1 + Q) + 1) * (2 * p.eval (2 * n + 1 + Q) + 3) * cM MV := by
  have h1 := size_tableau MV (p.eval (2 * n + 1 + ℓ)) (2 * n + 1 + ℓ) (vsrc n)
  have h2 : p.eval (2 * n + 1 + ℓ) ≤ p.eval (2 * n + 1 + Q) := poly_eval_mono p (by omega)
  refine h1.trans ?_
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))

theorem verCirc_size_le : (verCirc MV p n Q).size ≤
    (Q + 1) * ((p.eval (2 * n + 1 + Q) + 1) * (2 * p.eval (2 * n + 1 + Q) + 3) * cM MV) +
      (Q + 2) := by
  rw [verCirc, orComb_size]
  have hsum := List.sum_le_card_nsmul ((List.range (Q + 1)).map fun ℓ => (vcirc MV p n ℓ).size)
    ((p.eval (2 * n + 1 + Q) + 1) * (2 * p.eval (2 * n + 1 + Q) + 3) * cM MV) (by
      intro y hy
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hy
      exact vcirc_size_le MV p n Q (by simpa [Nat.lt_succ_iff] using hℓ))
  simp only [List.length_map, List.length_range, smul_eq_mul] at hsum
  omega

end Verifier

/-! ### The main theorem -/

/-- **Non-uniform Cook–Levin for `SAT_dense`.** If `SAT_dense` has polynomial-size circuits, then
so does every language in `NP_TM`. -/
theorem NP_TM_subset_Ppoly_of_SAT (hS : SAT_dense ∈ Ppoly) : NP_TM ⊆ Ppoly := by
  rintro L ⟨V, ⟨MV, p, hV⟩, q, hL⟩
  let Cn : ℕ → Circuit ((ℕ × WN MV) ⊕ ℕ) := fun n => verCirc MV p n (q.eval n)
  let Vn : ℕ → ℕ := fun n => (Cn n).regs.length + 1 + (n + q.eval n)
  let π : ℕ → List Proj := fun n => fullProj (Cn n) n (Vn n)
  let TQp : Polynomial ℕ := p.comp (2 * Polynomial.X + 1 + q)
  let Rbp : Polynomial ℕ :=
    (q + 1) * ((TQp + 1) * (2 * TQp + 3) * Polynomial.C (cM MV)) + (q + 2)
  let Vbp : Polynomial ℕ := Rbp + 1 + (Polynomial.X + q)
  refine Ppoly_of_projection hS π (fun n => fullProj_ok (Cn n) n (Vn n)) (18 * Vbp * Vbp) ?_ ?_
  · intro n
    have hR : (Cn n).regs.length ≤ Rbp.eval n := by
      have := verCirc_size_le MV p n (q.eval n)
      simp only [Rbp, TQp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_ofNat]
      exact this
    have hVb : Vn n ≤ Vbp.eval n := by
      simp only [Vn, Vbp, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
      omega
    have hlen := length_fullProj (Cn n) n (Vn n)
    have ht := length_tseitin (Cn n)
    have hRV : (Cn n).regs.length ≤ Vn n := by simp only [Vn]; omega
    have hnV : n ≤ Vn n := by simp only [Vn]; omega
    have h1V : 1 ≤ Vn n := by simp only [Vn]; omega
    show (fullProj (Cn n) n (Vn n)).length ≤ _
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    rw [hlen]
    set v := Vn n
    set vb := Vbp.eval n
    have hvv : v * v ≤ vb * vb := Nat.mul_le_mul hVb hVb
    have hT : (tseitin (Cn n)).length ≤ 3 * v + 2 := by omega
    calc 3 * v * (tseitin (Cn n)).length + n * (3 * v) ≤ 3 * v * (3 * v + 2) + v * (3 * v) := by
          gcongr
      _ ≤ 18 * (v * v) := by nlinarith
      _ ≤ 18 * (vb * vb) := Nat.mul_le_mul_left 18 hvv
      _ = 18 * vb * vb := by ring
  · intro x
    have hinp : ∀ a ∈ (Cn x.length).regs, ∀ i, (Cn x.length).gate a = .inp i →
        i < x.length + q.eval x.length := fun a _ i h => verCirc_inp MV p x.length _ a i h
    rw [mem_iff_verCirc MV p x.length hV hL x rfl, ← tseitin_sat_iff (Cn x.length) x.length x,
      ← encDense_mem_SAT_iff (Vn x.length) (by simp only [Vn]; omega) _
        (tseitin_vars (Cn x.length) (x.length + q.eval x.length) x.length (by omega) hinp x),
      encDense_full]

/-- `SAT_dense` is complete for `NP_TM` under non-uniform polynomial-size circuits:
`SAT_dense ∈ Ppoly ↔ NP_TM ⊆ Ppoly`. -/
theorem SAT_dense_mem_Ppoly_iff : SAT_dense ∈ Ppoly ↔ NP_TM ⊆ Ppoly :=
  ⟨NP_TM_subset_Ppoly_of_SAT, fun h => h SAT_dense_mem_NP_TM⟩

/-- **The circuit route to the decisive premise.** If any language in `NP_TM` requires
superpolynomial circuits, then `SATLowerBound` holds. -/
theorem satLowerBound_of_NP_not_Ppoly (h : ∃ L ∈ NP_TM, L ∉ Ppoly) : CrossingSAT.SATLowerBound := by
  apply satLowerBound_of_not_Ppoly
  intro hS
  obtain ⟨L, hL, hLn⟩ := h
  exact hLn (NP_TM_subset_Ppoly_of_SAT hS hL)

/-- ... and hence the classical-model separation `P_TM ≠ NP_TM`. -/
theorem P_ne_NP_of_NP_not_Ppoly (h : ∃ L ∈ NP_TM, L ∉ Ppoly) : P_TM ≠ NP_TM :=
  CrossingSAT.P_ne_NP_of_satLowerBound (satLowerBound_of_NP_not_Ppoly h)

/-- Equivalent form: `NP_TM ⊄ Ppoly → SATLowerBound`. -/
theorem satLowerBound_of_not_subset (h : ¬ NP_TM ⊆ Ppoly) : CrossingSAT.SATLowerBound := by
  apply satLowerBound_of_NP_not_Ppoly
  by_contra hc
  push_neg at hc
  exact h hc

end PVNP.CircuitCookLevin
