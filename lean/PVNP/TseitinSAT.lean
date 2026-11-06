import PVNP.SATVerifier

/-!
# Phase IX: Tseitin formulas — global consistency collapses to component parity

**Candidate invariant tested.** "Unavoidable constraint dependencies / global consistency":
on a constraint graph with strong expansion, every local decision is coupled to every other one,
so (the candidate claims) every correct SAT decider must pay for the coupling, e.g. through
resolution width/size, treewidth-style dynamic programming, or exhaustive propagation.

**Relation to `PVNP.Tseitin` (`Tseitin.lean`).** That module proves the obstruction direction
only (odd total charge ⇒ no GF(2) solution) and records the Gaussian-elimination bypass as an
analytic remark. This module proves the full characterization in both directions, the explicit
component computation, and the statement for the repository's language `SAT_dense`.

**What is proved here (kernel-checked).** For the Tseitin formula of *any* finite loopless
multigraph with *any* charge, membership of its dense encoding in `SAT_dense` is decided by the
parity of the charge on each connected component:

* `solvable_iff_parityOK`: the GF(2) Tseitin system is solvable iff every edge-closed vertex set
  (union of components) carries even charge. The proof is an induction on the edge list; it uses
  no connectivity library, spanning trees or linear-algebra duality.
* `parityOK_iff_comp`: it suffices to check the `|V|` explicitly computed components
  `comp E v` (`|V|` rounds of neighbour expansion each), a polynomial-time computation.
* `evalFormula_xorCNF`: the CNF of one XOR constraint (one clause per wrong-parity pattern) is
  exactly the constraint.
* `tseitin_mem_SAT_dense_iff`, `tseitin_mem_SAT_dense_iff_comp`, `tseitin_connected_iff`:
  the statements for the repository's own language `SAT_dense` and dense encoding.

**Consequence for the candidate invariant (stated in the Phase IX status document, not in Lean).**
For bounded-degree expanders with odd total charge every resolution refutation of the Tseitin
formula has size `2^{Ω(m)}` (Urquhart 1987; Ben-Sasson–Wigderson 2001), so DPLL/CDCL-style
deciders take exponential time on this family. The theorems below show that `SAT_dense`
restricted to the same family is decided by component parities in polynomial time. Hence
"every correct SAT decider incurs the resolution / global-consistency cost" is false: the cost
belongs to a proof system, not to the language.
-/

namespace PVNP.TseitinSAT

open Finset PVNP.PartI PVNP.Discrete.SATV

/-! ### Arithmetic in `ZMod 2` -/

theorem z2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

theorem z2_neg (a : ZMod 2) : -a = a := by
  fin_cases a <;> decide

theorem z2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all

section Algebra

variable {V : Type*} [DecidableEq V]

/-- Incidence multiplicity of `v` in the edge `e`, in `ZMod 2`. -/
def inc (e : V × V) (v : V) : ZMod 2 :=
  (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)

/-- Parity at `v` of the edge variables; edge `i` of the list carries the variable `x i`. -/
def degSum : List (V × V) → (ℕ → ZMod 2) → V → ZMod 2
  | [], _, _ => 0
  | e :: E, x, v => x 0 * inc e v + degSum E (fun i => x (i + 1)) v

/-- The Tseitin system of the edge list `E` with charge `χ` has a solution. -/
def Solvable (E : List (V × V)) (χ : V → ZMod 2) : Prop :=
  ∃ x : ℕ → ZMod 2, ∀ v, degSum E x v = χ v

/-- `C` is closed under the edges of `E`: no edge has exactly one end in `C`. Closed sets are
exactly the unions of connected components. -/
def Closed (E : List (V × V)) (C : Finset V) : Prop :=
  ∀ e ∈ E, (e.1 ∈ C ↔ e.2 ∈ C)

/-- Every union of connected components carries even total charge. -/
def ParityOK (E : List (V × V)) (χ : V → ZMod 2) : Prop :=
  ∀ C : Finset V, Closed E C → ∑ v ∈ C, χ v = 0

theorem sum_inc (e : V × V) (C : Finset V) :
    ∑ v ∈ C, inc e v = (if e.1 ∈ C then 1 else 0) + (if e.2 ∈ C then 1 else 0) := by
  simp only [inc, Finset.sum_add_distrib, Finset.sum_ite_eq]

theorem sum_inc_closed (e : V × V) (C : Finset V) (he : e.1 ∈ C ↔ e.2 ∈ C) :
    ∑ v ∈ C, inc e v = 0 := by
  rw [sum_inc]
  by_cases h : e.1 ∈ C
  · rw [if_pos h, if_pos (he.1 h)]; decide
  · rw [if_neg h, if_neg (fun h' => h (he.2 h'))]; decide

omit [DecidableEq V] in
theorem closed_of_cons {e : V × V} {E : List (V × V)} {C : Finset V} (h : Closed (e :: E) C) :
    Closed E C := fun e' he' => h e' (List.mem_cons_of_mem e he')

/-- Each edge is counted twice over a closed set, so a closed set sees zero total degree. -/
theorem sum_degSum_closed : ∀ (E : List (V × V)) (x : ℕ → ZMod 2) (C : Finset V),
    Closed E C → ∑ v ∈ C, degSum E x v = 0
  | [], _, _, _ => by simp [degSum]
  | e :: E, x, C, hC => by
    simp only [degSum, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_inc_closed e C (hC e (List.mem_cons_self ..)),
      sum_degSum_closed E _ C (closed_of_cons hC)]
    simp

/-- **Necessity**: a solvable Tseitin system has even charge on every union of components. -/
theorem parityOK_of_solvable {E : List (V × V)} {χ : V → ZMod 2} (h : Solvable E χ) :
    ParityOK E χ := by
  obtain ⟨x, hx⟩ := h
  intro C hC
  rw [← sum_degSum_closed E x C hC]
  exact Finset.sum_congr rfl fun v _ => (hx v).symm

theorem closed_sdiff {E : List (V × V)} {C D : Finset V} (hC : Closed E C) (hD : Closed E D) :
    Closed E (C \ D) := by
  intro e he
  simp only [Finset.mem_sdiff, hC e he, hD e he]

theorem closed_symm {E : List (V × V)} {C D : Finset V} (hC : Closed E C) (hD : Closed E D) :
    Closed E ((C ∪ D) \ (C ∩ D)) := by
  intro e he
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, hC e he, hD e he]

/-- In characteristic two, the charge of `C` plus that of `D` is the charge of their symmetric
difference. -/
theorem sum_symm (χ : V → ZMod 2) (C D : Finset V) :
    ∑ v ∈ C, χ v + ∑ v ∈ D, χ v = ∑ v ∈ (C ∪ D) \ (C ∩ D), χ v := by
  have h1 := Finset.sum_sdiff (f := χ) (Finset.inter_subset_union : C ∩ D ⊆ C ∪ D)
  have h2 := Finset.sum_union_inter (f := χ) (s₁ := C) (s₂ := D)
  rw [← h2, ← h1, add_assoc, z2_add_self, add_zero]

/-- **Sufficiency**: even charge on every union of components makes the Tseitin system
solvable. Induction on the edge list: the value of the first edge is forced to be the common
charge of the closed sets that it separates. -/
theorem solvable_of_parityOK [Fintype V] :
    ∀ (E : List (V × V)) (χ : V → ZMod 2), ParityOK E χ → Solvable E χ
  | [], χ, h => by
    refine ⟨fun _ => 0, fun v => ?_⟩
    have := h {v} (fun e he => by simp at he)
    simp only [Finset.sum_singleton] at this
    simp [degSum, this]
  | e :: E, χ, h => by
    classical
    set a := e.1
    set b := e.2
    -- the forced value of the first edge
    let t : ZMod 2 :=
      if hs : ∃ C : Finset V, Closed E C ∧ a ∈ C ∧ b ∉ C then ∑ v ∈ hs.choose, χ v else 0
    have hsep : ∀ C : Finset V, Closed E C → a ∈ C → b ∉ C → ∑ v ∈ C, χ v = t := by
      intro C hC haC hbC
      have hs : ∃ C : Finset V, Closed E C ∧ a ∈ C ∧ b ∉ C := ⟨C, hC, haC, hbC⟩
      obtain ⟨hC0, haC0, hbC0⟩ := hs.choose_spec
      have ht : t = ∑ v ∈ hs.choose, χ v := dif_pos hs
      have hD : Closed (e :: E) ((C ∪ hs.choose) \ (C ∩ hs.choose)) := by
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro ⟨-, h'⟩; exact absurd ⟨haC, haC0⟩ h'
          · rintro ⟨h', -⟩; rcases h' with h' | h' <;> contradiction
        · exact closed_symm hC hC0 e' he'
      have h0 := h _ hD
      rw [← sum_symm] at h0
      rw [ht]
      exact z2_eq_of_add_eq_zero h0
    have huniv : ∑ v ∈ (Finset.univ : Finset V), χ v = 0 := h _ (fun _ _ => by simp)
    set χ' : V → ZMod 2 := fun v => χ v + t * inc e v
    have hP' : ParityOK E χ' := by
      intro C hC
      have hsplit : ∑ v ∈ C, χ' v = ∑ v ∈ C, χ v + t * ∑ v ∈ C, inc e v := by
        simp only [χ', Finset.sum_add_distrib, Finset.mul_sum]
      rw [hsplit, sum_inc]
      by_cases hab : (a ∈ C ↔ b ∈ C)
      · have hC' : Closed (e :: E) C := by
          intro e' he'
          rcases List.mem_cons.1 he' with rfl | he'
          · exact hab
          · exact hC e' he'
        rw [h C hC']
        by_cases haC : a ∈ C
        · rw [if_pos haC, if_pos (hab.1 haC)]; simp [z2_add_self]
        · rw [if_neg haC, if_neg (fun h' => haC (hab.2 h'))]; simp
      · by_cases haC : a ∈ C
        · have hbC : b ∉ C := fun h' => hab ⟨fun _ => h', fun _ => haC⟩
          rw [hsep C hC haC hbC, if_pos haC, if_neg hbC]; simp [z2_add_self]
        · have hbC : b ∈ C := by
            by_contra h'; exact hab ⟨fun h'' => absurd h'' haC, fun h'' => absurd h'' h'⟩
          have hcC : Closed E (Finset.univ \ C) := closed_sdiff (fun _ _ => by simp) hC
          have hc := hsep (Finset.univ \ C) hcC (by simp [haC]) (by simp [hbC])
          have hsum := Finset.sum_sdiff (f := χ) (Finset.subset_univ C)
          rw [huniv, hc] at hsum
          have hCt : ∑ v ∈ C, χ v = t := (z2_eq_of_add_eq_zero hsum).symm
          rw [hCt, if_neg haC, if_pos hbC]; simp [z2_add_self]
    obtain ⟨x', hx'⟩ := solvable_of_parityOK E χ' hP'
    refine ⟨fun i => Nat.casesOn i t x', fun v => ?_⟩
    have hx'' : degSum E (fun i => (Nat.casesOn (i + 1) t x' : ZMod 2)) v = χ' v := hx' v
    simp only [degSum, hx'', χ']
    show t * inc e v + (χ v + t * inc e v) = χ v
    rw [add_comm, add_assoc, z2_add_self, add_zero]

/-- **Tseitin parity theorem.** The Tseitin system of a finite multigraph is solvable iff every
union of connected components carries even total charge. -/
theorem solvable_iff_parityOK [Fintype V] (E : List (V × V)) (χ : V → ZMod 2) :
    Solvable E χ ↔ ParityOK E χ :=
  ⟨parityOK_of_solvable, solvable_of_parityOK E χ⟩

/-! ### Components by explicit neighbour expansion -/

/-- One round of neighbour expansion. -/
def grow (E : List (V × V)) (S : Finset V) : Finset V :=
  S ∪ ((E.filter fun e => e.1 ∈ S).map Prod.snd).toFinset ∪
    ((E.filter fun e => e.2 ∈ S).map Prod.fst).toFinset

/-- The connected component of `v`: `|V|` rounds of neighbour expansion from `{v}`. -/
def comp [Fintype V] (E : List (V × V)) (v : V) : Finset V :=
  (grow E)^[Fintype.card V] {v}

theorem mem_grow {E : List (V × V)} {S : Finset V} {u : V} :
    u ∈ grow E S ↔ u ∈ S ∨ (∃ e ∈ E, e.1 ∈ S ∧ e.2 = u) ∨ (∃ e ∈ E, e.2 ∈ S ∧ e.1 = u) := by
  simp only [grow, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq, or_assoc]
  constructor
  · rintro (h | ⟨e, ⟨he, h1⟩, rfl⟩ | ⟨e, ⟨he, h1⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e, he, h1, rfl⟩)
    · exact Or.inr (Or.inr ⟨e, he, h1, rfl⟩)
  · rintro (h | ⟨e, he, h1, rfl⟩ | ⟨e, he, h1, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e, ⟨he, h1⟩, rfl⟩)
    · exact Or.inr (Or.inr ⟨e, ⟨he, h1⟩, rfl⟩)

theorem subset_grow (E : List (V × V)) (S : Finset V) : S ⊆ grow E S :=
  fun _ h => mem_grow.2 (Or.inl h)

theorem grow_subset_of_closed {E : List (V × V)} {S C : Finset V} (hC : Closed E C)
    (hS : S ⊆ C) : grow E S ⊆ C := by
  intro u hu
  rcases mem_grow.1 hu with h | ⟨e, he, h1, rfl⟩ | ⟨e, he, h1, rfl⟩
  · exact hS h
  · exact (hC e he).1 (hS h1)
  · exact (hC e he).2 (hS h1)

theorem iterate_subset_of_closed {E : List (V × V)} {S C : Finset V} (hC : Closed E C)
    (hS : S ⊆ C) : ∀ k : ℕ, (grow E)^[k] S ⊆ C
  | 0 => hS
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact grow_subset_of_closed hC (iterate_subset_of_closed hC hS k)

theorem closed_of_grow_eq {E : List (V × V)} {S : Finset V} (h : grow E S = S) : Closed E S := by
  intro e he
  constructor
  · intro h1; rw [← h]; exact mem_grow.2 (Or.inr (Or.inl ⟨e, he, h1, rfl⟩))
  · intro h2; rw [← h]; exact mem_grow.2 (Or.inr (Or.inr ⟨e, he, h2, rfl⟩))

theorem subset_iterate (E : List (V × V)) (S : Finset V) : ∀ k : ℕ, S ⊆ (grow E)^[k] S
  | 0 => fun _ h => h
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact (subset_iterate E S k).trans (subset_grow E _)

/-- Neighbour expansion stabilizes within `|V|` rounds. -/
theorem grow_comp [Fintype V] (E : List (V × V)) (v : V) : grow E (comp E v) = comp E v := by
  set f := grow E
  set S : ℕ → Finset V := fun k => f^[k] {v}
  have hmain : ∀ k, (∃ j ≤ k, f (S j) = S j) ∨ k + 1 ≤ (S k).card := by
    intro k
    induction k with
    | zero => right; simp [S]
    | succ k ih =>
      rcases ih with ⟨j, hj, hfix⟩ | hcard
      · exact Or.inl ⟨j, by omega, hfix⟩
      · by_cases hfix : f (S k) = S k
        · exact Or.inl ⟨k, by omega, hfix⟩
        · right
          have hsub : S k ⊂ S (k + 1) := by
            refine Finset.ssubset_iff_subset_ne.2 ⟨?_, fun h' => hfix ?_⟩
            · show S k ⊆ f^[k + 1] {v}
              rw [Function.iterate_succ_apply']; exact subset_grow E _
            · show f (S k) = S k
              have : S (k + 1) = f (S k) := Function.iterate_succ_apply' f k {v}
              rw [← this, ← h']
          have := Finset.card_lt_card hsub
          omega
  rcases hmain (Fintype.card V) with ⟨j, hj, hfix⟩ | hcard
  · have hS : S (Fintype.card V) = S j := by
      show f^[Fintype.card V] {v} = f^[j] {v}
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
      rw [hd, add_comm, Function.iterate_add_apply]
      exact Function.iterate_fixed hfix d
    show f (S (Fintype.card V)) = S (Fintype.card V)
    rw [hS, hfix]
  · exact absurd (Finset.card_le_univ (S (Fintype.card V))) (by omega)

theorem closed_comp [Fintype V] (E : List (V × V)) (v : V) : Closed E (comp E v) :=
  closed_of_grow_eq (grow_comp E v)

theorem mem_comp_self [Fintype V] (E : List (V × V)) (v : V) : v ∈ comp E v :=
  subset_iterate E {v} _ (Finset.mem_singleton_self v)

theorem comp_subset [Fintype V] {E : List (V × V)} {C : Finset V} (hC : Closed E C) {v : V}
    (hv : v ∈ C) : comp E v ⊆ C :=
  iterate_subset_of_closed hC (Finset.singleton_subset_iff.2 hv) _

/-- **Polynomial criterion.** It suffices to check the charge of the `|V|` explicitly computed
components. -/
theorem parityOK_iff_comp [Fintype V] (E : List (V × V)) (χ : V → ZMod 2) :
    ParityOK E χ ↔ ∀ v, ∑ u ∈ comp E v, χ u = 0 := by
  constructor
  · intro h v; exact h _ (closed_comp E v)
  · intro h
    have key : ∀ n : ℕ, ∀ C : Finset V, C.card = n → Closed E C → ∑ v ∈ C, χ v = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro C hcard hC
        rcases C.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
        · simp
        · have hsub := comp_subset hC hv
          have hlt : (C \ comp E v).card < n := by
            rw [← hcard]
            exact Finset.card_lt_card (Finset.sdiff_ssubset hsub ⟨v, mem_comp_self E v⟩)
          have h1 := ih _ hlt (C \ comp E v) rfl (closed_sdiff hC (closed_comp E v))
          rw [← Finset.sum_sdiff hsub, h1, h v, add_zero]
    exact fun C hC => key _ C rfl hC

omit [DecidableEq V] in
/-- On a connected multigraph (only `∅` and `V` are closed) the criterion is the total parity. -/
theorem parityOK_iff_total [Fintype V] (E : List (V × V)) (χ : V → ZMod 2)
    (hconn : ∀ C : Finset V, Closed E C → C = ∅ ∨ C = Finset.univ) :
    ParityOK E χ ↔ ∑ v, χ v = 0 := by
  constructor
  · intro h; exact h _ (fun _ _ => by simp)
  · intro h C hC
    rcases hconn C hC with rfl | rfl
    · simp
    · exact h

end Algebra

/-! ### The CNF encoding -/

/-- XOR of the listed variables under `α`. -/
def xorB (α : ℕ → Bool) : List ℕ → Bool
  | [] => false
  | i :: I => xor (α i) (xorB α I)

/-- CNF of the constraint `⊕_{i ∈ I} α i = c`: one clause excluding each wrong-parity pattern
of the listed variables (`2^{|I|-1}` clauses of width `|I|`). -/
def xorCNF : List ℕ → Bool → Formula
  | [], c => if c then [[]] else []
  | i :: I, c =>
    (xorCNF I c).map (List.cons (i, true)) ++ (xorCNF I (!c)).map (List.cons (i, false))

theorem evalFormula_append (α : ℕ → Bool) (F G : Formula) :
    evalFormula α (F ++ G) = (evalFormula α F && evalFormula α G) := by
  induction F with
  | nil => simp [evalFormula]
  | cons c F ih => simp [evalFormula, ih, Bool.and_assoc]

theorem evalFormula_map_cons (α : ℕ → Bool) (l : Literal) (F : Formula) :
    evalFormula α (F.map (List.cons l)) = (evalLiteral α l || evalFormula α F) := by
  induction F with
  | nil => simp [evalFormula]
  | cons c F ih =>
    simp only [List.map_cons, evalFormula, evalClause, ih]
    cases evalLiteral α l <;> simp

/-- The XOR CNF is exactly the XOR constraint. -/
theorem evalFormula_xorCNF (α : ℕ → Bool) :
    ∀ (I : List ℕ) (c : Bool), evalFormula α (xorCNF I c) = (xorB α I == c)
  | [], c => by cases c <;> rfl
  | i :: I, c => by
    rw [xorCNF, evalFormula_append, evalFormula_map_cons, evalFormula_map_cons,
      evalFormula_xorCNF α I c, evalFormula_xorCNF α I (!c)]
    simp only [evalLiteral, literalTrue, xorB]
    cases α i <;> cases xorB α I <;> cases c <;> rfl

theorem var_lt_of_mem_xorCNF : ∀ (I : List ℕ) (c : Bool), ∀ cl ∈ xorCNF I c, ∀ l ∈ cl, l.1 ∈ I
  | [], c => by cases c <;> simp [xorCNF]
  | i :: I, c => by
    intro cl hcl l hl
    simp only [xorCNF, List.mem_append, List.mem_map] at hcl
    rcases hcl with ⟨cl', hcl', rfl⟩ | ⟨cl', hcl', rfl⟩
    · rcases List.mem_cons.1 hl with rfl | hl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (var_lt_of_mem_xorCNF I c cl' hcl' l hl)
    · rcases List.mem_cons.1 hl with rfl | hl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (var_lt_of_mem_xorCNF I (!c) cl' hcl' l hl)

section Encoding

variable {V : Type*} [DecidableEq V]

/-- Indices of the edges of `E` incident to `v`. -/
def incIdx : List (V × V) → V → List ℕ
  | [], _ => []
  | e :: E, v => (if e.1 = v ∨ e.2 = v then [0] else []) ++ (incIdx E v).map (· + 1)

theorem lt_of_mem_incIdx : ∀ (E : List (V × V)) (v : V), ∀ i ∈ incIdx E v, i < E.length
  | [], v => by simp [incIdx]
  | e :: E, v => by
    intro i hi
    simp only [incIdx, List.mem_append, List.mem_map] at hi
    rcases hi with hi | ⟨j, hj, rfl⟩
    · split_ifs at hi <;> simp_all
    · have := lt_of_mem_incIdx E v j hj
      simp; omega

/-- The **Tseitin CNF**: for every listed vertex, the XOR CNF of its incident edge variables
with the vertex charge. -/
def tseitinCNF (E : List (V × V)) (χ : V → Bool) (vs : List V) : Formula :=
  vs.flatMap fun v => xorCNF (incIdx E v) (χ v)

/-- Booleans as elements of `ZMod 2`. -/
def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_injective : Function.Injective toZ := by
  intro a b h; cases a <;> cases b <;> simp_all [toZ]

theorem toZ_decide (z : ZMod 2) : toZ (decide (z = 1)) = z := by
  fin_cases z <;> decide

theorem xorB_append (α : ℕ → Bool) (I J : List ℕ) :
    xorB α (I ++ J) = xor (xorB α I) (xorB α J) := by
  induction I with
  | nil => simp [xorB]
  | cons i I ih => simp [xorB, ih]

theorem xorB_map_succ (α : ℕ → Bool) (I : List ℕ) :
    xorB α (I.map (· + 1)) = xorB (fun i => α (i + 1)) I := by
  induction I with
  | nil => rfl
  | cons i I ih => simp [xorB, ih]

/-- On a loopless edge list, the XOR of the incident variables is the `ZMod 2` degree sum. -/
theorem toZ_xorB_incIdx : ∀ (E : List (V × V)), (∀ e ∈ E, e.1 ≠ e.2) →
    ∀ (α : ℕ → Bool) (v : V), toZ (xorB α (incIdx E v)) = degSum E (fun i => toZ (α i)) v
  | [], _, α, v => rfl
  | e :: E, hE, α, v => by
    have hE' : ∀ e' ∈ E, e'.1 ≠ e'.2 := fun e' he' => hE e' (List.mem_cons_of_mem e he')
    have hne : e.1 ≠ e.2 := hE e (List.mem_cons_self ..)
    rw [incIdx, xorB_append, toZ_xor, xorB_map_succ, toZ_xorB_incIdx E hE' _ v, degSum]
    congr 1
    by_cases h1 : e.1 = v
    · have h2 : e.2 ≠ v := fun h2 => hne (h1.trans h2.symm)
      simp [h1, h2, inc, xorB]
    · by_cases h2 : e.2 = v
      · simp [h1, h2, inc, xorB]
      · simp [h1, h2, inc, xorB, toZ]

omit [DecidableEq V] in
theorem evalFormula_flatMap (α : ℕ → Bool) (vs : List V) (f : V → Formula) :
    evalFormula α (vs.flatMap f) = true ↔ ∀ v ∈ vs, evalFormula α (f v) = true := by
  induction vs with
  | nil => simp [evalFormula]
  | cons v vs ih => simp [List.flatMap_cons, evalFormula_append, ih]

/-- The Tseitin CNF is satisfiable iff the GF(2) system is solvable. -/
theorem satisfiable_tseitinCNF_iff [Fintype V] (E : List (V × V)) (hE : ∀ e ∈ E, e.1 ≠ e.2)
    (χ : V → Bool) (vs : List V) (hvs : ∀ v, v ∈ vs) :
    satisfiable (tseitinCNF E χ vs) ↔ Solvable E (fun v => toZ (χ v)) := by
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨fun i => toZ (α i), fun v => ?_⟩
    have hv := (evalFormula_flatMap α vs _).1 hα v (hvs v)
    rw [evalFormula_xorCNF, beq_iff_eq] at hv
    rw [← toZ_xorB_incIdx E hE α v, hv]
  · rintro ⟨x, hx⟩
    refine ⟨fun i => decide (x i = 1), (evalFormula_flatMap _ vs _).2 fun v _ => ?_⟩
    rw [evalFormula_xorCNF, beq_iff_eq]
    apply toZ_injective
    rw [toZ_xorB_incIdx E hE _ v]
    have : (fun i => toZ (decide (x i = 1))) = x := funext fun i => toZ_decide (x i)
    rw [this, hx]

theorem var_lt_tseitinCNF (E : List (V × V)) (χ : V → Bool) (vs : List V) :
    ∀ c ∈ tseitinCNF E χ vs, ∀ l ∈ c, l.1 < E.length := by
  intro c hc l hl
  simp only [tseitinCNF, List.mem_flatMap] at hc
  obtain ⟨v, -, hc⟩ := hc
  exact lt_of_mem_incIdx E v _ (var_lt_of_mem_xorCNF _ _ c hc l hl)

end Encoding

/-! ### `SAT_dense` on Tseitin instances -/

/-- **Tseitin instances of `SAT_dense`.** For a loopless multigraph on `Fin m` with `|E| ≤ n`
edges and charge `χ`, the dense encoding of the Tseitin CNF lies in `SAT_dense` iff every union
of connected components carries even charge. -/
theorem tseitin_mem_SAT_dense_iff {m : ℕ} (E : List (Fin m × Fin m))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (χ : Fin m → Bool) (n : ℕ) (hn : 1 ≤ n) (hEn : E.length ≤ n) :
    encDense n (tseitinCNF E χ (List.finRange m)) ∈ SAT_dense ↔
      ParityOK E (fun v => toZ (χ v)) := by
  rw [encDense_mem_SAT_iff n hn _ (fun c hc l hl =>
      lt_of_lt_of_le (var_lt_tseitinCNF E χ _ c hc l hl) hEn),
    satisfiable_tseitinCNF_iff E hE χ _ (List.mem_finRange), solvable_iff_parityOK]

/-- **Polynomial-time decision of `SAT_dense` on Tseitin instances**: membership is the
vanishing of the charge of each of the `m` explicitly computed components. -/
theorem tseitin_mem_SAT_dense_iff_comp {m : ℕ} (E : List (Fin m × Fin m))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (χ : Fin m → Bool) (n : ℕ) (hn : 1 ≤ n) (hEn : E.length ≤ n) :
    encDense n (tseitinCNF E χ (List.finRange m)) ∈ SAT_dense ↔
      ∀ v, ∑ u ∈ comp E v, toZ (χ u) = 0 := by
  rw [tseitin_mem_SAT_dense_iff E hE χ n hn hEn, parityOK_iff_comp]

/-- On a connected multigraph (for instance any connected expander) the Tseitin instance is in
`SAT_dense` iff the total charge is even: global consistency is one parity bit. -/
theorem tseitin_connected_iff {m : ℕ} (E : List (Fin m × Fin m))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) (χ : Fin m → Bool) (n : ℕ) (hn : 1 ≤ n) (hEn : E.length ≤ n)
    (hconn : ∀ C : Finset (Fin m), Closed E C → C = ∅ ∨ C = Finset.univ) :
    encDense n (tseitinCNF E χ (List.finRange m)) ∈ SAT_dense ↔ ∑ v, toZ (χ v) = 0 := by
  rw [tseitin_mem_SAT_dense_iff E hE χ n hn hEn, parityOK_iff_total _ _ hconn]

end PVNP.TseitinSAT
