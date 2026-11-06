import PVNP.CrossingSAT
import PVNP.CircuitCNF

/-!
# Toroidal diagonalization: a finite cyclic consistency test

A chain of Boolean wires on a periodic loop has equality constraints on its
ordinary edges and either an equality or an inequality constraint at the seam.
This is a *genuine finite, dense-CNF-encoded* test of a simple self-negating
feedback proposal. The odd loop is contradictory, the even loop satisfiable,
and both decisions have a trivial uniform polynomial-time rule.

In particular the odd loop does NOT diagonalize against all SAT deciders:
its non-membership is a property of the supplied formula, not an
algorithm-independent running-time lower bound. No P-vs-NP separation follows.
-/

namespace PVNP.ToroidalDiagonal

open PVNP.PartI PVNP.CrossingSAT PVNP.Discrete.SATV PVNP.CircuitCNF

/-- Two clauses force adjacent Boolean wires to agree. -/
def edgeFormula (i : ℕ) : Formula :=
  [[(i, false), (i + 1, true)], [(i, true), (i + 1, false)]]

/-- A periodic seam, equal for `flip = false`, inverted for `flip = true`. -/
def seamFormula (n : ℕ) (flip : Bool) : Formula :=
  if flip then
    [[(n, false), (0, false)], [(n, true), (0, true)]]
  else
    [[(n, false), (0, true)], [(n, true), (0, false)]]

/-- A linear-size CNF over wires `0, …, n`. The closing seam is the
topological identification of the two ends, with optional negation. -/
def ringFormula (n : ℕ) (flip : Bool) : Formula :=
  (List.range n).flatMap edgeFormula ++ seamFormula n flip

/-- Encode the loop into the repository's dense CNF-SAT language. -/
def encRing (n : ℕ) (flip : Bool) : List Bool :=
  encDense (n + 1) (ringFormula n flip)

private theorem edge_sem (a : ℕ → Bool) (i : ℕ) :
    (evalClause a [(i, false), (i+1, true)] = true ∧
     evalClause a [(i, true), (i+1, false)] = true) ↔
      a (i+1) = a i := by
  cases h : a i <;> cases h' : a (i+1) <;>
    simp_all [evalClause, evalLiteral, literalTrue]

private theorem odd_seam_sem (a : ℕ → Bool) (n : ℕ) :
    (evalClause a [(n, false), (0, false)] = true ∧
     evalClause a [(n, true), (0, true)] = true) ↔
      a n ≠ a 0 := by
  cases h : a n <;> cases h' : a 0 <;>
    simp_all [evalClause, evalLiteral, literalTrue]

/-- The open chain is constant, provided its adjacent edges agree. -/
theorem edge_chain_constant (a : ℕ → Bool) (n : ℕ)
    (h : ∀ i < n, a (i+1) = a i) : a n = a 0 := by
  have step : ∀ i : ℕ, i ≤ n → a i = a 0 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
        intro hi
        calc
          a (i+1) = a i := h i (by omega)
          _ = a 0 := ih (by omega)
  exact step n le_rfl

/-- No Boolean state can satisfy an equality ring with an inverted seam. -/
theorem odd_ring_no_state (n : ℕ) :
    ¬ ∃ a : ℕ → Bool,
      (∀ i < n, a (i+1) = a i) ∧ a n ≠ a 0 := by
  rintro ⟨a, hedges, hseam⟩
  exact hseam (edge_chain_constant a n hedges)

/-- With the ordinary seam, the constant-zero state is a valid cyclic state. -/
theorem even_ring_has_state (n : ℕ) :
    ∃ a : ℕ → Bool,
      (∀ i < n, a (i+1) = a i) ∧ a n = a 0 := by
  exact ⟨fun _ => false, by simp⟩

private theorem edge_clause_mem (n i : ℕ) (hi : i < n) :
    [(i, false), (i+1, true)] ∈ ringFormula n true ∧
    [(i, true), (i+1, false)] ∈ ringFormula n true := by
  constructor
  · apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨i, List.mem_range.mpr hi, by simp [edgeFormula]⟩
  · apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨i, List.mem_range.mpr hi, by simp [edgeFormula]⟩

/-- The dense-CNF ring with an inverted seam is unsatisfiable at every size. -/
theorem odd_ring_unsat (n : ℕ) : ¬ satisfiable (ringFormula n true) := by
  rintro ⟨a, ha⟩
  rw [evalFormula_iff] at ha
  have he : ∀ i < n, a (i+1) = a i := by
    intro i hi
    apply (edge_sem a i).mp
    exact ⟨ha _ (edge_clause_mem n i hi).1, ha _ (edge_clause_mem n i hi).2⟩
  have hw : a n ≠ a 0 := by
    apply (odd_seam_sem a n).mp
    constructor
    · apply ha
      simp [ringFormula, seamFormula]
    · apply ha
      simp [ringFormula, seamFormula]
  exact (odd_ring_no_state n) ⟨a, he, hw⟩

/-- Equality and seam clauses refer only to the `n+1` declared wires. -/
theorem ring_bounded (n : ℕ) (flip : Bool) :
    Bounded (ringFormula n flip) (n+1) := by
  intro c hc l hl
  simp only [ringFormula, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc
    have hib : i < n := List.mem_range.mp hi
    simp [edgeFormula] at hci
    rcases hci with rfl | rfl
    · simp at hl
      rcases hl with rfl | rfl <;> dsimp <;> omega
    · simp at hl
      rcases hl with rfl | rfl <;> dsimp <;> omega
  · cases flip with
    | false =>
        simp [seamFormula] at hc
        rcases hc with rfl | rfl
        · simp at hl
          rcases hl with rfl | rfl <;> dsimp <;> omega
        · simp at hl
          rcases hl with rfl | rfl <;> dsimp <;> omega
    | true =>
        simp [seamFormula] at hc
        rcases hc with rfl | rfl
        · simp at hl
          rcases hl with rfl | rfl <;> dsimp <;> omega
        · simp at hl
          rcases hl with rfl | rfl <;> dsimp <;> omega

/-- The even seam has an explicit constant assignment. -/
theorem even_ring_sat (n : ℕ) : satisfiable (ringFormula n false) := by
  refine ⟨fun _ => false, ?_⟩
  rw [evalFormula_iff]
  intro c hc
  simp only [ringFormula, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨i, hi, hci⟩ := List.mem_flatMap.mp hc
    simp [edgeFormula] at hci
    rcases hci with rfl | rfl <;>
      simp [evalClause, evalLiteral, literalTrue]
  · simp [seamFormula] at hc
    rcases hc with rfl | rfl <;>
      simp [evalClause, evalLiteral, literalTrue]

/-- A diagonal closing edge makes the *specified* SAT instance a no-instance,
not a lower bound on arbitrary SAT algorithms. -/
theorem odd_encRing_not_SAT (n : ℕ) : encRing n true ∉ SAT_dense := by
  intro h
  apply odd_ring_unsat n
  exact (encDense_mem_SAT_iff (n+1) (by omega) _ (ring_bounded n true)).mp h

/-- Closing the loop without negation produces a yes-instance. -/
theorem even_encRing_mem_SAT (n : ℕ) : encRing n false ∈ SAT_dense := by
  exact (encDense_mem_SAT_iff (n+1) (by omega) _ (ring_bounded n false)).mpr
    (even_ring_sat n)

private theorem edge_blocks_length (n : ℕ) :
    ((List.range n).flatMap edgeFormula).length = 2*n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append]
      simp [edgeFormula, ih]
      omega

theorem ringFormula_length (n : ℕ) (flip : Bool) :
    (ringFormula n flip).length = 2*n+2 := by
  rw [ringFormula, List.length_append, edge_blocks_length]
  cases flip <;> simp [seamFormula]

/-- The dense encoding is quadratic in n, so the contradiction is cheap
to construct and check. -/
theorem encRing_length (n : ℕ) (flip : Bool) :
    (encRing n flip).length = 3*(n+1)*(2*n+2) := by
  rw [encRing, length_encDense, ringFormula_length]

end PVNP.ToroidalDiagonal
