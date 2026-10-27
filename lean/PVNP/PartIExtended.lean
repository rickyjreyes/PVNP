import PVNP.PartI

/-!
# Part I — exact finite CNF semantics

This module verifies a concrete certificate checker and its exact
product-of-unsatisfied-literals semantics for arbitrary finite CNF formulas.
It does not assume geometric separation or curvature lower bounds.
-/

namespace PVNP.PartI

abbrev Literal := Nat × Bool
abbrev Clause := List Literal
abbrev Formula := List Clause

def evalLiteral (assignment : Nat → Bool) (literal : Literal) : Bool :=
  literalTrue (assignment literal.1) literal.2

def evalClause (assignment : Nat → Bool) : Clause → Bool
  | [] => false
  | literal :: rest => evalLiteral assignment literal || evalClause assignment rest

def clauseViolation (assignment : Nat → Bool) : Clause → Bool
  | [] => true
  | literal :: rest => !evalLiteral assignment literal && clauseViolation assignment rest

theorem violation_iff_not_clause (assignment : Nat → Bool) (c : Clause) :
    clauseViolation assignment c = !(evalClause assignment c) := by
  induction c with
  | nil => rfl
  | cons literal rest ih =>
      cases h : evalLiteral assignment literal <;>
        cases h2 : evalClause assignment rest <;>
        simp [clauseViolation, evalClause, ih, h, h2]

def evalFormula (assignment : Nat → Bool) : Formula → Bool
  | [] => true
  | clause :: rest => evalClause assignment clause && evalFormula assignment rest

def allPenaltiesZero (assignment : Nat → Bool) : Formula → Bool
  | [] => true
  | clause :: rest => !clauseViolation assignment clause && allPenaltiesZero assignment rest

/-- Corrected 3-SAT-style logic encoding works for every finite CNF list. -/
theorem no_clause_penalty_iff_formula_satisfied
    (assignment : Nat → Bool) (formula : Formula) :
    allPenaltiesZero assignment formula = evalFormula assignment formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp [allPenaltiesZero, evalFormula,
        violation_iff_not_clause, ih]

def satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Nat → Bool, evalFormula assignment formula = true

theorem satisfiable_iff_zero_penalties (formula : Formula) :
    satisfiable formula ↔
      ∃ assignment : Nat → Bool, allPenaltiesZero assignment formula = true := by
  simp only [satisfiable, no_clause_penalty_iff_formula_satisfied]

/-- A pair of opposite unit clauses is unsatisfiable. -/
def oppositeUnitClauses : Formula :=
  [[(0, true)], [(0, false)]]

theorem opposite_unit_clauses_unsat :
    ¬ satisfiable oppositeUnitClauses := by
  intro h
  rcases h with ⟨assignment, ha⟩
  cases hv : assignment 0 <;>
    simp [oppositeUnitClauses, evalFormula, evalClause,
      evalLiteral, literalTrue, hv] at ha

/-- A supplied satisfying assignment is verified by direct evaluation;
the checker does not enumerate the assignment space. -/
theorem supplied_assignment_decidable (assignment : Nat → Bool)
    (formula : Formula) :
    evalFormula assignment formula = true ∨
      evalFormula assignment formula = false := by
  cases evalFormula assignment formula <;> simp

end PVNP.PartI
