"""Explicit finite Boolean-cell torus for CNF, with charged constraint counts.

Standard propositional reduction, not a physical model. Each of
m = max(1, |F|) rows contains n Boolean cells. Two binary clauses copy
each cell to the next row, with periodic wrapping. Each original clause
is evaluated on the Boolean cells of its designated row.
"""
from dataclasses import dataclass
from itertools import product
from typing import Sequence

Literal = tuple[int, bool]
Clause = tuple[Literal, ...]
Formula = tuple[Clause, ...]

@dataclass(frozen=True)
class TorusCNF:
    variables: int
    rows: int
    formula: Formula
    constraints: Formula

    @property
    def equality_clause_count(self) -> int:
        return 2 * self.variables * self.rows

    @property
    def total_variable_count(self) -> int:
        return self.variables * self.rows

    @property
    def total_clause_count(self) -> int:
        return len(self.constraints)


def transform(variables: int, formula: Sequence[Sequence[Literal]]) -> TorusCNF:
    if type(variables) is not int or variables < 0:
        raise ValueError("Variable count must be a nonnegative integer")
    formula = tuple(tuple(c) for c in formula)
    for clause in formula:
        for var, sign in clause:
            if type(var) is not int or not 0 <= var < variables or type(sign) is not bool:
                raise ValueError("Unbounded or non-Boolean literal")
    rows = max(1, len(formula))
    constraints: list[Clause] = []
    for j in range(rows):
        next_row = (j + 1) % rows
        for var in range(variables):
            src, dest = j * variables + var, next_row * variables + var
            constraints.append(((src, False), (dest, True)))
            constraints.append(((src, True), (dest, False)))
    for j, clause in enumerate(formula):
        constraints.append(tuple((j * variables + var, sign) for var, sign in clause))
    out = TorusCNF(variables, rows, formula, tuple(constraints))
    assert out.total_clause_count == out.equality_clause_count + len(formula)
    return out


def satisfies(formula: Formula, assignment: Sequence[bool]) -> bool:
    return all(any(assignment[var] == sign for var, sign in clause)
               for clause in formula)


def lift(original: Sequence[bool], torus: TorusCNF) -> tuple[bool, ...]:
    if len(original) != torus.variables or any(type(x) is not bool for x in original):
        raise ValueError("Incorrect source assignment")
    return tuple(original) * torus.rows


def extract(torus_assignment: Sequence[bool], torus: TorusCNF) -> tuple[bool, ...]:
    if len(torus_assignment) != torus.total_variable_count:
        raise ValueError("Incorrect torus assignment length")
    if not satisfies(torus.constraints, torus_assignment):
        raise ValueError("Not a valid torus lock")
    return tuple(torus_assignment[:torus.variables])


def enumerated_sat(formula: Formula, variables: int) -> bool:
    return any(satisfies(formula, a)
               for a in product((False, True), repeat=variables))


def independently_verify(variables: int, max_clauses: int,
                         clause_width: int) -> dict[str, int]:
    from itertools import combinations
    if not (0 <= variables <= 3 and 0 <= max_clauses <= 4 and 0 <= clause_width <= 3):
        raise ValueError("Computational exhaustion must have explicit bounds")
    lits = [(j, sign) for j in range(variables) for sign in (False, True)]
    universe = [()]
    for k in range(1, min(clause_width, len(lits)) + 1):
        universe.extend(combinations(lits, k))
    total = positives = 0
    for size in range(max_clauses + 1):
        for clauses in product(universe, repeat=size):
            torus = transform(variables, clauses)
            sat_original = enumerated_sat(torus.formula, variables)
            sat_torus = enumerated_sat(torus.constraints, torus.total_variable_count)
            if sat_original != sat_torus:
                raise AssertionError(f"Reduction failed at n={variables}: {clauses}")
            for a in product((False, True), repeat=variables):
                if satisfies(torus.formula, a):
                    assert satisfies(torus.constraints, lift(a, torus))
            total += 1
            positives += sat_original
    return {"formulas": total, "satisfiable": positives, "unsatisfiable": total-positives,
            "disagreements": 0}


if __name__ == "__main__":
    print(independently_verify(2, 3, 2))
