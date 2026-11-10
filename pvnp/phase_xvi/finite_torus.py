"""Exhaustive finite-CNF versus formula-dependent logical torus comparison.

A row holds a full Boolean assignment. Adjacent rows copy the assignment
(including the closing seam), and row j checks clause j. This is a finite
logical CSP, NOT a WCT solution, physical evolution or complexity lower bound.
"""
from __future__ import annotations

import argparse
import itertools
import json
from typing import Iterator

Literal = tuple[int, bool]
Clause = tuple[Literal, ...]
Formula = tuple[Clause, ...]


def clause_holds(clause: Clause, assignment: tuple[bool, ...]) -> bool:
    return any(assignment[i] == positive for i, positive in clause)


def cnf_holds(formula: Formula, assignment: tuple[bool, ...]) -> bool:
    return all(clause_holds(clause, assignment) for clause in formula)


def sat_bruteforce(formula: Formula, variables: int) -> bool:
    return any(cnf_holds(formula, bits)
               for bits in itertools.product((False, True), repeat=variables))


def logical_torus_lock_bruteforce(formula: Formula, variables: int) -> bool:
    """Independently enumerate ring states. Never call the SAT oracle."""
    m = len(formula)
    if m == 0:
        return True
    states = tuple(itertools.product((False, True), repeat=variables))
    for rows in itertools.product(states, repeat=m):
        if any(rows[j] != rows[(j + 1) % m] for j in range(m)):
            continue
        if all(clause_holds(formula[j], rows[j]) for j in range(m)):
            return True
    return False


def bare_torus_lock_bruteforce(variables: int, clauses: int) -> bool:
    """Formula-independent cyclic agreement always has a constant lock."""
    zero = (False,) * variables
    rows = (zero,) * clauses
    return all(rows[j] == rows[(j + 1) % clauses]
               for j in range(clauses)) if clauses else True


def clause_universe(variables: int, max_width: int,
                    include_empty: bool = True) -> tuple[Clause, ...]:
    literals = tuple((i, positive) for i in range(variables)
                     for positive in (False, True))
    choices = [()] if include_empty else []
    for width in range(1, min(len(literals), max_width) + 1):
        choices.extend(itertools.combinations(literals, width))
    return tuple(choices)


def formulas(variables: int, max_clauses: int,
             max_width: int) -> Iterator[Formula]:
    choices = clause_universe(variables, max_width)
    for k in range(max_clauses + 1):
        yield from itertools.product(choices, repeat=k)


def investigate(variables: int, max_clauses: int, max_width: int) -> dict:
    if not (0 <= variables <= 5 and 0 <= max_clauses <= 6
            and 0 <= max_width <= 3):
        raise ValueError("Specify an explicitly bounded exhaustive domain")
    checked = yes = no = 0
    first_bare_counterexample: Formula | None = None
    for formula in formulas(variables, max_clauses, max_width):
        satisfiable = sat_bruteforce(formula, variables)
        locked = logical_torus_lock_bruteforce(formula, variables)
        if satisfiable != locked:
            raise AssertionError(
                f"Logical equivalence failed: {formula!r}, sat={satisfiable}, lock={locked}"
            )
        checked += 1
        yes += int(satisfiable)
        no += int(not satisfiable)
        if (not satisfiable and all(c for c in formula)
                and first_bare_counterexample is None):
            assert bare_torus_lock_bruteforce(variables, len(formula))
            first_bare_counterexample = formula
    return {
        "model": "finite_formula_dependent_boolean_torus_not_physical_wct",
        "variables": variables,
        "max_clauses": max_clauses,
        "max_width": max_width,
        "tested_formulas": checked,
        "satisfiable": yes,
        "unsatisfiable": no,
        "equivalence_failures": 0,
        "bare_lock_counterexample": first_bare_counterexample,
        "scope": "finite exhaustive evidence only; no general mathematical or physical proof",
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--variables", type=int, default=3)
    ap.add_argument("--max-clauses", type=int, default=3)
    ap.add_argument("--max-width", type=int, default=2)
    args = ap.parse_args()
    print(json.dumps(investigate(args.variables, args.max_clauses, args.max_width),
                     indent=2))


if __name__ == "__main__":
    main()
