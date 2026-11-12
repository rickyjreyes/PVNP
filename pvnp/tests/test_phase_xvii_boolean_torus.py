"""Adversarial checks for Phase XVII finite Boolean-cell torus construction."""
import unittest
from itertools import product

from pvnp.phase_xvi.boolean_torus_reduction import (
    transform, satisfies, lift, extract, independently_verify
)


class TestFiniteBooleanTorus(unittest.TestCase):
    def test_exhaustive_two_variables_three_clauses(self):
        self.assertEqual(independently_verify(2, 3, 2), {
            "formulas": 1464, "satisfiable": 951,
            "unsatisfiable": 513, "disagreements": 0,
        })

    def test_complete_witness_correspondence(self):
        cases = [
            (0, ()), (0, ((),)),
            (1, (((0, True),),)),
            (1, (((0, True),), ((0, False),))),
            (3, (((0, True), (1, False)), ((1, True), (2, False)),
                 ((0, False), (2, True)))),
        ]
        for n, formula in cases:
            torus = transform(n, formula)
            self.assertEqual(torus.total_variable_count, n * max(1, len(formula)))
            self.assertEqual(torus.total_clause_count,
                             2 * n * max(1, len(formula)) + len(formula))
            for assignment in product((False, True), repeat=n):
                self.assertEqual(satisfies(formula, assignment),
                                 satisfies(torus.constraints, lift(assignment, torus)))
                if satisfies(formula, assignment):
                    self.assertEqual(extract(lift(assignment, torus), torus), assignment)

    def test_bad_encoding_rejected(self):
        with self.assertRaises(ValueError):
            transform(1, (((1, True),),))
        with self.assertRaises(ValueError):
            transform(1, (((0, 1),),))
        with self.assertRaises(ValueError):
            transform(-1, ())

    def test_invalid_lock_cannot_be_extracted(self):
        torus = transform(1, (((0, True),), ((0, False),)))
        for assignment in product((False, True), repeat=torus.total_variable_count):
            with self.assertRaises(ValueError):
                extract(assignment, torus)


if __name__ == "__main__":
    unittest.main()
