"""Independent regression tests for Phase XVI finite logical torus.

These test finite formulas only. The general Lean proof and physical I-37
remain separate obligations.
"""
import unittest

from pvnp.phase_xvi.finite_torus import (
    bare_torus_lock_bruteforce,
    clause_universe,
    investigate,
    logical_torus_lock_bruteforce,
    sat_bruteforce,
)


class TestFiniteToroidalCNF(unittest.TestCase):
    def test_unit_contradiction_disproves_bare_lock(self):
        formula = (((0, True),), ((0, False),))
        self.assertFalse(sat_bruteforce(formula, 1))
        self.assertFalse(logical_torus_lock_bruteforce(formula, 1))
        self.assertTrue(bare_torus_lock_bruteforce(1, 2))

    def test_empty_cases(self):
        self.assertTrue(sat_bruteforce((), 0))
        self.assertTrue(logical_torus_lock_bruteforce((), 0))
        self.assertFalse(sat_bruteforce(((),), 0))
        self.assertFalse(logical_torus_lock_bruteforce(((),), 0))

    def test_exhaustive_three_variable_bounded_cnf(self):
        result = investigate(3, 3, 2)
        self.assertEqual(result["tested_formulas"], 11155)
        self.assertEqual(result["satisfiable"], 9214)
        self.assertEqual(result["unsatisfiable"], 1941)
        self.assertEqual(result["equivalence_failures"], 0)
        self.assertEqual(len(clause_universe(3, 2)), 22)
        self.assertEqual(result["bare_lock_counterexample"],
                         (((0, False),), ((0, True),)))

    def test_invalid_bounds_are_rejected(self):
        with self.assertRaises(ValueError):
            investigate(6, 2, 2)


if __name__ == "__main__":
    unittest.main()
