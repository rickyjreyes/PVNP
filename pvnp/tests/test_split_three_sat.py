#!/usr/bin/env python3
"""Exhaustive regression for the PVNP split 3-CNF SAT reduction.

Uses an actual list of tripled-literal clauses; no external dependencies.
Command: python -m unittest discover -s pvnp/tests -p "test_split_three_sat.py"
"""
import itertools
import math
import unittest


def cnf_split(a, b):
    assert len(a) == len(b)
    clauses = []
    for i, (av, bv) in enumerate(zip(a, b)):
        if av:
            clauses.append(((i, True),) * 3)
        if bv:
            clauses.append(((i, False),) * 3)
    return clauses


def eval_cnf(clauses, z):
    return all(any(z[i] == positive for i, positive in clause) for clause in clauses)


def disjoint(a, b):
    return all(not (av and bv) for av, bv in zip(a, b))


def centralized_decider(a, b):
    # A counterexample to reading private-input communication hardness as
    # an unrestricted SAT time lower bound: O(n) with joint input access.
    return not any(av and bv for av, bv in zip(a, b))


class Split3CNF(unittest.TestCase):
    def test_all_small_pairs_and_assignments(self):
        for n in range(5):
            bitstrings = list(itertools.product((False, True), repeat=n))
            for a, b in itertools.product(bitstrings, repeat=2):
                clauses = cnf_split(a, b)
                self.assertLessEqual(len(clauses), 2 * n)
                self.assertTrue(all(len(c) == 3 for c in clauses))
                satisfiable = any(eval_cnf(clauses, z) for z in bitstrings)
                self.assertEqual(satisfiable, disjoint(a, b))
                self.assertEqual(centralized_decider(a, b), satisfiable)
                if satisfiable:
                    self.assertTrue(eval_cnf(clauses, a))
                if not disjoint(a, b):
                    self.assertFalse(satisfiable)

    def test_quantized_cut_capacity_sample_values(self):
        for n in range(1, 20):
            # Binary alphabet: q = 2 requires m >= n.
            self.assertGreaterEqual(2 ** n, 2 ** (n - 1) + 1)
            self.assertLess(2 ** (n - 1), 2 ** n)
            for q in (2, 3, 4, 8):
                m = math.ceil(n / math.log2(q))
                self.assertGreaterEqual(q**m, 2**n)
                if m > 0:
                    self.assertLess(q**(m - 1), 2**n)


if __name__ == "__main__":
    unittest.main()
