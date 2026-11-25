"""Finite numerical sanity checks for the SAT readout *algebra*.

These tests do not evaluate WCT dynamics and do not verify Lean theorems.
"""
import random
import unittest


class SATReadoutAlgebraTests(unittest.TestCase):
    def test_initial_skew_triangle(self):
        rng = random.Random(21026)
        for _ in range(5000):
            a0, b0, a1, b1 = [rng.uniform(-15, 15) for _ in range(4)]
            eps = abs(a0 - b0) + rng.uniform(0, 2)
            delta = abs(a1 - b1)
            if eps <= delta:
                target = (delta - eps) / 2
                self.assertLessEqual(target, max(abs(a1 - a0), abs(b1 - b0)) + 1e-10)

    def test_noisy_margin(self):
        rng = random.Random(11026)
        for _ in range(5000):
            threshold = rng.uniform(-15, 15)
            margin = rng.uniform(0.01, 3)
            rho = rng.uniform(0, margin)
            reported_yes = threshold + margin + rng.uniform(0, 3)
            reported_no = threshold - margin - rng.uniform(0, 3)
            physical_yes = reported_yes + rng.uniform(-rho, rho)
            physical_no = reported_no + rng.uniform(-rho, rho)
            self.assertLessEqual(
                2 * (margin - rho),
                abs(physical_yes - physical_no) + 1e-10,
            )

    def test_combined_budget(self):
        rng = random.Random(12026)
        for _ in range(3000):
            T = rng.uniform(0.01, 10)
            G = rng.uniform(0.01, 5)
            gu, gv = G * rng.random(), G * rng.random()
            Bu, Bv = rng.uniform(0, 10), rng.uniform(0, 10)
            rhs_u = gu**4 * T**3 * Bu
            rhs_v = gv**4 * T**3 * Bv
            # Choose a d satisfying the formal disjunction.
            d = rng.random() * max(rhs_u, rhs_v) ** 0.25
            self.assertLessEqual(
                d**4,
                G**4 * T**3 * (Bu + Bv) + 1e-8,
            )

    def test_preloaded_answer_is_not_transported(self):
        # No positive transport lower bound follows if input encoding has
        # already placed the full output contrast into the detector at t=0.
        a0, b0, aT, bT = 1.0, -1.0, 1.0, -1.0
        eps, delta = abs(a0 - b0), abs(aT - bT)
        self.assertEqual((delta - eps) / 2, 0)
        self.assertEqual(abs(aT - a0) + abs(bT - b0), 0)


if __name__ == "__main__":
    unittest.main()
