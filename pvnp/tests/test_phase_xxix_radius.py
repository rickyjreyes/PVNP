"""Smoke test for the Phase XXIX analyticity-radius probe (evidence tooling, not a proof)."""
import math
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "phase_xxix"))

import radius_experiment  # noqa: E402


class RadiusProbeTest(unittest.TestCase):
    def test_mass_conserved_and_rate_finite(self):
        rows = radius_experiment.run(K=8, A=1.0, T=0.5, dt=2e-3, samples=3)
        m0 = rows[0][1]
        for t, mass, sig, an, nh in rows:
            self.assertLess(abs(mass - m0), 1e-6)
        _, _, sig, _, _ = rows[-1]
        self.assertTrue(math.isfinite(sig) and sig > 0)

    def test_linear_flow_preserves_spectrum(self):
        rows = radius_experiment.run(K=8, A=1.0, beta=0.0, gamma=0.0, T=0.5, dt=2e-3, samples=3)
        # with no nonlinearity the Fourier moduli are invariant, so the analytic norm is constant
        a0 = rows[0][3]
        for row in rows:
            self.assertAlmostEqual(row[3], a0, places=9)


if __name__ == "__main__":
    unittest.main()
