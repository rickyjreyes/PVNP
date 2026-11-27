"""Smoke test for the Phase XXX detector probe (evidence tooling, not a proof)."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "phase_xxix"))

import detector_experiment as de  # noqa: E402


class DetectorProbeTest(unittest.TestCase):
    def test_detector_error_below_state_error(self):
        _, rows = de.compare("trig", 1.0, [6], 10, 0.5, 2e-3, 1)
        for K, t, full, det in rows:
            if t > 0:
                self.assertLess(det, full)

    def test_integrators_agree(self):
        base = de.initial("trig", 1.0, 8)
        a = de.lawson(base, 8, 0.2, 2e-3, 1)[-1][1]
        b = de.strang(base, 8, 0.2, 1e-3, 1)[-1][1]
        self.assertLess(abs(de.detector(a, 8) - de.detector(b, 8)), 1e-4)


if __name__ == "__main__":
    unittest.main()
