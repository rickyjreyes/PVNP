"""Phase XXXI progress bars: the registry is consistent and only audited proofs count."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "phase_xxxi"))

import progress as pg  # noqa: E402


def uniform_registry(obligation):
    return {"categories": [
        {"id": f"C{i}", "title": "t", "subjective_percent": 0,
         "obligations": [dict(obligation, id=f"{obligation['id']}{i}")]}
        for i in range(1, 13)]}


class PhaseXXXIProgressTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.audited = pg.audited_names()
        cls.sources = pg.lean_sources()
        cls.rows, cls.errors = pg.evaluate(pg.load_registry(), cls.audited, cls.sources)

    def test_registry_consistent(self):
        self.assertEqual(self.errors, [])

    def test_twelve_categories(self):
        self.assertEqual(len(self.rows), 12)

    def test_separation_and_classical_problem_open(self):
        by_id = {r[0]: r for r in self.rows}
        self.assertEqual(by_id["C9"][2], 0)
        self.assertEqual(by_id["C12"][2], 0)

    def test_derivations_never_count(self):
        reg = uniform_registry({"id": "X", "status": "derived",
                                "lean": ["PVNP.DetectorQuadratic.detector_split"]})
        rows, _ = pg.evaluate(reg, self.audited, self.sources)
        self.assertTrue(all(r[2] == 0 for r in rows))

    def test_unaudited_declarations_rejected(self):
        reg = uniform_registry({"id": "Y", "status": "proved",
                                "lean": ["PVNP.NoSuchModule.no_such_theorem"]})
        rows, errors = pg.evaluate(reg, self.audited, self.sources)
        self.assertTrue(all(r[2] == 0 for r in rows))
        self.assertEqual(len(errors), 12 * 2)

    def test_new_theorems_counted(self):
        for name in ("PVNP.Discrete.SweepArith.div_exact_tm",
                     "PVNP.Discrete.SweepArith.fixdiv_tm",
                     "PVNP.DetectorQuadratic.detector_band_quadratic",
                     "PVNP.DetectorQuadratic.device_detector_quadratic"):
            self.assertIn(name, self.audited)
            self.assertTrue(pg.is_declared(name, self.sources))


if __name__ == "__main__":
    unittest.main()
