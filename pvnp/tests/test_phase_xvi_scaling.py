import unittest
from fractions import Fraction

from pvnp.phase_xvi.scaling import scale_witness


class TestQuadraticScalingWitness(unittest.TestCase):
    def test_rational_grid(self):
        trials = 0
        for numerator in range(1, 11):
            for denominator in range(1, 11):
                floor = Fraction(numerator, denominator)
                for energy in (Fraction(0), Fraction(1, 100), Fraction(1),
                               Fraction(10), Fraction(1000)):
                    amplitude, scaled = scale_witness(energy, floor)
                    self.assertLess(scaled, floor)
                    self.assertGreater(amplitude, 0)
                    trials += 1
        self.assertEqual(trials, 500)

    def test_invalid(self):
        with self.assertRaises(ValueError):
            scale_witness(Fraction(-1), Fraction(1))
        with self.assertRaises(ValueError):
            scale_witness(Fraction(1), Fraction(0))


if __name__ == "__main__":
    unittest.main()
