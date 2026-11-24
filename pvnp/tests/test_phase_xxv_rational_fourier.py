import unittest
from fractions import Fraction as F
from pvnp.phase_xxv.rational_fourier import Arithmetic, field_box, midpoint_step


class RationalFourierTests(unittest.TestCase):
    def assert_enclosed(self, interval, expected):
        self.assertLessEqual(interval[0], expected)
        self.assertGreaterEqual(interval[1], expected)

    def test_pi_and_phase(self):
        a = Arithmetic(40)
        re, im = a.exp_i(a.pi())
        self.assert_enclosed(re, F(-1))
        self.assert_enclosed(im, F(0))
        re, im = a.exp_i(a.box(0))
        self.assert_enclosed(re, F(1))
        self.assert_enclosed(im, F(0))

    def test_exact_zero_mode(self):
        # Exact cancellation of the free phases, nonzero real and imaginary parts.
        s = {(0, 0): (F(1, 2), F(1, 4))}
        L, kappa, beta, gamma, t = F(2), F(1), F(3), F(2), F(1, 3)
        z = field_box(s, s, L, kappa, beta, gamma, t, 40)[(0, 0)]
        x, y = s[(0, 0)]
        m = (x*x+y*y)/L**2
        coeff = -beta*m+gamma*m*m
        self.assert_enclosed(z[0], coeff*y)
        self.assert_enclosed(z[1], -coeff*x)

    def test_rounding_certificate(self):
        s = {(0, 0): (F(1, 2), F(1, 4))}
        h = F(1, 16)
        x, y = s[(0, 0)]
        m = x*x+y*y
        c = -m+m*m
        expected = x+h*c*y, y-h*c*x
        result, bound = midpoint_step(s, s, 1, 0, 1, 1, 0, h, 32)
        actual_l1 = sum(abs(a-b) for a,b in zip(result[(0,0)], expected))
        self.assertLessEqual(actual_l1, bound)
        self.assertLess(bound, F(1, 1000000))

    def test_zero_input(self):
        z, error = midpoint_step({}, {(0, 0)}, 1, 0, 1, 1, 0, F(1, 16), 32)
        self.assertEqual(z[(0,0)], (0,0))
        self.assertEqual(error, 0)

    def test_precision_reduces_certificate(self):
        s = {(0, 0): (F(1, 3), F(1, 5))}
        _, lo = midpoint_step(s, s, 2, 1, 1, 1, F(1,4), F(1,16), 24)
        _, hi = midpoint_step(s, s, 2, 1, 1, 1, F(1,4), F(1,16), 48)
        self.assertLess(hi, lo)


if __name__ == "__main__":
    unittest.main()
