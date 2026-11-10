"""Adversarial finite smoke tests for the ORIGINAL II-10 polynomial writers.

These are tests of finite executions, not proofs of the original FP or
MTM.Outputs obligations. Exercise empty coefficients, input longer than the
radius, nonconstant Horner polynomials, and the exact trailing blank
convention checked by execute().
"""
import itertools
import unittest

from pvnp.two_phase_tape_writer import window_writer, input_writer, execute
from pvnp.two_phase_state_serializer import enumerate_states, original_input_bits


class TestPhaseXVIIITenPolynomialWriter(unittest.TestCase):
    def test_zero_radius_with_long_input(self):
        machine = window_writer((0,))
        expected = [True, False, False, True, False]
        for n in range(9):
            for x in itertools.product((False, True), repeat=n):
                actual, steps = execute(machine, x)
                self.assertEqual(actual, expected, (n, x))
                self.assertLessEqual(steps, machine.step_bound(n))

    def test_horner_radius_and_output_length(self):
        for coefficients in ((), (0, 0), (0, 2), (2, 0, 1), (1, 0, 0, 1)):
            machine = window_writer(coefficients)
            for n in range(4):
                radius = sum(c * n ** i for i, c in enumerate(coefficients))
                expected = [True] * (radius + 1) + [False, False] + [True] * (2 * radius + 1) + [False]
                self.assertEqual(len(expected), 3 * radius + 5)
                for x in itertools.product((False, True), repeat=n):
                    actual, steps = execute(machine, x)
                    self.assertEqual(actual, expected, (coefficients, n, x))
                    self.assertLessEqual(steps, machine.step_bound(n))

    def test_input_writer_longer_input_than_radius(self):
        alphabet = enumerate_states(("_", "0", "1"), ("q",))
        kwargs = dict(blank="_", zero="0", one="1", start="q", accept="q", reject="q")
        for coefficients in ((0,), (1,), (0, 1), (1, 0, 1)):
            machine = input_writer(coefficients, alphabet, **kwargs)
            for n in range(7):
                for x in (tuple(False for _ in range(n)), tuple(i % 2 == 0 for i in range(n))):
                    actual, steps = execute(machine, x)
                    expected = original_input_bits(x, coefficients, alphabet, **kwargs)
                    self.assertEqual(actual, expected, (coefficients, n, x))
                    self.assertLessEqual(steps, machine.step_bound(n))


if __name__ == "__main__":
    unittest.main()
