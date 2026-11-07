"""Independent executable checks of original Part II canonical bit writers.

Tests are reference cross-checks, *not* a Lean/MTM polynomial runtime proof.
Run: python3 -m unittest pvnp.tests.test_two_phase_reference
"""

import itertools
import unittest

from pvnp.two_phase_reference import (
    InitialCell,
    enumerated_encoder_bits,
    enumerated_window_bits,
    original_encoder_bits,
    original_initial_cell,
    original_window_bits,
    polynomial_value,
)


def state_code(cell: InitialCell):
    """A fixed six-bit test code, intentionally not claiming Lean stateBits order."""
    return [
        True,
        cell.symbol == "1",
        cell.symbol == "0",
        cell.head_state == "q0",
        not cell.phase,
        False,
    ]


class OriginalWriters(unittest.TestCase):
    def test_polynomial_horner(self):
        for n in range(10):
            for coeffs in ([], [0], [1], [3, 2], [1, 0, 2], [0, 1, 1, 1]):
                self.assertEqual(polynomial_value(coeffs, n),
                                 sum(c * n**k for k, c in enumerate(coeffs)))
        for coeffs, n in (([1, -1], 2), ([1], -1)):
            with self.assertRaises(ValueError):
                polynomial_value(coeffs, n)

    def test_lattice_bitmap_exact_for_many_polynomials(self):
        polys = ([0], [1], [2], [1, 1], [0, 2], [2, 0, 1])
        for n in range(6):
            for bits in itertools.product((False, True), repeat=n):
                for p in polys:
                    with self.subTest(n=n, input=bits, p=p):
                        generated = original_window_bits(bits, p)
                        expected = enumerated_window_bits(bits, p)
                        L = polynomial_value(p, n)
                        self.assertEqual(generated, expected)
                        self.assertEqual(len(generated), 3*L + 5)
                        self.assertEqual(generated[:L+1], [True] * (L+1))
                        self.assertEqual(generated[L+1:L+3], [False, False])
                        self.assertEqual(generated[-1], False)

    def test_initial_config_has_head_origin_and_input(self):
        x = [True, False, True]
        for i in range(-4, 5):
            cell = original_initial_cell(
                x, i, blank="_", symbol_of_bit=lambda b: "1" if b else "0",
                initial_state="q0")
            self.assertEqual(cell.head_state, "q0" if i == 0 else None)
            self.assertEqual(cell.symbol, ("1" if x[i] else "0") if 0 <= i < len(x) else "_")
            self.assertFalse(cell.phase)

    def test_encoder_canonical_config_and_boundaries(self):
        kwargs = {
            "blank": "_",
            "symbol_of_bit": lambda b: "1" if b else "0",
            "initial_state": "q0",
            "state_bits": state_code,
        }
        for n in range(6):
            for x in itertools.product((False, True), repeat=n):
                for p in ([0], [1], [1, 1], [2, 0, 1]):
                    with self.subTest(n=n, input=x, p=p):
                        out = original_encoder_bits(x, p, **kwargs)
                        self.assertEqual(out, enumerated_encoder_bits(x, p, **kwargs))
                        L = polynomial_value(p, n)
                        self.assertEqual(len(out), (2*L+1)*6)

    def test_encoder_uses_true_fixed_width_codes(self):
        with self.assertRaises(ValueError):
            original_encoder_bits(
                [True], [1], blank="_",
                symbol_of_bit=lambda b: "1" if b else "0",
                initial_state="q0",
                state_bits=lambda cell: [True] if cell.head_state else [True, False])


if __name__ == "__main__":
    unittest.main()
