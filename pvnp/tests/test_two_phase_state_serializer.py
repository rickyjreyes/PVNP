"""Tests for the original W_M fixed-width one-hot serializer.

Run: python3 -m unittest discover -s pvnp/tests -p 'test_two_phase_state_serializer.py'
These are executable checks, not a formal MTM time-bound proof.
"""

import itertools
import unittest

from pvnp.two_phase_state_serializer import (
    TwoPhaseState, enumerate_states, state_bits, initial_state, original_input_bits,
)


class TestStateSerialization(unittest.TestCase):
    def setUp(self):
        self.alphabet = enumerate_states(('_', '0', '1'), ('start', 'accept', 'reject'))

    def test_alphabet_cardinality(self):
        self.assertEqual(len(self.alphabet), 3 * (1 + 3 * 3) * 2)
        self.assertEqual(len(set(self.alphabet)), len(self.alphabet))

    def test_all_codes_have_fixed_width_and_are_injective(self):
        codes = [tuple(state_bits(s, self.alphabet, 'accept', 'reject')) for s in self.alphabet]
        self.assertEqual(len(codes), len(set(codes)))
        self.assertTrue(all(len(code) == 3 + 2 * len(self.alphabet) for code in codes))
        self.assertTrue(all(code[0] for code in codes))
        self.assertTrue(all(not code[j] for code in codes for j in range(3, len(code), 2)))
        for i, code in enumerate(codes):
            self.assertTrue(code[4 + 2 * i])
            self.assertEqual(sum(code[4::2]), 1)

    def test_accept_reject_header_precedence(self):
        a = TwoPhaseState('_', ('q', 'accept'), False)
        r = TwoPhaseState('_', ('q', 'reject'), False)
        self.assertEqual(state_bits(a, self.alphabet, 'accept', 'reject')[1:3], [True, False])
        self.assertEqual(state_bits(r, self.alphabet, 'accept', 'reject')[1:3], [False, True])

    def test_all_initial_words(self):
        k = 3 + 2 * len(self.alphabet)
        for n in range(5):
            for x in itertools.product((False, True), repeat=n):
                for coeffs in ([0], [1], [1,1], [0,1], [1,0,1]):
                    r = sum(c * n**j for j,c in enumerate(coeffs))
                    y = original_input_bits(x,coeffs,self.alphabet,
                         blank='_',zero='0',one='1',start='start',
                         accept='accept',reject='reject')
                    self.assertEqual(len(y), (2*r+1)*k)
                    for j, i in enumerate(range(-r,r+1)):
                        piece = y[j*k:(j+1)*k]
                        state = initial_state(('1' if x[i] else '0') if 0 <= i < n else '_',
                                              'start' if i == 0 else None)
                        self.assertEqual(piece, state_bits(state,self.alphabet,'accept','reject'))

    def test_reject_duplicate_enumeration(self):
        with self.assertRaises(ValueError):
            enumerate_states(('_','_'),('q',))
        with self.assertRaises(ValueError):
            state_bits(self.alphabet[0], (self.alphabet[0],self.alphabet[0]), 'accept','reject')


if __name__ == '__main__':
    unittest.main()
