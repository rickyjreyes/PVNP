"""Executable regression for the proposed finite-control literal MTM.

The interpreter mirrors exactly the explicit transition function of
TwoPhaseFixedWord.literalMTM. These tests are independent of the Lean
kernel: they do NOT certify the Lean proof or the general II-10 claim.
"""
from __future__ import annotations
import itertools
import unittest
from pvnp.two_phase_reference import original_window_bits


def literal_mtm_run(word, input_word):
    tape = {i: bit for i, bit in enumerate(input_word)}
    state, head, first_halt = 0, 0, None
    for t in range(len(word) + 2):
        if state == len(word) + 1 and first_halt is None:
            first_halt = t
            break
        if state < len(word):
            tape[head] = word[state]
            state += 1
        else:
            tape[head] = None
            state = len(word) + 1
        head += 1
    return first_halt, tape, state, head


class FixedWordTests(unittest.TestCase):
    def test_fixed_radii_and_inputs(self):
        for radius in range(30):
            word = original_window_bits([], [radius])
            self.assertEqual(len(word), 3*radius + 5)
            for n in range(9):
                for x in itertools.product((False, True), repeat=n):
                    first, tape, state, head = literal_mtm_run(word, x)
                    self.assertEqual(first, len(word)+1)
                    self.assertEqual(head, len(word)+1)
                    self.assertEqual(state, len(word)+1)
                    self.assertEqual([tape[i] for i in range(len(word))], word)
                    self.assertIsNone(tape[len(word)])

    def test_empty_word_and_overlong_input(self):
        for n in range(30):
            first, tape, state, head = literal_mtm_run([], [True]*n)
            self.assertEqual((first, state, head), (1, 1, 1))
            self.assertIsNone(tape[0])


if __name__ == "__main__":
    unittest.main()
