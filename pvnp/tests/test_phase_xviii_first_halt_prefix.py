"""Exact finite execution regression for the original II-10 pre-dispatch phase.

This tests the transition function mirrored by the Lean writer. It is *not*
a replacement for the Lean first-halt or MTM.Outputs proof.
"""
import itertools
import unittest

from pvnp.two_phase_tape_writer import (
    BLANK, HALT, LEFT, START, Cell, input_writer, window_writer,
)
from pvnp.two_phase_state_serializer import enumerate_states


class TestPhaseXVIIIFirstHaltPrefix(unittest.TestCase):
    def check_prefix(self, machine, input_bits):
        n = len(input_bits)
        tape = dict(enumerate(input_bits))
        head = 0
        control = START
        states = []
        for step in range(2 * n + 4):
            self.assertNotEqual(control, HALT, ("early halt", step, input_bits))
            states.append(control)
            control, symbol, direction = machine.transition(
                control, tape.get(head, BLANK))
            tape[head] = symbol
            head += direction

        self.assertEqual(states[0], START)
        self.assertEqual(states[1], ("mark",))
        self.assertEqual(states[2: n + 3], [("normalize",)] * (n + 1))
        self.assertEqual(
            states[n + 3:], [("return", machine.entry)] * (n + 1)
        )
        self.assertEqual(control, ("scan", machine.entry))
        self.assertEqual(head, 0)
        self.assertEqual(tape.get(-1), LEFT)
        self.assertEqual(
            [tape.get(i) for i in range(n)],
            [Cell(inp=bit) for bit in input_bits],
        )
        self.assertIsNone(tape.get(n))
        return control, tape, head

    def test_window_writer_all_binary_prefixes(self):
        for coefficients in ((), (0,), (1,), (0, 1), (1, 0, 1), (2, 3)):
            machine = window_writer(coefficients)
            for n in range(9):
                for bits in itertools.product((False, True), repeat=n):
                    with self.subTest(coefficients=coefficients, bits=bits):
                        self.check_prefix(machine, bits)

    def test_input_writer_all_binary_prefixes(self):
        alphabet = enumerate_states(("_", "0", "1"), ("q",))
        args = dict(blank="_", zero="0", one="1",
                    start="q", accept="q", reject="q")
        for coefficients in ((), (0,), (0, 1), (2, 1)):
            machine = input_writer(coefficients, alphabet, **args)
            for n in range(7):
                for bits in itertools.product((False, True), repeat=n):
                    with self.subTest(coefficients=coefficients, bits=bits):
                        self.check_prefix(machine, bits)


if __name__ == "__main__":
    unittest.main()
