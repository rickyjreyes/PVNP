"""Finite execution audit of the actual original writer's final .finish scan.

This tests the concrete transition function on fully staged output cells.
It does not replace the Lean first-halt proof or prove the assembler produces
the staged cells.
"""
import itertools
import unittest

from pvnp.two_phase_tape_writer import (
    BLANK, HALT, Cell, Instruction, Writer,
)


class TestPhaseXVIIIFinishScan(unittest.TestCase):
    def test_staged_words_have_exact_first_halt_and_blank(self):
        finish = Writer((Instruction("finish", (), ()),), 0, (), 1)
        for n in range(10):
            for bits in itertools.product((False, True), repeat=n):
                for terminal in (BLANK, Cell(), False, True):
                    with self.subTest(bits=bits, terminal=terminal):
                        tape = {i: Cell(out=b) for i, b in enumerate(bits)}
                        tape[n] = terminal
                        tape[-1] = "left-end"
                        state, head = ("scan", 0), 0
                        for i, bit in enumerate(bits):
                            self.assertNotEqual(state, HALT)
                            self.assertEqual(state, ("scan", 0))
                            state, written, move = finish.transition(
                                state, tape.get(head, BLANK))
                            self.assertEqual(written, bit)
                            self.assertEqual(move, 1)
                            tape[head] = written
                            head += move
                            self.assertEqual(head, i + 1)
                        self.assertNotEqual(state, HALT)
                        state, written, move = finish.transition(
                            state, tape.get(head, BLANK))
                        self.assertEqual(state, HALT)
                        self.assertIs(written, BLANK)
                        self.assertEqual(move, 1)
                        tape[head] = written
                        head += move
                        self.assertEqual(head, n + 1)
                        self.assertEqual(
                            [tape.get(i, BLANK) for i in range(n)], list(bits))
                        self.assertIs(tape[n], BLANK)
                        self.assertEqual(tape[-1], "left-end")

    def test_true_and_false_output_bits_are_distinct(self):
        finish = Writer((Instruction("finish", (), ()),), 0, (), 1)
        for bit in (False, True):
            state, symbol, direction = finish.transition(
                ("scan", 0), Cell(out=bit))
            self.assertEqual((state, symbol, direction),
                             (("scan", 0), bit, 1))


if __name__ == "__main__":
    unittest.main()
