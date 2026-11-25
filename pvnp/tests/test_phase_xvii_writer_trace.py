"""Trace-level adversarial tests of the original II-10 writer."""
import itertools
import unittest

from pvnp.phase_xvi.writer_trace_audit import audit_trace
from pvnp.two_phase_tape_writer import input_writer, window_writer
from pvnp.two_phase_state_serializer import enumerate_states, original_input_bits


class TestOriginalWriterTrace(unittest.TestCase):
    def test_window_writer_all_short_inputs(self):
        coefficient_lists = (
            (), (0,), (1,), (2,), (3, 1), (0, 1), (0, 2),
            (1, 0, 1), (2, 1, 0), (0, 0, 1),
        )
        for cs in coefficient_lists:
            writer = window_writer(cs)
            for n in range(5):
                radius = sum(c * (n ** degree) for degree, c in enumerate(cs))
                expected = ([True] * (radius + 1) + [False, False]
                            + [True] * (2 * radius + 1) + [False])
                for x in itertools.product((False, True), repeat=n):
                    with self.subTest(coefficients=cs, input=x):
                        result = audit_trace(writer, x, expected)
                        self.assertLessEqual(result.steps, result.step_bound)
                        self.assertEqual(result.output_length, 3 * radius + 5)
                        self.assertEqual(result.min_head, -1)
                        self.assertGreater(result.return_to_left_end_count, 0)

    def test_input_writer_boundaries_and_horner(self):
        alphabet = enumerate_states(("_", "0", "1"), ("q",))
        params = dict(blank="_", zero="0", one="1", start="q",
                      accept="q", reject="q")
        for cs in ((0,), (1,), (2,), (0, 1), (1, 1), (1, 0, 1)):
            writer = input_writer(cs, alphabet, **params)
            for n in range(5):
                samples = set((tuple(False for _ in range(n)),
                               tuple(True for _ in range(n)),
                               tuple(i % 2 == 0 for i in range(n))))
                for x in samples:
                    expected = original_input_bits(x, cs, alphabet, **params)
                    with self.subTest(coefficients=cs, input=x):
                        audit_trace(writer, x, expected)

    def test_input_validation(self):
        with self.assertRaises(ValueError):
            audit_trace(window_writer((0,)), (1,), (True, False))
        with self.assertRaises(ValueError):
            audit_trace(window_writer((0,)), (), (1,))


if __name__ == "__main__":
    unittest.main()
