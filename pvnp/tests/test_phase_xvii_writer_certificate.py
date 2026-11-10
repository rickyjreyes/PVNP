"""II-10 original transducer finite-control certificate regression."""
import itertools
import unittest

from pvnp.two_phase_tape_writer import (
    Instruction, Writer, window_writer, input_writer
)
from pvnp.two_phase_state_serializer import enumerate_states, original_input_bits
from pvnp.phase_xvi.writer_certificate import certify_control, certify_execution


class TestWriterCertificates(unittest.TestCase):
    def test_structural_certificates_and_all_boolean_inputs(self):
        coefficients = ((), (0,), (1,), (2, 1), (1, 0, 1), (0, 2), (1, 1, 1))
        for cs in coefficients:
            machine = window_writer(cs)
            cert = certify_control(machine)
            self.assertEqual(cert.coefficients, cs)
            self.assertLess(cert.entry, cert.instruction_count)
            self.assertGreater(cert.branch_edges, 0)
            for n in range(5):
                radius = sum(c * n**i for i, c in enumerate(cs))
                expected = [True] * (radius + 1) + [False, False] + (
                    [True] * (2 * radius + 1)) + [False]
                for x in itertools.product((False, True), repeat=n):
                    run = certify_execution(machine, x, expected)
                    self.assertEqual(run.output_length, 3 * radius + 5)
                    self.assertLessEqual(run.actual_steps, run.stated_step_bound)

    def test_original_input_state_serialization(self):
        alphabet = enumerate_states(("_", "0", "1"), ("q",))
        kwargs = dict(blank="_", zero="0", one="1",
                      start="q", accept="q", reject="q")
        for cs in ((0,), (1,), (0, 1), (1, 1)):
            machine = input_writer(cs, alphabet, **kwargs)
            certify_control(machine)
            for n in range(4):
                inputs = (tuple(False for _ in range(n)),
                          tuple(i % 2 == 0 for i in range(n)))
                for x in inputs:
                    expected = original_input_bits(x, cs, alphabet, **kwargs)
                    certify_execution(machine, x, expected)

    def test_malformed_control_rejected(self):
        broken = Writer((Instruction("take", (), (0, 1)),), 0, (), 1)
        with self.assertRaisesRegex(ValueError, "Dangling"):
            certify_control(broken)
        broken2 = Writer((Instruction("emit", (True,), ()),), 0, (), 1)
        with self.assertRaisesRegex(ValueError, "Invalid instruction"):
            certify_control(broken2)

    def test_bad_input_rejected(self):
        with self.assertRaises(ValueError):
            certify_execution(window_writer((0,)), (0,), [True, False])


if __name__ == "__main__":
    unittest.main()
