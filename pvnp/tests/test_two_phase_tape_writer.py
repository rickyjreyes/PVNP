import itertools
import unittest

from pvnp.two_phase_state_serializer import enumerate_states, original_input_bits
from pvnp.two_phase_tape_writer import execute, input_writer, window_writer


class TestCanonicalTapeWriter(unittest.TestCase):
    def test_horner_on_actual_single_head(self):
        for cs in ((), (0,), (3,), (0,1), (1,0,1), (2,1,0)):
            machine = window_writer(cs)
            for n in range(5):
                L = sum(a * n**j for j, a in enumerate(cs))
                for x in itertools.product((False, True), repeat=n):
                    word, steps = execute(machine, x)
                    self.assertEqual(word, [True]*(L+1) + [False,False] + [True]*(2*L+1) + [False])
                    self.assertLessEqual(steps, machine.step_bound(n))

    def test_input_short_long_and_empty(self):
        alphabet = enumerate_states(('_','0','1'), ('q',))
        kwargs = dict(blank='_', zero='0', one='1', start='q', accept='q', reject='q')
        for cs, inputs in (((), [(), (False,True,True)]),
                           ((0,1), [(), (False,), (True,False)]),
                           ((1,0,1), [(True,)])):
            machine = input_writer(cs, alphabet, **kwargs)
            for x in inputs:
                word, steps = execute(machine, x)
                self.assertEqual(word, original_input_bits(x, cs, alphabet, **kwargs))
                self.assertLessEqual(steps, machine.step_bound(len(x)))
