"""Exact rational witnesses to the unnormalized quadratic-energy obstruction.

These are arithmetic counterexamples to a *hypothesis-free* positive lower
bound, not physical WCT device configurations. A robust fixed readout gap
can exclude the small amplitudes exhibited here.
"""
from fractions import Fraction


def scale_witness(e: Fraction, c: Fraction) -> tuple[Fraction, Fraction]:
    if e < 0 or c <= 0:
        raise ValueError("Energy coefficient must be nonnegative and the floor positive")
    a = c / (2 * (e + c + 1))
    energy = a * a * e
    assert 0 < a < 1 and energy < c
    return a, energy
