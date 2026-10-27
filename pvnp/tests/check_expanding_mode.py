#!/usr/bin/env python3
"""Exact-ansatz numerical checks for the expanding-torus WCT Hamiltonian mode.

Analytic proof is in ../proofs/expanding-domain-hamiltonian-mode.md.
Only standard Python library; execute: python pvnp/tests/check_expanding_mode.py
"""
import cmath
import math

KAPPA, BETA, GAMMA = 1.0, 2.0, 1.0
MASS, EPSILON, ALPHA = 1.0, 1.0, 0.0
T = math.pi / KAPPA**2

def row(n: int) -> dict:
    L = 2 * math.pi * n
    V = L * L
    q = 1.0 / (n*n)
    s = MASS / V
    omega = (KAPPA - q)**2 - BETA*s + GAMMA*s*s
    H = MASS * (KAPPA - q)**2 - 0.5 * BETA*MASS*MASS/V + (
        GAMMA * MASS**3 / (3 * V*V))
    d2 = MASS*q*q
    weight = s/(s + EPSILON**2 * math.exp(-2 * ALPHA * s))**2
    Q = weight*d2
    delta = MASS**0.5 * abs(cmath.exp(-1j*omega*T)-1)
    return dict(n=n, V=V, omega=omega, H=H, mass=MASS, delta=delta,
                d2=d2, weight=weight, Q=Q)

def test_expanding_mode():
    rows = [row(n) for n in (3, 6, 12, 24, 48)]
    for r in rows:
        assert r["mass"] == 1.0
        assert r["H"] <= 4.0/3.0 + 1e-10
        assert r["delta"] > 1.0   # exact phase contrast stays detectable
        assert 0 < r["weight"] <= 1/r["V"]
        assert 0 < r["Q"] <= r["d2"]/r["V"]
    for prev, curr in zip(rows, rows[1:]):
        assert curr["weight"] < prev["weight"]
        assert curr["Q"] < prev["Q"]
    assert rows[-1]["delta"] > 1.99
    assert rows[-1]["Q"] < rows[0]["Q"]/1e6
    return rows

if __name__ == "__main__":
    for r in test_expanding_mode():
        print(
            f"n={r['n']:2d} V={r['V']:9.3f} H={r['H']:.8f} "
            f"contrast={r['delta']:.8f} "
            f"ratio={r['weight']:.4e} Q={r['Q']:.4e}"
        )
