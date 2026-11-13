"""Numerical checks for the frozen-torus SAT device of `lean/PVNP/WCTSATDevice.lean`.

A small pseudo-spectral (Strang split-step) solver for
    i psi_t = (Delta + kappa)^2 psi - beta |psi|^2 psi + gamma |psi|^4 psi
on the torus [0, L]^2 with L = 2*pi, field = L^-1 sum_k c_k e^{i k.x}.

These are numerical sanity checks. They do not verify the Lean proofs; the
two-mode flux formula checked here is proved in `lean/PVNP/WCTSATBlind.lean`
(`Jdot_twoMode`).
"""
import cmath
import math
import unittest

L = 2 * math.pi
N = 8
KAPPA, BETA, GAMMA = 2.0, 0.3, 0.2
MODES = [k - N // 2 for k in range(N)]
GRID = [L * j / N for j in range(N)]


def to_field(coef):
    """coef: dict (k1, k2) -> c. Returns grid values psi[j1][j2]."""
    psi = [[0j] * N for _ in range(N)]
    for (k1, k2), c in coef.items():
        if c == 0:
            continue
        for j1, x1 in enumerate(GRID):
            for j2, x2 in enumerate(GRID):
                psi[j1][j2] += c * cmath.exp(1j * (k1 * x1 + k2 * x2)) / L
    return psi


def to_coef(psi):
    coef = {}
    for k1 in MODES:
        for k2 in MODES:
            s = 0j
            for j1, x1 in enumerate(GRID):
                for j2, x2 in enumerate(GRID):
                    s += psi[j1][j2] * cmath.exp(-1j * (k1 * x1 + k2 * x2))
            coef[(k1, k2)] = s * L / N ** 2
    return coef


def omega(k):
    return (KAPPA - (k[0] ** 2 + k[1] ** 2)) ** 2


def nonlinear(psi, dt):
    out = [[0j] * N for _ in range(N)]
    for j1 in range(N):
        for j2 in range(N):
            z = psi[j1][j2]
            r2 = abs(z) ** 2
            out[j1][j2] = z * cmath.exp(-1j * (-BETA * r2 + GAMMA * r2 * r2) * dt)
    return out


def step(coef, dt):
    """One Strang step: half nonlinear, full linear, half nonlinear."""
    psi = nonlinear(to_field(coef), dt / 2)
    coef = to_coef(psi)
    coef = {k: c * cmath.exp(-1j * omega(k) * dt) for k, c in coef.items()}
    return to_coef(nonlinear(to_field(coef), dt / 2))


def evolve(coef, t, steps):
    dt = t / steps
    for _ in range(steps):
        coef = step(coef, dt)
    return coef


def detector_reading(coef):
    """J = int chi |psi|^2 with chi(x) = L^-1 (1 + cos x1), by the grid rule (exact here)."""
    psi = to_field(coef)
    total = 0.0
    for j1, x1 in enumerate(GRID):
        for j2 in range(N):
            total += (1 + math.cos(x1)) / L * abs(psi[j1][j2]) ** 2
    return total * (L / N) ** 2


class ZeroModeTests(unittest.TestCase):
    def test_zero_mode_is_exact_and_reads_constant(self):
        for c in (1.0, 2.0):
            coef = {(0, 0): complex(c)}
            om = KAPPA ** 2 - BETA * c ** 2 / L ** 2 + GAMMA * c ** 4 / L ** 4
            t = 0.7
            out = evolve(coef, t, 7)
            exact = c * cmath.exp(-1j * om * t)
            self.assertAlmostEqual(abs(out[(0, 0)] - exact), 0, places=9)
            others = max(abs(v) for k, v in out.items() if k != (0, 0))
            self.assertLess(others, 1e-9)
            self.assertAlmostEqual(detector_reading(out), c ** 2 / L, places=9)
            self.assertAlmostEqual(detector_reading(coef), c ** 2 / L, places=9)

    def test_preloaded_readings_and_margin(self):
        yes, no = detector_reading({(0, 0): 2}), detector_reading({(0, 0): 1})
        threshold, margin = 5 / (2 * L), 3 / (2 * L)
        self.assertAlmostEqual(yes, threshold + margin, places=12)
        self.assertAlmostEqual(no, threshold - margin, places=12)
        self.assertAlmostEqual(abs(yes - no), 2 * margin, places=12)


class TwoModeFluxTests(unittest.TestCase):
    def test_two_mode_flux_matches_formula(self):
        a, b = 1.0 + 0j, 1j
        coef = {(0, 0): a, (1, 0): b}
        h = 1e-3
        jp = detector_reading(evolve(coef, h, 4))
        jm = detector_reading(evolve(coef, -h, 4))
        numeric = (jp - jm) / (2 * h)
        q = 1.0  # |xi_{e1}|^2 = (2 pi / L)^2
        formula = ((KAPPA - q) ** 2 - KAPPA ** 2) * (a.conjugate() * b).imag / L
        self.assertAlmostEqual(numeric, formula, places=5)
        self.assertNotAlmostEqual(formula, 0, places=6)

    def test_blind_pair_separates(self):
        two = {(0, 0): 1.0 + 0j, (1, 0): 1j}
        j0 = detector_reading(two)
        zero = {(0, 0): complex(math.sqrt(L * j0))}
        self.assertAlmostEqual(detector_reading(zero), j0, places=12)
        t = 0.2
        j_two = detector_reading(evolve(two, t, 20))
        j_zero = detector_reading(evolve(zero, t, 4))
        self.assertAlmostEqual(j_zero, j0, places=9)
        self.assertGreater(abs(j_two - j_zero), 1e-2)


if __name__ == "__main__":
    unittest.main()
