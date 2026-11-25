"""Finite and numerical checks of the interwoven-Psi SAT energy model.

The functions below transcribe the definitions of `lean/PVNP/InterwovenSAT.lean`
(`Elog`, `Ecoup`, `Ecurv`, `energy`, `energySB`). The tests check the Lean
statements on small instances; they do not verify the Lean proofs.
"""
import cmath
import itertools
import math
import random
import unittest

# A literal is (variable, positive); a clause is a triple of literals.
CPOS = ((0, True), (1, True), (1, True))
CNEG = ((0, False), (1, False), (1, False))
FXOR = [CPOS, CNEG]
GPOS = ((0, True),) * 3
GNEG = ((0, False),) * 3
G = [GPOS, GNEG]


def phase(z):
    return cmath.phase(z)


def score(theta, lit):
    v, pos = lit
    eta = 1.0 if pos else -1.0
    return (1 + eta * math.cos(theta[v])) / 2


def elog(F, psi):
    theta = {i: phase(z) for i, z in psi.items()}
    total = 0.0
    for c in F:
        p = 1.0
        for lit in c:
            p *= 1 - score(theta, lit)
        total += p
    return total


def edges(F):
    out = []
    for c in F:
        out += [(c[0][0], c[1][0]), (c[0][0], c[2][0]), (c[1][0], c[2][0])]
    return out


def variables(F):
    seen = []
    for c in F:
        for v, _ in c:
            if v not in seen:
                seen.append(v)
    return seen


def ecoup(F, psi):
    return sum(1 - (psi[a] * psi[b].conjugate()).real for a, b in edges(F))


def glap(F, psi, v):
    s = 0j
    for a, b in edges(F):
        if a == v:
            s += psi[b] - psi[v]
        if b == v:
            s += psi[a] - psi[v]
    return s


def ecurv(F, psi):
    grad = sum(abs(psi[a] - psi[b]) ** 2 for a, b in edges(F))
    lap = sum(abs(glap(F, psi, v)) ** 2 for v in variables(F))
    return grad + lap


def energy(F, lam, mu, psi):
    return elog(F, psi) + lam * ecoup(F, psi) + mu * ecurv(F, psi)


def energy_sb(F, lam, mu, psi):
    sq = {i: z * z for i, z in psi.items()}
    return elog(F, psi) + lam * ecoup(F, sq) + mu * ecurv(F, sq)


def clause_val(a, c):
    return any(a[v] if pos else not a[v] for v, pos in c)


def sat(F, n):
    return any(all(clause_val(dict(enumerate(bits)), c) for c in F)
               for bits in itertools.product([False, True], repeat=n))


def field_of(bits):
    return {i: (1 + 0j) if b else (-1 + 0j) for i, b in enumerate(bits)}


def random_unit_field(rng, n):
    return {i: cmath.exp(1j * rng.uniform(-math.pi, math.pi)) for i in range(n)}


class NaiveModelTests(unittest.TestCase):
    def test_fxor_sat_and_g_unsat(self):
        self.assertTrue(sat(FXOR, 2))
        self.assertFalse(sat(G, 1))

    def test_ground_energy_quarter_at_i(self):
        psi = {0: 1j, 1: 1j}
        for lam, mu in [(0, 0), (0.1, 0), (0, 0.05), (1, 1)]:
            self.assertAlmostEqual(energy(FXOR, lam, mu, psi), 0.25, places=12)
            self.assertAlmostEqual(energy(G, lam, mu, {0: 1j}), 0.25, places=12)

    def test_fxor_energy_at_least_quarter(self):
        rng = random.Random(1311)
        for lam, mu in [(1 / 24, 0), (0, 1 / 48), (0.5, 0.5)]:
            self.assertGreaterEqual(4 * mu + 2 * lam, 1 / 12 - 1e-15)
            for _ in range(4000):
                psi = random_unit_field(rng, 2)
                self.assertGreaterEqual(energy(FXOR, lam, mu, psi), 0.25 - 1e-12)

    def test_g_energy_at_least_quarter(self):
        rng = random.Random(1312)
        for _ in range(4000):
            psi = random_unit_field(rng, 1)
            self.assertGreaterEqual(energy(G, 0.3, 0.2, psi), 0.25 - 1e-12)

    def test_satisfying_assignment_is_not_ground(self):
        lam, mu = 0.05, 0.0
        self.assertGreater(4 * mu + 2 * lam, 1 / 16)
        for bits in itertools.product([False, True], repeat=2):
            a = dict(enumerate(bits))
            if all(clause_val(a, c) for c in FXOR):
                self.assertGreater(energy(FXOR, lam, mu, field_of(bits)),
                                   energy(FXOR, lam, mu, {0: 1j, 1: 1j}))

    def test_zero_energy_fails_with_coupling(self):
        rng = random.Random(1313)
        lam, mu = 0.01, 0.0
        best = min(energy(FXOR, lam, mu, random_unit_field(rng, 2)) for _ in range(20000))
        self.assertGreater(best, 0)


class SignBlindModelTests(unittest.TestCase):
    def random_formula(self, rng, n, m):
        return [tuple((rng.randrange(n), rng.random() < 0.5) for _ in range(3)) for _ in range(m)]

    def test_binary_fields_cost_only_logic(self):
        rng = random.Random(1314)
        for _ in range(200):
            F = self.random_formula(rng, 4, 6)
            for bits in itertools.product([False, True], repeat=4):
                psi = field_of(bits)
                self.assertAlmostEqual(energy_sb(F, 0.7, 0.3, psi), elog(F, psi), places=12)

    def test_sat_iff_zero_ground_energy_on_binary_fields(self):
        rng = random.Random(1315)
        for _ in range(300):
            n = rng.randrange(1, 5)
            F = self.random_formula(rng, n, rng.randrange(1, 9))
            emin_binary = min(energy_sb(F, 0.5, 0.5, field_of(bits))
                              for bits in itertools.product([False, True], repeat=n))
            self.assertEqual(sat(F, n), emin_binary < 1e-12)

    def test_unsat_gap_on_random_fields(self):
        rng = random.Random(1316)
        checked = 0
        for _ in range(300):
            n = rng.randrange(1, 4)
            F = self.random_formula(rng, n, rng.randrange(4, 12))
            if sat(F, n):
                continue
            checked += 1
            for _ in range(200):
                self.assertGreaterEqual(energy_sb(F, 0.4, 0.4, random_unit_field(rng, n)),
                                        1 / 8 - 1e-12)
        self.assertGreater(checked, 0)

    def test_sign_readout_below_eighth(self):
        rng = random.Random(1317)
        hits = 0
        for _ in range(3000):
            n = 3
            F = self.random_formula(rng, n, 4)
            psi = random_unit_field(rng, n)
            if energy_sb(F, 0.2, 0.2, psi) < 1 / 8:
                hits += 1
                a = {i: psi[i].real >= 0 for i in range(n)}
                self.assertTrue(all(clause_val(a, c) for c in F))
        self.assertGreater(hits, 0)


if __name__ == "__main__":
    unittest.main()
