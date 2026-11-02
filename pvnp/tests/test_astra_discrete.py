"""Executable cross-checks of the ASTRA Lean constructions (not proofs).

* The alternating shifted-sweep TM of `lean/PVNP/WCCtoTM.lean` reproduces the
  first-answer output of random finite quiescent radius-one WCCs, within the
  proved time bound 1 + (s+1)(n + 2s + 5).
* The compiled TM -> WCC rule of `lean/PVNP/TMtoWCC.lean` tracks random TMs
  step for step.
* Fourier coefficients used in `lean/PVNP/FourierReceiverProjection.lean`.
* Parity boundary identity of `lean/PVNP/PhysicalComplexityClasses.lean`.
"""
import itertools
import random
import unittest
from collections import defaultdict


def ca_out(cfg, blank, acc, rej):
    vals = set(cfg.values()) | {blank}
    if any(acc[v] for v in vals):
        return True
    if any(rej[v] for v in vals):
        return False
    return None


def ca_step(cfg, blank, rule):
    keys = set()
    for i in cfg:
        keys |= {i - 1, i, i + 1}
    new = {}
    for i in keys:
        v = rule[(cfg.get(i - 1, blank), cfg.get(i, blank), cfg.get(i + 1, blank))]
        if v != blank:
            new[i] = v
    return new


def ca_first_answer(x, A, limit):
    blank, rule, inp, origin, acc, rej = A
    cfg = {}
    cfg[0] = origin[x[0] if x else None]
    for i in range(1, len(x)):
        cfg[i] = inp[x[i]]
    cfg = {k: v for k, v in cfg.items() if v != blank}
    for s in range(limit + 1):
        o = ca_out(cfg, blank, acc, rej)
        if o is not None:
            return s, o
        cfg = ca_step(cfg, blank, rule)
    return None


def sweep_tm(x, A, limit):
    """Direct transcription of `WCC.simδ` with tape symbols None / ('raw',b) / ('cell',s)."""
    blank, rule, inp, origin, acc, rej = A
    tape = defaultdict(lambda: None)
    for i, b in enumerate(x):
        tape[i] = ("raw", b)

    def val(sym):
        if sym is None:
            return blank
        return inp[sym[1]] if sym[0] == "raw" else sym[1]

    q = ("pre",)
    head = 0
    for t in range(limit + 1):
        if q[0] == "yes":
            return t, True
        if q[0] == "no":
            return t, False
        z = tape[head]
        if q[0] == "pre":
            bit = z[1] if z is not None and z[0] == "raw" else None
            tape[head] = ("cell", origin[bit])
            q = ("rs", None, None, acc[blank], rej[blank])
            continue
        kind, xx, y, fa, fr = q
        if y is None and z is None:
            if fa:
                q = ("yes",)
                continue
            if fr:
                q = ("no",)
                continue
            new = rule[(val(xx), val(y), val(z))] if kind == "rs" else rule[(val(z), val(y), val(xx))]
            tape[head] = ("cell", new)
            q = ("ls" if kind == "rs" else "rs", None, None, acc[blank], rej[blank])
            continue
        new = rule[(val(xx), val(y), val(z))] if kind == "rs" else rule[(val(z), val(y), val(xx))]
        tape[head] = ("cell", new)
        q = (kind, y, z, fa or acc[val(z)], fr or rej[val(z)])
        head += 1 if kind == "rs" else -1
    return None


def random_wcc(rng, k):
    S = list(range(k))
    blank = 0
    rule = {}
    for a, b, c in itertools.product(S, repeat=3):
        rule[(a, b, c)] = 0 if (a, b, c) == (0, 0, 0) else rng.choice(S)
    inp = {False: rng.choice(S), True: rng.choice(S)}
    origin = {None: rng.choice(S[1:]), False: rng.choice(S[1:]), True: rng.choice(S[1:])}
    acc = {s: False for s in S}
    rej = {s: False for s in S}
    acc[k - 1] = True
    rej[k - 2] = True
    return blank, rule, inp, origin, acc, rej


class TestSweepSimulator(unittest.TestCase):
    def test_random_wcc(self):
        rng = random.Random(20261102)
        checked = 0
        for _ in range(300):
            A = random_wcc(rng, rng.choice([3, 4, 5]))
            for n in range(0, 5):
                x = [rng.random() < 0.5 for _ in range(n)]
                ca = ca_first_answer(x, A, 12)
                if ca is None:
                    continue
                s, b = ca
                bound = 1 + (s + 1) * (n + 2 * s + 5)
                tm = sweep_tm(x, A, bound)
                self.assertIsNotNone(tm)
                self.assertEqual(tm[1], b)
                self.assertLessEqual(tm[0], bound)
                checked += 1
        self.assertGreater(checked, 100)


def tm_to_wcc_check(rng):
    k, m = 3, 3
    delta = {}
    for q in range(k):
        for a in range(m):
            delta[(q, a)] = None if q == k - 1 else (rng.randrange(k), rng.randrange(m), rng.choice([-1, 0, 1]))
    tape = defaultdict(int)
    for i in range(4):
        tape[i] = rng.randrange(m)
    q, head = 0, 0
    cells = {i: (tape[i], q if i == head else None) for i in range(-30, 31)}
    for _ in range(20):
        # compiled rule
        def rule(l, c, r):
            if c[1] is not None:
                d = delta[(c[1], c[0])]
                if d is None:
                    return c
                q2, a, mv = d
                return (a, q2) if mv == 0 else (a, None)
            if l[1] is not None:
                d = delta[(l[1], l[0])]
                if d is not None and d[2] == 1:
                    return (c[0], d[0])
            if r[1] is not None:
                d = delta[(r[1], r[0])]
                if d is not None and d[2] == -1:
                    return (c[0], d[0])
            return c
        cells = {i: rule(cells.get(i - 1, (0, None)), cells[i], cells.get(i + 1, (0, None)))
                 for i in cells}
        d = delta[(q, tape[head])]
        if d is not None:
            q2, a, mv = d
            tape[head] = a
            q, head = q2, head + mv
        expect = {i: (tape[i], q if i == head else None) for i in cells}
        if any(abs(i) > 25 for i in [head]):
            break
        for i in range(-25, 26):
            assert cells[i] == expect[i], (i, cells[i], expect[i])


class TestCompiler(unittest.TestCase):
    def test_random_tm(self):
        rng = random.Random(7)
        for _ in range(200):
            tm_to_wcc_check(rng)


class TestFourier(unittest.TestCase):
    def test_modes(self):
        u = {1: 1, 2: 1}
        ubar = {-k: v for k, v in u.items()}

        def conv(f, g):
            h = defaultdict(int)
            for a, x in f.items():
                for b, y in g.items():
                    h[a + b] += x * y
            return h
        cubic = conv(conv(u, u), ubar)
        quintic = conv(conv(conv(conv(u, u), u), ubar), ubar)
        self.assertEqual((cubic[3], cubic[4]), (1, 0))
        self.assertEqual((quintic[3], quintic[4]), (5, 1))


class TestParity(unittest.TestCase):
    def test_boundary(self):
        for n in range(1, 7):
            count = 0
            for x in itertools.product([0, 1], repeat=n):
                for i in range(n):
                    y = list(x)
                    y[i] ^= 1
                    count += (sum(x) % 2) != (sum(y) % 2)
            self.assertEqual(count, n * 2 ** n)


if __name__ == "__main__":
    unittest.main()
