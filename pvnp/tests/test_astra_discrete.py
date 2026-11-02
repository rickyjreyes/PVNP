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


def pair(x, w):
    out = []
    for b in x:
        out += [True, b]
    return out + [False] + list(w)


def unpair_tm(M, y, limit):
    """Transcription of `TM.uδ` (lean/PVNP/PSubsetNP.lean). M = (delta, start, acc, rej, blank, inp)."""
    delta, start, acc, rej, blank, inp = M
    BL = ("g", blank)
    tape = defaultdict(lambda: BL)
    for i, b in enumerate(y):
        tape[i] = ("raw", b)

    def uval(z):
        if z[0] == "g":
            return z[1]
        if z[0] == "raw":
            return inp[z[1]]
        return blank  # erased

    q, head = ("E",), 0
    for t in range(limit + 1):
        if q[0] == "sim" and acc[q[1]]:
            return t, True
        if q[0] == "sim" and rej[q[1]]:
            return t, False
        if q[0] == "rejHalt":
            return t, False
        z = tape[head]
        k = q[0]
        if k == "E":
            if z == ("raw", True):
                q, head = ("Skip",), head + 1
            elif z == ("raw", False):
                tape[head] = ("erased",); q, head = ("W",), head + 1
            else:
                q = ("rejHalt",)
        elif k == "Skip":
            if z[0] == "raw":
                q, head = ("E",), head + 1
            else:
                q = ("rejHalt",)
        elif k == "W":
            if z[0] == "raw":
                tape[head] = ("erased",); head += 1
            else:
                q, head = ("Back",), head - 1
        elif k == "Back":
            if z[0] == "g":
                q, head = ("Go",), head + 1
            else:
                head -= 1
        elif k == "Go":
            q, head = ("sim", start), head + 1
        elif k == "sim":
            d = delta.get((q[1], uval(z)))
            if d is None:
                return None
            q2, a, mv = d
            tape[head] = ("g", a)
            if mv == 0:
                q = ("sim", q2)
            elif mv == 1:
                q, head = ("midR", q2), head + 1
            else:
                q, head = ("midL", q2), head - 1
        elif k in ("midR", "midL"):
            q, head = ("sim", q[1]), head + (1 if k == "midR" else -1)
    return None


def run_tm(M, x, limit):
    delta, start, acc, rej, blank, inp = M
    tape = defaultdict(lambda: blank)
    for i, b in enumerate(x):
        tape[i] = inp[b]
    q, head = start, 0
    for t in range(limit + 1):
        if acc[q]:
            return t, True
        if rej[q]:
            return t, False
        d = delta.get((q, tape[head]))
        if d is None:
            return None
        q, a, mv = d
        tape[head] = a
        head += mv
    return None


class TestUnpair(unittest.TestCase):
    def test_random_machines(self):
        rng = random.Random(11)
        checked = 0
        for _ in range(300):
            k, m = 4, 3
            acc = {q: q == 2 for q in range(k)}
            rej = {q: q == 3 for q in range(k)}
            delta = {}
            for q in range(2):
                for a in range(m):
                    delta[(q, a)] = (rng.randrange(k), rng.randrange(m), rng.choice([-1, 0, 1]))
            M = (delta, 0, acc, rej, 0, {False: 1, True: 2})
            for n in range(0, 4):
                x = [rng.random() < 0.5 for _ in range(n)]
                base = run_tm(M, x, 40)
                if base is None:
                    continue
                s, b = base
                for wl in range(0, 3):
                    w = [rng.random() < 0.5 for _ in range(wl)]
                    y = pair(x, w)
                    bound = 2 * len(y) + 3 + 2 * s
                    res = unpair_tm(M, y, bound)
                    self.assertEqual(res[1], b)
                    self.assertLessEqual(res[0], bound)
                    checked += 1
                # malformed inputs are rejected
                for bad in ([], [True], [True, True], [True, False, True]):
                    res = unpair_tm(M, bad, 2 * len(bad) + 3)
                    self.assertEqual(res[1], False)
        self.assertGreater(checked, 100)


if __name__ == "__main__":
    unittest.main()
