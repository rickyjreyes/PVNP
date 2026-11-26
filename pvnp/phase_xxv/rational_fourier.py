"""Exact-rational outward-rounded evaluator for the frozen torus field.

Prototype, not yet a Lean refinement. All intervals are dyadic after each
primitive. The phase uses a rational Taylor polynomial plus an analytic
remainder bound, not a floating-point library call.
"""
from fractions import Fraction as F
from math import ceil, floor


class Arithmetic:
    def __init__(self, bits, max_taylor_degree=None):
        if bits < 1:
            raise ValueError("positive precision required")
        self.bits = bits
        self.max_taylor_degree = max_taylor_degree
        self.scale = 1 << bits

    def box(self, lo, hi=None):
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        if lo > hi:
            raise ValueError("reversed interval")
        return F(floor(lo*self.scale), self.scale), F(ceil(hi*self.scale), self.scale)

    def add(self, a, b):
        return self.box(a[0]+b[0], a[1]+b[1])

    def neg(self, a):
        return -a[1], -a[0]

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def mul(self, a, b):
        vals = [x*y for x in a for y in b]
        return self.box(min(vals), max(vals))

    def div(self, a, b):
        if b[0] <= 0 <= b[1]:
            raise ArithmeticError("denominator interval contains zero")
        vals = [x/y for x in a for y in b]
        return self.box(min(vals), max(vals))

    def real(self, x):
        return self.box(x), self.box(0)

    def cadd(self, a, b):
        return self.add(a[0], b[0]), self.add(a[1], b[1])

    def cmul(self, a, b):
        return (self.sub(self.mul(a[0], b[0]), self.mul(a[1], b[1])),
                self.add(self.mul(a[0], b[1]), self.mul(a[1], b[0])))

    def scale_c(self, a, b):
        return self.mul(a[0], b), self.mul(a[1], b)

    def pi(self):
        # Machin's identity; alternating arctan series bounds.
        def atan_bounds(d):
            n = self.bits + 5
            s = sum((F((-1)**j, (2*j+1)*d**(2*j+1)) for j in range(n)), F(0))
            nxt = F((-1)**n, (2*n+1)*d**(2*n+1))
            return min(s, s+nxt), max(s, s+nxt)
        a, b = atan_bounds(5), atan_bounds(239)
        return self.box(16*a[0]-4*b[1], 16*a[1]-4*b[0])

    def exp_i(self, interval):
        # Evaluate at the exact rational midpoint; exp(i x) is 1-Lipschitz.
        x = (interval[0]+interval[1])/2
        rad = (interval[1]-interval[0])/2
        # For degree 2r-1, remainder <= |x|^(2r)/(2r)! <= (x*x/r)^r.
        r = max(self.bits+2, ceil(2*x*x), 1)
        if self.max_taylor_degree is not None and 2*r-1 > self.max_taylor_degree:
            raise ArithmeticError("phase Taylor degree cap")
        term = F(1)
        re, im = F(1), F(0)
        for j in range(1, 2*r):
            term *= x/j
            if j % 4 == 0:
                re += term
            elif j % 4 == 1:
                im += term
            elif j % 4 == 2:
                re -= term
            else:
                im -= term
        err = rad + F(1, 1 << r)
        return self.box(max(-1, re-err), min(1, re+err)), self.box(max(-1, im-err), min(1, im+err))


def field_box(state, support, L, kappa, beta, gamma, t, bits, *, max_taylor_degree=None):
    """Enclose P_S Gf(t,state) for a dyadic/rational weighted coefficient state.

    state maps (integer,int) to (rational real,rational imaginary).
    Parameters and time are exact rational inputs. Missing modes are zero.
    Output is a mapping to rectangular complex intervals.
    """
    a = Arithmetic(bits, max_taylor_degree)
    S = set(support)
    if not set(state) <= S or F(L) <= 0:
        raise ValueError("invalid support or torus length")
    l, kap, t = a.box(L), a.box(kappa), a.box(t)
    invL = a.div(a.box(1), l)
    qscale = a.mul(a.mul(a.box(2), a.pi()), invL)
    qscale = a.mul(qscale, qscale)

    def weight_phase(k, reverse=False):
        q = a.mul(qscale, a.box(k[0]**2+k[1]**2))
        w = a.add(a.box(1), q)
        d = a.sub(kap, q)
        omega = a.mul(d, d)
        angle = a.mul(omega, t)
        return w, a.exp_i(angle if reverse else a.neg(angle))

    def conv(u, v):
        out = {}
        for (kx, ky), x in u.items():
            for (jx, jy), y in v.items():
                k = (kx+jx, ky+jy)
                out[k] = a.cadd(out.get(k, a.real(0)), a.cmul(x, y))
        return {k: a.scale_c(z, invL) for k, z in out.items()}

    co = {}
    for k, (re, im) in state.items():
        w, phase = weight_phase(k)
        invw = a.div(a.box(1), w)
        co[k] = a.scale_c(a.cmul((a.box(re), a.box(im)), phase), invw)
    conjugate = {(-k[0], -k[1]): (z[0], a.neg(z[1])) for k, z in co.items()}
    p2 = conv(co, co)
    p3 = conv(p2, conjugate)
    p5 = conv(conv(conv(p2, co), conjugate), conjugate)
    out = {}
    for k in sorted(S):
        w, phase = weight_phase(k, True)
        z = a.cadd(a.scale_c(p3.get(k, a.real(0)), a.box(-F(beta))),
                   a.scale_c(p5.get(k, a.real(0)), a.box(gamma)))
        z = a.cmul(a.scale_c(z, w), phase)
        out[k] = z[1], a.neg(z[0])  # multiply by -i
    return out


def midpoint_step(state, support, L, kappa, beta, gamma, t, h, bits, *, max_taylor_degree=None):
    """Return rounded Euler step and rational upper bound on its H²-coordinate defect.

    The L1 sum of rectangular component errors bounds the Euclidean norm.
    A caller must reject the step if this certificate exceeds its budget.
    """
    a = Arithmetic(bits, max_taylor_degree)
    field = field_box(state, support, L, kappa, beta, gamma, t, bits,
                      max_taylor_degree=max_taylor_degree)
    result, error = {}, F(0)
    for k, z in field.items():
        old = state.get(k, (F(0), F(0)))
        coords = []
        for j in range(2):
            target = a.add(a.box(old[j]), a.mul(a.box(h), z[j]))
            mid = (target[0]+target[1])/2
            rounded = F(round(mid*a.scale), a.scale)
            error += max(abs(rounded-target[0]), abs(rounded-target[1]))
            coords.append(rounded)
        result[k] = tuple(coords)
    return result, error


def detector_box(state, detector, L, kappa, t, bits, *, max_taylor_degree=None):
    """Enclose Jdet at U(t)state; detector uses weighted Fourier coordinates.

    The detector dictionary is the COMPLETE finite detector. Missing
    coefficients are zero, not unknown. The real-field symmetry is checked.
    Only its coefficients at differences of occupied state modes are used.
    """
    a = Arithmetic(bits, max_taylor_degree)
    L = F(L)
    if L <= 0:
        raise ValueError("positive torus length required")
    zero = (F(0), F(0))
    for (k, j), (re, im) in detector.items():
        if detector.get((-k, -j), zero) != (re, -im):
            raise ValueError("detector must represent a real field")
    invL = a.div(a.box(1), a.box(L))
    qscale = a.mul(a.mul(a.box(2), a.pi()), invL)
    qscale = a.mul(qscale, qscale)
    weight_cache = {}

    def frequency(k):
        if k not in weight_cache:
            q = a.mul(qscale, a.box(k[0]**2+k[1]**2))
            weight_cache[k] = q, a.add(a.box(1), q)
        return weight_cache[k]

    u = {}
    for k, z in state.items():
        q, w = frequency(k)
        d = a.sub(a.box(kappa), q)
        angle = a.neg(a.mul(a.mul(d, d), a.box(t)))
        u[k] = a.scale_c(a.cmul((a.box(z[0]), a.box(z[1])), a.exp_i(angle)),
                         a.div(a.box(1), w))
    chi = {}
    total = a.box(0)
    for k, z in u.items():
        zbar = z[0], a.neg(z[1])
        for j, y in u.items():
            d = k[0]-j[0], k[1]-j[1]
            if d not in detector:
                continue
            if d not in chi:
                w = frequency(d)[1]
                q = detector[d]
                chi[d] = a.scale_c((a.box(q[0]), a.box(q[1])), a.div(a.box(1), w))
            term = a.cmul(zbar, a.cmul(chi[d], y))[0]
            total = a.add(total, term)
    return a.mul(total, invL)
