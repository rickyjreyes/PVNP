"""Fail-closed rational simulation certificate for explicitly finite input.

The mathematical radius and Euler bounds come from Phase XXV. This is a
prototype implementation, not a kernel-verified refinement. Resource caps
are explicit: an exhausted budget returns no decision, never a guessed bit.
"""
from fractions import Fraction as F
from math import ceil, isqrt
from .rational_fourier import midpoint_step, detector_box


class BudgetExceeded(ArithmeticError):
    pass


def sqrt_upper(x, bits=48):
    x = F(x)
    if x < 0:
        raise ValueError("negative square-root argument")
    scale = 1 << bits
    n = ceil(x * scale * scale)
    root = isqrt(n)
    return F(root + (root*root < n), scale)


def l1_bound(state):
    return sum((abs(F(x))+abs(F(y)) for x,y in state.values()), F(0))


def radius_upper(L, kappa, beta, gamma, B):
    # Sobolev bound C_S <= 1/L+1/2 follows from SL <= (1+L/2)^2.
    L,kappa,beta,gamma,B = map(F,(L,kappa,beta,gamma,B))
    if L <= 0 or gamma <= 0 or B < 0:
        raise ValueError("requires L>0, gamma>0, B>=0")
    C = 1/L + F(1,2)
    E = ((abs(kappa)+1)*B)**2 + 3*abs(beta)*C**2*B**4 + 5*gamma*C**4*B**6
    return (1+abs(kappa))*B + sqrt_upper(E+3*beta**2*B**2/(16*gamma))


def lf_upper(L, beta, gamma, R):
    C = 4*(1/F(L)+F(1,2))
    return 3*abs(F(beta))*C**2*R**2 + 5*abs(F(gamma))*C**4*R**4


def exp_upper(x, max_exponent):
    # exp(x) <= 2^ceil(2*x) for x>=0 because log(2)>=1/2.
    if x < 0:
        raise ValueError("nonnegative exponent required")
    e = ceil(2*x)
    if e > max_exponent:
        raise BudgetExceeded("amplification budget exceeds cap")
    return F(1 << e)


def certified_decision(initial, detector, L, kappa, beta, gamma, T, threshold,
                       margin, cutoff, *, slack=F(1,16), max_modes=10000,
                       max_steps=100000, max_bits=256, max_exponent=4096,
                       max_taylor_degree=10000):
    """Return a certificate with decision True/False/None.

    Both coefficient dictionaries are complete finite weighted states.
    All scalar inputs are rational. The cutoff is a square |k_i|<=cutoff.
    An inconclusive interval or resource cap cannot certify a decision.
    The claimed detector margin is a target tolerance, not assumed truth.
    """
    L,kappa,beta,gamma,T,threshold,margin,slack = map(
        F,(L,kappa,beta,gamma,T,threshold,margin,slack))
    if L<=0 or gamma<=0 or T<0 or margin<=0 or slack<=0 or cutoff<0:
        raise ValueError("invalid parameter or resource bound")
    if not isinstance(cutoff,int):
        raise ValueError("integer cutoff required")
    if (2*cutoff+1)**2 > max_modes:
        raise BudgetExceeded("mode cap")
    S = {(i,j) for i in range(-cutoff,cutoff+1) for j in range(-cutoff,cutoff+1)}
    zero=(F(0),F(0))
    for (i,j),(x,y) in detector.items():
        if detector.get((-i,-j),zero)!=(x,-y):
            raise ValueError("nonreal detector")
    R = radius_upper(L,kappa,beta,gamma,l1_bound(initial))
    C = l1_bound(detector)/L
    A = lf_upper(L,beta,gamma,R+slack)
    E = exp_upper(A*T,max_exponent)
    # pi<4 provides conservative frequency upper bounds.
    def omega(q):
        return (abs(kappa)+2*(8*q/L)**2)**2
    M,Q = omega(cutoff),omega(5*cutoff)
    D = A**2*(R+slack)+A*(R+slack)*(M+Q)
    # pi>3 gives an omitted-mode weight lower bound.
    K = 1+(6*(cutoff+1)/L)**2
    spatial = 4*C*R**2*E/K
    # At T=0 exact projection incurs no error if all modes were retained.
    if T==0 and set(initial)<=S:
        spatial=F(0)
    if spatial > margin/4:
        raise BudgetExceeded("spectral cutoff insufficient for target margin")
    if C==0:
        eps=slack
    else:
        eps=min(slack, margin/(4*C*(2*R+slack)))
    N=0 if T==0 else max(1,ceil(3*D*T*T*E/eps))
    if N>max_steps:
        raise BudgetExceeded("step cap")
    h=T/N if N else F(0)
    xi=eps/(3*N*E) if N else F(0)
    # Bound phase Taylor cost before evaluation. The midpoint of an
    # outward rounded angle lies near the true angle. Use a conservative
    # cap enforced by the primitive itself below (not only this estimate).
    if T*M and 2*ceil(2*(T*M+1)**2)>max_taylor_degree:
        raise BudgetExceeded("phase Taylor degree cap")
    x={k:tuple(map(F,z)) for k,z in initial.items() if k in S}
    # Exact rational initial projection: delta=0. Subsequent states dyadic.
    accumulated=F(0)
    peak_bits=0
    for i in range(N):
        for bits in range(16,max_bits+1,8):
            try:
                y,err=midpoint_step(x,S,L,kappa,beta,gamma,i*h,h,bits,
                                    max_taylor_degree=max_taylor_degree)
            except ArithmeticError:
                continue
            if err<=xi:
                break
        else:
            raise BudgetExceeded("per-step precision cap")
        x=y
        accumulated+=err
        peak_bits=max(peak_bits,bits)
    numerical_state_error=(D*h*T+N*xi)*E
    if numerical_state_error>slack:
        raise BudgetExceeded("radius certificate failed")
    numerical_readout=C*(2*R+slack)*numerical_state_error
    for bits in range(16,max_bits+1,8):
        try:
            lo,hi=detector_box(x,detector,L,kappa,T,bits,
                               max_taylor_degree=max_taylor_degree)
        except ArithmeticError:
            continue
        if hi-lo<=margin/4:
            break
    else:
        raise BudgetExceeded("detector precision cap")
    peak_bits=max(peak_bits,bits)
    error=spatial+numerical_readout
    lower,upper=lo-error,hi+error
    return {"decision": True if lower>threshold else False if upper<threshold else None,
            "interval": (lower,upper), "spatial_error": spatial,
            "numerical_state_error": numerical_state_error,
            "numerical_readout_error": numerical_readout,
            "detector_interval": (lo,hi), "modes":len(S), "steps":N,
            "peak_precision_bits":peak_bits, "radius_upper":R,
            "amplification_upper":E, "step_error_budget":xi,
            "sum_measured_step_errors":accumulated}
