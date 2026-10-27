# Physical curvature versus information transport: a bridge and two no-go tests

**PVNP research audit · 27 October 2026 · Model-relative, not a proof of P≠NP**

The proposed inference
\[
\text{information must cross an interface}\quad\Longrightarrow\quad
C_{\Theta,\varepsilon}\ge \kappa\,\text{bits}
\]
is **false without additional admissibility assumptions**, even when the
receiver can distinguish bit values exactly. This note derives a sharp
positive estimate under fixed endpoint/contrast assumptions and a full
communication-to-curvature lower bound in a concrete discrete implementation.

## 1. Zero-curvature profiles with distinct outputs

On a one-dimensional channel \(0\le x\le L\), let
\(\psi_b(x)=1+b x\), \(b\in\{0,1\}\), and \(\varepsilon>0\).
Then \(\psi_b''=0\), so
\[
C_{\Theta,\varepsilon}[\psi_b]=
\int_0^L \left|\frac{\psi_b''}{\psi_b+\varepsilon}\right|^2 dx=0.
\]
But \(\psi_0(L)=1\) and \(\psi_1(L)=1+L\). In particular, different
receiver values do **not** imply positive curvature. This is a static
counterexample, not a signal sent causally after a shared initial state.
It identifies the failure of an unrestricted observability-to-curvature step.

## 2. A causal wave that arbitrarily lowers integrated curvature by taking more time

For a stronger physically dynamic test, fix channel length \(L>0\),
propagation speed \(c>0\), baseline \(u_0>0\), contrast \(\delta>0\),
and a smooth nondecreasing switching function \(h:\mathbb R\to[0,1]\)
with \(h(s)=0\) for \(s\le0\) and \(h(s)=1\) for \(s\ge1\).
For every ramp width \(W>0\) set
\[
\psi_W(x,t)=u_0+\delta\,h\!\left(\frac{ct-x}{W}\right),
\quad 0\le x\le L,\quad
0\le t\le T_W=\frac{L+W}{c}.
\]
Then \(\partial_t^2\psi_W=c^2\partial_x^2\psi_W\) exactly.
At \(t=0\), \(\psi_W(x,0)=u_0\) throughout the channel; hence the
receiver is not preloaded with the message. At final time \(T_W\),
\(\psi_W(L,T_W)=u_0+\delta\). The sender controls the time-dependent
boundary value \(x=0\).

The spacetime-integrated shifted curvature cost is bounded by
\[
\begin{aligned}
\mathcal C_W
&=\int_0^{T_W}\int_0^L
 \left|\frac{\psi_{W,xx}}{\psi_W+\varepsilon}\right|^2 dx\,dt \\
&\le \frac{\delta^2 L}{c(u_0+\varepsilon)^2 W^3}
    \int_{\mathbb R}|h''(s)|^2\,ds.
\end{aligned}
\]
For each x, this follows from \(\psi_{W,xx}=\delta W^{-2}
h''((ct-x)/W)\), the substitution \(s=(ct-x)/W\), and nonnegativity of
the denominator. Thus **the infimum of this curvature cost for a fixed
detectable bit is zero as T→∞**. This rules out any strictly positive
time-independent curvature cost per bit in the unforced linear-wave
model with unrestricted transmission time.

This says nothing about the energy of the source actuator, receiver
noise, precision, damping, fixed deadlines, or nonlinear WCT rails:
those were not charged to the curvature functional.

## 3. Sharp positive fixed-endpoint curvature trace inequality

Let \(u\in H^2(0,L)\), \(u(0)=u(L)=0\), \(u(L/2)\ge\delta>0\),
and \(0\le u(x)\le M\) a.e. With the Dirichlet Green kernel
\[
G(x,y)=\frac{\min(x,y)(L-\max(x,y))}{L},
\]
we have
\[
u(L/2)=-\int_0^L G(L/2,y)u''(y)\,dy.
\]
The squared kernel norm evaluates exactly to
\[
\int_0^L G(L/2,y)^2dy=\frac{L^3}{48}.
\]
Cauchy–Schwarz therefore gives the **sharp** estimate
\[
\int_0^L|u''|^2dx\ge\frac{48\delta^2}{L^3}.
\]
For any fixed \(\varepsilon>0\), since \(0\le u\le M\),
\[
\boxed{\quad
\int_0^L\left|\frac{u''}{u+\varepsilon}\right|^2dx
\ge \frac{48\delta^2}{(M+\varepsilon)^2L^3}.\quad}
\]
The underlying \(L^2\)-derivative inequality has the optimal constant
48 (take \(u''\) proportional to \(-G(L/2,\cdot)\)).
The weighted bound need not be optimal.

**Crucial limitations:** Both endpoint values are prescribed; this
models an internally driven or preconfigured channel snapshot, not
ordinary boundary-driven transmission to the receiving endpoint.
The amplitude upper bound prevents evading the lower bound by adding
a large positive background. Changing the boundary conditions,
introducing uncharged constant/affine modes, or allowing indefinite
transmission time defeats a universal curvature-only inequality.

## 4. Lean-checked three-node physical realization and deterministic communication

For each Boolean bit b, use an independently anchored three-node
channel with endpoint values 0 and middle amplitude \(a_b=1+b\).
Choose regularizer \(\varepsilon=1\). At the middle node
\(\Delta_d a_b=-2a_b\), giving
\[
c_b=\left(\frac{2a_b}{a_b+1}\right)^2
=\begin{cases}1 & b=0,\\16/9 & b=1.\end{cases}
\]
Thus \(c_b\ge1\) **for either transmitted bit**. With q physically
separate paid slots, the snapshot curvature cost is at least q.
If an exact deterministic split-input protocol for DISJ_n produces
q-bit *fixed-length* transcripts and protocol transcripts satisfy
the standard rectangle condition, the previously formalized fooling
set proves \(2^n\le 2^q\), hence \(q\ge n\).

Combining these now yields the new model-relative theorem:
\[
\boxed{\quad C_{\rm anchored\,slots}(\tau)\ge q\ge n.\quad}
\]
This is a direct bridge from a real communication lower bound to
the explicitly defined physical *discrete curvature* of its fixed-slot
representation. The proof has no ad hoc universal claim about WCT PDEs.

**Assumptions doing the work:** Finite binary transcripts, distinct
anchored cells, zero endpoint values in *every* channel, a positive
amplitude bias even for bit 0, a spatial snapshot cost summed over all
slots, no analog/higher-radix compression, and charging idle/padded slots.
Removing these conditions can change the cost; especially, this is
not a universal bit-energy cost for all implementations of the protocol.

## 5. Verdict for the PVNP research program

- **No-go:** Positive per-bit curvature cost from *distinguishability alone* is false; static affine fields and slow causal waves demonstrate two independent failure mechanisms.
- **Proved analytically:** Fixed-endpoint, bounded-amplitude channels have a positive \(H^2\) trace cost with sharp unweighted constant 48.
- **Lean target:** For fixed-anchor three-node implementations, the communication fooling-set bound implies a linear snapshot-curvature lower bound.
- **Still open:** Extend the interface theorem to a user-defined physically faithful WCT PDE with verified source energy, noise resilience, bounded-time detection, locality and precision costs. Neither an exponential SAT lower bound nor P≠NP follows.

## References

- [PVNP deterministic communication theorem](../../lean/PVNP/Communication.lean).
- [Previous polynomial-cost curvature countermodel](curvature-barrier-audit.md).
- [Princeton lecture notes on rectangle/fooling-set arguments](https://www.cs.princeton.edu/~smattw/Teaching/521fa17lec20.pdf).
- [Toronto 1D wave equation boundary-value notes](https://www.math.utoronto.ca/courses/apm346h1/20159/PDE-textbook/Chapter2/S2.6.html).
