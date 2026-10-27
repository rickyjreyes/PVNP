# Exact expanding-domain Hamiltonian mode: why input-size constants matter

**PVNP rigorous follow-up, 27 October 2026.** This is an explicit mathematical **countermodel to a domain-independent curvature coefficient**, not a SAT lower bound, and not a claim about every physical realization. The result supplements, rather than supersedes, the fixed-domain fixed-mass nodal coercivity paper.

## 1. Source PDE and exact solution

Take the actual separately maintained projection-free WCT Hamiltonian
\[
i\partial_t u=(\Delta+\kappa)^2u-\beta|u|^2u+\gamma|u|^4u,
\qquad \kappa>0,\ \beta,\gamma>0.
\]
It is implemented in [wct-pde](https://github.com/rickyjreyes/wct-pde/blob/main/src/wct_pde/projection_free.py), not identified with the full S004 parent action.

Let \(\Omega_L=(\mathbb R/L\mathbb Z)^2\) with volume \(V=L^2\).
Fix mass \(M>0\) independent of \(L\). Take
\[
k_L=(2\pi/L,0),\quad q_L=|k_L|^2=4\pi^2/V,\quad
s_L=M/V
\]
and let
\[
e_{k_L}(x)=V^{-1/2}e^{i k_L\cdot x},\quad
u_L(x,t)=\sqrt M\,e_{k_L}(x)\,e^{-i\omega_Lt},\qquad
\omega_L=(\kappa-q_L)^2-\beta s_L+\gamma s_L^2.
\]
This is an **exact solution**: \(\Delta u_L=-q_Lu_L\), while the nonlinear factor is a constant because \(|u_L|^2=s_L\). The left side equals \(\omega_L u_L\), precisely the right side.

The mass remains exactly
\[
\|u_L(t)\|_2^2=M.
\]
The maintained Hamiltonian equals
\[
H_L=M(\kappa-q_L)^2-\frac{\beta M^2}{2V}
+\frac{\gamma M^3}{3V^2}
\longrightarrow \kappa^2 M.
\]
It is therefore bounded **uniformly for all sufficiently large L**.
This does not assert exactly the same numerical Hamiltonian at every L;
it proves a stronger counterexample to any proposed estimate based only
on *one uniform Hamiltonian upper rail*.

## 2. Exact failure of domain-independent density-weight coercivity

The separately defined WCT density-weighted curvature functional is
\[
Q_{\varepsilon,\alpha}[u]=
\int_{\Omega_L}
\frac{|u|^2}{(|u|^2+\varepsilon^2e^{-2\alpha|u|^2})^2}
|\Delta u|^2\,dx,\quad \varepsilon>0,\quad\alpha\ge0.
\]
For the exact plane-wave solution, the weight is spatially constant, so
\[
\|\Delta u_L\|_2^2=Mq_L^2=\frac{16\pi^4M}{V^2},
\quad
\frac{Q_{\varepsilon,\alpha}[u_L]}{\|\Delta u_L\|_2^2}
= \frac{M/V}{(M/V+\varepsilon^2e^{-2\alpha M/V})^2}.
\]
For every fixed \(\alpha\ge0\) and \(\varepsilon>0\), as \(V\to\infty\),
\[
\frac{Q_{\varepsilon,\alpha}[u_L]}{\|\Delta u_L\|_2^2}
\sim \frac{M}{\varepsilon^4V}\longrightarrow0,
\]
and
\[
Q_{\varepsilon,\alpha}[u_L]\sim
\frac{16\pi^4M^2}{\varepsilon^4 V^3}.
\]
In particular, **no \(c>0\) uniform in domain area** can satisfy
\(Q_{\varepsilon,\alpha}[u]\ge c\|\Delta u\|_2^2\)
for all exact trajectories with one fixed positive mass and one common
upper Hamiltonian rail. This counterexample does not even need nodes.

This does **not refute** the fixed-domain nodal coercivity theorem:
its constant \(c_*(\Omega,M,H_*,\varepsilon)\) is explicitly allowed to
depend on \(\Omega\), and here \(\Omega_L\) changes.

## 3. Coherent phase readout within fixed time

Use the L²-normalized spatial coherent detector
\(\chi_L=e_{k_L}\), of zero mean and unit L² norm.
For the exact solution,
\[
Z_{\chi_L}(t)=\langle\chi_L,u_L(t)\rangle
=\sqrt M\,e^{-i\omega_Lt}.
\]
Because \(\omega_L\to\kappa^2>0\), choosing
\(T=\pi/\kappa^2\) gives the fixed, nonvanishing asymptotic contrast
\[
\delta_L=|Z_{\chi_L}(T)-Z_{\chi_L}(0)|
\longrightarrow 2\sqrt M .
\]
Nevertheless
\[
\int_0^T Q_{\varepsilon,\alpha}[u_L(t)]\,dt
=T Q_{\varepsilon,\alpha}[u_L]\longrightarrow0.
\]
So an unconditional positive density-curvature cost for a **coherent
observable's time-change** cannot be made uniform in a growing device
even with fixed mass, bounded Hamiltonian and fixed detection time.

The globally phase-safe *comparison* functional obeys
\[
C_{\mathrm{safe}}[u_L]
=\frac{Mq_L^2}{s_L+\varepsilon^2}=O(V^{-2}),
\]
and also tends to zero. The previous finite-time theorem remains valid
because its detector constant involves the first positive spectral gap
\(\lambda_1=q_L\), so \(K_{\chi_L}\) grows as \(O(V)\).
Its bound is therefore consistent with the example.

**Readout caution:** \(\chi_L\) coherently measures an entire expanding
spatial Fourier mode against a phase reference. This is a global
detector, not a physically modeled local receiver. A single trajectory
whose observable changes in time is not, by itself, a two-message
causal communication protocol. These are deliberate model limitations,
not assumptions that may be silently dropped.

## 4. Lean and executable sanity check

For the normalized choice \(M=1\), \(\varepsilon=1\),
\(\alpha=0\), put \(V\ge1\). The curvature-to-Laplacian ratio is
\[
F(1/V)=\frac{V}{(V+1)^2}\le\frac1V.
\]
The Lean module [ExpandingDomain.lean](../../lean/PVNP/ExpandingDomain.lean)
checks the weight inequality and its absence of a positive
domain-independent floor, plus a bound on the normalized plane-wave
Hamiltonian for \(0\le q\le1\), \(V\ge1\). The full complex PDE solution
and Fourier scaling are conventional mathematical proofs in this note,
not Lean-formalized continuum results.

A standard-library executable test
[check_expanding_mode.py](../tests/check_expanding_mode.py)
evaluates the exact closed-form formulas for increasing \(L\) and
checks mass, bounded Hamiltonian, phase contrast and the curvature
ratio. This is a numerical sanity check, not a substitute for proof.

## 5. Implication for the complete PVNP proof program

Fixed-domain fixed-resource nodal coercivity is a worthwhile theorem.
But it does **not** imply a uniform cost of computation for a family of
devices where domain, spectral gap, source/detector geometry, or
precision varies with SAT input length \(n\). That bridge needs an
explicit **uniform scaling theorem** with all resource growth charged.

This countermodel refutes a **stronger-than-established uniform
coercivity claim**, not a restricted physical-WCC complexity
separation and not any version of classical P versus NP.
