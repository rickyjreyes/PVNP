# Deriving finite-time readout costs from maintained WCT PDEs

**Research date:** 2026-10-27. **Status:** A conditional continuum *transport theorem* is proved analytically from the declared projection-free Hamiltonian PDE; the finite algebraic steps are checked in Lean. This is not an all-solver curvature lower bound, and does not prove physical or classical P ≠ NP.

## 1. Source-model audit (do not conflate models)

We used the two explicitly distinct models maintained in
[rickyjreyes/wct-pde README](https://github.com/rickyjreyes/wct-pde/blob/main/README.md)
and
[projection_free.py](https://github.com/rickyjreyes/wct-pde/blob/main/src/wct_pde/projection_free.py).

**H (projection-free Hamiltonian rail, complex field):**
\[
 i\partial_t\psi=(\Delta+\kappa)^2\psi
 -\beta|\psi|^2\psi+\gamma|\psi|^4\psi,\qquad
 \kappa=k_\star^2\ge0,\quad\beta,\gamma>0.
\]
Its natural periodic-domain conserved quantities for smooth unforced solutions are
\[
 P^2=\int_\Omega|\psi|^2,\qquad
 H=\int_\Omega\left[|(\Delta+\kappa)\psi|^2
 -\frac\beta2|\psi|^4+\frac\gamma3|\psi|^6\right].
\]

**G (the maintained real Swift–Hohenberg gradient-flow baseline):**
\[
 A_t=rA-a\Delta A-b\Delta^2A-\beta A^3
       =-\frac{\delta E}{\delta A},
\]
where
\(E[A]=\int[-rA^2/2-a|\nabla A|^2/2+b|\Delta A|^2/2+\beta A^4/4]\).
This rail has energy dissipation rather than Hamiltonian mass conservation.

Neither PDE is demonstrated to equal the full corrected higher-derivative
S004 action, and the discrete WCC formalism does not automatically supply
either one's physical implementation costs.

## 2. New unconditional model-relative coercivity result for H

Put \(s=|\psi|^2\). A pointwise *exact square identity* gives
\[
 -\frac{\beta}{2}s^2+\frac\gamma3s^3+
 \frac{3\beta^2}{16\gamma}s
 =\frac\gamma3s\left(s-\frac{3\beta}{4\gamma}\right)^2\ge0.
\]
Consequently, denoting
\(K(t)=\|(\Delta+\kappa)\psi(t)\|_2\), conserved mass norm \(P=\|\psi\|_2\),
\[
 K(t)^2 \le H_0+\frac{3\beta^2}{16\gamma}P^2=:K_0^2.
\]
The right-hand side is nonnegative whenever such a solution exists.
Since \(\Delta\psi=(\Delta+\kappa)\psi-\kappa\psi\),
\[
 D(t):=\|\Delta\psi(t)\|_2\le K_0+\kappa P=:D_0.
\]
On a fixed 2D torus, a standard Fourier Sobolev estimate supplies
\(\|\psi\|_\infty\le S_\Omega(P+D_0)=:U_0\).
These are **derived H² and amplitude bounds**, not added energy rails.

They require a sufficiently regular solution and actual continuum mass and
Hamiltonian conservation. No global existence theorem is claimed here.

## 3. Exact localized-mass derivative identity

Let \(\chi\in C^\infty(\Omega;\mathbb R)\) be a real detector weight and set
\(J_\chi(t)=\int_\Omega\chi(x)|\psi(t,x)|^2\,dx\).
Write \(a=\|\nabla\chi\|_\infty\) and \(b=\|\Delta\chi\|_\infty\).
Differentiating along (H), integrating by parts and using that the cubic–quintic
nonlinearity is **real-valued times ψ** (hence contributes zero imaginary
part), yields
\[
\begin{aligned}
\left|\frac{dJ_\chi}{dt}\right|
&\le
(4a\|\nabla\psi\|_2+2bP)\|\Delta\psi\|_2
+4\kappa aP\|\nabla\psi\|_2.
\end{aligned}
\]
This is derived directly from the fourth-order Hamiltonian, not an assumed
finite-speed/light-cone principle.

By periodic integration by parts,
\(\|\nabla\psi\|_2^2=-\Re\langle\psi,\Delta\psi\rangle\le P D(t)\).
Using \(0\le D(t)\le D_0\) gives the **instantaneous flux inequality**
\[
|J_\chi'(t)|\le\Gamma\,\sqrt{D(t)},\quad
\Gamma=
4a\sqrt P\,D_0+2bP\sqrt{D_0}
+4\kappa aP\sqrt P.
\]
If \(\Gamma=0\), this predicts no observable change; below assume
\(T>0,\Gamma>0\).

## 4. Derived curvature-time tradeoff for mass-sensitive readout

If the detected localized mass changes by at least
\(\delta=|J_\chi(T)-J_\chi(0)|>0\), Hölder's inequality yields
\[
\delta\le\Gamma\int_0^T D(t)^{1/2}dt
 \le\Gamma T^{3/4}
 \left(\int_0^T D(t)^2dt\right)^{1/4},
\]
and therefore
\[
\boxed{\int_0^T\|\Delta\psi(t)\|_2^2dt
       \ge\frac{\delta^4}{\Gamma^4T^3}.}
\]

For a **globally phase-safe** regularizer with \(\varepsilon>0\),
\[
\mathcal C_{\varepsilon,T}[\psi]
=\int_0^T\!\int_\Omega
  \frac{|\Delta\psi|^2}{|\psi|^2+\varepsilon^2}\,dx\,dt,
\]
the derived amplitude bound \(\|\psi\|_\infty\le U_0\) implies
\[
\boxed{\mathcal C_{\varepsilon,T}[\psi]\ge
\frac{\delta^4}{\Gamma^4 T^3 (U_0^2+\varepsilon^2)}.}
\]
This is a nonzero **actual-PDE finite-time curvature/readout lower bound**
under the stated regularity, conservation, finite-time and detector
contrast hypotheses.

**For the WCT density-weighted curvature** appearing in the revised
geometry registry,
\[
F_{\varepsilon,\alpha}(s)=
\frac{s}{(s+\varepsilon^2e^{-2\alpha s})^2},
\qquad \alpha\ge0,
\]
we can instead conclude, *only if the field is uniformly node-free*
\(0<m\le|\psi(t,x)|\le U_0\), that
\[
F_{\varepsilon,\alpha}(|\psi|^2)
\ge \frac{m^2}{(U_0^2+\varepsilon^2)^2},
\]
and therefore
\[
\boxed{\int_0^T\!\int_\Omega
 F_{\varepsilon,\alpha}(|\psi|^2)|\Delta\psi|^2
 \ge \frac{m^2\delta^4}
 {\Gamma^4T^3(U_0^2+\varepsilon^2)^2}.}
\]
**This transfer fails without the node-free hypothesis.** The expression
\(F_{\varepsilon,\alpha}\) vanishes at zero density, so the energy does
not uniformly control \(\|\Delta\psi\|_2^2\) for general complex fields.
The positive phase-safe regularizer in the preceding display is a
*comparison functional*, not the same one as this WCT density weight.

## 5. Binary communication corollary and its scope

Consider two source choices 0 and 1 under the same unforced evolution,
with equal detector readings initially:
\(J_\chi^{(0)}(0)=J_\chi^{(1)}(0)\), while
\(|J_\chi^{(1)}(T)-J_\chi^{(0)}(T)|\ge\delta\).
By the triangle inequality, at least one source trajectory has
\(|J_\chi(T)-J_\chi(0)|\ge\delta/2\).
If both obey the *same* uniform \(P,K_0,U_0,\Gamma\) rails, the larger
of their two curvature costs obeys
\[
\max(C^{(0)},C^{(1)})\ge
\frac{\delta^4}{16\Gamma^4T^3(U_0^2+\varepsilon^2)}.
\]
The contrast is explicitly **localized mass**; phase readouts may not
obey this corollary. This shows how the maintained PDE naturally
constrains finite-time detectable signals, without imposing artificial
anchored three-node channels.

The fourth-order dispersion
\(\omega(k)=(|k|^2-\kappa)^2\) has group velocity
\(\nabla_k\omega=4(|k|^2-\kappa)k\), unbounded as \(|k|\to\infty\).
**There is no finite-speed causal cone derived for this PDE.** Fixed
spectral support also cannot be silently assumed under nonlinear flow.

## 6. Separate direct result for gradient-flow rail G

For the maintained real scalar gradient flow with smooth periodic
solutions,
\[
 E[A(0)]-E[A(T)]=\int_0^T\|A_t\|_2^2dt.
\]
A linear receiver readout \(R_\chi(A)=\langle\chi,A\rangle\) with
\(|R_\chi(A(T))-R_\chi(A(0))|\ge\delta\) satisfies
\[
\delta\le\|\chi\|_2\sqrt{T\,[E(0)-E(T)]},
\]
so
\[
\boxed{E(0)-E(T)\ge
\frac{\delta^2}{T\|\chi\|_2^2}.}
\]
This is a **dissipation/time** bridge, not a direct lower bound on the
WCT curvature functional. It cannot be transferred to the Hamiltonian
rail without changing models.

## 7. Exactly what remains open

1. **Kernel formalization of PDE calculus**: the local commutator identity,
integration-by-parts estimate, Sobolev control, Hölder integral estimate,
mass/energy conservation and strong well-posedness on the chosen torus.
The accompanying Lean code proves the exact cubic–quintic square identity
and the *algebraic composition* of the continuum inequalities, not the
continuum evolution theorem itself.
2. **Actual physical WCT parent action**: no derivation is supplied that
identifies the two maintained PDE rails with the full S004 action.
3. **An all-channel theorem**: phase encodings, node-containing fields,
nonlocal detectors, sources/boundary drives and noisy readouts require
different estimates.
4. **SAT lower bounds**: the estimate bounds finite-time change of
one local mass observable; it does not imply exponential time or an
arbitrary-WCC SAT curvature lower bound, let alone P≠NP.

### Sources

- [Maintained PDE models and Hamiltonian](https://github.com/rickyjreyes/wct-pde/blob/main/README.md).
- [Projection-free complex-field equation](https://github.com/rickyjreyes/wct-pde/blob/main/src/wct_pde/projection_free.py).
- [Real-gradient baseline equation](https://github.com/rickyjreyes/wct-pde/blob/main/docs/EQUATION_MAP.md).
- [Source-model matrix and limits](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/docs/foundational/FOUNDATIONAL_ACTION_AUDIT.md).
- [Previous communication and countermodel attempts](curvature-communication-bridge.md).
