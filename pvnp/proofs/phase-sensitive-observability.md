# Phase-sensitive observability and the nodal obstruction in the maintained WCT Hamiltonian

**Richard J. Reyes PVNP independent mathematical audit · 27 October 2026.**

**Scope:** A static spectral curvature bound and a finite-time bound for spatially mean-zero coherent observables in the actual maintained projection-free cubic–quintic Hamiltonian PDE. The functional called **phase-safe** below is a comparison functional, not identical to the density-weighted WCT curvature functional. Analytic continuum statements are not yet formalized in Lean; only their supporting algebra and counterexample identities are kernel checked. **No universal communication or SAT complexity separation follows.**

## 1. Governing equation and resource rails

The maintained, separate projection-free rail of [wct-pde](https://github.com/rickyjreyes/wct-pde/blob/main/src/wct_pde/projection_free.py) is
\[
i\partial_t\psi=(\Delta+\kappa)^2\psi-\beta|\psi|^2\psi+\gamma|\psi|^4\psi,
\quad \kappa=k_\star^2,\quad \beta,\gamma>0 .
\]
We work on a **fixed connected rectangular two-dimensional torus** \(\Omega\), and assume sufficiently smooth unforced periodic solutions. Let
\(P=\|\psi(t)\|_2\) and \(H\) be the conserved mass norm and Hamiltonian. From the exact cubic–quintic square identity proved in
[HamiltonianTransport.lean](../../lean/PVNP/HamiltonianTransport.lean),
\[
\|(\Delta+\kappa)\psi\|_2^2
 \le H+\frac{3\beta^2}{16\gamma}P^2.
\]
Thus \(\|\Delta\psi\|_2\) and, by the **two-dimensional** periodic \(H^2\hookrightarrow L^\infty\) embedding, \(\|\psi\|_\infty\le U\) have finite bounds depending on \(H,P,\Omega,\kappa,\beta,\gamma\). The uniform \(U\) requires the stated conservation, smoothness, and domain hypotheses. It is not a universal constant independent of input size.

## 2. Exact failure for the spatially uniform phase mode

A complex spatially constant solution has the form
\[
\psi(t,x)=A e^{-i\omega t},\qquad
\omega=\kappa^2-\beta A^2+\gamma A^4,\quad A>0.
\]
It solves the **actual nonlinear Hamiltonian PDE** because \(\Delta\psi=0\) and \(i\psi_t=\omega\psi\). For the maintained defaults \(\kappa=1,\beta=2,\gamma=1\), choose \(A=2\); then \(\omega=9\). Its phase changes while \(\Delta\psi=0\) identically. Therefore even **causal-in-time phase evolution** with conserved mass and Hamiltonian does not imply positive spatial-Laplacian curvature cost.

A detector \(Z_\chi=\int\bar\chi\psi\) with nonzero mean would measure this global rotation relative to an external phase reference. A closed \(U(1)\)-invariant theory does not make absolute global phase intrinsically observable; such a reference and its resources must be declared. An observable that removes the constant mode eliminates this particular loophole.

## 3. Spectral bound for a spatially coherent relative-phase readout

On a periodic connected domain, use the orthonormal Fourier basis
\(e_k(x)=|\Omega|^{-1/2}e^{ik\cdot x}\). For \(k\ne0\), define
\(z_k(t)=\langle e_k,\psi(t)\rangle\).
The Fourier/Laplacian identity and Parseval imply
\[
\|\Delta\psi(t)\|_2^2
=\sum_q|q|^4|z_q(t)|^2
\ge |k|^4|z_k(t)|^2.
\]
The globally phase-safe comparison curvature is
\[
C_{\mathrm{safe},\varepsilon}[\psi(t)]
=\int_\Omega\frac{|\Delta\psi(t)|^2}{|\psi(t)|^2+\varepsilon^2}\,dx.
\]
For \(\|\psi(t)\|_\infty\le U\),
\[
\boxed{\quad C_{\mathrm{safe},\varepsilon}[\psi(t)]
\ge\frac{|k|^4|z_k(t)|^2}{U^2+\varepsilon^2}.\quad}
\]
This does **not** require \(|\psi|\ge m>0\), so nodes do not obstruct this particular comparison bound. It is a snapshot inequality for a **specified nonconstant mode**, not a cost per arbitrary bit. Frequency \(k=0\) is excluded: it has no Laplacian curvature.

The modulus \(|z_k|\) is invariant under a global \(U(1)\) phase, but one mode's modulus does not distinguish every possible relative phase. A coherent spatially weighted detector with two mode components can: for \(k\ne\ell\), both nonzero, take
\(\psi_\theta=A(e_k+e^{i\theta}e_\ell)\) and
\(\chi=(e_k+e_\ell)/\sqrt2\). Then
\[
|Z_\chi|^2=A^2(1+\cos\theta),
\]
which depends on **relative**, not global, phase. Such a coherent spatial-mode detector has practical implementation and noise costs that are **not** included in the functional.

## 4. Finite-time result from the nonlinear PDE

Take \(\chi\in H^4(\Omega;\mathbb C)\) with **zero spatial mean**
\(\int_\Omega\chi=0\), and define
\[
Z_\chi(t)=\int_\Omega\overline{\chi(x)}\psi(t,x)\,dx.
\]
Let \(m(t)=|\Omega|^{-1}\int_\Omega\psi(t,x)\,dx\) and
\(N(z)=-\beta|z|^2z+\gamma|z|^4z\). By periodic self-adjointness of
\(L=(\Delta+\kappa)^2\), differentiation along the actual PDE gives
\[
iZ_\chi'(t)
=\langle L\chi,\psi(t)-m(t)\rangle+
 \langle\chi,N(\psi(t))-N(m(t))\rangle.
\]
Both subtractions are legitimate because \(\int\chi=\int L\chi=0\).
For all complex \(z,w\) of modulus at most \(U\),
\[
|N(z)-N(w)|
\le (3\beta U^2+5\gamma U^4)|z-w|.
\]
This follows by the triangle inequality from the familiar product
Lipschitz estimates for \(|z|^2z\) and \(|z|^4z\); the coefficients 3 and
5 are explicit, not hidden in an unspecified constant.

Let \(\lambda_1>0\) be the smallest positive eigenvalue of \(-\Delta\)
on this connected torus. The mean-zero periodic Poincaré estimate gives
\[
\|\psi-m\|_2\le\lambda_1^{-1}\|\Delta\psi\|_2.
\]
Therefore
\[
|Z_\chi'(t)|\le K_\chi\|\Delta\psi(t)\|_2,
\quad
K_\chi:=
\frac{\|L\chi\|_2+
      (3\beta U^2+5\gamma U^4)\|\chi\|_2}{\lambda_1}.
\]
For \(T>0\), a detected change
\(\delta=|Z_\chi(T)-Z_\chi(0)|\) obeys
\[
\delta^2\le K_\chi^2\,T
   \int_0^T\|\Delta\psi(t)\|_2^2dt.
\]
Since \(|\psi|\le U\), the phase-safe integrated curvature satisfies
\[
\boxed{\quad
\mathcal C_{\mathrm{safe},\varepsilon,T}[\psi]
\ge
\frac{\delta^2}
{K_\chi^2\,T\,(U^2+\varepsilon^2)}.\quad}
\]
This is a **1/T tradeoff**, improving the earlier localized-mass
\(1/T^3\) estimate for a particular mean-zero coherent observable.
It is derived analytically using the actual nonlinear Hamiltonian PDE.
It is valid if \(K_\chi>0\) and the smooth evolution/energy rails exist.
If \(K_\chi=0\), the preceding derivative bound enforces \(\delta=0\).

For two unforced trajectories beginning with the **same detector reading**
and ending \(\delta\)-apart in that reading, at least one changes by
\(\delta/2\); assuming a common uniform \(K_\chi,U,T\), at least one
phase-safe curvature cost is \(\ge \delta^2/[4K_\chi^2T(U^2+\varepsilon^2)]\).
This is **not** a causal SAT communication theorem: the two initial
global field configurations may already differ outside the detector.
The fourth-order dispersive equation has unbounded high-frequency
group velocity, so no strict finite-speed light cone is supplied.

## 5. Nodes obstruct transfer to WCT density-weighted curvature

The alternative WCT weight from the geometry registry is
\[
F_{\varepsilon,\alpha}(s)
=\frac{s}{(s+\varepsilon^2e^{-2\alpha s})^2}.
\]
It vanishes at \(s=0\). This is not merely a formal denominator issue.
On the one-dimensional torus, let
\(\psi_N(x)=N^{-2}\sin(Nx)\), \(N\ge1\).
Then \(\psi_N''=-\sin(Nx)\) and
\[
\int_0^{2\pi}|\psi_N''|^2dx=\pi.
\]
For \(\alpha=0\),
\[
\int_0^{2\pi}
 F_{\varepsilon,0}(|\psi_N|^2)|\psi_N''|^2dx
\le\frac{\pi}{\varepsilon^4 N^4}\longrightarrow0.
\]
For fixed \(\alpha\ge0\), the same behavior holds with an extra
factor at most \(e^{4\alpha}\), since \(|\psi_N|\le1\).
Hence there is **no uniform coercivity constant** \(c>0\) satisfying
\(\int F(|\psi|^2)|\Delta\psi|^2\ge c\|\Delta\psi\|_2^2\)
over all smooth node-containing fields.

This sequence has mass tending to zero; it is an explicit no-go for
a field-uniform comparison, not a refutation of a theorem restricted to
a fixed positive-mass, dynamically invariant manifold. That stronger
fixed-mass question requires a separate analysis.

## 6. Input-size dependence and unresolved computational bridge

The constants contain \(\lambda_1(\Omega)^{-1}\), \(\|\chi\|_2\),
\(\|(\Delta+\kappa)^2\chi\|_2\), \(U\), and the conserved mass and
Hamiltonian. On expanding tori \(\lambda_1\sim L_{\max}^{-2}\);
a detector whose frequency or spatial localization changes with
problem size may also change \(K_\chi\). These dependencies must be
reported explicitly in any family-level statement.

A positive finite-time curvature bound for a selected observable is
not a superpolynomial lower bound against all SAT algorithms.
Algorithm universality, phase detectors, node-weight degeneracy, and
input-size rails all remain substantive proof obligations.

## Lean certification and source provenance

[PhaseObservability.lean](../../lean/PVNP/PhaseObservability.lean)
checks the algebraic endpoint of the Fourier/PDE inequalities,
the zero-curvature constant profile, and the density-weight node
degeneracy. **It does not claim Lean proofs of Fourier/Parseval,
nonlinear PDE differentiability, conservation, the Sobolev embedding,
Poincaré, or the nonlinear complex Lipschitz estimate.** Those are
analytical arguments documented above.

Equation source:
[rickyjreyes/wct-pde projection_free.py](https://github.com/rickyjreyes/wct-pde/blob/main/src/wct_pde/projection_free.py)
and [model README](https://github.com/rickyjreyes/wct-pde/blob/main/README.md).
Related prior result:
[WCT Hamiltonian transport note](wct-pde-transport-bound.md).
