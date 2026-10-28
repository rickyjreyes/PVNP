# Noise-robust mass–bandwidth packing bound for Fourier-observed WCT states

**Auxiliary resource theorem, 27 October 2026.** An elementary Euclidean ball-packing theorem applied to the actually conserved \(L^2\) mass of the maintained, unforced, projection-free WCT Hamiltonian model. The **geometric inequality is proved analytically**, not yet formalized in Lean. It is a static coding bound on an explicitly finite-dimensional receiver and does **not** prove an SAT time lower bound.

## Physical model and hypotheses

The maintained complex-field Hamiltonian
\[
i\partial_t\psi=(\Delta+\kappa)^2\psi
   -\beta|\psi|^2\psi+\gamma|\psi|^4\psi
\]
has conserved mass \(\|\psi(t)\|_2^2=M\) on smooth unforced periodic solutions. This model is an independent maintained PDE rail, not automatically the original WCT action or every WCC device. [Equation source](https://github.com/rickyjreyes/wct-pde/blob/main/src/wct_pde/projection_free.py).

At a declared readout instant \(t_*\), the receiver observes the orthogonal projection \(P_D\psi\) onto a **specified complex \(D\)-dimensional spectral subspace**. Here \(D\ge1\). Parseval gives
\[
\|P_D\psi\|_2\le\|\psi\|_2=\sqrt M.
\]
Suppose a family of \(N\) admissible computational labels is encoded by \(N\) readout vectors \(v_j=P_D\psi_j(t_*)\). Assume *worst-case deterministic reliability* against every complex-vector measurement error of Euclidean norm at most \(\eta>0\). If every label must be decoded distinctly and unambiguously, its noise ball must be disjoint from every other label's noise ball. It is sufficient (and, with closed-ball adversarial error, necessary for unique decoding) that
\[
\|v_j-v_k\|_2>2\eta,\qquad j\ne k.
\]

## Full analytical packing proof

Identify \(\mathbb C^D\) with \(\mathbb R^{2D}\). The open radius-\(\eta\) balls \(B(v_j,\eta)\) are pairwise disjoint, and since \(\|v_j\|\le\sqrt M\), every such ball lies in \(B(0,\sqrt M+\eta)\). Euclidean volume in real dimension \(2D\) scales as radius to the power \(2D\). Therefore,
\[
N\,\operatorname{vol}_{2D}(B(0,\eta))
\le\operatorname{vol}_{2D}(B(0,\sqrt M+\eta)).
\]
After canceling the common ball-volume constant:
\[
\boxed{\quad N\le\left(1+\frac{\sqrt M}{\eta}\right)^{2D}.\quad}
\]
In particular, **if** all \(N=2^n\) labels must be independently recovered,
\[
\boxed{\quad n\le 2D\log_2\!\left(1+\frac{\sqrt M}{\eta}\right).\quad}
\]
The same inequality rearranges (for \(D\ge1\)) to
\[
\boxed{\quad M\ge\eta^2\bigl(2^{n/(2D)}-1\bigr)^2.\quad}
\]
For fixed complex mode count \(D\) and fixed noise scale \(\eta>0\), faithful storage of \(n\) *arbitrary independently recoverable* bits requires exponential mass as \(n/D\) grows. With \(D=\Omega(n)\), constant mass and constant noise are not ruled out by this packing inequality.

**No premise about curvature energy is needed**, and the proof is uniform over *all possible codes in the specified finite-dimensional noisy receiver class*. Noise-tolerant distinguishability, mass, and spectral dimension are the assumptions doing the work.

## Source-bandwidth and volume cannot be treated as free

On a square two-dimensional periodic domain of side \(L\), allowed modes have \(k=(2\pi/L)(j_1,j_2)\), \(j_i\in\mathbb Z\). If a receiver only observes modes with \(|k|\le K\), the number \(D\) obeys the elementary upper bound
\[
D\le\left(2\left\lfloor\frac{LK}{2\pi}\right\rfloor+1\right)^2.
\]
This is an upper bound by enclosing the frequency disk in its bounding lattice square, not a claimed exact count. The Hamiltonian nonlinear evolution is **not known to preserve exact finite spectral support**; the assumption concerns a deliberately bandwidth-limited *receiver*, including costs of extracting/maintaining those observables. If the domain and readout bandwidth expand with SAT input length, the inferred \(D\) expands and the bound may become weak. Charging only mass while silently allowing unbounded \(D\) would invalidate any strong complexity conclusion.

Receiver access to global coherent phase/frequency modes requires an explicit reference and physical measurement architecture. Those resources, detector locality and energy, source preparation, switching time, and stochastic noise are **not** bounded by the static sphere-packing calculation.

## The essential decision-vs-encoding limitation

The inequality counts *distinctly decoded messages*. A SAT decision problem has two possible outputs (satisfiable/unsatisfiable), so it does **not** require a receiver to resolve all \(2^n\) Boolean assignments as different output symbols. Many inputs may intentionally map to the same accepted or rejected output.

Consequently the strong-looking exponential \(M\) lower bound for fixed \(D\) **cannot be invoked as an exponential SAT-solving lower bound**. To use it for hard SAT, an independent theorem must show that every admissible correct decider is forced to realize \(2^{\Omega(n)}\) mutually distinguishable *intermediate* states at a charged cut or receiver. No such uniform all-algorithm theorem has been proved.

This is complementary to the narrower [two-party split 3-CNF lower bound](split-3sat-reliable-channel.md), where the fooling-set argument truly forces \(2^n\) **different full communication transcripts**. Transferring the latter to WCT requires a proof that those transcript classes are physically represented by independently and robustly recoverable receiver vectors under the same resource rails. Do not silently equate a classical transcript with a PDE trajectory.

## Verification scope

- The Euclidean packing and algebraic corollaries above are complete conventional proofs using standard finite-dimensional volume scaling.
- No new Lean kernel theorem of ball packing or the Fourier projection is claimed. The related [SplitSATCapacity.lean](../../lean/PVNP/SplitSATCapacity.lean) checks the exact discrete private-SAT communication bound.
- This does not address the unrestricted classical P vs NP problem or prove a physical WCC separation. It establishes an explicit, reproducible information-resource *ceiling* for a declared finite-band, noise-robust wave receiver.
