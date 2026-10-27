# Curvature-barrier audit: explicit polynomial-cost SAT witness encodings

**Status:** New proof and countermodel. This is **not** a classical or physical P-versus-NP separation. It tests the inference from expander structure to exponential *configuration curvature*, not a lower bound against all SAT deciders.

## I. Exact discrete bound

Let \(x=(x_1,\ldots,x_n)\in\{0,1\}^n\) and store bit \(x_i\) at a lattice vertex by amplitude \(\psi_i=1+x_i\). For any ring of \(n\) sites set
\[
(\Delta_d\psi)_i=\psi_{i-1}-2\psi_i+\psi_{i+1},\qquad
C_{\Theta,1}(\psi)=\sum_{i=1}^n
\left(\frac{(\Delta_d\psi)_i}{\psi_i+1}\right)^2 .
\]
Since \(1\le\psi_i\le 2\), we have \(|\Delta_d\psi_i|\le 2\) and \(\psi_i+1\ge 2\). Hence for every \(x\),
\[
\boxed{0\le C_{\Theta,1}(\psi_x)\le n}.
\]
Readout \(x_i=\psi_i-1\) is exact and local, and the map \(x\mapsto\psi_x\) is injective. This proves a **state-storage** upper bound, not a SAT decision algorithm.

### Any bounded-degree graph, including expanders

For a graph \(G=(V,E)\) with \(|V|=n\) and maximum degree \(d\), use the combinatorial graph Laplacian
\[
(\Delta_G\psi)(v)=\sum_{u\sim v}(\psi(u)-\psi(v)).
\]
Since each difference is in \(\{-1,0,1\}\), \(|(\Delta_G\psi)(v)|\le d\). Therefore
\[
\boxed{\sum_{v\in V}|(\Delta_G\psi)(v)|^2\le nd^2}.
\]
For the shift-regularized version, \(\psi_v+1\ge2\), yielding
\[
\boxed{\sum_{v\in V}\left|\frac{(\Delta_G\psi)(v)}{\psi_v+1}\right|^2\le\frac{nd^2}{4}}.
\]
A constant-degree expander has \(d=O(1)\); this particular representation therefore has only \(O(n)\) graph-curvature storage cost. Expansion of the *clause-variable incidence graph* does not by itself prohibit this encoding. It does not certify a local, stationary realization of every clause interaction under a fixed continuous WCT PDE.

## II. Continuum smooth-field construction with fixed mass

Take a nonzero, nonnegative \(\rho\in C_c^\infty(B(0,r))\) in \(\mathbb R^3\), with \(0<r<1/4\). For every bit position \(i=1,\ldots,n\), choose two possible centers
\[
p_{i,0}=(3i,1,1),\qquad p_{i,1}=(3i,2,1).
\]
In a containing box \(\Omega_n=(0,3n+3)\times(0,3)\times(0,3)\) define
\[
\psi_x(y)=\sum_{i=1}^n \rho(y-p_{i,x_i}).
\]
All translated supports are mutually disjoint. Every assignment is encoded injectively: read bit \(i\) by checking which of the two disjoint local subregions contains its bump.

The total mass and derivative energies are **independent of the assignment**:
\[
\|\psi_x\|_{L^2}^2=n\|\rho\|_{L^2}^2,\qquad
\|\nabla\psi_x\|_{L^2}^2=n\|\nabla\rho\|_{L^2}^2,\qquad
\|\Delta\psi_x\|_{L^2}^2=n\|\Delta\rho\|_{L^2}^2.
\]
For the original shifted curvature functional with \(\varepsilon>0\),
\[
C_{\Theta,\varepsilon}[\psi]
=\int_{\Omega_n}\left|\frac{\Delta\psi}{\psi+\varepsilon}\right|^2dy,
\]
we have \(\psi_x\ge0\), hence \(\psi_x+\varepsilon\ge\varepsilon\), and disjointness gives the **exact identity**
\[
\boxed{C_{\Theta,\varepsilon}[\psi_x]
=n\int_{\mathbb R^3}\frac{|\Delta\rho(z)|^2}
{(\rho(z)+\varepsilon)^2}\,dz
\le\frac{n}{\varepsilon^2}\|\Delta\rho\|_{L^2}^2}.
\]
The bounding volume is \(O(n)\), all fields are smooth, and total mass is the same for every assignment. Consequently **exponentially many distinct assignment states** exist *as alternatives*, each with only \(O(n)\) state curvature. There is no need to build all \(2^n\) states simultaneously.

### Scope

These fields are admissible smooth, finite-energy encodings for the explicitly defined functional. A stronger physical WCC class can exclude them by requiring solutions or invariant states of a particular curvature-feedback PDE, wave-phase semantics, a uniform clause interaction, or a specific admissibility manifold. **Such restrictions must be stated, proved consistent with polynomial witness verification, and shown invariant under alternative encodings** before a universal lower bound can follow.

## III. What can be proved about all local computations?

If a synchronous radius-\(r\) local machine must read an input bit at graph distance \(D\) from its designated output cell, a direct causal-cone induction shows that it needs at least \(\lceil D/r\rceil\) rounds: configurations differing only at that distant cell produce identical output-cell states for fewer rounds. This is a valid **linear propagation lower bound** on appropriate long-path inputs, but not an exponential SAT lower bound.

Thus the original proposed upgrade from *locked-expander geometry* or *search-path cost* to exponential cost for **all admissible SAT solvers** remains unproved. In the minimal curvature model above, exponential cost of static witness storage is **false**.

## Formal proof scope

The accompanying [Lean module](../../lean/PVNP/CurvatureBarrier.lean) checks the discrete signed-amplitude inequalities, injection, and graph-energy upper bounds. The continuum smooth-field construction above is a traditional analytic proof and is **not formalized as a Sobolev or integral theorem in Lean**.

*Research note for the revised PVNP trilogy. Original publication chronology is unchanged.*
