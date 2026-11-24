# Phase XXV: finite nonlinear residual evaluation (partial #99)

The frozen interaction-picture Gf is U(-t) applied to the cubic-quintic
polynomial Fnl(U(t)v), with scalar -i. U is diagonal and does not enlarge
support. The actual co coefficient map divides by a nonzero weight, so
support in weighted coordinates is the same support in physical coordinates.

For finite S, product support is contained in S+T (Minkowski sum), and
conjugation reflects the support. Thus Gf(t,v) vanishes outside
N(S)=(S+S-S) union (S+S+S-S-S). For a trial derivative supported in D,
the full H2 residual norm squared is precisely the finite sum over
D union N(S). Each convolution is itself a finite sum over the support
of the right operand. The candidate Lean module uses the original
TorusNonlin and TorusFlow definitions, not an abstract surrogate PDE.

For a square of integer modes [-K,K]^2, N(S) is contained in [-5K,5K]^2,
so at most (10K+1)^2 coefficients are needed. Direct binary convolution
of successive bounded-degree factors uses O((K+1)^4) scalar arithmetic
operations; no FFT is necessary. This is an arithmetic-operation upper
bound, not a bit-complexity result. For a general finite S one may
explicitly construct the sumsets; their size is <= |S|^3+|S|^5.

A posteriori integration strategy: use a piecewise polynomial finite
trial trajectory with derivative supported in the same S. On each
time slab evaluate and bound the full residual over N(S) union S,
including the modes omitted by the Galerkin solver. Combine interval
enclosures for phase multipliers, coefficients, and rounding with the
existing residual certificate and Gronwall estimate. Split time slabs
at derivative discontinuities; restart the comparison at each endpoint.
An infinite nonlinear tail oracle is not needed on this trial class.
The finite trial residual may be large; this theorem does not guarantee
a given target tolerance can be reached with a polynomial cutoff.
Initial truncation in H2 still needs a separate effective certificate.
The existing no_uniform_H2_cutoff is unchanged. Uniform interval
enclosures, an effective approximation rate and bit costs including
the exponential stability factor remain open. Do not infer P_phys
subset P_TM without those and the input-indexed encoding costs.

New file FiniteNonlinearResidual.lean implements candidate proofs of
the support and residual identities. The square-envelope/count and
arithmetic-cost arguments above are mathematical, not yet formalized.
All new theorem roots are in AxiomAudit.lean. The pinned build and
audit have not yet passed; #99 and its original classification stay open.
