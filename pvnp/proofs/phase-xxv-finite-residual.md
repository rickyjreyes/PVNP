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


## Quantitative time-slab extension

For a fixed finite trial support S, choose upper bounds M on the free frequencies
omega(k)=(kappa-qf(L,k))^2 for k in S and N on the same frequencies for
k in nonlinearSupport(S). The free-group increment bound is
||U(s)v-U(t)v|| <= M |s-t| ||v||.
Splitting the interaction-picture vector field difference at the intermediate
nonlinearity Fnl(U(t)v) yields
||Gf(s,v)-Gf(t,v)|| <= LF(R) R (M+N) |s-t|
on the radius-R trial ball. For a slab W(t)=x+(t-a)d, combining this with
the spatial Lipschitz bound yields
||d-Gf(t,W(t))|| <= eta + LF(R) (||d||+R(M+N)) |t-a|,
provided ||x|| and ||W(t)|| are <= R and the left-end residual <= eta.
The left-end residual includes off-cutoff nonlinear terms and numerical
evaluation errors, not merely the projected ODE defect.

Thus a uniform residual target rho > eta can be certified with
h <= (rho-eta)/(LF(R)(||d||+R(M+N))) when the denominator is positive.
If it is zero the displayed bound imposes no step-size restriction.
A sufficient radius certificate is ||x||+h||d|| <= R.
The time-modulus and affine residual inequalities are candidate Lean
proofs in CertifiedIntegrator.lean, imported and registered for audit.
The step-size corollaries above are mathematical consequences, not
separately mechanized. No claim of polynomial integration cost: eta may
already be larger than rho due to spectral truncation, and the global
Gronwall amplification, input-indexed cutoffs and finite-bit enclosure
costs still need certification. The fixed finite support hypothesis
does not apply to the true infinite-dimensional trajectory.


## Effective weak-norm alternative

Let ||v||_w=||Lc(L)v||, the physical L² norm of the H²-weighted
coefficient state. If wt(L,k)>=K>0 on omitted modes, then
||P_S v-v||_w <= ||v||/K. This follows coefficientwise from
co(L,v,k)=v(k)/wt(L,k). No H4 budget is needed.
The actual detector satisfies
|J(v)-J(w)| <= Cdet (||v||_w+||w||_w)||v-w||_w.
The actual multiplication operator has the bound
||mulH(v,w)||_w <= CA ||v|| ||w||_w, by the existing L1 convolution
estimate, and commutativity gives the other orientation.
Telescoping the cubic and quintic chains yields
||Gf(t,v)-Gf(t,w)||_w <= LF(R)||v-w||_w on the H2 radius-R ball.
Consequently ||P_S Gf(t,P_S v)-Gf(t,v)||_w <= 2 LF(R) R/K.

For an exact trajectory w and finite Galerkin trajectory W both
bounded in H2 by R on [0,T], compare W'=P_S Gf(t,W) with w'=Gf(t,w)
in the weak norm. Since W is supported in S,
||W'-Gf(t,W)||_w <= LF(R)R/K.
If W(0)=P_S w(0), the initial error is <= R/K.
Applying the bounded-set weak-norm differential inequality gives
||W(t)-w(t)||_w <= (R/K)e^(LF(R)t)
 + (R/K)(e^(LF(R)t)-1) <= 2R e^(LF(R)t)/K
(including LF=0 by direct comparison). This uses H2 bounds for both
trajectories, not merely the exact PDE. To obtain a uniform bound
for the Galerkin flow, prove its restricted Hamiltonian and mass
conservation and apply the original coercivity inequality, or give
a separate certified numerical radius bound. The weak differential
comparison and Galerkin conservation have not yet been mechanized.
The ten candidate weak-norm lemmas in WeakNormApproximation.lean
are included in the root import and axiom audit; verification pending.

For a square cutoff |k_i|<=m on a fixed torus, K can be taken
as 1+(2*pi*(m+1)/L)^2. Thus the number of retained modes grows
as O(1+L² K). For bounded radius and detector norm, this removes
the qualitative spatial-tail obstruction, but the estimate can require
K exponential in LF(R)T. If LF(R)T=O(log n) and all other
magnitudes and inverse target margin are polynomially bounded in n,
the sufficient cutoff is polynomial. If LF(R)T is polynomial rather
than logarithmic, this proof alone may require exponentially many
modes; polynomial precision bits do not imply polynomial mode count.
This is a sufficient error estimate, not a complexity lower bound.
No P_phys=P_TM or SAT separation claim follows.


## Conservation and global weak comparison extension

The projected flow uses W'=P_S Gf(t,W), with W=P_S W. The projection
commutes with U and acts orthogonally in the mass and kinetic Fourier
pairings. In differentiating mass, P_S on the second operand can be
removed because the first operand is supported. In differentiating
the kinetic energy, the same removal applies to the Ac pairing.
For the potential term, U(t)W'=-i P_S Fnl(U(t)W), and the inner
product of Fnl with P_S Fnl in the physical mass pairing equals the
squared norm of P_S Fnl, which is real. Its product with -i has zero
real part. The remaining kinetic/potential mixed terms cancel by
complex conjugate symmetry, exactly as in the unprojected energy proof.

Thus the same mass and Hamiltonian as the full PDE are conserved.
The existing coercive bound Rap on the initial projected mass and
Hamiltonian controls the entire trajectory. The clipped global
existence construction now admits the original clopen continuation
argument, with support preserved and the radius cutoff inactive.
GalerkinConservation.lean contains twelve candidate theorem roots.

WeakGlobalComparison.lean formalizes the weak differential comparison
by applying the existing bounded-set Gronwall theorem to Lc(W) and
Lc(w). Lc is injective; weakLift is a set-theoretic inverse on its
image. The induced field is Lipschitz only on the image of the H2
ball. No continuity or algorithm for weakLift is required. The actual
projected residual is at most LF(R)R/K, because W already lies in
the support, and the initial error is at most R/K. The seven new
theorem roots culminate in the precise gronwallBound statement.

To choose a single radius uniformly in S from an input H2 bound B,
the initial projected mass is <= B², kinetic energy <= (|kappa|+1)² B²,
and potential energy is bounded above using the Sobolev algebra
estimate and the polynomial nonlinearity. This remaining explicit
uniform-radius estimate and the final detector/bit-cost integration
are not yet implemented in this patch. In particular the exponential
stability factor remains, and no polynomial full-class simulation
or universal SAT lower bound is established.

Hosted full build at b7b8ff7 failed in FiniteNonlinearResidual.lean
on the rewrite of tsum of the zero function; replaced by simp after
the function equality. Other modules depending on it were not checked
in that build. The new conservation and global comparison modules
are candidates pending full kernel verification and axiom audit.


## Cutoff-independent radius and end-to-end detector approximation

For initial H2 norm <= B, put C_S=L^{-1} sqrt(SL L), and
E_B=(|kappa|+1)^2 B^2+3|beta| C_S^2 B^4+5|gamma| C_S^4 B^6.
The diagonal kinetic multiplier bound gives ||Ac v|| <=
(|kappa|+1)||v||. The existing potential Taylor estimate at zero
bounds the absolute potential by (3|beta| C_S^2 B^2+
5|gamma| C_S^4 B^4) mass(v). Both v and P_S v have H2 norm <= B.
For gamma>0 the radius R_B=Rap(kappa,beta,gamma,B^2,E_B)
therefore bounds the exact and all projected trajectories globally.

For omitted weights >= K>0, the global Galerkin L2 error is at most
2 R_B exp(LF(R_B) T)/K. The physical detector consequently obeys
|J_S-J| <= 4 Cdet R_B^2 exp(LF(R_B)T)/K.
For margin m>0, a sufficient cutoff condition is
m K >= 8 Cdet R_B^2 exp(LF(R_B)T), preserving either decision sign.
UniformGalerkinRadius.lean implements thirteen candidate theorem
roots from initial energy to detector decision, registered for audit.

For a square cutoff of coordinate radius q on the integer lattice,
K=1+(2*pi*(q+1)/L)^2 and the mode count is (2q+1)^2.
If the input-indexed L, R_B, Cdet, 1/m and LF(R_B) are polynomial
in n and LF(R_B) T=O(log n), the sufficient spectral dimension is
polynomial. For this restricted regime, first-order time stepping
can also use polynomially many steps, subject to a charged
H2 stability/radius certificate and polynomial cost evaluation of
the finite initial coefficients, detector, and physical parameters.
A polynomial numerical time-stepping proof, finite-bit evaluation
and all input-indexed encoding obligations remain open. In
particular a uniform cutoff rate is not a polynomial full-class
simulation, nor a lower bound on arbitrary simulation algorithms.
All new Lean declarations remain candidates until the complete
kernel build and transitive axiom audit pass.
