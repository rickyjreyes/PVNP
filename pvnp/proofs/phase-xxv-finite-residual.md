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


## Rounded Euler and finite-bit evaluator

Take R=R_B and a positive radius slack b. Set A=LF(R+b),
D=A^2(R+b)+A(R+b)(M+Q), where M and Q bound the frequencies on
S and nonlinearSupport(S). On an exact Galerkin trajectory the speed
is <= A(R+b); combining space and time moduli and applying the
mean-value bound on a time slab gives the conservative local Euler
defect <= D h^2. For approximate iterates x_i with per-step
update defect <= xi in H2, the error e_i against the exact Galerkin
trajectory satisfies e_(i+1) <= (1+A h)e_i+D h^2+xi whenever
e_i <= b. The explicit envelope
e_i <= (delta+i(D h^2+xi)) exp(A h i)
follows by induction using 1+A h <= exp(A h).
If the envelope at N is <= b, monotonicity and the recurrence
bootstrap certify every iterate in the radius R+b. This is not
an assumption of global numerical stability.

For T>0, an upper bound E>=exp(A T), and target epsilon<=b,
choose N>=max(1,3D T^2 E/epsilon), h=T/N,
delta<=epsilon/(3E), xi<=epsilon/(3NE).
Then the envelope is <=epsilon. The T=0 case only needs initial
approximation. If A T=O(log n) and D,T,1/epsilon are polynomially
bounded, so is the sufficient step count. It is A at the enlarged
radius that must meet the amplification condition, not merely
LF(R) at the exact radius. One can instead choose a smaller
positive slack if its inverse is polynomial and the enlarged
amplification remains logarithmic.

RoundedStepBudget.lean implements nine candidate theorem roots:
the scalar envelope, budget split, finite field time and speed,
local defect, and radius-bootstrap Euler comparison. All are
registered in the audit, pending kernel verification.

The prototype pvnp/phase_xxv/rational_fourier.py implements the
actual weighted torus field, not an unrelated ODE. It encloses
pi by Machin's alternating arctan identity; for exp(i x) at a
rational midpoint x, the Taylor remainder after degree 2r-1 is
<= |x|^(2r)/(2r)! <= (x^2/r)^r <= 2^-r when r>=2x^2.
The input interval radius is added using the unit Lipschitz
constant of the phase. Every ordinary arithmetic primitive rounds
outward to dyadics. Physical coefficients divide by wt, the
cubic/quintic convolutions each use the exact L^-1 normalization,
and the output is multiplied by wt, the reversed free phase,
and -i. The step certificate sums the componentwise interval
errors, bounding the Euclidean H2-coordinate error.

For polynomially bounded phase magnitudes, r=max(p+2,ceil(2x^2))
is polynomial in n and precision p. Rational Taylor intermediates
have polynomial bit length (powers and factorials at degree 2r).
Machin's rational partial sums also have polynomial bit length.
The convolution circuit has polynomial size and fixed
multiplicative depth for bounded-degree factors; sums introduce
only polynomial amplification of interval widths. Positive L
bounded away from zero by an inverse polynomial and wt>=1 give
polynomial conditioning for divisions once precision is sufficient.
Thus polynomially many bits suffice for inverse-polynomial step
budgets under the stated magnitude/conditioning bounds. This
analytical bit-cost argument is not yet a machine-checked
complexity theorem or a formal executable refinement.
The separate rational regression workflow is added; tests have
not yet been observed passing. Remaining obligations include
uniform input coefficient access, detector evaluation, explicit
operation and precision budgets in Lean, and the unrestricted
amplification regime. No full-class simulation or SAT lower
bound follows.

The preceding hosted Lean build stopped at the zero-function
tsum in FiniteNonlinearResidual.lean. This patch explicitly
proves the pointwise summand is zero and invokes tsum_zero on a
constant lambda, instead of relying on rewriting tsum 0.


## Finite detector and complete finite-input decision prototype

For a state with support S, the exact physical detector is
J(v)=Re[L^{-1} sum_{k,j in S} conj(co(v,k)) co(chi,k-j) co(v,j)].
At time T use ph(T,k)co(v,k) for each state coefficient.
Only the detector coefficients on S-S matter, even for an infinite
real H2 detector. Three candidate theorem roots in FiniteDetector.lean
prove this using Jdet_eq_re, inner_Lc, co_mulH and finite_pr.
The readout costs O(|S|^2) complex arithmetic terms and does not
require evaluating an infinite convolution.

The executable detector_box encloses this expression for a complete
finite rational detector, checking its real-field symmetry. The
certified_decision prototype accepts complete finite rational initial
and detector dictionaries and explicit square cutoff, time, threshold,
and target margin. Its radius uses an exact rational upper square root,
the H2 coordinate L1 bound for the input, and C_S<=1/L+1/2.
The detector constant is bounded by the detector coordinate L1 norm/L.
Pi bounds 3<pi<4 give conservative cutoff and phase-frequency estimates.
For A>=LF(R+b), E=2^ceil(2AT)>=exp(AT). The driver caps the exponent
before allocating E. It uses the sufficient Euler step count from the
previous section and checks each interval-based update defect against
the uniform budget xi. The exact rational projected initial state has
zero numerical initialization error. The analytical trajectory and
spatial error budgets expand the final detector interval:
 spatial <= 4 C R^2 E/K;
 numerical state <= (D h T + N xi) E;
 numerical readout <= C(2R+b) numerical state.
Only an interval strictly on one side of the threshold returns a
Boolean; overlap returns None. Resource or precision cap exhaustion
raises BudgetExceeded. No truth value is asserted on failure.

The executable restricts to fully specified finite rational inputs;
it does not accept an arbitrary infinite input as an oracle. For a
broader input class, charge the coefficient-access algorithm, an
effective norm certificate, and its precision and encoding costs.
For polynomially bounded scalar magnitudes and inverse L, polynomial
mode count, polynomial input bit length, inverse-polynomial margin,
and A T=O(log n), the sufficient bounds support a polynomial-time
algorithm on this restricted promise class. In particular the Euler
step count, Taylor degree, coefficient circuit size and required
precision are polynomial; the determinant of this claim is the
promise on the enlarged-radius amplification, not merely polynomial
physical time. The implementation's caps must be chosen to dominate
the proven resources and are not themselves a proof of totality.
No unrestricted simulation, hardness lower bound, or executable Lean
refinement has been established.

The previous five rational Fourier regression tests passed hosted CI
at fcc63fb (run 45471920038). Six additional tests cover the detector,
difference support, real symmetry, square root, decision signs and
abstention, and resource caps. Those new tests await verification.
The hosted Lean build at f7acd149 passed FiniteNonlinearResidual but
failed in CertifiedIntegrator at the scalar norm rewrite. The new
commit removes the redundant Complex.norm_real rewrite; full
kernel verification of all dependent modules is still pending.


## Restricted promise totality and polynomial resource majorants

The previous one-quarter error allocation certified any returned sign
but did not guarantee totality on every separated input. With detector
interval width <= m/8, spatial error <= m/8 and numerical readout
error <= m/8, the expanded interval has width <= 5m/8 < m. Since it
contains the exact reading, a true separation of at least m forces
one of the strict sign tests to succeed. The prototype now uses this
allocation and automatically chooses q >= L sqrt(32 C R² E/m)/6
when no cutoff is supplied, using a rational upper square root.
The explicit resource caps still cause rejection if too small.

RestrictedResourceBudget.lean provides six independent candidate
scalar theorems. If a common majorant P>=1 bounds L,C,R,E and 1/m,
q>=4 P^4 suffices: 1+(6(q+1)/L)^2 >=64 P^6 >=32 P^5,
and 4 C R² E/K <= m/8. Thus O(P^8) modes suffice. Once the
cutoff is selected, D is a polynomial in q and the parameter
magnitudes including 1/L. A (possibly larger) common majorant P'
of D,T,E,1/epsilon yields sufficient N>=3(P')^5. These are loose
majorants, not lower bounds. The fixed-depth convolution circuit
and interval arithmetic argument in the preceding section give
a polynomial bit-cost route under these promises; no fully
formal Turing-machine implementation is claimed.

## Exponential amplification is not purely a Gronwall artifact

A concrete linearized instability occurs for the frozen PDE itself.
Let g(s)=-beta*s+gamma*s² and a>0. The constant background
u0=a exp(-i (kappa²+g(a²)) t) is an exact plane-wave solution.
Write u=exp(-i (kappa²+g(a²)) t)(a+z). The first variation of
g(|a+z|²)(a+z)-g(a²)(a+z) is
c(z+conj z), where c=a²(-beta+2 gamma a²).
For z=(x+iy) cos(k dot x) with q=|k|², the shifted linear
dispersion is H=(kappa-q)²-kappa²=q²-2 kappa q.
Thus the linearized equation gives x'=H y and
y'=-(H+2c)x. Its eigenvalue square is -H(H+2c).

Take L=2*pi, k=(1,0), kappa=0, a=1, beta=2, gamma=1/2.
Then H=1, c=-1, and x=y=exp(t) is an exact growing solution
of the linearized sideband system. It also lies in the linearization
of any symmetric Galerkin system retaining the zero and both
sideband modes. Hence conservation of mass and Hamiltonian does
not itself imply a polynomial-in-time Lipschitz bound for the flow.
A uniform derivative bound on a finite-dimensional solution map
containing this background must allow exponential amplification.
This observation is not an exponential simulation-time lower bound:
a different algorithm, higher-order method, or device subclass
might bypass the first-order worst-case resource estimate.
SidebandAmplification.lean contains four candidate algebra and
linear ODE theorems. The full PDE Frechet derivative and nonlinear
flow-map lower bound are not yet mechanized.

The full CI at e59a2e8 reached WeakNormApproximation.lean and exposed
the inverse inequality name, missing nonnegativity, and mismatched
telescoping orientation. The fixes use the proper product orientation
matching the existing H2 proof, without altering theorem statements.
The 11 rational regressions passed at e59a2e8 (run 45473531101).
The new automatic cutoff and separated-promise test await retest.


## Actual nonlinearity variation, stable sidebands, and detector conditioning

The rotated nonlinearity has a genuine directional derivative along
real epsilon, not a complex-linear derivative:
d/de [fnl(a+e z)-g(a²)(a+e z)] at e=0 = c(z+conj z).
The new actual_field_first_variation theorem applies it to the
reconstructed field of the maintained Fnl using its existing constant
mode mode(L,0,L*a) and arbitrary H² perturbation. The derivative is
pointwise in space; a full Frechet derivative of the evolution map is
not asserted by this Lean theorem.

For h=H and g=c the signed quadratic sideband energy
(h+2g)x²+h y² is conserved by the linearized system.
If h>0 and h+2g>0, it bounds x²+y² uniformly in time with ratio
max(h,h+2g)/min(h,h+2g). In particular all q>0 have this positive
energy when kappa<=0 and beta<=2 gamma a². For h>0 the unstable
region is exactly h+2g<0. These are statements about linearized
sidebands, not nonlinear orbital stability or an input-uniform
simulation theorem. The neutral boundary may exhibit secular growth.

There is also a direct detector conditioning obstruction. For the
three-mode symmetric Galerkin system S={0,+k,-k}, the rotating
finite-dimensional ODE is polynomial in real coordinates. Its smooth
flow is differentiable in initial data for each fixed finite time
(the conserved radius supplies existence); the derivative solves the
variational equation. In the explicit unstable example L=2*pi,
k=(1,0), kappa=0, a=1, beta=2, gamma=1/2, perturb the constant initial
physical field by e(1+i) cos(x1). The exact variational field in the
rotating frame is exp(t)(1+i)cos(x1). Choose the fixed real detector
chi(x)=cos(x1). The global phase does not affect J. Differentiating
J=integral chi |u|² at e=0 gives
  dJ/de = 2 exp(t) integral cos²(x1) = L² exp(t).
The unweighted initial L² perturbation direction has norm L, and
the weighted H² norm is 2L (q=1). Therefore the local detector
condition number in this direction is L exp(t) in L² or
(L/2) exp(t) in H². For each fixed t, sufficiently small nonzero e
yields at least half this amplification by the derivative limit.
This rules out a uniform polynomial-in-time readout Lipschitz
constant for this Galerkin subclass, not a polynomial-time algorithm.
The argument is analytical; the smooth finite-flow derivative and
the specific cosine integral bridge have not been kernel-verified.
It does not imply an exponentially small decision margin, and the
precision-bit cost of resolving exp(-t) is only linear in t.

SidebandAmplification.lean adds nine candidate roots: scalar and
actual-field directional derivatives, energy conservation and
positive energy bound, sufficient stable background condition,
unstable sign equivalence, and exact quadratic detector expansion
and derivative. The latter two use the original Jdet identity, not
a surrogate receiver. A rational regression compares actual Fourier
field evaluations for symmetric positive and negative perturbations
against the derivative formula at nonzero mode. Full verification
of these additions is pending.


## Kernel verification and completion (26 November 2026)

All ten Phase XXV modules compile on Lean 4.23.0 with the pinned Mathlib. Seven needed no change:
`FiniteNonlinearResidual`, `CertifiedIntegrator`, `WeakNormApproximation`, `GalerkinConservation`,
`WeakGlobalComparison`, `FiniteDetector` and `RestrictedResourceBudget`. The remaining failures were
elaboration problems; no theorem statement was changed.

- `SidebandAmplification`: `λ` is a reserved keyword and cannot be a binder (renamed in
  `growing_rate`, `eigenvector`). Numerals are now normalized explicitly in `exponential_solution`.
  The `convert` goals of `rotated_fnl_deriv` left unapplied `Pi` arithmetic, now evaluated pointwise.
  `mul_neg_iff_of_pos_left` is absent from the pinned Mathlib, so `unstable_sideband_iff` is proved
  directly.
- `UniformGalerkinRadius`: beta-reduction before `dmul_apply` (`kinetic_norm_bound`); `Torus.field`
  disambiguated from Mathlib's `field` simproc (`potential_zero`); in `weak_readout_error` the norm
  sum and the weak error bound are restated in the normal form the detector Lipschitz inequality
  produces.
- `RoundedStepBudget`: the implicit physical parameters of `galerkin_lipschitz` and
  `galerkin_time_modulus` are now passed explicitly; a heartbeat-exhausting `simpa` over an ℓ² norm
  is replaced by a direct rewrite of the zero time index (`rounded_galerkin_euler`).

New theorem `SidebandAmplification.stable_sideband_ratio_bound`: if `h > 0` and `h + 2g > 0`, every
solution of the linear sideband system satisfies
`x(t)² + y(t)² ≤ (max(h, h+2g) / min(h, h+2g)) (x(0)² + y(0)²)` for all `t`. The earlier
`stable_sideband_bound` holds without its positivity hypotheses (which it does not use) and is
uninformative without them; the new theorem gives the uniform-in-time bound stated above.

Statement review: each theorem's hypotheses are checkable certificates or physical assumptions
(radius bounds, cutoff weights, real detector, per-step update defects). None embeds its conclusion.
`exists_certified_galerkin_readout` is unconditional in the trajectory: it constructs the Galerkin
trajectory and bounds the readout error from the initial H² bound alone. `RestrictedResourceBudget`
contains scalar majorants only and is not a complexity theorem.

Verification on the merged head (main through PR #108 merged into this branch): `lake build PVNP`
passed (7,419 jobs). `lake env lean audit/AxiomAudit.lean` with `audit/check_axioms.py` passed for
all 1,003 registered declarations (every Phase XXV theorem included), using only `propext`,
`Classical.choice` and `Quot.sound`; no `sorryAx` occurs. The Lean tree is that of merge commit
`f057fec`; later commits change documentation and generated dashboard data only. The 13 rational Fourier regressions
(`pvnp/tests/test_phase_xxv_rational_fourier.py`) pass.

Classification: I-11 stays Restricted; its estimate moves from 55% to 65%, because two of its three
recorded obligations — an effective tail bound along the trajectory and certified time
discretization — are now kernel-checked in the weak norm that the detector uses. Still open:
a formal bit-complexity (Turing-machine) implementation, and the regime where `LF(R_B)·T` is
superlogarithmic. There, the sufficient mode and step counts are exponential and the linearized
sideband modes give genuine exponential sensitivity, but no runtime lower bound is proved.
