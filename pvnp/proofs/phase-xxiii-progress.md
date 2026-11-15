# Phase XXIII: forced escape and finite Fourier certificates

Base: `b89993b`, main after merged PRs #95 and #96. This is partial mathematical
progress, not closure of the five remaining targets. No percentage is increased.

## Source and PR audit

PR #95 (`e23e749`, merge `df8bd7f`) supplied the four Phase XXII modules;
PR #96 (`49c262a`, merge `a6e2e3b`) applied the 80/2/5/3/1 ledger.
The relevant merged history #88–#94 supplies physical readout, the sign-blind
encoding, charged zero-mode devices, distributed causality and the false well.
Open PRs #44, #62, #63, #67 and #71 were enumerated and their scope inspected.
They concern earlier restricted bounds, prior proof integration, release staging,
or III-22. None supplies the missing universal SAT bound or nonlinear simulation.
They are not merged by this work. Old PR statements about absent kernel verification
are historical and are not evidence for the present head.

## I-3: 60% → 60%, Restricted

The task's baseline is 60%; the merged registry already said 70%. The registry's
70% is retained as its historical research estimate, with no increase. These are
subjective estimates, not measured proof coverage or probabilities.

New declarations, namespace `PVNP.SATDynamics`:

- `energy_cap_trapped`
- `readout_requires_energy_excursion`
- `bounded_forcing_cannot_readout`
- `every_corner_requires_excursion`

Mathematical derivation: write the three positive-literal scores as
`s_i(t)=(1+Re Ψ_i(t))/2`. They are continuous for an admissible continuous field.
Inside `s_i≤1/8`, the existing polynomial inequality gives
`E(t)≥1+(s_0+s_1+s_2)/2`. At the first crossing of `max_i s_i=1/8`, therefore,
`E≥17/16`. An energy cap strictly below `17/16` prevents crossing on the entire
finite interval. Unlike the old theorem, no monotonicity is used. At the false
corner `E(0)=1`; successful readout `E(T)<1/8` consequently requires some
`t∈[0,T]` with `E(t)-E(0)≥1/16`. Any forced extension with a certified peak-increase
budget below `1/16` fails on this satisfiable instance.

Polarity-flip symmetry transports the bound to every fixed corner: for each
preparation corner a there is a satisfiable flipped formula requiring the same
1/16 peak increase along any successful continuous admissible trajectory.

The strict inequality is intentional: equality at the barrier is not excluded.
The bound concerns the dimensionless sign-blind energy, not joules, integrated
work, control power or stochastic escape probability. It is a necessary cost,
not a sufficient escape protocol. It applies to this preparation and this false
well; it is not universal over preparations or algorithms.

### Constructive escape with a matching optimal barrier

`SATForcedEscape.lean` supplies `escape_admissible`, `escape_continuous`,
`escape_start`, `escape_end`, `escape_curvature`, `escape_energy`,
`escape_energy_bound`, `escape_readout`, `trapEnergy_decomposition`,
`trapEnergy_mean_lower`, `trapEnergy_before_saddle`, `trapEnergy_saddle`,
and `readout_requires_sharp_peak`, all in `PVNP.SATDynamics`.

The prescribed common phase command is Ψ_i(t)=exp(iπ(1−t)). It starts at the
false corner, has unit modulus throughout, and reaches the true corner at time
one. Its squared components are equal, so graph curvature and sign-blind coupling
vanish. For s=(1+cos(π(1−t)))/2 its energy is (1−s)²(1+5s), bounded by 32/25 via

    32/25 − (1−s)²(1+5s) = (s−1/5)²(7−5s).

The terminal energy is zero. This is a controlled escape for the fixed seven-clause
instance, not a solver for arbitrary SAT or a frozen-PDE realization theorem.

The lower bound matches it. Set S=x+y+z. The exact cyclic sum-of-squares identity is

    trapEnergy(x,y,z) = (1−S/3)²(1+5S/3)
      + Σ_cyclic (1/2−23S/54+2x/3+7z/9)(x−y)².

For nonnegative scores and S≤3/5, the coefficients are positive. Energy is at
least one before this surface and at least 32/25 on S=3/5. Every successful
continuous path from the false corner crosses this surface by the intermediate
value theorem. Nonnegative coupling terms can only increase energy. Therefore
**every successful path crosses energy 32/25 and the explicit path never exceeds
it**. The optimal peak increase is 7/25 above initial energy one on this fixed
instance. The weaker 1/16 theorem is retained. No SI energy conversion or finite-bit
controller cost follows from these statements.

Still missing: a formula-dependent controlled evolution with SAT and UNSAT
correctness and explicit preparation, time, physical energy, curvature, precision
and readout costs. The prior `sat_iff_corner_sweep` proves exhaustive correctness,
not the existence of that continuous controlled device. No Exact promotion.

## I-11: 55% → 55%, Restricted

New declarations in `PVNP.TorusGalerkin`:
`trunc_norm_le`, `trunc_sub`, `galerkin_support`, `galerkin_lipschitz`,
`consistency_bound`, `galerkin_consistent`, `residual_certificate`,
`no_uniform_H2_cutoff`, `higher_regularity_tail`, `certified_readout`.

For a finite mode set S, let P_S be the repository's Fourier truncation in the
weighted ℓ² coordinates representing H². Define the finite vector field

    G_S(t,v) = P_S G(t,P_S v).

Its output vanishes outside S. Orthogonal coordinate deletion is contractive,
so the finite vector field has the same local Lipschitz constant LF on an H²
ball. The triangle inequality and contraction give the actual consistency bound

    ||G_S(t,v)-G(t,v)|| ≤ LF ||P_S v-v|| + ||P_S G(t,v)-G(t,v)||.

Both tails tend to zero for each fixed (t,v), by ℓ² summability. Thus the finite
vector fields converge pointwise to the actual frozen-PDE vector field. This
is not yet convergence of numerically computed trajectories.

For a candidate trajectory W with finite-system residual η and nonlinear tail τ,

    ||W' - G(t,W)|| ≤ η + τ.

`certified_readout` feeds that sum directly into the already proved frozen-flow
Gronwall detector estimate. All continuity, derivative, radius and initial-error
hypotheses are explicit. The theorem does not assume its detector conclusion.
The finite-system residual and nonlinear tail still need numerical certification;
this phase supplies the composition theorem, not an executable certifier.

A stronger regularity hypothesis yields an explicit tail rate. If
`Σ_k wt(L,k)^2 |v_k|² ≤ B`, this is a squared H⁴ budget in the weighted coordinates,
and if every omitted mode satisfies `wt(L,k)≥K>0`, then

    ||P_S v-v||² ≤ B/K².

Proof: on every omitted coordinate, multiply `K²≤wt²` by `|v_k|²`, sum the
nonnegative inequalities, and use the ℓ² norm identity. On retained coordinates
the error is zero. Summability of the H⁴ series and its budget are hypotheses.
Neither propagation of that budget nor a polynomial bound for it is claimed.

A rigorous obstruction shows why the stronger hypothesis matters: for every
finite S, choose k outside S and v=δ_k in the weighted coordinates. Then
`||v||=1`, `P_S v=0`, and `||P_S v-v||=1`. Consequently an H² bound alone cannot
select a uniform finite H² cutoff, regardless of the geometry of S. This is a
statement about fixed Fourier truncation, not about all representations, adaptive
algorithms, detector accuracy, or Turing simulability. A far-out mode can have
small physical L² mass while keeping H² norm one.

Still missing: construction and convergence of the Galerkin trajectory itself,
effective propagated regularity, time discretization, numerical residual generation,
and arithmetic bit complexity. Qualitative compactness of an individual trajectory
could give uniform-in-time tails without giving a computable or polynomial rate.
The full charged class has no polynomial simulation theorem here. No Exact promotion.

## I-32: 20% → 20%, Open

No new theorem is claimed. The precise existing declarations are
`ExpanderInterface.expanderGrowth_SAT_iff` and
`expanderGrowth_implies_P_ne_NP`. In the charged constant subclass the equivalence
with P ≠ NP is partly a quantifier issue: under separation no such polynomial
constant device decides SAT, so the universal device statement is vacuous in that
subclass. It is not an independent geometric lower bound for arbitrary deciders.
The original general interface theorem remains unproved. A spatial interface
invariant must also cover spatially constant registers with charged temporal
computation, or explicitly justify excluding them. The failed separator-price
argument is retained. No Exact promotion.

## I-2: 15% → 15%, Open

No new nonconstructibility theorem is claimed. `NonconstructibleFamily` defines
`npFamilyModel` and `wavefieldModel`, and proves `npFamily_separation_iff` and
`wavefield_separation_iff` for those specified models. Those are not a classification
of every conceivable preparation model. The new no-uniform-cutoff result supplies
a representation obstruction for fixed Fourier truncations; it does not prove
that an input-indexed family with an NP verifier requires superpolynomial preparation.
That inference would confuse an approximation representation with a computational
lower bound. A stronger family model still needs an explicit uniform constructor,
precision, representation, verifier and all resource costs. No Exact promotion.

## I-16: 15% → 15%, Open

No new universal lower-bound theorem is claimed. `DepthBarrier.wccDepth_SAT_iff`
and `CookLevin.Gen.satLowerBound_iff_P_ne_NP` identify the exact outstanding target.
An invariant for arbitrary deterministic deciders would need a proven per-transition
bound and a necessary large value on arbitrarily large SAT inputs for every correct
decider. The physical barrier established here is preparation-specific and has a
constant height; it supplies neither condition. Projection dimension likewise is
not a time lower bound on an arbitrary machine. Single-tape crossing bounds are
preserved, without presenting a quadratic bound as superpolynomial. No Exact promotion.

## I-37: original scope Restricted, revised specification proved

The original sentence leaves “ψ-electron” undefined. In `SpatialToroidalLocking`,
`MField = ℕ → ℓ2`, `pt L Ψ x i = field L (co L (Ψ i)) x`, and the reference
component is exactly i=0. The relative field is
`pt L Ψ x (i+1) * conj (pt L Ψ x 0)`. `Locked` requires unit modulus, vanishing
sign-blind density and zero gradient energy for every component.

`locked_iff` proves that these fields are spatially constant. There is no extra
charge, spin, winding or localization condition, nor an independent electron-model
identification theorem. Those features are not silently added as new requirements;
the point is that the original term has no definition to which correspondence can
be proved. Defining it to mean a constant reference component is an amendment.

Therefore the revised static specification is exactly proved by `sat_iff_locked`,
but the original manuscript claim should remain Restricted. The prior proofs and
historical addenda are preserved. The scope correction changes the ledger to
79 Exact / 3 Restricted / 5 Refuted / 3 Open / 1 Interpretive. The distinction between
existence, invariance and dynamic acquisition remains explicit.

## Verification

Verification results are recorded below after running the gates. New declarations
are imported by `PVNP.lean` and registered individually in `audit/AxiomAudit.lean`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
