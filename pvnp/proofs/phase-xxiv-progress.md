# Phase XXIV: trajectory approximation

Base: `ead83a5`, following merged PR #97. The construction below is implemented in
`lean/PVNP/TorusGalerkinTrajectory.lean` and kernel-checked (see Verification).

## Mathematical construction before implementation

Let P_S be the finite Fourier projection and r_R the repository's radial
retraction onto the H² ball of radius R. Use the finite vector field

    F_S(t,x) = P_S G(t,r_R(P_S x)).

Projection is contractive and r_R is 2-Lipschitz. Thus F_S is globally
2 LF(R)-Lipschitz, continuous in time and bounded by LF(R)R. Picard–Lindelöf
therefore gives trajectories on every finite time interval. Starting at P_S u₀,
the coordinates outside S remain zero because their derivative vanishes.

For an exact interaction-picture trajectory w(t) bounded by R, both w and P_S w
lie in the retraction ball, so

    ||F_S(t,w(t)) - G(t,w(t))||
      ≤ LF(R)||P_S w(t)-w(t)|| + ||P_S G(t,w(t))-G(t,w(t))||.

Each continuous trajectory on a compact time interval has compact image. A
uniformly bounded family of projections converging pointwise to the identity
converges uniformly on compact sets: cover the compact image by finitely many
small balls, choose one cutoff for all centers, and use contraction to control
the rest of each ball. Apply this to the state trajectory and its continuous
nonlinear vector-field image. The displayed residual then tends uniformly to
zero, without assuming a quantitative Fourier tail modulus.

Compare the finite trajectory with w using F_S as the common globally Lipschitz
vector field. The finite trajectory has residual zero; w has the above residual.
Gronwall gives a uniform error controlled by the initial projection error and
the residual. This avoids assuming that all finite trajectories already satisfy
the exact solution's conservation bounds. If R has positive slack above the
exact trajectory norm, sufficiently accurate finite trajectories stay inside R;
the retraction is then inactive and they solve the original Galerkin equation.

This argument gives qualitative approximation, not an effective tail modulus,
finite-bit implementation, or polynomial-time Turing simulation. Compactness
must not be presented as a computable resource bound.

## Lean statements

Namespace `PVNP.TorusGalerkin`; `clipped S … R t v = P_S Gtr(t, P_S v)`, where `Gtr` applies
the retraction `retr R` before the frozen vector field `Gf`.

- `trunc_lipschitz`, `compact_uniform_tail`: truncation is 1-Lipschitz, and pointwise Fourier
  convergence is uniform on every compact set of `H²` states.
- `clipped_lipschitz`, `clipped_bound`, `clipped_continuous_time`, `clipped_support`,
  `clipped_eq_galerkin`: the clipped field is globally `2·LF(R)`-Lipschitz, bounded by `LF(R)·R`,
  continuous in time, supported on `S`, and equal to the Galerkin field on the `R`-ball.
- `exists_local_clipped`, `exists_global_clipped`: Picard–Lindelöf on `[−T, T]`, glued by
  uniqueness into a global trajectory; `clipped_trajectory_support`: coordinates outside `S` stay
  zero.
- `clipped_uniform_consistency`: along a continuous trajectory bounded by `R` on a compact time
  set, the clipped field converges uniformly to `Gf`.
- `clipped_trajectory_error`: Gronwall comparison using the clipped field for both curves, with no
  radius hypothesis on the finite trajectory.
- `exists_convergent_clipped`, `exists_convergent_galerkin`: uniform convergence on every compact
  forward interval; with one unit of radius slack the cutoff is eventually inactive, so the
  trajectories solve the original Galerkin system there.
- `frozen_galerkin_approximation`: for every frozen solution `u`, every `T ≥ 0` and `ε > 0` there
  are a finite mode set `S` and a trajectory `W` of the Galerkin system with `W(0) = P_S u(0)`,
  support in `S`, and `‖e^{tA} W(t) − u(t)‖_{H²} < ε` on `[0, T]`.

## Scope

This is qualitative convergence of actual finite-dimensional trajectories, the step recorded as
missing in Phase XXIII. The mode set `S` comes from compactness and is not computed from the data:
no tail modulus, rate, time discretization or arithmetic cost is established. I-11 therefore stays
Restricted at 55%, with remaining obligation: an effective tail bound along the trajectory,
certified time discretization and counted bit complexity.

## Verification

The draft head `0762634` failed hosted CI. Fixes in the completion commit:

- `clipped_uniform_consistency` timed out in `isDefEq`: elaborating `(continuous_Gf hL).comp …`
  against the target lambda forces the higher-order unification `?g ∘ ?f =?= fun t => …`. The
  composite is now elaborated first and then matched; the final arithmetic uses `linarith` on an
  explicit identity instead of `nlinarith` with a `let`.
- `clipped_trajectory_support` used `ContinuousLinearMap.restrictScalars_apply`, absent from the
  pinned Mathlib; it now uses the repository's `Torus.hasDerivAt_apply`.
- `exists_convergent_clipped`: a redundant `ring` after `field_simp` was removed, and the final
  chain uses `gronwall_diagonal_scale` at `T` explicitly.

Local results on the completion commit (Lean 4.23.0): `lake build PVNP` passed, 7,409 jobs; 76 Python regressions, 13 dashboard check groups, the status registry, manuscript-alignment and release-document checks passed; local axiom audit of the 912 registered declarations still running at this commit (the hosted `lean` job runs the same audit).
No classification or progress estimate changes.
