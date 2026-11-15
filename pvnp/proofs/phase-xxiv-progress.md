# Phase XXIV: trajectory approximation

Base: `ead83a5`, following merged PR #97. Work in progress; statements below
describe the mathematical construction until the verification section records
kernel checks.

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

## Verification

Pending implementation and kernel verification. No claim classification or
progress estimate is changed by this draft.
