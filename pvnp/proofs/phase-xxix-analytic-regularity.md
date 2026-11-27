# Phase XXIX: analytic regularity, end-to-end simulation, and verified TM arithmetic (27 November 2026)

Base: `main` at `07929a7` (Phase XXVIII merged). New Lean modules:
- `lean/PVNP/AnalyticNorm.lean`
- `lean/PVNP/AnalyticPropagation.lean`
- `lean/PVNP/AnalyticSimulation.lean`
- `lean/PVNP/SweepArith.lean`

New numerical probe: `pvnp/phase_xxix/radius_experiment.py` (evidence only).

## Outcome

- **Proved, uniformly over Galerkin truncations.** Analytic regularity of the frozen cubic–quintic
  flow propagates globally, with an analyticity radius that decays **at most exponentially**:
  `σ(t) ≥ σ₀ 4^{−⌊t/τ⌋}`. The rate `1/τ` is polynomial in the conserved data and in the initial
  analytic norm.
- **Proved, end to end.** From analytic data, a Fourier cutoff plus the Phase XXVIII certified
  Taylor integrator reaches the true PDE state within any `ε`. All parameters are explicit.
- **Polynomial simulation.** It holds for horizons `T = O(τ log n)`, with logarithmic dependence on
  the accuracy. For polynomial horizons the proved cutoff is exponential in `T/τ`. Whether the
  radius really shrinks exponentially is **open**: the numerical evidence is inconclusive, and the
  energy method cannot decide it.
- **Verified machine arithmetic, first layer.** Binary addition, subtraction and comparison run
  on the repository's actual single-tape TM, with exact transition counts. Multiplication,
  division, rational, fixed-point and complex arithmetic and the evaluator itself are not built.
- **I-11 stays Restricted; issue #99 stays open; I-2, I-16 and I-32 stay Open.** Classical P versus
  NP remains unresolved.

## 1. Analytic norms (`AnalyticNorm`)

In the repository's `H²` coordinates `v_k = (1 + q_L(k)) ψ̂_k`,
`A_σ(v)² = Σ_k e^{2σ|k|}|v_k|²`, with `|k| = |k₁| + |k₂|`. This is the requested norm with the
`L`-scaled weight `(1 + q_L(k))²`.

- **Analytic Banach algebra** (`asum_mulH`, `anorm_mulH_le`):
  `A_σ(mulH v w) ≤ C_A A_σ(v) A_σ(w)`, with the same constant `C_A` as the `H²` algebra estimate.
  - The proof lifts `v` to `ṽ_k = e^{σ|k|}|v_k|`.
  - Subadditivity `|k| ≤ |k − j| + |j|` turns the weighted convolution into a convolution of lifts
    (`aw_mulH_le`).
  - The repository's `H²` estimate is then applied to the lifts.
- Conjugation (`asq_conjH`) and the free dispersion `U(t)` (`asq_U`) are isometries. The
  truncation `P_S` is a contraction (`asq_trunc_le`).
- `anorm_Fnl_le`: `A_σ(Fnl u) ≤ |β|C_A²A_σ(u)³ + |γ|C_A⁴A_σ(u)⁵`.
- Interpolation (`asq_interp`): `A_{σ'}(v)² ≤ e^{2σ'N}‖v‖² + e^{−2(σ−σ')N}A_σ(v)²` for
  `σ' ≤ σ` and every `N`.
- Tails (`tail_le`): `Σ_{|k|≥N}|v_k|² ≤ e^{−2σN}A_σ(v)²`.

No constant depends on a cutoff.

## 2. Propagation (`AnalyticPropagation`)

The setting is a physical-picture Galerkin trajectory `u' = −i(A_S u + P_S Fnl u)`, supported
in `S`.

- **Dispersion cancels.** `d/dt A_σ(u)² ≤ 2A_σ(u)A_σ(Fnl u)` (`hasDerivAt_asq`,
  `deriv_asq_le`), because `Re⟨u_k, −i om_k u_k⟩ = 0` (`inner_disp_zero`). The skew-adjoint
  fourth-order dispersion contributes nothing.
- **Local step** (`local_propagation`). If `A_σ(u(t₀)) ≤ M`, then `A_σ(u(t₀+s))² ≤ 4M²` for
  `0 ≤ s ≤ τ(M) = 1/(2(8|β|C_A²M² + 32|γ|C_A⁴M⁴ + 1))`. The proof is the comparison principle
  (`image_le_of_deriv_right_lt_deriv_boundary`) with barrier `2M²e^{ct}`.
- **Global bound** (`global_propagation`, `radius_at`). Suppose `‖u(t)‖_{H²} ≤ R` for all `t`, as
  conservation of mass and Hamiltonian gives for actual trajectories. Suppose also `2R ≤ M` and
  `A_{σ₀}(u(0)) ≤ M`. Then `A_{σ₀/4^j}(u(t))² ≤ 4M²` for `t ∈ [jτ, (j+1)τ]`. At each restart,
  interpolation with `N = ln 2/(2σ')` brings the norm back to `M` at radius `σ/4`. Hence
  `σ(t) = σ₀ 4^{−⌊t/τ⌋} ≥ σ₀ e^{−(ln 4)(t/τ + 1)}`.

## 3. End-to-end simulation (`AnalyticSimulation`)

- `galerkin_analytic` applies the global bound to every actual Galerkin trajectory. `R` comes from
  the conserved quantities, or from `uniformRadius`, which does not depend on `S`.
- `pde_apriori` is the matching bound for PDE trajectories.
- `analytic_galerkin_pde_error` is the weak (`L²`) Galerkin-to-PDE error bound.
- `analytic_end_to_end` is the full statement: the certified integrator, run on the Galerkin
  system with per-step implementation errors `≤ ρ`, ends within `ε₁ + ε₂` of `U(T)w(T)`.

**Explicit parameters** (all proved sufficient). Write:
- `J = ⌊T/τ⌋` and `σ_T = σ₀4^{−J}`;
- `M_tot = M + |β|C_A²(2M)³ + |γ|C_A⁴(2M)⁵`;
- `λ = 4(Ω + 64|β|C_A²(R+1)² + 4096|γ|C_A⁴(R+1)⁴)`;
- `L' = Ω + LF(2(R+1))`.

| Quantity | Sufficient value |
|---|---|
| Fourier cutoff `N` (every omitted mode has `\|k\| ≥ N`) | `σ_T N ≥ LF(R)T + log(M_tot(1+T)/ε₂)` |
| Retained modes | `\|{\|k\| < N}\| ≤ 2N² + 2N + 1` |
| Dispersion bound `Ω` | `max_S (κ − q_L(k))² ≤ (\|κ\| + (2π/L)²N²)²` |
| Time steps | `N_t` with `(T/N_t)(2λ + 2) ≤ 1` |
| Taylor order `q` | `2^{q+1}ε₁ ≥ 4(R+1)N_t e^{L'T}` |
| Per-step precision `ρ` | `2N_t e^{L'T}ρ ≤ ε₁` |
| Weak error at `T` | `≤ ε₁ + ε₂` |

**Detector and decision margin.** The repository's quadratic detector is Lipschitz in the weak
norm on bounded sets (`weak_detector_lipschitz`). A margin-`m` readout is therefore preserved once
`ε₁ + ε₂ ≤ m/(C_det(2R + 1))`. This composition is the Phase XXII–XXV argument and is not
restated as a new theorem.

**Where the exponentials are.**
1. **The cutoff.** `N ∝ 4^{T/τ}(LF·T + log(1/ε))/σ₀`. This is the only factor exponential in the
   horizon, and it comes from the radius bound.
2. **The precision.** `log₂(1/ρ) ∝ L'T`. It is polynomial in `N` and `T`, but `L'` contains the
   dispersion bound `Ω ∝ N⁴`. That is because Gronwall was applied to the physical-picture field
   (Phase XXVIII). The dispersion is unitary, so an interaction-picture estimate would remove `Ω`
   from the exponent. That refinement is not formalized.
3. **Coefficient access.** `π` and `C_A = 4√(SL(L))/L` must be approximated. `SL` is an infinite
   lattice sum with a computable tail. This is not formalized.
4. **Preparation.** The analytic norm `A_{σ₀}(u₀)` of the input must be bounded. A degree-`n`
   trigonometric polynomial has `A_{1/n}(u₀) ≤ e‖u₀‖_{H²}`.

**Admissibility conditions under which every factor is polynomial in the input size `n`:**
1. analytic initial data with `σ₀ ≥ 1/poly(n)` and `A_{σ₀}(u₀) ≤ poly(n)`, which includes every
   finitely described input of degree `≤ n`;
2. a horizon `T ≤ c·τ(M) log n`;
3. a decision margin with `log(1/m) ≤ poly(n)`;
4. rational parameters `L, κ, β, γ`.

These conditions, together with a machine-level operation count (§5), give
`P_phys ⊆ P_TM` for this restricted class. The original general `H²`-admissible class is not
covered: `no_uniform_H2_cutoff` (Phase XXIII) shows that it admits no uniform cutoff.

## 4. Is exponential radius decay necessary?

**Theory.**
- The factor `1/4` per step is intrinsic to this energy method. Restarting at `M ≫ R` loses less
  radius per step, `1 − O(1/log(M/R))`, but the step shrinks like `1/M⁴`. The best rate per unit
  time is at `M ≈ 2R`.
- Methods that give *polynomial* lower bounds on the radius for related dispersive equations,
  such as almost-conservation of modified analytic energies in Bourgain spaces, use dispersive
  smoothing. That machinery is not available here and is not formalized.
- For the linear flow the radius is exactly preserved, and plane waves keep it infinite. So
  exponential decay is not necessary in general. For the nonlinear flow on `T²`, energy cascades
  exist for related equations, so some decay should be expected.
- **No rigorous counterexample** (a solution whose radius provably shrinks exponentially) and
  **no polynomial lower bound** was found.

**Numerical probe** (`radius_experiment.py`; evidence only).
- Setup:
  - the exact Galerkin system on `T²` with `L = 2π`, `κ = 0`, `β = γ = 1`, and data
    `A(cos x + ½e^{i(x+y)} + 0.3 cos 2y)`;
  - a quintic-alias-free grid (`M ≥ 6K + 1`);
  - exact dispersion with Lawson RK4.
- `σ_eff(t)` is the fitted exponential decay rate of `max_{|k|=n}|ψ̂_k|` in `n`. Mass is
  conserved to about `10⁻⁵` over the runs.

Results (`pvnp/phase_xxix/results/`, amplitude `A = 1`, `dt = 2·10⁻³`):

| t | σ_eff (K = 24) | σ_eff (K = 32) | σ_eff (K = 40) |
|---|---|---|---|
| 2 | 0.7380 | 0.7380 | 0.7380 |
| 10 | 0.6354 | 0.6352 | 0.6352 |
| 20 | 0.5700 | 0.5616 | 0.5616 |
| 28 | 0.4933 | 0.4662 | 0.4662 |
| 34 | 0.4003 | 0.3908 | 0.3633 |
| 40 | 0.2905 | 0.3115 | 0.2970 |

- **The decline is converged dynamics, not a cutoff artefact.** `K = 32` and `K = 40` agree to four
  digits up to `t = 28`. `K = 24` departs after `t ≈ 18`, when its spectrum reaches the truncation
  boundary.
- **The effective radius shrinks, at an accelerating rate.** The exponential rate
  `−d ln σ/dt` over the windows `[2,10], [10,20], [20,28], [28,40]` is
  `0.019, 0.012, 0.023, 0.038`. The log–log slope is `0.09, 0.18, 0.55, 1.26`. No single power law
  `t^{−α}` with small `α` fits, so the data do not support a polynomial lower bound on the radius.
  They are consistent with exponential-type decay at late times.
- At amplitude `A = 2` the cascade is much faster: `σ_eff` goes from 0.39 at `t = 1` to 0.20 at
  `t = 3`. The spectrum reaches the boundary almost immediately, and explicit RK4 loses accuracy
  after `t ≈ 3` (mass drift above 1%). That run is not converged.
- **Comparison with the theorem.** For `A = 1`, `M ≈ 2R` and `C_A ≤ 6` give
  `τ(M) ≈ 10⁻⁸`. The proved bound is therefore about `10⁹` times more pessimistic than the observed
  rate (about 0.02–0.04), although both describe decay.

**Conclusion.** Exponential decay is not a necessity for this equation in general: it is absent
for linear and plane-wave solutions. For generic cubic–quintic interactions, the converged
numerics show genuine, accelerating loss of analyticity over the window studied, so the
exponential character of the proved bound is plausibly real rather than only an artefact.
Asymptotics are not determined by finite simulations, and no rigorous counterexample or
polynomial bound was found. If the true radius decays exponentially, then any **Fourier-
truncation** simulation needs cutoffs exponential in polynomial horizons. That would still not be
a lower bound for other representations or algorithms.

## 5. Verified binary arithmetic (`SweepArith`)

Numbers are little-endian bit lists on parallel tracks (`Cell`: operand tracks `a`, `b` and a
result track `r`). Each primitive is one round trip of a sweep program. Correctness is proved on
the transducer semantics, and `Prog.reach_run` / `Prog.toTM_firstAnswer` transfer it to the
compiled single-tape TM with exact transition counts.

| Primitive | Correctness | TM transitions |
|---|---|---|
| Addition (`add_tm`) | `val r = val a + val b`, overflow bit included (`add_value`) | `2n + 2 + [carry] ≤ 2n + 3` |
| Subtraction (`sub_tm`) | `val r = val a − val b` when `val b ≤ val a`, no final borrow (`sub_value`) | `2n + 2` |
| Comparison (`cmp_tm`) | first answer `decide (val a < val b)` (`fscan_cmp`) | `2n + 4` |

**Not built:**
- multiplication (designed as shift-and-add over `n` trips, `O(n²)` transitions: the backward
  pass selects add or skip from the next multiplier bit);
- division, rational and fixed-point arithmetic, polynomial evaluation, finite convolution and
  complex arithmetic;
- the uniform evaluator built from them.

The bit-complexity results of Phases XXVII and XXVIII are therefore **not** yet mechanized at the
machine level.

## 6. Status of I-11 and issue #99

| Obligation | Status |
|---|---|
| Temporal integration | Proved (Phase XXVIII). |
| Spatial cutoff for analytic data | Proved, with a cutoff exponential in `T/τ` (this phase). Polynomial horizons are open. |
| Spatial cutoff for general `H²` data | No uniform cutoff exists (`no_uniform_H2_cutoff`). |
| Finite-bit arithmetic on the TM | Addition, subtraction and comparison proved. The rest is open. |
| Coefficient access (`π`, `C_A`) | Open. |
| Machine runtime of the evaluator | Open. |

I-11 stays Restricted, and issue #99 stays open.

## 7. Separation (I-2, I-16, I-32)

The question was whether the new nonlinear regularity yields an invariant or a construction
relevant to SAT.
- **Obstruction side.** Analytic propagation and the end-to-end simulation make the frozen device
  *easier* to simulate classically. Any physical lower bound must now come from the spatial
  cascade, that is, from a failure of polynomial radius bounds. Even that would bound the
  *simulation* of a device, not `SAT_dense` against all uniform deciders. Representation-
  independent superpolynomial obstructions still reduce to `P_TM ≠ NP_TM` (Phase XXVI). No new
  invariant was found.
- **Algorithmic side.** The analytic and Taylor structure gives efficient simulation of the
  dynamics. It does not give a polynomial-time SAT decider, because the SAT-encoding devices of
  earlier phases (corner sweeps, energy landscapes) need exponentially many trajectories or
  exponential horizons (`SATDynamics.sat_iff_corner_sweep`, `no_corner_preparation_decides`).
  No polynomial-time SAT algorithm emerged.
- `CrossingSAT.SATLowerBound` remains unproved and unrefuted. **Classical P versus NP remains
  unresolved.**

## Verification

Local, Lean 4.23.0, on the Lean tree of commit `6d1c9f3`:
- `lake build PVNP` passed (7,430 jobs). The four new modules build without warnings; the
  warnings in the log come from pre-existing modules.
- `lake env lean audit/AxiomAudit.lean` with `audit/check_axioms.py` passed for all 1,179
  registered declarations, including the 73 new ones: 54 analytic (`PVNP.Analytic`) and 19
  arithmetic (`PVNP.Discrete.SweepArith`). They use only `propext`, `Classical.choice` and
  `Quot.sound`, and no `sorryAx` occurs.
- The intermediate head `22b4d51` was also built (7,429 jobs) and audited (1,160 declarations).

Later commits change documentation, the numerical probe and its recorded output, and generated
dashboard data only. The dashboard, status registry, manuscript-alignment and release-document
checks, the Python suite and `git diff --check` pass. Hosted CI is recorded on the pull request.
