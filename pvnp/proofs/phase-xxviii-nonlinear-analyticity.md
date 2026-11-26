# Phase XXVIII: temporal analyticity of the cubic–quintic Galerkin flow (26 November 2026)

Base: `main` at `504ccf1`. New modules: `lean/PVNP/TaylorMajorant.lean`,
`lean/PVNP/GalerkinTaylorNorm.lean`, `lean/PVNP/GalerkinTaylorSeries.lean`,
`lean/PVNP/TaylorIntegrator.lean`, `lean/PVNP/SpatialModeCount.lean`.

## The estimate

Take the finite Fourier Galerkin system in the physical picture, `u' = −i(A u + P_S Fnl(u))`. Its
Taylor coefficients `c_n` at a point satisfy
`(n+1) c_{n+1} = −i(A c_n + P_S [Fnl]_n)`, where `[Fnl]_n` is the `n`-th Taylor coefficient of the
cubic and quintic nonlinearity. That coefficient is a Cauchy product of the `c_k` (and their
conjugates) through `mulH`. With `‖mulH v w‖ ≤ C_A ‖v‖‖w‖` and `‖conj v‖ = ‖v‖`, the norms
`a_n = ‖c_n‖` satisfy
`(n+1) a_{n+1} ≤ Ω a_n + B (a⋆a⋆a)_n + G (a⋆a⋆a⋆a⋆a)_n`.
Here `Ω` bounds the free frequencies on `S`, `B = |β| C_A²` and `G = |γ| C_A⁴`.

## Kernel-checked results (namespace `PVNP.TaylorMajorant`)

- `weighted_conv_le`: `Σ_{i+j=n} w_i w_j ≤ 8 w_n` for `w_n = 1/(n+1)²`. It follows from
  `Σ_i w_i ≤ 2` (`sum_wt_le_two`) and the pointwise bound `w_i w_j ≤ 2(w_i + w_j)/(n+2)²`
  (`wt_mul_le`), which is equivalent to `(p+q)² ≤ 2(p²+q²)`.
- `cauchy_bound`, `powers_bound`: if `a_k ≤ K λ^k w_k` up to index `n`, then the Cauchy powers
  satisfy `a⋆a⋆a ≤ 64 K³ λ^n w_n` and `a⋆a⋆a⋆a⋆a ≤ 4096 K⁵ λ^n w_n`.
- `majorant`: if `a_n ≥ 0`, `a_0 ≤ K` and the recursion holds, then for all `n`
  `a_n ≤ K λ^n/(n+1)²` with `λ = 4(Ω + 64 B K² + 4096 G K⁴)`. The proof is strong induction, and
  the step uses `(n+2)² ≤ 4(n+1)³` (`wt_step`).
- `taylor_tail_le`: if `λh ≤ 1/2`, the Taylor tail after `q` terms is at most `2K(λh)^{q+1}`.

## Norm reduction for the actual nonlinearity (`lean/PVNP/GalerkinTaylorNorm.lean`)

Namespace `PVNP.GalerkinTaylor`. `cauchyH` is the coefficientwise Cauchy product through the
repository's `mulH`. `fnlCoeff L β γ c n` is the `n`-th formal Taylor coefficient of `Fnl` along
a coefficient sequence `c`, built from exactly the products in the definition of `Fnl`.

- `norm_fnlCoeff_le`: `‖fnlCoeff L β γ c n‖ ≤ |β| C_A² (a⋆a⋆a)_n + |γ| C_A⁴ (a⋆a⋆a⋆a⋆a)_n`,
  where `a = ‖c‖`. It uses `norm_mulH_le`, `norm_conjH`, and commutativity
  (`cauchy_comm`) and monotonicity (`cauchy_mono`) of the scalar product.
- `galerkin_taylor_majorant`: if `‖c_0‖ ≤ K` and
  `(n+1)‖c_{n+1}‖ ≤ Ω‖c_n‖ + ‖fnlCoeff L β γ c n‖` for all `n`, then
  `‖c_n‖ ≤ K λ^n/(n+1)²` with `λ = 4(Ω + 64|β|C_A²K² + 4096|γ|C_A⁴K⁴)`.

The hypothesis is the norm form of the Galerkin Taylor recursion
`(n+1) c_{n+1} = −i(A c_n + P_S fnlCoeff c n)`, given `‖A v‖ ≤ Ω‖v‖` and `‖P_S v‖ ≤ ‖v‖`. This
pins down the constants `Ω`, `B`, `G` for the frozen field.

## Identification with the actual trajectory (`lean/PVNP/GalerkinTaylorSeries.lean`)

This module removes the remaining hypothesis: the actual Galerkin trajectory is the sum of its
Taylor series. Nothing is assumed about the trajectory beyond its being a solution, and no
linear system replaces the nonlinear evolution.

- **Physical picture.** `hasDerivAt_phys`: if `W` is an interaction-picture Galerkin trajectory
  (`HasDerivAt W (galerkin S L κ β γ t (W t)) t`, supported in `S`), then `u(t) = U(t) W(t)` solves
  `u' = −i(A_S u + P_S Fnl(u))`. Here `A_S` (`Aop`) is the diagonal dispersion `om(k) = (κ − q_L(k))²`
  on `S`, and `‖A_S v‖ ≤ Ω‖v‖` whenever `om ≤ Ω` on `S` (`norm_Aop_le`).
- **Coefficients.** `coeff L κ β γ S u₀` is defined by the exact recursion, `c_0 = u₀` and
  `(n+1) c_{n+1} = −i(A_S c_n + P_S fnlCoeff c n)` (`coeff_zero`, `coeff_recursion`; locality is
  `fnlCoeff_congr`). `coeff_dom` gives `‖c_n‖ ≤ K λ^n/(n+1)²` whenever `‖u₀‖ ≤ K`, with
  `λ = 4(Ω + 64|β|C_A²K² + 4096|γ|C_A⁴K⁴)`. By uniqueness of power-series coefficients this means
  `‖u^{(n)}(t₀)‖ ≤ n! K λ^n/(n+1)²`. That restatement in terms of derivatives is not separately
  formalized.
- **Products of series.** `hasSum_mulH` is the Cauchy product of absolutely convergent series
  through `mulH`, proved by summing over `ℕ × ℕ` and regrouping along antidiagonals.
  `hasSum_mulH_pow` and `hasSum_Fnl` show that `Fnl(Σ h^n c_n) = Σ h^n fnlCoeff c n` for
  dominated `c`.
- **The series solves the system.** `series_solves`: on `(−r, r)` with `λ r ≤ 1/2`, the sum
  `Σ h^n c_n` is differentiable with derivative `−i(A_S v + P_S Fnl v)`. The proof is termwise
  differentiation (`hasDerivAt_series`, via `hasDerivAt_tsum_of_isPreconnected`) plus the
  recursion. The sum stays in the ball of radius `2K` (`norm_series_le`).
- **Uniqueness.** The physical field is Lipschitz on every ball, with constant `Ω + LF(R)`
  (`physField_lipschitz`). `galerkin_taylor_series` then applies `ODE_solution_unique_of_mem_Ioo`:
  if `u` solves the system with `‖u(t)‖ ≤ K` for all `t`, then
  `HasSum (h^n c_n(u(t₀))) (u(t₀ + h))` for every `t₀` and `|h| < r`.
- **Convergence of high-order Taylor integration.** `taylor_poly_error`: the degree-`q` Taylor
  polynomial at `u(t₀)` approximates `u(t₀ + h)` within `2K (λ|h|)^{q+1}`.
- **Applied to the actual trajectory.** `radius_admissible`: `r = 1/(2λ + 1)` is admissible.
  `actual_galerkin_taylor` applies the results to the global trajectory of
  `exists_uniform_galerkin` with `K = uniformRadius L κ β γ B`, which does not depend on `S`.
  `galerkin_trajectory_taylor` applies them to *every* Galerkin trajectory, with `K` the a priori
  bound `Rap` from its conserved mass and Hamiltonian.

**What this establishes.** The frozen cubic–quintic Galerkin flow is real-analytic in time. The
radius is at least `1/(2λ + 1)`, uniform along the whole trajectory. `λ` is a polynomial in `Ω`
(polynomial in the cutoff radius of `S`) and in the `S`-independent radius `K`. A single Taylor
step of size `h ≤ 1/(2λ+1)` with `q + 1` terms has error at most `2K·2^{-(q+1)}`.

## Certified multi-step integrator (`lean/PVNP/TaylorIntegrator.lean`)

The integrator restarts the order-`q` Taylor step `taylorStep q h v = Σ_{n≤q} h^n c_n(v)` from
computed values. A computed step may differ from the exact Taylor polynomial by any error of
norm at most `ρ`, from rounding or any other source.

- `tail_bound`: `‖Ψ_h(v) − taylorStep q h v‖ ≤ 2K(λh)^{q+1}` for every `‖v‖ ≤ K`, where
  `Ψ_h(v) = Σ h^n c_n(v)` (`flowSeries`). The bound holds at every point of the ball, not only on
  the trajectory.
- `flowSeries_lipschitz`: `‖Ψ_h(v) − Ψ_h(w)‖ ≤ e^{L'h}‖v − w‖` for `‖v‖, ‖w‖ ≤ K` and
  `0 ≤ h < r`, with `L' = Ω + LF(2K)`. The proof applies Gronwall's inequality
  (`dist_le_of_trajectories_ODE_of_mem`) to the two series solutions.
- `step_error`: if `‖ṽ − u(t)‖ ≤ 1`, one step from `ṽ` lands within
  `e^{L'h}‖ṽ − u(t)‖ + 2K(λh)^{q+1}` of `u(t+h)`. Here `K = K₀ + 1`, and the proof uses the
  identification `Ψ_h(u(t)) = u(t+h)`.
- `integrator_error`: discrete Gronwall. If the bound `E_N` below satisfies `E_N ≤ 1`, then
  `‖ũ_j − u(jh)‖ ≤ E_j = A^j e₀ + (Σ_{i<j} A^i)(τ + ρ)` for all `j ≤ N`. Here `A = e^{L'h}` and
  `τ = 2K(λh)^{q+1}`.
- `certified_integrator`: suppose `h = T/N` with `h(2λ+2) ≤ 1`, `2^{q+1} ε ≥ 4KN e^{L'T}` and
  `2N e^{L'T} ρ ≤ ε`, and the integrator starts from `u(0)`. Then `‖ũ_N − u(T)‖ ≤ ε`.

**Parameters.** The conditions are met with the following choices:
- `N = ⌈T(2λ+2)⌉` steps;
- order `q + 1 = ⌈log₂(4KN/ε) + L'T log₂e⌉`;
- per-step accuracy `log₂(1/ρ) = log₂(2N/ε) + L'T log₂e` bits.

All three are linear in `T` and in `log(1/ε)`, and `λ` and `L'` are polynomials in `Ω` and `K`.
The exponential sensitivity `e^{L'T}` costs `O(L'T)` bits of precision and `O(L'T)` extra Taylor
terms, not exponentially many steps.

**Derived but not kernel-checked: the operation count.** Computing `c_0..c_q` takes `O(q²)`
coefficientwise products `mulH`. Each acts on vectors supported in bounded sum sets of `S`.
Hence `O(N q² · poly(|S|))` arithmetic operations at `log₂(1/ρ) + O(log(q|S|))` bits. The
constants `π` (through `q_L`) and `C_A` must also be approximated. This count is not formalized in
a machine model.

## Spatial complexity (`lean/PVNP/SpatialModeCount.lean`)

The weak-norm comparison bounds the Galerkin error at time `T` by
`gronwallBound δ LF η T ≤ (δ + ηT) e^{LF·T}` (`gronwallBound_le`). Here `δ` is the initial tail
and `η` bounds the omitted output tail along the Galerkin trajectory. The question is therefore
how fast these tails decay.

- **Effective tails.** `weighted_tail`: if every omitted mode has weight `ω_k ≥ Θ > 0`, then
  `‖P_S ψ − ψ‖_{L²} ≤ M/√Θ` whenever `Σ ω_k |ψ̂_k|² ≤ M²`. `analytic_tail`: with `ω_k = e^{2σ|k|}`
  and omitted modes of size at least `N`, the tail is at most `M e^{−σN}`. The Phase XXV bound
  `weak_projection_tail` is the Sobolev case `ω = wt` (tail `≤ R/K`).
- **Analytic decay gives a cutoff linear in `T`.** `analytic_mode_count` and
  `galerkin_error_of_tail`: if both tails are at most `M e^{−σN}`, the weak Galerkin error at
  time `T` is at most `ε` once `σN ≥ LF·T + log(M(1+T)/ε)`. The cutoff size is linear in `T`, so
  on `T²` the number of modes is `O(N²)`, polynomial in `T` and `log(1/ε)`.
- **Sobolev decay leaves the sufficient count exponential.** `sobolev_count_lower`: from tails
  `M N^{−s}` the same sufficient condition needs `N^s ≥ M(1+T)e^{AT}/ε`. This concerns the
  sufficient condition only; it is not a lower bound on the number of modes.

**Answer to "does exponential amplification require exponentially many modes?"** Not by itself.
The amplification `e^{LF·T}` is absorbed by a cutoff linear in `T` whenever the tails decay
analytically, and it always costs only `O(LF·T)` precision bits. For the linearized
constant-background dynamics, the exponential growth sits at the fixed sideband wavenumbers
(`SidebandAmplification`), where it costs precision, not modes. What remains open is the
propagation of analytic (or Gevrey) decay by the nonlinear frozen flow, uniformly in `S`, with a
radius `σ(t)` that decays at most polynomially in `t`. Without it the conserved `H²` bound gives
only the Sobolev case and the Phase XXV count `K ∝ e^{LF(R_B)T}/m`. No lower bound on the
necessary number of modes is known either.

## Turing-machine implementation (issue #99)

The repository's verified machine layer consists of:
- `Discrete.TM`;
- the sweep-program compiler with exact step counts;
- the two-phase writers;
- the multitape Horner counters of the Cook–Levin construction, which compute polynomial step
  bounds in unary.

It has no verified binary arithmetic: no addition, multiplication or division of binary integers
with step counts. A Turing-machine implementation of the exponential evaluator (`ExpTaylorBits`)
or of `taylorStep` needs those subroutines, a representation of complex dyadic vectors indexed by
`S`, loops for the Cauchy products, and approximations of `π` and `C_A`. None of this is
formalized. The mathematical side of the cost is now explicit: steps, order and per-step
precision are given by `certified_integrator`. Only the machine-level operation count is
missing. Issue #99 stays open: its mode-cutoff obligation (effective propagated regularity) and
its bit-cost obligation are not met.

## Separation (I-2, I-16, I-32)

Phase XXVIII bears on the separation program only through simulation, and it narrows rather than
opens that route.
- For a device class whose state is a finite Galerkin trajectory with a given mode set, time
  integration is polynomial in `T`, `|S|` and the precision. Any superpolynomial physical cost
  would therefore have to come from the spatial mode count, that is, from a failure of propagated
  analytic decay.
- Even such a failure would make the *device* hard to simulate. It would not give a lower bound
  for `SAT_dense` against arbitrary uniform deciders. Lower bounds on physical devices already
  transfer to classical ones (Phase XX), so they are at least as hard as `P_TM ≠ NP_TM`.
- No new invariant or algorithm was found. I-16 is exactly `SAT_dense ∉ P_TM`. I-2 and I-32 are
  equivalent to `P_TM ≠ NP_TM` in their non-vacuous formal readings (Phase XXVI).
- `CrossingSAT.SATLowerBound` remains unproved, no polynomial-time SAT decider is known, and
  classical P versus NP remains unresolved.

## Not established

1. **Operation count in a machine model.** The integrator error analysis and parameter choice
   are kernel-checked, with per-step errors arbitrary up to `ρ`. A Turing-machine (or other formal)
   implementation of `taylorStep` with a verified operation and bit count is not.
2. **Spatial cost.** The dichotomy is now formal (`SpatialModeCount`): analytic tails give a
   cutoff linear in `T`, while Sobolev tails leave the sufficient count exponential. Propagated
   analytic or Gevrey decay of the frozen flow, uniformly in `S`, is not proved and not refuted.
   Without it the Phase XXV count `K ∝ e^{LF(R_B)T}/m` stands.
3. **Turing-machine implementation** of the exponential or nonlinear evaluator: not done.
4. **Separation.** No new mechanism for I-2, I-16 or I-32 and no polynomial-time SAT algorithm.
   `CrossingSAT.SATLowerBound` remains unproved; classical P versus NP remains unresolved.

## Verification

Local, Lean 4.23.0, on the Lean tree of commit `94446fd`:
- `lake build PVNP` passed (7,426 jobs). The five new modules build without warnings; the
  warnings in the log come from pre-existing modules.
- `lake env lean audit/AxiomAudit.lean` with `audit/check_axioms.py` passed for all 1,106
  registered declarations. That includes the 86 new Phase XXVIII declarations: 13
  `TaylorMajorant`, 9 `GalerkinTaylorNorm`, 48 `GalerkinTaylorSeries`, 10 `TaylorIntegrator` and
  6 `SpatialModeCount`. They use only `propext`, `Classical.choice` and `Quot.sound`, and no
  `sorryAx` occurs.

Later commits change documentation and generated dashboard data only. The dashboard (13 groups),
status registry, manuscript-alignment and release-document checks, the Python suite (89 tests)
and `git diff --check` pass. Hosted CI is recorded on the pull request.
