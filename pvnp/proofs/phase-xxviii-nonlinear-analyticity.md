# Phase XXVIII: temporal analyticity of the cubic–quintic Galerkin flow (26 November 2026)

Base: `main` at `504ccf1`. New module: `lean/PVNP/TaylorMajorant.lean`.

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
discharges the identification of the constants `Ω`, `B`, `G` for the frozen field. What remains
is that the actual trajectory is the sum of its Taylor series.

## Consequences, once the estimate is applied to the actual trajectory

With `K = R`, the conserved radius bound (`TorusGalerkin.galerkin_apriori` and `uniformRadius`),
the following would hold:
- The Galerkin solution is analytic in time with radius at least `1/λ`, where
  `λ = 4(Ω + 64|β|C_A²R² + 4096|γ|C_A⁴R⁴)`. This is polynomial in the frequency bound `Ω` and in
  `R`.
- A Taylor step of size `1/(2λ)` with `q` terms has local truncation error at most
  `2R·2^{-(q+1)}`. Reaching time `T` takes `2λT` steps.
- The `e^{LF·T}` stability factor then costs about `LF·T` extra bits per step.

So the *temporal* cost is polynomial in `T`, `Ω`, `R` and the precision bits. `Ω` grows only
polynomially with the cutoff radius of `S`.

## Not established

1. **Identification.** The actual Galerkin trajectory is the sum of its Taylor series. The
   constants are now identified (`galerkin_taylor_majorant`), but the series identification is not. This needs analyticity of
   polynomial ODE flows: construct the series, sum it, and identify the sum by uniqueness. It is
   not formalized. Until it is, the consequences above are conditional.
2. **Spatial cost.** The number of modes needed (`K ∝ e^{LF(R_B)T}/m` from Phase XXV) is
   unchanged. Improving it needs propagated Sobolev, analytic or Gevrey decay of the true
   solution. No such bound is proved here, and none is refuted.
3. **Turing-machine implementation** of the exponential or nonlinear evaluator: not done.
4. **Separation.** No new mechanism for I-2, I-16 or I-32 and no polynomial-time SAT algorithm.
   `CrossingSAT.SATLowerBound` remains unproved; classical P versus NP remains unresolved.

## Verification

Pending: full build, transitive axiom audit, hosted CI.
