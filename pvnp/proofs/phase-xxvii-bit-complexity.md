# Phase XXVII: finite-bit evaluation of exponential amplification (26 November 2026)

Base: Phase XXVI (`ExpTaylorAmplification`). New module: `lean/PVNP/ExpTaylorBits.lean`.

## Results (namespace `PVNP.ExpTaylorBits`)

For a rational argument `x = a/b` with `a ≥ 0`, `b ≥ 1`, and `Q(m,k) = m!/k!` (`fallQ`):

- `partial_sum_eq`: `Σ_{k≤m} (a/b)^k/k! = N_m / D_m` with
  `N_m = Σ_{k≤m} a^k b^{m−k} Q(m,k)` (`taylorNum`) and `D_m = b^m m!` (`taylorDen`).
  These are exact integers.
- `num_le_pow`, `den_le_pow`: if `max(a,b) ≤ 2^β` and `m + 1 ≤ 2^γ`, then
  `N_m, D_m ≤ 2^{γ + m(β+γ)}`. Every intermediate integer of this representation therefore has bit
  length at most `γ + m(β+γ)`, polynomial in `m` and in the bit lengths of `a`, `b`, `m`.
- `round_error`: `|y − ⌊2^p y⌋/2^p| ≤ 2^{-p}`.
- `exp_dyadic_approx`: with `m = ⌈2x⌉ + p`, so that `m + 1` terms are summed, the `p`-bit dyadic
  rounding of `N_m/D_m` is within `2^{1−p}·e^x` of `e^x`.
- `dyadic_num_le`: its integer numerator is at most `2^{p + γ + m(β+γ)}`.

## What this establishes and what it does not

Established. The relative-precision Taylor approximation of the amplification factor `e^x` has an
exact rational representation. Its integers have polynomially many bits in `m = ⌈2x⌉ + p` and in
the input bit lengths, and the dyadic output has polynomially many bits. Combined with
`ExpTaylor.taylor_terms_for_precision`, exponential amplification `e^x` costs polynomially many
bits in `x` and `p` to evaluate.

Not established:
- No Turing-machine implementation in the repository's `TM` model, and therefore no formal
  bit-operation count. Evaluating `N_m` by `m + 1` products and a sum, plus one integer division,
  is polynomial with schoolbook arithmetic. That cost statement is argued, not mechanized.
- The term count `m` is polynomial in the *value* `x`, as for the physical time `T`, not in its
  bit length.
- Nothing here is about the nonlinear frozen PDE. A time-analyticity radius for the Galerkin flow
  and propagated spatial Fourier decay remain open (see `phase-xxvi-separation.md`, §3).

## Separation objective

No new separation mechanism and no polynomial-time SAT algorithm was found in this phase.
Classical P versus NP remains unresolved, and I-2, I-16 and I-32 remain Open.

## Verification

Local, Lean 4.23.0, Lean tree of commit `54939c9`: `lake build PVNP` passed (7,421 jobs). The
transitive axiom audit passed for all 1,020 registered declarations, the nine `ExpTaylorBits`
theorems included, using only `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` occurs.
Hosted CI runs on the pull request.
