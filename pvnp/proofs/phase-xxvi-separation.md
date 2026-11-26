# Phase XXVI: the original separation mechanism (26 November 2026)

Base: `main` at `4cc4b29` (Phase XXV merged).

## Outcome

- **No valid separation mechanism was found.** Classical P versus NP remains unresolved; neither
  `CrossingSAT.SATLowerBound` nor its negation is proved. I-2, I-16 and I-32 stay Open.
- **New kernel-checked result** (`lean/PVNP/ExpTaylorAmplification.lean`): the exponential
  sensitivity established in Phase XXV for the sideband linearization does not force exponential
  computation. The exponential series reaches relative precision `2^{-p}` after `⌈2x⌉ + p + 1`
  terms (`ExpTaylor.taylor_terms_for_precision`). That count is linear in the growth exponent and
  in the precision bits, whereas the first-order Phase XXV budget charges `∝ e^{AT}/ε` steps.

## 1. The original mechanism, as recovered in the inventory

Part I's separation chain combined:
- non-constructible verifiable states (I-1, I-4, I-20);
- an inference from state non-constructibility to language separation (I-25–I-28);
- a depth conjecture for discrete WCC deciders (I-16, `conj:wcc_depth`);
- a uniform separator price (I-31);
- encoding-independent interface growth (I-32).

The state-to-language inferences I-25–I-28 are refuted by Lean counterexamples. I-31 is refuted for
the frozen trajectory class (`SeparatorFrozen.no_uniform_separator_price`).

What remains passes through one of three statements:
- **I-16.** Through the proved discrete WCC–Turing equivalence this is exactly
  `SAT_dense ∉ P_TM` (`DepthBarrier.wccDepth_SAT_iff`, `CookLevin.Gen.satLowerBound_iff_P_ne_NP`,
  `SATTarget.satLowerBound_iff_superpolynomial`).
- **I-2.** Each non-vacuous formal reading is equivalent to `P_TM ≠ NP_TM`
  (`NonconstructibleFamily.npFamily_separation_iff`).
- **I-32.** Its formal reading in the charged constant class is likewise equivalent to
  `P_TM ≠ NP_TM`.

Repairing the mechanism therefore means proving the universal SAT lower bound itself. There is no
weaker intermediate premise left to discharge.

## 2. Candidate invariants examined

Each candidate had to meet two requirements: (a) every correct uniform SAT decider incurs it, and
(b) its magnitude forces superpolynomial charged time. Neither was assumed.

1. **Computational history / logical depth.** For (a) to hold for every decider, the invariant
   must be minimized over all deciders. A history's length is the decider's running time, and
   polynomial-time simulation changes time-bounded depth only polynomially. So the minimized
   invariant is the time complexity up to polynomial factors, and (a)+(b) is equivalent to
   `SAT_dense ∉ P_TM`. **Obstruction:** the invariant is running time in disguise and gives no
   independent leverage.
2. **Time-bounded description complexity of states or witnesses.**
   - Explicit states are always constructible in linear time (`DepthBarrier.explicit_no_separation`).
   - A decider outputs one bit and need not construct a witness (search versus decision).
   - Tseitin systems (`TseitinSAT`, the parity theorem `parityOK_of_solvable` /
     `solvable_of_parityOK`) are hard for resolution yet decided by linear algebra over ℤ/2.
   **Obstruction:** hardness of a proof or witness system does not transfer to decision.
3. **Spatiotemporal causal interfaces.**
   - Unconditional bounds are linear (`WCTDistributedSAT.distributed_energy_requires_causal_coverage`).
   - The uniform interface price is refuted (`SeparatorFrozen`).
   - Constant-field devices have zero separator measure (`ExpanderInterface.sep_const`), yet the
     charged constant class decides every language in `P_TM`.
   **Obstruction:** an interface invariant necessary for all deciders would have to vanish on
   these devices unless it is equivalent to P ≠ NP.
4. **Crossing sequences.**
   - Single-tape deciders need quadratic time on arbitrarily large budgets
     (`QuadraticHorizon.quadratic_every_budget`).
   - The verifier crossing-information bound (`VerifierCrossing.crossingInfo_SAT_dense`) is
     polynomial.
   - Machines with two tapes or a lattice recognize the standard crossing-hard languages in linear
     time.
   **Obstruction:** crossing bounds give at most a quadratic gap for one tape and do not transfer
   across the proved model equivalences with superpolynomial strength.
5. **Compression and decompression.** A lower bound on the description size of intermediate states
   can be traded for time by recomputation. A time bound would need a time–space trade-off for
   SAT. Known trade-offs hold only for sublinear space and give fixed polynomial exponents.
   **Obstruction:** no superpolynomial time bound follows.
6. **Uniformity and finite horizons.**
   - `FiniteHorizonSAT.fast_through_horizon` and `no_common_hard_horizon`: for every correct decider
     and every horizon there is a fast decider agreeing up to that horizon, and no finite set of
     hard instances is common to all deciders.
   - Resource-bounded diagonalization yields languages outside `P_TM`
     (`PhysicalDiagonal.diagonal_not_mem_P_TM`), but transferring hardness to SAT needs
     NP-hardness plus the separation itself.
   - Diagonalization and simulation arguments relativize. Baker–Gill–Solovay oracles with
     `P^A = NP^A` rule out any purely relativizing proof.
   **Obstruction:** separating finite-horizon efficiency from asymptotic uniformity requires a
   non-relativizing asymptotic argument; none was found.
7. **Known barriers.** Every candidate above either relativizes (diagonalization, measures that
   simulation preserves) or is a restricted-model bound (crossing sequences, causal cones,
   resolution). Natural proofs (Razborov–Rudich) block constructive, large circuit properties
   under standard pseudorandomness assumptions. Algebrization (Aaronson–Wigderson) blocks their
   arithmetized extensions. None of these barriers is formalized here; they are cited.

**The opposite outcome.** No polynomial-time SAT algorithm emerged. The Phase XXII corner sweep is
exponential (`SATDynamics.sat_iff_corner_sweep`), and energy descent from formula-independent
preparations is refuted (`SATDynamics.no_corner_preparation_decides`).

## 3. New verified result: exponential sensitivity versus computational cost

Namespace `PVNP.ExpTaylor`:

- `exp_partial_sum_error`: if `x ≥ 0` and `2x ≤ K + 1`, then
  `0 ≤ e^x − Σ_{k<K+j} x^k/k! ≤ 2·2^{-j}·e^x`.
- `taylor_terms_for_precision`: `⌈2x⌉ + p + 1` terms give relative precision `2^{-p}`.
- `sideband_growth_taylor`: the same bound for the factor `e^{rt}` of an exponential sideband mode.
  `SidebandAmplification.exponential_solution` is the case `r = 1`.
- Supporting: `exp_eq_tsum`, `term_succ`, `term_shift_le`, `exp_sub_partial_eq`, `exp_tail_le`.

What this classifies about the factors `e^{LF·T}` in the I-11 analysis:

- **Precision.** The bits needed are linear in `T` (`ContinuumPrecision.precision_suffices`), not
  exponential.
- **Time integration.** For linear dynamics the exponential factor is an artifact of the
  first-order method: Taylor integration needs terms linear in the growth exponent and in the
  precision bits. For the nonlinear finite-dimensional Galerkin flow the analogous statement needs
  a lower bound on the time-analyticity radius on the conserved ball; that is not proved here.
- **Spatial cutoff.** The Phase XXV mode count `K ∝ e^{LF(R_B)T}/m` comes from the Gronwall
  weak-norm comparison. Avoiding it needs propagated Fourier decay of the true solution (for
  example polynomial-in-time `H^s` growth bounds for `s > 2`, as known for related NLS equations on
  `T²`). That is not proved here.

This is an arithmetic-term count for a scalar or diagonalizable linear flow. It is not a
bit-complexity theorem for the PDE, and it does not change I-11's classification (Restricted,
65%).

## 4. Status

| Claim | Status | Remaining obligation |
|---|---|---|
| I-16 | Open | `SAT_dense ∉ P_TM` against every uniform decider: a non-relativizing, non-natural, non-algebrizing superpolynomial lower bound |
| I-2 | Open | equivalent to `P_TM ≠ NP_TM` in each non-vacuous formal reading |
| I-32 | Open | equivalent to `P_TM ≠ NP_TM` in the charged constant class |
| I-11 | Restricted (65%) | Turing-machine bit-complexity implementation; nonlinear time-analyticity radius; propagated spatial decay |
| Classical P vs NP | **unresolved** | — |

## 5. Next proof obligations

1. A lower bound on the time-analyticity radius of the finite Galerkin flow on the conserved
   ball, giving Taylor time integration with `poly(T, p, |S|)` terms.
2. A polynomial-in-time `H^s` (`s > 2`) growth bound for the frozen PDE, or uniformly for its
   Galerkin truncations, giving a polynomial mode count.
3. A Turing-machine implementation of the certified evaluator (`pvnp/phase_xxv/`).
4. I-16: a superpolynomial lower bound for `SAT_dense` against all uniform deciders. Open.

## Verification

Local, Lean 4.23.0: `lake build PVNP` passed (7,420 jobs) and the new module compiles without
warnings. `lake env lean audit/AxiomAudit.lean` with `audit/check_axioms.py` passed for all 1,011
registered declarations, the eight `ExpTaylor` theorems included, using only `propext`,
`Classical.choice` and `Quot.sound`; no `sorryAx` occurs. The Lean tree is that of commit
`3fd90d1`; later commits change documentation and generated dashboard data only. Dashboard (13 groups), status registry, manuscript-alignment and
release-document checks pass.
