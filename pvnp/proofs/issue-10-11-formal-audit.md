# Issue #10 / #11 — discrete equivalence and lower-bound audit

**Source boundaries.** Release 12 https://doi.org/10.5281/zenodo.17732642
(publication Nov 26, 2025); Release 03 https://doi.org/10.5281/zenodo.17743607
(original May 7, 2025). The current repository LaTeX sources bear an
Oct 27, 2026 revision date. Historical abstracts contain stronger
claims than the Lean artifacts; those claims are not silently upgraded to
kernel-certified theorems.

## Frozen discrete semantics (existing)

`PVNP.PartII.RadiusOneMachine S` has one constant blank in a fixed
finite alphabet, a fixed radius-one local rule `S³ → S`, and
`Configuration n S = Fin n → S`. The two boundaries see a blank.
Global updates are simultaneous. No physical wavefield, phase, curvature
cost or PDE evolution is part of these definitions.

## New concrete theorems

| Claim | Exact Lean declaration | Scope |
| --- | --- | --- |
| Finite speed / prefix cone | `PVNP.LocalityLowerBound.prefix_agree_iterate` | Every local update rule; arbitrary finite tape; fixed direct encoding |
| Distal-bit pair not distinguished | `PVNP.LocalityLowerBound.indistinguishable_far_input` | Input bit at t+1, output cell 0, t rounds |
| All-rule restricted lower-bound witness | `PVNP.LocalityLowerBound.every_local_rule_fails_far_bit_by_t` | Every rule, any cell-zero decoder; excludes nonlocal preprocessing |
| Arbitrary TM single-cell transition compilation | `PVNP.TMCellCompiler.compile`, `on_head_writes`, `on_head_stay`, `on_head_move` | Local rule semantics, not complete TM trace |
| Exact serialized finite sweep | `PVNP.ReplayCost.serializeStep_correct` | Finite WCC stencil semantics |
| Cost accounting with all lengths | `PVNP.ReplayCost.totalReplayCharge_cubic` | Declared list-lookup/table-scan interpreter, not tape-TM runtime |

The distal-bit theorem is **unconditional and nontrivial** for the exact
direct-input, fixed-location-output radius-one model. At input length
`n=t+2`, any algorithm whose output is only the leftmost cell requires
more than `n-2` rounds to decide the *last-bit language* correctly for all
inputs. This is a linear causal bound, not superpolynomial SAT hardness.

## Counterexamples and universal bound ledger

The existing `CurvatureBarrier.lean` proves local finite-state storage cost
at most `n` for every Boolean input and bounded-degree graph cost at most
`n*d²`. Hence a universal exponential **storage curvature** lower bound
over that encoding is false. `ExpandingDomain.lean` proves that a
positive size-independent density-weight coercivity floor fails on
expanding domains; `PhaseObservability.lean` records phase and nodal
observability obstructions. None automatically produces a SAT decider,
and these countermodels cannot be used to refute a different,
well-defined operational resource.

Algorithmic bypass to test: a centralized split-SAT solver scans pairs in
O(n) even though a private-partition communication model incurs linear
communication. This demonstrates why a communication lower bound cannot
be promoted to a SAT runtime lower bound.

## Uniformity and size dependence

Let input length be n, witness length w, machine/table size d,
finite-tape length c, and number of synchronous rounds t.
For an explicit list-based evaluator that sequentially emits c outputs
per round, charging up to (c+1) per list read and d per finite-table
lookup, the stated conservative total charge is

`R = n+w+d+c + t*c*(3*(c+1)+d+8) + c`.

The Lean declaration `totalReplayCharge_cubic` proves

`R ≤ 4*(n+w+d+c+t+16)^3 + 2*(n+w+d+c+t+16)`.

The polynomial is uniform in all arguments; **this does not yet prove
that the particular interpreter cost model corresponds to an actual
ordinary single-tape TM**, nor that the abstract local rule table and
input/witness encoders can be extracted with that complexity for every
machine family. For NP equivalence, w must separately be polynomial
in n, and d cannot encode a nonuniform input-length-dependent advice
table at zero cost.

## Missing from a complete #11 proof

1. Universal TM syntax, fixed finite alphabet and states, explicit bit
   serialization of arbitrary transitions and machine descriptions.
2. TM global step in a separate semantic definition, single-head
   invariant and proof that `compile` commutes with that step on an
   explicitly bounded tape for all transitions including boundary cases.
3. Reverse simulator written as an actual TM, with a derivation of its
   instruction count from scanning, rule lookup, encoding and decoding.
4. Encodings and polynomial bounds as functions of input and witness
   lengths, including uniform description-size constraints.
5. Two directions of polynomial-time language inclusion and verifier
   class equivalence. No statement `P_WCC = P_TM` or `NP_WCC = NP_TM`
   is currently Lean certified.

## Missing from a universal #10 theorem

1. Freeze and justify a physically realizable, uniform architecture
   class with full encoding, readout, time, energy, amplitude, bandwidth,
   precision, mass and domain resources charged.
2. Prove a lower-bound transfer from distinguishability of *decision
   outputs* to universal resource consumption for **all** correct
   algorithms in that class. A detector-specific inequality is not enough.
3. Control all constants as functions of n; settle phase-only channels,
   zero-amplitude nodes, expanding volume and parallel/nonlocal shortcuts.
4. Separately show a polynomial-resource physical verifier and identify
   one *same* language for an internal separation. A classical P versus NP
   implication requires additional model-faithful reductions.

This checkpoint is a proof/result ledger, not a declaration of either
mission's full success. Discrete symbol operations alone do not prove
physical curvature preservation.
