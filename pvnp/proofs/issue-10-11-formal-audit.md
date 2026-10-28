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

## Radius r extension and local decoder limitations

For fixed radius `r`, time `t`, and `m` observed output cells,
`PVNP.RadiusCausality.prefix_iterate` derives the causal dependence
radius `t*r` for the full finite stencil (not merely a three-cell
radius-one special case). `prefix_decoder_equal` permits **any**
postprocessing function of the observed `m` cells, so additional decoder
complexity alone cannot restore information that has not propagated.

For direct configurations of length `n=t*r+m+1`, the last input
bit lies outside that cone and `no_prefix_decoder_last_bit` rules
out an all-input correct decider within `t` rounds. It is equivalent
to a lower bound `t*r >= n-m` for a correct fixed-prefix readout,
when the radius and prefix length have been fixed in advance.

The construction explicitly fails for general uncharged encoding:
`shortcut_encoding_reads_far_at_zero` puts an arbitrary remote bit
at the first cell at initialization and allows zero-round readout.
Global readout likewise bypasses the fixed-prefix assumption.
A time-varying/long-range rule with an effectively unbounded radius
must pay for that dependence separately.

This proof does not require nonzero wave amplitudes or assume a mass
detector. It does **not** establish that a continuous wave's phase,
nodal geometry or remote optical readout obeys the same symbolic
causal cone; that would require an independent physical realization
theorem with explicit constants.

## Bounded-tape TM representation extension

`TMGlobal.lean` adds a mathematical Turing tape, head position and
control state, proves the single-marker encoding property, and checks
the tape-write behavior of the compiled WCC local rule at every site.
Correct head travel (including boundary cases), total trace
semiconjugacy, and actual serialized Turing interpreter bounds are
still required before claiming exact class equivalence.

## Finite alphabet and stationary-head checkpoint

The original `RadiusOneMachine State` accepts an arbitrary mathematical
type and arbitrary local function. Without an effective finite rule
description and a uniform encoding, this is not itself a standard
Turing machine model.

`FiniteWCCCode.FiniteWCC s` fixes the state alphabet as `Fin s`
and encodes all `s^3` transition rows as one-hot bit vectors.
Its bit count is `s+s^4` and is polynomial in `s`.
`MachineCode.FiniteTable q g` represents arbitrary finite TM
transition tables with code size `g+q*g*(q+g+3)`, and the two
encodings have injectivity targets. This is a *representation
lemma*, not a proof that a tape TM can parse and execute this bit
grid within the stated instruction bound.

`TMStayTrace` supplies a nontrivial all-time compilation theorem
for stationary-head Turing machines and a witness to the preserved
unique head. Its scope does not include left/right moves. General
bounded-tape simulation and the reverse finite-WCC Turing interpreter
remain unproved, so neither exact discrete P nor NP equivalence
may be labeled kernel-certified.

## October 28 verified baseline and new work

A complete Lean CI run passed at `9077a840`:
https://github.com/rickyjreyes/PVNP/actions/runs/40701665817.
This checked `RadiusCausality`, `TMGlobal`, `TMStayTrace`,
`MachineCode`, `FiniteWCCCode`, `OracleObstruction`,
`TMCellCompiler`, `ReplayCost`, and all preexisting modules.
The accepted scope is an unconditional finite-locality information
lower bound, static finite code representations, a correct global tape
write rule, and an exact trace for **stationary-head machines**.

The stronger radius-r cost ledger distinguishes two synchronized,
finite-stencil stages: encoder radius `r_e`, encoder rounds `e`,
computer radius `r_c`, computer rounds `t`, and a decoder receiving
only the first `m` cells. The initial-data causal footprint ends at
index `e*r_e+t*r_c+m-1`. If `n>e*r_e+t*r_c+m`, the final bit lies
outside the cone; the new `no_two_stage_prefix_last_bit` statement
exhibits a pair differing only at the final position and contradicts
correctness on all length-n inputs. This is stronger than an assumption
that input encoding is a free, arbitrary operation. The *decisional*
corollary is new and must pass CI at its exact commit.

The latest `TMHeadMotion` source separately checks a right-moving
head arrives at `p+1`, a left-moving head arrives at `p-1`, a
non-stationary head leaves its previous cell, and a stationary head
remains. These use the independent bounded-tape configuration and
actual local compiler semantics. They do not yet prove that **no other**
cell is marked after an arbitrary move; hence arbitrary finite-trace
preservation and a moving-head TM compiler are still open.

Full ordinary-TM execution-step and memory bounds require a genuinely
finite coded interpreter with explicit tape and instruction operations.
The declared list `ReplayCost` formula is not that program. Uniform
polynomial-time language-equivalence and P/NP witness class proofs
remain **unproved**. No resource lower bound is extrapolated to
physical phase, nodes, curvature, all algorithms, SAT hardness,
or classical P versus NP.


## No-spurious-head support audit

`TMHeadSupport.headless_outside_original_neighborhood` isolates
the finite-range **support** of a head marker after one compiled step.
Its hypotheses are numeric exclusions of all three possible positions:
`i != p`, `i != p+1`, and `i+1 != p`. It proves
the newly updated cell cannot carry a marker. By contraposition,
`head_marker_support` confines every successor marker to at most
those three sites. These do not presuppose the target simulator result,
a cost bound, or any physical wave curvature property.

To complete global head-marker invariance, eliminate all but the
actual movement-selected successor site in left/right/stay cases,
then prove a valid total bounded-tape step relation and its iteration.
For an unbounded tape, the left/right boundary condition must be
handled by a non-degenerate embedding or expanding work tape. A
bounded-tape step theorem alone does not prove universal
polynomial-time simulation, and an arbitrary rule function without a
finite encoded truth table does not define an ordinary effective TM.
