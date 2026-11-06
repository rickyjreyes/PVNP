# Phase VII: actual Turing-machine crossing traces and local splicing

This checkpoint extends PR #35 while preserving the original Part I objective.

## Definitions and new theorem targets

`CrossingTrace.lean` defines an actual crossing event by comparing the head positions of `TM.Cfg` and `TM.next` across a fixed integer cut. Every event records the **post-transition finite-control state** and direction. The trace is computed from successive machine configurations, including halting (fixed-point) transitions. The number of events in the first `t` steps is at most `t`. The prior split-3-CNF-SAT information bound is then instantiated with this concrete execution-derived record:

\[
2^n \leq (|\Lambda \times \{L,S,R\}| + 1)^t,
\]

still **conditional on** a correct split-SAT record classifier and the required rectangular splicing property of the complete record.

`CrossingSplice.lean` develops a separate actual-machine fact. Let `mixTape(cut,l,r)` use `l` for cells strictly below the cut and `r` otherwise. For a machine configuration `c` whose head is left of the cut, the single-step identity is

\[
\operatorname{next}(c[\mathrm{tape}:=\mathrm{mix}(c.\mathrm{tape},r)])
=
\operatorname{next}(c)[\mathrm{tape}:=\mathrm{mix}(\operatorname{next}(c).\mathrm{tape},r)].
\]

The symmetric right-hand step lemma and finite-run left-hand theorem are also included. This is unconditional transition-level locality for the **actual bi-infinite single-tape TM**, including stationary and halting transitions. It does not assume that arbitrary full crossing records are rectangular.

## Remaining mathematical work

Prove the full multi-segment crossing-sequence splicing theorem, handling each alternating crossing, same-length control sequences, early decisions, and input layout. Then prove the SAT fooling-family consequence for the concrete encoding and extract a quantified time lower bound.

A fixed-machine cut-record count generally yields only a linear lower bound in the amount of information crossing a fixed cut. No superpolynomial SAT lower bound follows without a new unrestricted amplification theorem. No claim in the 70/91 manuscript ledger changes status from this checkpoint.

## Gate

Kernel-check both modules through the PVNP import tree, run the axiom audit, and merge only when all exact-head required CI jobs succeed.

## Update, 6 November 2026 (Phase VIII)

The "remaining mathematical work" above is now done for this machine model; see
`phase-viii-separation-status.md`.

- `CrossingHennie.splice_core` and `hennie` prove the full multi-segment splicing theorem.
- `CrossingSAT.hmixed_of_halting` and `dtrace_injective` derive the diagonal mixed-acceptance
  premise.
- `CrossingSAT` and `CrossingSATSets` extract quantified single-tape time lower bounds, up to
  `Ω(N²/(log N · log|Λ|))`.

These remain fixed-polynomial bounds. `SAT_dense ∉ P_TM` is still open. The build defects that made
this module fail on `main` after PR #36 are repaired in PR #37.

