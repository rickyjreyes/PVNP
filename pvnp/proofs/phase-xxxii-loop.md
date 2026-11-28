# Phase XXXII: a loop combinator for verified sweep programs (27 November 2026)

New Lean modules:
- `lean/PVNP/SweepLoop.lean`, with 11 registered theorems. It builds on the composition framework
  (`SweepCompose`).
- `lean/PVNP/SweepLayout.lean`, with 17 registered theorems: the first application of the loop.

## Outcome

- **Proved (kernel-checked), new registry obligation C7.10.** A loop combinator with
  data-dependent iteration counts, exact charged costs, and its compiled-TM form
  (`loop_reachFirst`, `loop_tm`).
- **Why it is needed.** `ProgOn.seq` composes a fixed number of stages. Several remaining
  components iterate a number of times that depends on the data:
  - the greatest common divisor for normalized rationals (C5.5);
  - sums over a mode set (convolution, C6.5);
  - the terms of the Taylor recurrence (C6.6);
  - the time steps of the evaluator (C7.6).
- **First application (`shift_by_counter`, `shift_by_counter_tm`).** A track is shifted by an
  amount given in binary on a counter track, with a data-dependent number of iterations. A tape
  of length `n` with counter value `W` ends with `x = X·2^W mod 2ⁿ` and a zero counter, in
  exactly `(3W + 1)(2n + 2)` transitions.
- **Not done.** The gcd, the convolution, the Taylor recurrence and the evaluator remain open,
  and #99 stays open.
- **Classical P versus NP remains unresolved.**

## 1. The combinator

`loop T B eT eB` has instructions `T.I ⊕ B.I` and buffers `T.B ⊕ B.B`. Its scans, trips and costs
are those of `seq T B eT`. Its transitions are:
- a step of the test `T` into `eT` goes to `inr B.start`;
- a step of the body `B` into `eB` goes back to `inl T.start`;
- every other step is the corresponding step of `T` or `B`.

Any other exit `eF` of the test is an exit of the loop.

## 2. Theorems

| Theorem | Statement |
|---|---|
| `loop_trip_inl`, `loop_trip_inr`, `loop_tripCost_inl`, `loop_tripCost_inr` | the loop's trips and costs are those of `T` and `B` |
| `loop_stepP_inl_ne`, `loop_stepP_inl_exit`, `loop_stepP_inr_ne`, `loop_stepP_inr_exit` | the loop's steps, with the two redirections |
| `loop_body_then` | a first arrival of the body at `eB`, followed by a first arrival of the loop from the test's start, is a first arrival of the loop |
| `loop_reachFirst` | **the loop theorem** (below) |
| `loop_tm` | the same on the compiled single-tape TM |

**The loop theorem.**
- *Hypotheses:* `T.start ≠ eF` and `eF ≠ eT`.
- *Iterations:* for `k < n`, the single-trip test sends `(T.start, l_k)` to `(eT, m_k)`, and the
  body first-arrives at `eB` from `(B.start, m_k)` with output `l_{k+1}` and cost `b_k`.
- *Stop:* at `l_n` the test sends `(T.start, l_n)` to `(eF, out)`.
- *Conclusion:* the loop first-arrives at `inl eF` from `(inl T.start, l₀)` with output `out` and
  cost exactly `Σ_{k<n} (t_k + b_k) + t_n`, where `t_k` is the test's trip cost on `l_k`.

The proof is an induction on `n`. Each body run is lifted with `loop_body_then`, and the costs
combine by `Finset.sum_range_succ'`.

The test is a single trip, such as a comparison or zero test. A test with several trips can be
composed in front of the body with `seq`.

## 3. First application: shifting a track by a binary counter

`SweepLayout` works on the alphabet `SCell`, with a shifted track `x` and a counter track `c`.

**Single-trip programs.**
- `shlProg` doubles `x` modulo `2ⁿ` (`fscan_shl`, `shl_first`).
- `decProg` decrements the counter with a borrow ripple whose initial borrow is `1`
  (`fscan_dec`, `dec_first`).
- `testProg` branches on `c ≠ 0`. Its forward buffer records whether a set bit was seen
  (`fscan_nz`, `test_step`).

**The loop.**
- The body is `seq shl dec`, a two-stage composite (`body_first`). One body step doubles `x`
  modulo `2ⁿ` and decrements a nonzero counter (`bodyStep_x`, `bodyStep_c`).
- `shiftLoop = loop test body` iterates the body exactly `W = c` times. `iter_spec` is the
  invariant by induction over the iterates.

| Theorem | Statement |
|---|---|
| `fscan_shl`, `fscan_shl_c`, `fdec_spec`, `fscan_dec`, `fscan_dec_x`, `fscan_nz` | the three transducers: doubling with carry-out, decrement with borrow-out, and the nonzero test; each leaves the other track unchanged |
| `shl_first`, `dec_first`, `test_step`, `test_cost` | the three single-trip programs: first arrivals, the test's branch and its cost |
| `body_first`, `bodyStep_length`, `bodyStep_x`, `bodyStep_c` | the body in first-arrival form and one body step |
| `iter_spec` | after `k ≤ W` iterations: length unchanged, counter `W − k`, and `x = X·2^k mod 2ⁿ` |
| `shift_by_counter` | **the shift loop first-arrives at the test's `no` exit** in exactly `(3W + 1)(2n + 2)` transitions, with `x = X·2^W mod 2ⁿ` and a zero counter |
| `shift_by_counter_tm` | the same on the compiled single-tape TM |

**Cost.** Each iteration costs one test trip and two body trips, `3(2n + 2)`. The final test
adds one more trip.

**Use.** Some verified primitives fix a layout by convention. An example is the divider's
divisor, which is placed at `D·2^W`. A machine can produce such a placement when the shift
amount is on the tape in binary. The evaluator will need this where tracks cannot be shared.

## 4. Progress (registry)

- C7.10 is a new obligation, recorded as proved by `loop_reachFirst` and `loop_tm`. The registry
  also cites the application `shift_by_counter_tm`. C7.10 is infrastructure for the evaluator,
  in the same way as C7.8 (composition) and C7.9 (track lenses).
- C7 moves from 6/9 to 7/10. The remaining C7 obligations are C7.5 (the arithmetic library),
  C7.6 (the uniform evaluator) and C7.7 (its polynomial runtime). All three are open.
- The ledger is unchanged.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepLoop` and `PVNP.SweepLayout` compile without warnings and use no `sorry`, `admit`,
  `native_decide` or custom axiom.
- `lake build PVNP` passed (7,444 jobs).
- The full transitive axiom audit (`audit/check_axioms.py`) passed for all 1,480 registered
  declarations: the 1,452 earlier ones and the 28 new theorems. Each uses only `propext`,
  `Classical.choice` and `Quot.sound`, or none, and no `sorryAx` occurs. The audited file is the
  committed `lean/audit/AxiomAudit.lean`.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head.
