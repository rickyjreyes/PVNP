# Phase XXXII: a loop combinator for verified sweep programs (27 November 2026)

New Lean module: `lean/PVNP/SweepLoop.lean`, with 11 registered theorems. It builds on the
composition framework (`SweepCompose`).

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
- **Not done.** No application of the loop is built yet. The gcd, the convolution, the Taylor
  recurrence and the evaluator remain open, and #99 stays open.
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

## 3. Progress (registry)

- C7.10 is a new obligation, recorded as proved by `loop_reachFirst` and `loop_tm`. It is
  infrastructure for the evaluator, in the same way as C7.8 (composition) and C7.9 (track
  lenses).
- C7 moves from 6/9 to 7/10. The remaining C7 obligations are C7.5 (the arithmetic library),
  C7.6 (the uniform evaluator) and C7.7 (its polynomial runtime). All three are open.
- The ledger is unchanged.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepLoop` compiles without warnings and uses no `sorry`, `admit`, `native_decide` or
  custom axiom.
- `lake build PVNP` and the full transitive axiom audit are run on this tree. The results are
  recorded on the pull request.
