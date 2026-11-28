# Phase XXXII: polynomial evaluation on the Turing machine by a Horner loop (28 November 2026)

New Lean module: `lean/PVNP/SweepPoly.lean`, with 21 registered theorems. It builds on:
- the loop combinator (`SweepLoop`);
- uniform word access (`SweepAccess`);
- multiplication (`SweepMul`) and subtraction (`SweepArith`);
- two's-complement codes (`SweepFixMul`);
- the cellwise map (`SweepGcd`).

## Outcome

- **Proved (kernel-checked), registry C6.4.** One compiled single-tape TM evaluates a
  polynomial `p(x) = Σ_{k<K} c_k x^k` with signed integer coefficients at a signed integer point.
  The machine is uniform in the degree (`poly_tm`).
  - *Input:* the coefficients as `L`-bit words in excess `s = 2^{L−1}` (`d_k = c_k + s`), packed
    on one track; the point `x` in `N`-bit two's complement; the counter `K`; the offset `(K − 1)L`;
    the constants `L`, `2^{L−1}` and the mask `2^L − 1` of the word format.
  - *Output:* the result track, read in `N`-bit two's complement, is `p(x)`.
  - *Hypotheses:*
    - `0 < L ≤ N`;
    - every coefficient lies in the `L`-bit range `[−2^{L−1}, 2^{L−1})`;
    - the packed excess codes lie below `2^N`, and `KL < 2^N`;
    - the value `p(x)` lies in the `N`-bit range.
  - *Cost:* exactly `hornerTrips L (trips (tc_N x)) K · (2N + 2)` transitions, where `trips` is
    the bit length. It is at most `(1 + K(3KL + N + 11))(2N + 2)` (`hornerTrips_le`).
- **Only the value must fit.** The intermediate Horner values need no range condition. Every
  step is an exact code modulo `2^N` (`tc_mul`, `tc_add`, `sub_tc_value`).
- **Why it is needed.** The Taylor integrator advances each Fourier coefficient by a Taylor
  polynomial in the time step. Its coefficients come from the recurrence (C6.6) and are stored as
  a vector. Evaluating it is a polynomial evaluation with coefficients read at indices that are
  data.
- **Not done.**
  - computing the initial offset `(K − 1)L` from `K` on the machine. It is part of the layout,
    like the counter of the access machine;
  - fixed-point coefficients and points. The machine evaluates exactly over the integers. A
    scaled evaluation needs one more rounding stage per step, and C5.2 provides that stage, but
    the composite is not built here;
  - the constants, convolution and the Taylor recurrence (C6.2, C6.3, C6.5, C6.6);
  - the evaluator (C7.5–C7.7, #99, which stays open).
- **Classical P versus NP remains unresolved.**

## 1. The machine

**Alphabet.** `HCell` has these tracks:
- the access cells: the work track, the access counter, the packed coefficients `v` and the mask;
- the multiplier's tracks;
- the offset `off`;
- the constants `lL = L` and `sT = 2^{L−1}`;
- the counter `cnt`, the point `px` and the result `res`;
- two scratch tracks.

**One Horner step** (`BODYP`, `body_poly`) is an eight-stage composite. From counter `j > 0`:
1. a cellwise map loads the offset `(j − 1)L` into the access counter;
2. the access machine (`SweepAccess`) reads the word `d_{j−1}`;
3. a cellwise map loads the multiplier: the accumulator holds `d_{j−1}`, the multiplicand `res`
   and the multiplier `x`;
4. the verified multiplier leaves `d_{j−1} + res·x` modulo `2^N`;
5. the verified subtractor removes the excess `s`, which writes `res·x + c_{j−1}` to `res`;
6. the subtractor steps the offset down by `L`;
7. a cellwise map stores the new offset;
8. the counter decrements.

The step takes exactly `(3(j − 1)L + trips(x) + 10)(2N + 2)` transitions. The access stage reads
at offset `(j − 1)L`, so it accounts for the `3(j − 1)L` term.

**The loop** (`hornerLoop`, `poly_loop`). A single-trip test continues while the counter is
nonzero (`testP_step`). The proof is by induction on the counter, through `loop_iter` and
`loop_stop`. From result `tc(R)` and counter `j`, the loop first-arrives at its stop exit with
result `tc(hornerW R j)`.

**Correctness.**
- `hornerW` is Horner's scheme on the packed words. The words are the coefficients
  (`pack_word`, `hornerW_eq`).
- From the top, Horner's scheme computes `R xʲ + Σ_{k<j} c_k x^k` (`hornerFrom_eq`). With `R = 0`
  and `j = K` this is `p(x)`.

**Frames.**
- Composites, loops and lifted programs never extend the tape (`seq_ext_none`, `loop_ext_none`,
  `viaLens_ext_none`).
- `access_run` is strengthened: the access machine also leaves the vector and mask tracks and the
  length unchanged.
- The stages leave the invariant tracks unchanged: the vector, the mask, `L`, `2^{L−1}` and `x`
  (`HInv`).

**Layout** (`polyInput`).
- *Data:* the packed excess codes, the point, the counter `K` and the offset `(K − 1)L`.
- *Format constants:* `L`, `2^{L−1}` and `2^L − 1`. They depend only on the word format.

Every other track is zero.

## 2. Theorems

| Theorem | Statement |
|---|---|
| `seq_ext_none`, `loop_ext_none`, `viaLens_ext_none` | sequential composites, loops and lifted programs of non-extending programs never extend the tape |
| `fscan_sub_ab`, `accessProg_ext` | the subtractor leaves its operands unchanged; the access machine never extends the tape |
| `hornerFrom_eq` | Horner's scheme from the top: `hornerFrom R j = R xʲ + Σ_{k<j} c_k x^k` |
| `fscan_nzP`, `testP_step`, `testP_cost` | the loop test continues exactly while the counter is nonzero, in `2N + 2` transitions |
| `st_acc`, `st_mul`, `st_sub`, `st_dec` | the access, multiplier, subtractor and counter stages on `HCell`, with their frames |
| `map_proj`, `pv_congr` | unchanged views have unchanged track values |
| `body_poly` | **one Horner step**: `res = tc(R) ↦ tc(Rx + c_{j−1})`, counter `j ↦ j − 1`, offset down by `L`, in exactly `(3(j − 1)L + trips(x) + 10)(2N + 2)` transitions |
| `hornerTrips_le` | the trip count is at most `1 + K(3KL + t + 11)` |
| `poly_loop` | **the Horner loop** first-arrives at its stop exit with `res = tc(hornerW R j)` and exact cost |
| `hornerW_eq` | Horner's scheme on the packed words is Horner's scheme on the coefficients |
| `mkH_spec`, `poly_tm` | the layout; **polynomial evaluation on the compiled TM** |

## 3. Progress (registry)

```
C6   Constants and series on the TM                                               [#######.............]  33% (2/6)    25%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [###############.....]  73% (8/11)    70%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

- C6.4 is proved, so C6 moves from 1/6 to 2/6. Its subjective estimate moves from 15% to 25%.
  Polynomial evaluation is a building block for the Taylor sums. It is not itself the Taylor
  recurrence (C6.6), and it does not compute any constant (C6.2, C6.3).
- C7 is unchanged at 8/11. C7.5, C7.6 and C7.7 stay open.
- The ledger is unchanged. I-11 stays Restricted.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepPoly` compiles without warnings and uses no `sorry`, `admit`, `native_decide` or
  custom axiom. `poly_tm`, `poly_loop` and `body_poly` depend only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `lake build PVNP` passed (7,449 jobs).
- The full transitive axiom audit (`audit/check_axioms.py`) passed for all 1,582 registered
  declarations: the 1,561 earlier ones and the 21 new theorems. Each uses only `propext`,
  `Classical.choice` and `Quot.sound`, or none, and no `sorryAx` occurs. The audited file is the
  committed `lean/audit/AxiomAudit.lean`. The audited Lean tree includes the strengthened
  `access_run`.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head.
