# Phase XXXII: the Euclidean algorithm and normalized rational arithmetic (28 November 2026)

New Lean modules:
- `lean/PVNP/SweepGcd.lean`, with 24 registered theorems: the Euclidean algorithm as a loop of
  verified programs, and normalization of fractions.
- `lean/PVNP/SweepRat.lean`, with 11 registered theorems: sums and products of signed fractions,
  in lowest terms.

They build on the loop combinator (`SweepLoop`), the shift loop (`SweepLayout`), long division
(`SweepDiv`), multiplication (`SweepMul`) and sign-and-negate (`SweepSDiv`).

## Outcome

- **Proved (kernel-checked), registry C5.5.** Normalized rational arithmetic on the compiled
  single-tape Turing machine.
  - `radd_tm`, the sum: for integers `a, c` and positive `b, d` with `bd < 2^W` and
    `|ad + cb| < 2^W`, the machine computes `N/D = a/b + c/d` in lowest terms.
  - `rmul_tm`, the product: with `|ac| < 2^W` it computes `N/D = (a/b)(c/d)` in lowest terms.
  - *Output, in both cases:* `N` is read in `2W`-bit two's complement. Then `D > 0` and
    `gcd(|N|, D) = 1`.
  - *Cost:* the cost is exact. It is at most `(8W² + 23W + 22)(4W + 2)` transitions for the sum
    and `(8W² + 23W + 20)(4W + 2)` for the product.
- **Proved: the Euclidean algorithm on the TM** (`gcd_loop`) and normalization of fractions
  (`norm_tm`). For `P < 2^W` and `0 < Q < 2^W`:
  - the machine returns the coprime pair `(P/g, Q/g)`, `g = gcd(P, Q)`, with the same value;
  - it takes exactly `(s(4W + 6) + 8W + 12)(4W + 2)` transitions, where `s ≤ 2W` is the number
    of Euclidean steps (`euclidSteps_le`).
- **Only the results must fit.** The operands need no range condition. The products and the
  sum are exact codes modulo `2^{2W}`, and only `|P|` and `Q` must lie below `2^W`.
- **C5 is complete (6/6).** Fixed point, signed, complex, rational and signed division are all
  proved.
- **Not done.**
  - quotients of fractions (one more multiplication with a sign);
  - constants, convolution and the Taylor recurrence (C6);
  - the evaluator (C7.5–C7.7, #99, which stays open).
- **Classical P versus NP remains unresolved.**

## 1. The Euclidean loop

**Alphabet.** `GCell` has these tracks:
- the divider's tracks;
- the shift counter `c`;
- the Euclidean pair `a, b`;
- the saved counter `c0 = W` and marker `m0 = 2^W`;
- the fraction `p/qq` and the results `rp, rq`;
- a carried block `xc` that normalization leaves unchanged. `SweepRat` uses it for the
  operands, the multiplier and the sign.

**One Euclidean step** (`BODYG`, `body_iter`) is a four-stage composite:
1. a cellwise map loads `a` as the dividend, `b` as the divisor, quotient `0`, marker `m0` and
   counter `c0`;
2. the verified shift loop (`SweepLayout`) shifts the divisor track by `W` places, which is
   the divider's convention `D·2^W`;
3. the verified divider leaves `a mod b` on the dividend track;
4. a cellwise map moves `b` to `a` and the remainder to `b`.

It maps `(a, b)` to `(b, a mod b)` in exactly `(4W + 5)(4W + 2)` transitions.

**The loop** (`gcdLoop`, `gcd_loop`). A single-trip test continues while `b ≠ 0`. The proof is
by strong induction on `b`. It uses two new loop lemmas:
- `loop_iter`: one iteration;
- `loop_stop`: the stop.

The cost is exactly `(s(4W + 6) + 1)(4W + 2)`, with `s = euclidSteps(A, B)`.

**The iteration bound** (`two_mod_lt`, `euclidSteps_le`). Two Euclidean steps at least halve the
second argument. If `r = a mod b` and `r ≤ b/2`, then `b mod r < r ≤ b/2`. Otherwise
`b mod r = b − r < b/2`. Hence `s ≤ 2k` when `b < 2^k`.

**Normalization** (`normProg`, `norm_run`).
1. Load `(p, qq)` into the Euclidean pair.
2. Run the loop.
3. Divide `p` and `qq` by `a = gcd(p, qq)` with the same load, shift and divide stages.
4. Save the quotients in `rp` and `rq`.

`norm_run` holds on any tape with the stated track values, and it leaves the carried block
unchanged. `norm_layout` instantiates it on the explicit layout `normInput`.

## 2. Rational arithmetic

**The multiplier** runs on the carried tracks `x, y, acc` and accumulates
`acc ← (acc + x·y) mod 2ⁿ` (`stage_mul`).

**The adder** (`raddProg`):
1. `Q = bd`;
2. `P = ad`, with `Q` saved;
3. `P = ad + cb`, accumulated.

In two's complement these are exact codes: `tc(a)·d ≡ ad` and `tc(c)·b ≡ cb` modulo `2ⁿ`
(`tc_mul`, `tc_add`). The multiplier (`rmulProg`) computes `Q = bd` and `P = ac` instead.

**The tail** (`TAIL`, `tail_run`), shared by both machines:
1. sign and negate the accumulator: it becomes `|P|`, and the flag `fl` holds the sign of `P`;
2. load `|P|` as the numerator;
3. normalize `|P|/Q`;
4. negate the reduced numerator where `fl` is set.

Read in two's complement, the result is `P / g`. The result is exactly `P / g` because
`g` divides `P`.

**The certificate** (`reduced_frac`). For `0 < Q`, the pair `(P / g, Q / g)` with
`g = gcd(|P|, Q)` is coprime, has a positive denominator, and has the value `P/Q`.

**Layout** (`ratInput`).
- *Constants:* the counter `W` and the marker `2^W` in binary.
- *Numerators:* the `2W`-bit codes of `a` and `c`.
- *Denominators:* `b` and `d`.

Every other track is zero. The constants are data-independent. They are the same kind of
convention as the divider's marker in `divInput`.

## 3. Theorems

| Theorem | Statement |
|---|---|
| `loop_iter`, `loop_stop` | one iteration and the stop of a loop, in first-arrival form |
| `fscan_map`, `map_first` | the single-trip cellwise map |
| `euclidSteps_zero`, `euclidSteps_pos`, `two_mod_lt`, `euclidSteps_le` | the Euclidean step count and its bound `2k` for `b < 2^k` |
| `tv_congr`, `val_false`, `tv_map`, `keep_map`, `six_map` | track values and frames |
| `shiftLoop_ext`, `fscan_nzB`, `testB_step`, `testB_cost` | the shift loop never extends the tape; the loop test |
| `shdiv` | shift and divide on `GCell`: quotient `N / D`, remainder `N mod D`, other tracks unchanged |
| `body_iter`, `gcd_loop` | one Euclidean step; **the Euclidean loop** with `a = gcd(A, B)` and exact cost |
| `normInput_spec`, `norm_run`, `norm_layout`, `norm_tm` | **normalization** on any tape, on the layout, and on the compiled TM |
| `stage_mul`, `stage_negA`, `stage_fixR` | one stage of rational arithmetic on `GCell`, with its frame |
| `ratInput_spec`, `first_stage`, `tail_run` | the layout; the first product; the common tail |
| `radd_layout`, `rmul_layout` | the adder and the multiplier first-arrive with the reduced fraction |
| `reduced_frac` | the reduced pair is coprime, has a positive denominator and the same value |
| `radd_tm`, `rmul_tm` | **the sum and the product on the compiled TM**, in lowest terms, with exact and polynomial costs |

## 4. Progress (registry)

```
C5   TM fixed-point, rational, signed and complex arithmetic; certified rounding  [####################] 100% (6/6)    90%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [##############......]  70% (7/10)    70%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

- C5.5 is proved, so C5 moves from 5/6 to 6/6. Its subjective estimate moves from 75% to 90%. The
  remaining work is integration into the evaluator, which C7 measures.
- The ledger is unchanged. I-11 stays Restricted.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepGcd` and `PVNP.SweepRat` compile without warnings and use no `sorry`, `admit`,
  `native_decide` or custom axiom. `norm_tm`, `radd_tm`, `rmul_tm` and `gcd_loop` depend only on
  `propext`, `Classical.choice` and `Quot.sound`.
- `lake build PVNP` passed (7,447 jobs).
- The full transitive axiom audit (`audit/check_axioms.py`) passed for all 1,544 registered
  declarations: the 1,509 earlier ones and the 35 new theorems. Each uses only `propext`,
  `Classical.choice` and `Quot.sound`, or none, and no `sorryAx` occurs. The audited file is the
  committed `lean/audit/AxiomAudit.lean`.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head.
