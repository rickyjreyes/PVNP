# Phase XXXII: certified fixed-point and two's-complement arithmetic by composition (27 November 2026)

New Lean module: `lean/PVNP/SweepFixMul.lean`, with 34 registered theorems. It builds on the
composition and track-lens modules (`SweepCompose`, `SweepLens`; see
`phase-xxxii-composition.md`). It is the first use of that framework on the repository's
verified primitives.

## Outcome

- **Proved (kernel-checked).** Multiplication in first-arrival form (`mul_first`).
- **Proved.** First arrivals compose (`ProgOn.seq_reachFirst`), so a composite can itself be
  composed again.
- **Proved, registry C5.2.** Certified fixed-point multiplication on the compiled single-tape
  Turing machine, unsigned (`fixmul_tm`) and signed in two's complement (`sfixmul_tm`). It is one
  machine, the composite `seq` of the verified multiplier and the verified divider on a common
  alphabet. The divider reads the product where the multiplier left it.
- **Proved, registry C5.3.** Signed two's-complement arithmetic: addition (`sadd_tm`), subtraction
  and negation (`ssub_tm`), comparison (`slt_iff`) and fixed-point multiplication with certified
  rounding (`sfixmul_tm`).
- **New open obligation, C5.6.** Signed fixed-point division with certified rounding is not
  built (§5). It is recorded so that the gap stays visible.
- **Not done.**
  - complex arithmetic (C5.4) and normalized rationals (C5.5);
  - the constants, convolution and the Taylor recurrence (C6);
  - the evaluator (#99, which stays open).
- **Classical P versus NP remains unresolved.**

## 1. The composite machine

**Common alphabet.** `FCell = MCell × DCell` carries:
- the multiplier's tracks: multiplicand `x`, multiplier `y` and accumulator `acc`;
- the divider's tracks: dividend `n`, shifted divisor `d`, quotient `q` and marker `m`.

**Lenses.**
- `lensM` views the multiplier's tracks.
- `lensD` is the divider's view. Its dividend track **is the multiplier's accumulator**, so
  `get x = ⟨x.1.acc, x.2.d, x.2.q, x.2.m⟩`.
- `lensS` views the divider's own tracks.
- `lensM` is independent of `lensS` (`indep_MS`). By `reachFirst_lens_frame`, the multiplier
  therefore leaves the divisor, quotient and marker unchanged.

**Program.** `fmulProg = seq mulOn divOn MulI.done`, where `mulOn` and `divOn` are the verified
`mulProg` and `divProg` lifted along `lensM` and `lensD`. No copying or layout-conversion
program is needed.

**Layout** (`fmulInput L p X Y`, `L` cells, `p < L`).
- The multiplier's tracks hold `X`, `Y` and `0`.
- The divider's tracks hold the divisor `2^p` shifted by `K = L − 1 − p` places (the fixed word
  `2^(L−1)`), the quotient `0` and the marker `2^K`.

All of these are data-independent except `X` and `Y`.

## 2. Theorems

| Theorem | Statement |
|---|---|
| `mul_loop_first`, `mul_first` | the multiplier first-arrives at `done` after exactly `(trips Y + 1)(2n + 2)` transitions, with `acc ≡ A₀ + XY (mod 2ⁿ)` and a cleared multiplier track |
| `ProgOn.reachFirst_lift_inr`, `ProgOn.seq_reachFirst` | when `B.start ≠ e_B`, two first arrivals compose to a first arrival of `seq A B e` at `inr e_B`, with cost exactly `c₁ + c₂` |
| `fmul_first` | given a zero accumulator, divisor `2^p·2^K`, marker `2^K`, zero quotient and `2ⁿ ≤ 2·2^p·2^K`, the composite first-arrives at the divider's `done` with cost exactly `(trips Y + 1)(2n + 2) + (K + 2)(2n + 2)`; quotient `⌊(XY mod 2ⁿ)/2^p⌋`, remainder `(XY mod 2ⁿ) mod 2^p` |
| `fmulInput_views`, `fmul_layout` | the same on the explicit `L`-cell layout, for `X, Y < 2^L` |
| `fmul_exact` | with also `XY < 2^L`: quotient `⌊XY/2^p⌋`, remainder `XY mod 2^p` |
| `fixmul_certified` | `q = ⌊XY/2^p⌋` satisfies `q/2^p ≤ (X/2^p)(Y/2^p) < (q + 1)/2^p` |
| `fmul_cost_le` | the exact cost is at most `(2L + 2)²` |
| `fixmul_tm` | **unsigned, on the compiled TM**: from any tape representing the layout, the TM of `fmulProg` reaches the divider's `done` in exactly `(trips Y + 1)(2L + 2) + (L + 1 − p)(2L + 2) ≤ (2L + 2)²` transitions, with the certified quotient |
| `tc_cast`, `tc_lt`, `tc_mul`, `tc_add`, `tc_shift`, `sval_tc`, `sval_neg_iff` | two's-complement identities (§3) |
| `sfix_word`, `sfixmul_certified` | the quotient word read in two's complement is `⌊xy/2^p⌋`, with the same certificate over ℚ |
| `sfixmul_tm` | **signed, on the compiled TM**: the same machine on the layout of the codes `x mod 2^L`, `y mod 2^L` returns `⌊xy/2^p⌋` in `(L − p)`-bit two's complement whenever that value lies in the `(L − p)`-bit range; same exact cost |
| `add_tc_value`, `sadd_tm` | signed addition: the low `n` bits of the adder's result read back `x + y`, in `addCost ≤ 2n + 3` transitions |
| `sub_tc_value`, `ssub_tm` | signed subtraction (negation for `x = 0`): the result word is the code of `x − y` whatever the final borrow; `2n + 2` transitions |
| `slt_iff` | signed comparison: `x < y` exactly when the difference word has its top bit set |

Every machine statement holds from **any** tape representing the input. Its cost is an exact
transition count of the compiled single-tape TM `Prog.toTM`, not a bound on an abstract step
count.

## 3. Two's complement over the unsigned primitives

The `L`-bit code of an integer `x` is `tc L x = x mod 2^L` (as a natural number). The reading of
an `n`-bit word is `sval n N = N` if `N < 2^(n−1)`, and `N − 2^n` otherwise.

- `sval_tc`: an integer in `[−2^(n−1), 2^(n−1))` is read back from its code.
- `tc_mul` and `tc_add`: codes multiply and add modulo `2^L`. The unsigned multiplier, adder and
  subtractor therefore already compute signed products, sums and differences modulo `2^L`.
- `tc_shift`: shifting an `L`-bit code right by `p` places (a logical shift, which is unsigned
  division by `2^p`) gives the `(L − p)`-bit code of the floor quotient `⌊z/2^p⌋`.
  - *Proof.* Write `z = N + 2^L k` with `N = tc L z`. Since `2^L = 2^(L−p)·2^p`,
    `⌊z/2^p⌋ = ⌊N/2^p⌋ + 2^(L−p) k`. Finally `⌊N/2^p⌋ < 2^(L−p)`.

Unsigned multiply-then-divide is therefore signed fixed-point multiplication with floor rounding.
The only hypothesis is that the result fits in the output word.

## 4. Sanity runs (not part of the proof)

A scratch `#eval` of `fmulProg.toProg.stepP` on concrete inputs (not committed) agrees with
the theorems:
- unsigned `(L, p, X, Y) = (8, 3, 13, 11)`: quotient 17 and remainder 7, in 198 transitions;
- unsigned `(10, 4, 31, 29)`: 56 and 3, in 286;
- unsigned `(6, 0, 7, 5)`: 35;
- signed `(10, 3, −13, 11)`: −18 = ⌊−143/8⌋;
- signed `(10, 3, −13, −11)`: 17;
- signed `(12, 4, −37, 21)`: −49 = ⌊−777/16⌋.

Every observed transition count equals the proved formula.

## 5. What remains on the machine side

- **Signed division (C5.6).** The offset identity
  `⌊x/D⌋ = ⌊(x + 2^(n−1)D)/D⌋ − 2^(n−1)` for `x ≥ −2^(n−1)` and `D ≥ 1` reduces it to three
  stages: an addition, the verified unsigned division and a subtraction. The adder and subtractor
  run on the `Cell` alphabet, so a common alphabet that also contains `Cell` tracks is needed, or
  layout conversion. Not built.
- **Complex arithmetic (C5.4).** It needs four products and two additions. This is a multi-stage
  composition on a larger alphabet, which `seq_reachFirst` now makes possible. Not built.
- **Normalized rationals (C5.5).** They need a greatest-common-divisor program, a loop with a
  data-dependent number of rounds. The composition theorem provides sequencing only. Not built.
- **Constants, convolution, the Taylor recurrence and the evaluator (C6, C7.5–C7.7, #99).** Not
  built.

## 6. Progress (registry)

```
C5   TM fixed-point, rational, signed and complex arithmetic; certified rounding  [##########..........]  50% (3/6)    50%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [#############.......]  67% (6/9)    65%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

- C5.2 and C5.3 move from open to proved.
- C5.6 (signed division) is added as open, so C5 moves from 1/5 to 3/6.
- C7.8 also cites `seq_reachFirst`.
- No other bar changes, and the ledger is unchanged.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `lake build PVNP` passed (7,440 jobs). `PVNP.SweepFixMul` builds without warnings and uses no
  `sorry`, `admit`, `native_decide` or custom axiom.
- The full transitive axiom audit (`audit/check_axioms.py`) runs over all 1,383 registered
  declarations, the 1,349 earlier ones and the 34 new theorems. The result is recorded on the
  pull request.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head.
