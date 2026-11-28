# Phase XXXII: certified π on the Turing machine (28 November 2026)

New Lean module: `lean/PVNP/SweepPi.lean`, with 23 registered theorems. It builds on:
- the Euclidean alphabet `GCell` and its verified shift-and-divide stage `shdiv` (`SweepGcd`);
- the loop combinator (`SweepLoop`);
- the subtractor, the counter and the cellwise map;
- Mathlib's arctangent series (`Real.hasSum_arctan`) and addition formula (`Real.arctan_add`).

## Outcome

- **Proved (kernel-checked), registry C6.2.** One compiled single-tape TM computes a certified
  rational approximation of `π` (`pi_tm_prec`).
  - *Input:* the precision `q ≥ 1`, through the layout `piInput (q + 3) (2^q) (2q + 1)`.
  - *Output:* an integer `A`, read in two's complement, with `|4A/2^q − π| ≤ (16q + 14)/2^q`.
  - *Cost:* exactly `((4q + 3)(8q + 38) + 4)(4q + 14)` transitions, a polynomial of degree 3 in `q`.
- **The general form** (`pi_tm`). For odd `J`, `3Z < 2^W`, `2J + 3 < 2^W` and `9 < 2^W`:
  - the machine runs exactly `((2J + 1)(8W + 14) + 4)(4W + 2)` transitions;
  - it leaves `A = atSum Z 2 J + atSum Z 3 (J + 1)` with `|4A − Zπ| ≤ 8J + 4 + (16/3) Z/4^J`
    (`piA_err`).
- **No series is evaluated in the layout.** The layout holds only:
  - the loops' data `2Z, 4, 1, J` and `3Z, 9, 1, J + 1`;
  - the code of `−2`, the counter constant `W` and the marker `2^W`.

  Every term of both series is computed by the machine.
- **Not done.**
  - the algebra constant `C_A = 4√(SL L)/L` (C6.3), with `SL L = Σ_{k ∈ ℤ²} (1 + |ξ_k|²)^{−2}`.
    - The tail of this lattice sum beyond `|k| ≤ R` decays only like `R^{−2}`. A direct partial
      sum certified to `2^{−p}` therefore needs about `2^{p/2}` terms, which is exponential in
      `p`. A polynomial-time certificate needs accelerated summation (for example Poisson
      summation), which is not attempted here.
    - The evaluator's error bounds need only an upper bound, such as `CA_le : C_A ≤ 6` for
      `L ≥ 1`. The obligation asks for an approximation, so it stays open;
  - the Taylor recurrence (C6.6);
  - the evaluator (C7.5–C7.7, #99, which stays open).
- **Classical P versus NP remains unresolved.**

## 1. The series

**Euler's formula** (`pi_euler`). `arctan(1/2) + arctan(1/3) = arctan 1 = π/4`, by the addition
formula.

**The tail** (`arctan_tail`). For `0 ≤ x ≤ 1/2`, the arctangent series after `J` terms is within
`(4/3) x^{2J+1}` of `arctan x`. Its terms are bounded by a geometric series in `x²`.

**The machine's terms** (`atTerm`, `atTerm_err`). These are
`tₙ = ⌊Z / ((2n + 1) m^{2n+1})⌋`, each within `1` of `Z/((2n + 1) m^{2n+1})`. So the
alternating sum `atSum Z m J = Σ_{n<J} (−1)ⁿ tₙ` satisfies
`|atSum Z m J − Z arctan(1/m)| ≤ J + (4/3) Z m^{−(2J+1)}` for `m ≥ 2` (`atSum_err`).

## 2. The arctangent loop

**Alphabet.** `GCell`, as in `SweepGcd`. It has these tracks:
- `a`, the power term `u`;
- `b`, the divisor `m²`;
- `p`, the odd number `d`;
- `rp`, the term `t`;
- `qq`, the sum `S`;
- `rq`, the next sum;
- `xc.z`, the code of `−2`;
- `xc.ia`, the counter.

The divider's tracks, the counter constant and the marker serve `shdiv`. The tracks
`xc.x, xc.y, xc.acc, xc.fl, xc.id` are carried unchanged (`lensX5`).

**One step** (`BODYA`, `body_at`) has eleven stages:
1. load the divider with `u` and `m²`, by a cellwise map;
2. shift;
3. divide, so `u' = ⌊u/m²⌋`;
4. store `u'` and load the divider with `u'` and `d`, by a cellwise map;
5. shift;
6. divide, so `t = ⌊u'/d⌋`;
7. store `t`, by a cellwise map;
8. the subtractor writes `S' = t − S`;
9. the subtractor writes `d − (−2) = d + 2`;
10. move both into place, by a cellwise map;
11. the counter decrements.

The step takes exactly `(8W + 13)(4W + 2)` transitions.

**The sign without a conditional.** The update `S := t − S` gives
`S_J = (−1)^{J+1} Σ_{n<J} (−1)ⁿ tₙ` (`atR_eq`). So an odd step count yields `+atSum` and an even
one `−atSum`.

**The loop** (`atLoop`, `at_loop`). A single-trip test continues while the counter is nonzero.
The proof is by induction on the counter. From `u = mZ` the `n`-th term is
`⌊⌊mZ/m^{2n+2}⌋/(2n + 1)⌋ = tₙ` (`atU_term`).

## 3. The π machine

`piProg` (`pi_run`) has four parts:
1. the loop runs `J` steps for `m = 2`, with `J` odd, so it leaves `atSum Z 2 J`;
2. a cellwise map saves the sum on `xc.id` and loads the second loop's data from the carried
   tracks;
3. the loop runs `J + 1` steps for `m = 3`, an even count, so it leaves `−atSum Z 3 (J + 1)`;
4. the subtractor forms `A = atSum Z 2 J + atSum Z 3 (J + 1)`.

**Decoding.** `|A| ≤ (2J + 1) Z < 2^{2W−1}` (`atSum_abs_le`). So the `2W`-bit two's-complement
reading of the result track is `A` itself (`pi_tm`).

## 4. Theorems

| Theorem | Statement |
|---|---|
| `pi_euler` | `π = 4 (arctan(1/2) + arctan(1/3))` |
| `arctan_tail` | the arctangent tail after `J` terms is at most `(4/3) x^{2J+1}` for `0 ≤ x ≤ 1/2` |
| `atTerm_err`, `atSum_err`, `piSum_err` | the machine terms and the alternating sums against `Z arctan(1/m)` and `Zπ` |
| `fscan_nzA`, `testA_step`, `testA_cost` | the loop test on the counter |
| `stg_sub`, `stg_dec`, `dec_value` | the subtractor and counter stages on `GCell`, with their frames |
| `body_at` | **one arctangent step**, with exact cost and the carried tracks unchanged |
| `atU_le`, `at_loop` | **the arctangent loop**, with exact cost |
| `atU_eq`, `atU_term`, `atR_eq` | the loop's terms are `tₙ`, and its sum is `(−1)^{J+1} atSum` |
| `pi_run` | **the π machine on any tape** |
| `piA_err`, `atSum_abs_le` | the certificate `|4A − Zπ| ≤ 8J + 4 + (16/3) Z/4^J`; the size of `A` |
| `tv_range`, `pi_tm` | the layout; **π on the compiled TM** |
| `pi_tm_prec` | **certified π to precision `q`**, in a cubic number of transitions |

## 5. Progress (registry)

```
C6   Constants and series on the TM                                               [#############.......]  67% (4/6)    45%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [###############.....]  73% (8/11)    70%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

- C6.2 is proved, so C6 moves from 3/6 to 4/6. Its subjective estimate moves from 35% to 45%.
  The dispersion symbol `ω_k = (κ − |ξ_k|²)²` of the vector field (`TorusH2.om`) involves `π`
  through `ξ_k = 2πk/L`. Computing it on the machine still needs the fixed-point products of
  C5, which are not composed here. C6.3 (the constant `C_A`) and C6.6 (the Taylor recurrence)
  remain.
- C7 is unchanged at 8/11. C7.5, C7.6 and C7.7 stay open.
- The ledger is unchanged. I-11 stays Restricted.

## 6. Separation (I-2, I-16, I-32)

- **No new mechanism.**
  - `CrossingSAT.SATLowerBound` is neither proved nor refuted.
  - No verified polynomial-time SAT algorithm is given.
  - C9 stays at 0/3, and C12 stays at 0/1.
- **This phase works on the simulation side.** The arithmetic here and in the companion notes
  (C5, C6.2, C6.4, C6.5) builds parts of an explicit polynomial-time TM simulation of the
  restricted analytic class (C7.5–C7.7, #99).
- **That simulation cannot separate.** Once it is complete:
  - a polynomial-time decision procedure in the class becomes a classical one;
  - a superpolynomial lower bound for the class becomes a lower bound for `P_TM`. That is the
    statement `CrossingSAT.SATLowerBound` (equivalent to `P_TM ≠ NP_TM`, Phase IX).
- **So the restricted class gives no route to separation** that avoids the classical problem.
  Restricted physical lower bounds are not substituted for universal hardness.
- **Classical P versus NP remains unresolved.**

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepPi` compiles without warnings and uses no `sorry`, `admit`, `native_decide` or
  custom axiom. `pi_tm_prec`, `pi_tm`, `piA_err`, `pi_run`, `at_loop`, `body_at`, `pi_euler` and
  `atSum_err` depend only on `propext`, `Classical.choice` and `Quot.sound`.
- `lake build PVNP` passed (7,451 jobs).
- The full transitive axiom audit (`audit/check_axioms.py`) passed for all 1,658 registered
  declarations: the 1,635 earlier ones and the 23 new theorems. Each uses only `propext`,
  `Classical.choice` and `Quot.sound`, or none, and no `sorryAx` occurs. The audited file is the
  committed `lean/audit/AxiomAudit.lean`.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head.
