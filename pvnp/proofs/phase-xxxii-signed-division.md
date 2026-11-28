# Phase XXXII: signed fixed-point division with certified rounding (28 November 2026)

New Lean module: `lean/PVNP/SweepSDiv.lean`, with 29 registered theorems. It builds on:
- the composition framework (`SweepCompose`, `SweepLens`);
- long division (`SweepDiv`);
- the two's-complement library (`SweepFixMul`, `SweepComplex`).

## Outcome

- **Proved (kernel-checked), registry C5.6.** Signed fixed-point division with certified
  rounding, on the compiled single-tape Turing machine, in two's complement (`sdiv_tm`).
  - *Hypotheses:* `D ≠ 0`, `−2^W ≤ 2D < 2^W` and `|N|·2^p < 2^W`.
  - *Output:* the quotient track, read in `2W`-bit two's complement, is `q = tdiv(N·2^p, D)`.
    This is `N·2^p/D` rounded toward zero. The remainder track holds `|tmod(N·2^p, D)|`.
  - *Certificate:* `|q/2^p − N/D| < 2^{−p}` (`sdiv_certified`).
  - *Cost:* exactly `(W + 7)(4W + 2)` transitions.
- **One machine, four stages.** The stages run on one common alphabet and are chained by
  `ProgOn.seq_reachFirst`:
  1. sign and negate the dividend;
  2. sign and negate the divisor;
  3. the verified long-division machine on the magnitudes;
  4. negate the quotient when the signs differ.

  Each stage reads its inputs where the earlier stages left them. Frame preservation keeps the
  other tracks unchanged.
- **Not done.**
  - normalized rationals (C5.5);
  - complex division;
  - constants, convolution and the Taylor recurrence (C6);
  - the evaluator (#99, which stays open).
- **Classical P versus NP remains unresolved.**

## 1. The machine

**Alphabet.** `SDCell` has the divider's four tracks (`DCell`: dividend `n`, shifted divisor `d`,
quotient `q`, marker `m`) and two sign flags, `fn` and `fd`.

**Conditional negation.** One transducer serves three stages. `fnegBy p` negates a word in two's
complement where the predicate `p` holds: it inverts the bit and adds the carry, with carry-in
`1`. It works on the view `NCell`, which has a word `w` and two flags `f` and `g`.
- `cnegProg` (sign and negate) takes two trips.
  - *First trip:* the forward pass carries the last bit seen, so its final buffer is the top bit
    of `w`. The backward pass writes that bit on the flag `f` of every cell.
  - *Second trip:* the forward pass negates `w` where `f` is set.
- `fixProg` (sign correction) takes one trip. It negates `w` where `f ≠ g`.

**Lenses.**
- `lensNn` views `(n, fn, fd)`: the first stage negates the dividend and sets `fn`.
- `lensNd` views `(d, fd, fn)`: the second stage negates the divisor and sets `fd`.
- `lensDv` views the four division tracks: the third stage is the verified divider.
- `lensNq` views `(q, fn, fd)`: the fourth stage negates the quotient where `fn ≠ fd`.

**Program.**

```
sdivProg = seq (seq (seq NEGN NEGD) DIVS) FIXQ
```

**Layout.** `sdivInput W p N D` has `2W` cells:
- the dividend track holds the `2W`-bit code of `N·2^p`;
- the divisor track holds the `2W`-bit code of `D·2^W`;
- the quotient track holds zero and the marker track holds `2^W`;
- both flags are clear.

By `tc_mul_pow`, the two codes are the `(2W − p)`-bit code of `N` placed at offset `p` and the
`W`-bit code of `D` placed at offset `W`. They are placements of codes, as in the unsigned layout
`divInput`, which places the divisor at `D·2^W`. No arithmetic is done in the layout.

## 2. Theorems

| Theorem | Statement |
|---|---|
| `fnegBy_w`, `fscan_negBy_on`, `fscan_negBy_off`, `fscan_negBy_f`, `fscan_negBy_g`, `negBy_value` | conditional negation: an enabled word becomes `(2ⁿ − w) mod 2ⁿ`, a disabled word is unchanged, and the flags are unchanged |
| `fscan_sgn`, `bscan_set`, `setF_length`, `vW_setF`, `lastW_eq` | the sign trip: its forward buffer is the top bit, which is set exactly when `w ≥ 2^{n−1}` |
| `cneg_step1`, `cneg_step2`, `cneg_first`, `cneg_spec` | sign and negate first-arrives in two trips; it writes the top bit on every flag `f` and negates the word if that bit is set |
| `fix_first`, `fix_spec` | the single-trip sign correction, for uniform flags |
| `tc_neg`, `cneg_abs` | two's-complement negation of a code, and sign and negate on a code returns `|x|` with the sign `x < 0` |
| `tc_mul_pow` | the code of `x·2^p` is the `(n − p)`-bit code of `x` shifted by `p` places |
| `tdiv_cases` | `tdiv x d` is `±(|x| / |d|)`, with the sign negative exactly when the signs of `x` and `d` differ |
| `sdiv_certified` | `|tdiv(N·2^p, D)/2^p − N/D| < 2^{−p}` |
| `stage_cneg`, `stage_div`, `stage_fix` | one stage on the common alphabet: transported first arrival, result, and frame for every independent lens |
| `sdivInput_spec`, `all_eq_of_map` | the track views of the layout; uniform flags from a mapped equation |
| `sdiv_layout` | the composite first-arrives at its exit in exactly `(W + 7)(4W + 2)` transitions, with quotient `tdiv(N·2^p, D)` and remainder `|tmod(N·2^p, D)|` |
| `sdiv_tm` | **signed fixed-point division on the compiled TM**, with the certificate and the exact run |

**Proof structure of `sdiv_layout`.**
- Stage 1 turns the dividend track into `|N·2^p|` and sets `fn` to the sign of `N·2^p`
  (`cneg_spec`, `cneg_abs`). The other three division tracks are unchanged by frames.
- Stage 2 turns the divisor track into `|D|·2^W` and sets `fd` to the sign of `D`. Its view
  carries `fn` as the untouched flag `g`, so `fn` survives.
- Stage 3 is `div_reach_first` with `K = W` and divisor `|D|`. The marker `2^W` and the zero
  quotient come from the layout by frames.
- Stage 4 reads `fn` and `fd`, which the divider left unchanged (`lensFl` frame), and negates
  the quotient exactly when the signs differ (`fix_spec`).
- The quotient word is read back by `tc_neg`, `sval_tc` and `tdiv_cases`.

**Why truncation.** Sign-magnitude division rounds toward zero. Rounding down would need one more
conditional decrement when the signs differ and the remainder is nonzero. The evaluator needs
the certified error bound `|q/2^p − N/D| < 2^{−p}`, the same kind of certificate as
`cmul_certified`, and it does not need a particular rounding direction.

## 3. What remains on the machine side

- **Normalized rationals (C5.5).** A greatest-common-divisor program can now be written as a loop
  (`SweepLoop`), with a test for a zero remainder and a body that divides. It is not built.
- **Constants, convolution, the Taylor recurrence and the evaluator (C6, C7.5–C7.7, #99).** None
  of these is built.

## 4. Progress (registry)

```
C5   TM fixed-point, rational, signed and complex arithmetic; certified rounding  [#################...]  83% (5/6)    75%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [##############......]  70% (7/10)    70%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

- C5.6 is proved, so C5 moves from 4/6 to 5/6. Its subjective estimate moves from 65% to 75%; the
  remaining obligation, C5.5, needs a gcd loop.
- The ledger is unchanged. I-11 stays Restricted.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepSDiv` compiles without warnings and uses no `sorry`, `admit`, `native_decide` or
  custom axiom. `sdiv_tm`, `sdiv_layout` and `sdiv_certified` depend only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `lake build PVNP` passed (7,445 jobs).
- The full transitive axiom audit (`audit/check_axioms.py`) passed for all 1,509 registered
  declarations: the 1,480 earlier ones and the 29 new theorems. Each uses only `propext`,
  `Classical.choice` and `Quot.sound`, or none, and no `sorryAx` occurs. The audited file is the
  committed `lean/audit/AxiomAudit.lean`.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head.
