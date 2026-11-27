# Phase XXXII: certified complex fixed-point arithmetic by multi-stage composition (27 November 2026)

New Lean module: `lean/PVNP/SweepComplex.lean`, with 19 registered theorems. It builds on the
composition framework (`SweepCompose`, `SweepLens`) and on certified fixed-point
multiplication (`SweepFixMul`).

## Outcome

- **Proved (kernel-checked), registry C5.4.** Complex arithmetic on pairs, on the compiled
  single-tape Turing machine, in two's complement:
  - multiplication with certified rounding (`cmul_tm`);
  - addition and subtraction (`caddsub_tm`).
- **One machine.** Multiplication is a six-stage composite. Four lifted copies of the verified
  multiply-then-divide machine compute `⌊ac/2^p⌋`, `⌊bd/2^p⌋`, `⌊ad/2^p⌋` and `⌊bc/2^p⌋` on four
  blocks of tracks. The verified subtractor and a modular adder then form the real and
  imaginary parts.
  - Each stage reads its inputs where the earlier stages left them. No copying program is used.
  - Frame preservation keeps every block unchanged while the others run.
- **Certificate.** Let `z = (a + bi)/2^p` and `w = (c + di)/2^p`. The machine returns
  `Re = ⌊ac/2^p⌋ − ⌊bd/2^p⌋` and `Im = ⌊ad/2^p⌋ + ⌊bc/2^p⌋`, with
  `|Re/2^p − Re(zw)| < 2^{−p}` and `|Im/2^p − Im(zw)| < 2·2^{−p}`. It takes exactly the sum of the
  six stage costs, at most `4(2L + 2)² + 2(2L + 2)` transitions.
- **Only the results must fit.** The four products need no range condition, because their quotient
  words are exact codes modulo `2^{L−p}`. Only `Re` and `Im` must lie in the `(L − p)`-bit range.
- **Not done.**
  - signed division (C5.6) and normalized rationals (C5.5);
  - complex division, which needs real division;
  - constants, convolution and the Taylor recurrence (C6);
  - the evaluator (#99, which stays open).
- **Classical P versus NP remains unresolved.**

## 1. The machine

**Alphabet.** `CCell` has four product blocks `p1, …, p4 : FCell`, plus the real and imaginary
tracks.

**Lenses.**
- `lens1, …, lens4` view the blocks.
- `lensSub` views the quotient tracks of blocks 1 and 2 and the real track.
- `lensAdd` views the quotient tracks of blocks 3 and 4 and the imaginary track.

**Program.**

```
cmulProg = seq (seq (seq (seq (seq F1 F2) F3) F4) SUB) ADD
```

- `F_k = fmulProg.viaLens lens_k`.
- `SUB` is the verified subtractor along `lensSub`.
- `ADD` is the modular adder `addModProg` along `lensAdd`. This is the verified ripple-carry pass
  without the overflow cell, and it returns `(x + y) mod 2ⁿ`.

**Layout.** `cmulInput L p A B C D` puts the fixed-point layouts of `(A, C)`, `(B, D)`,
`(A, D)` and `(B, C)` on the four blocks, and zero on the result tracks. The operands are
duplicated in the layout.

## 2. Theorems

| Theorem | Statement |
|---|---|
| `addMod_first`, `addMod_value` | the modular adder first-arrives in `2n + 2` transitions and returns `(x + y) mod 2ⁿ` |
| `sub_first` | the subtractor in first-arrival form |
| `fmulProg_ext` | the fixed-point machine never extends the tape |
| `stage_fmul`, `stage_sub`, `stage_add` | one stage on the common alphabet: transported first arrival, result, and frame for every independent lens |
| `mkC_spec`, `cmulInput_spec` | the block and track views of the layout |
| `cmul_layout` | the composite first-arrives at its exit with the exact summed cost; real track `(q₁ − q₂) mod 2^L`, imaginary track `(q₃ + q₄) mod 2^L` |
| `tc_natCast`, `tc_mod_pow`, `tc_sub_tc`, `fq_word` | two's-complement identities: low `L − p` bits of an `L`-bit code, codes of differences, quotient words |
| `cmul_certified` | `|Re/2^p − Re(zw)| < 2^{−p}`, `|Im/2^p − Im(zw)| < 2·2^{−p}` |
| `cmul_tm` | **signed complex multiplication on the compiled TM**, with exact cost `≤ 4(2L + 2)² + 2(2L + 2)` |
| `cadd_first`, `csub_first`, `caddsub_tm` | complex addition and subtraction on pairs, `2(2n + 2)` transitions each, on the compiled TM |

**Proof structure of `cmul_layout`.** Each stage is applied to the tape the previous stage left:
- `stage_fmul` takes the block view, which earlier stages did not touch (by frames), and returns
  the next tape;
- the results are chained by `ProgOn.seq_reachFirst`, five times;
- the frame equations carry each block's quotient track to the subtraction and addition stages.

## 3. What remains on the machine side

- **Signed division (C5.6).** The offset identity reduces it to an addition, an unsigned
  division and a subtraction. It is not built.
- **Normalized rationals (C5.5).** A greatest-common-divisor program needs iteration with a
  data-dependent number of rounds. The composition theorem gives sequencing only, and no loop
  combinator is built yet.
- **Constants, convolution, the Taylor recurrence and the evaluator (C6, C7.5–C7.7, #99).** A
  uniform evaluator needs iteration over the mode set, which also requires a loop combinator.
  None of these is built.

## 4. Progress (registry)

```
C5   TM fixed-point, rational, signed and complex arithmetic; certified rounding  [#############.......]  67% (4/6)    65%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [#############.......]  67% (6/9)    70%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

C5.4 is proved, so C5 moves from 3/6 to 4/6. The ledger is unchanged.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepComplex` compiles without warnings and uses no `sorry`, `admit`, `native_decide` or
  custom axiom. `cmul_layout`, `cmul_tm` and `cmul_certified` depend only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `lake build PVNP` and the full transitive axiom audit (`audit/check_axioms.py`, all 1,452
  registered declarations) are run on this tree. The results are recorded on the pull request.
- A scratch `#eval` of the full six-stage composite exhausted memory and is not used. The
  fixed-point stages were checked by `#eval` in `phase-xxxii-fixed-point.md`.
