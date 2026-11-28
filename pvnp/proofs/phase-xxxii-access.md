# Phase XXXII: uniform access to packed words on the Turing machine (28 November 2026)

New Lean module: `lean/PVNP/SweepAccess.lean`, with 17 registered theorems. It builds on the loop
combinator (`SweepLoop`), the counter programs (`SweepLayout`) and the cellwise map (`SweepGcd`).

## Outcome

- **Proved (kernel-checked), new registry obligation C7.11.** Uniform input access: the
  compiled single-tape TM reads the `k`-th word of a packed input vector (`access_tm`).
  - *Input:* `L`-bit words `ws` stored on one track as `pack L ws = w₀ + 2^L w₁ + ⋯`, and the
    offset `kL` in binary on a counter track.
  - *Output:* the work track holds `ws[k]`.
  - *Cost:* exactly `(3kL + 3)(2n + 2)` transitions on `n` cells. It is uniform in `k`: one
    machine serves every index.
- **Why it is needed.** The evaluator works on vectors: the Fourier coefficients of the state,
  the Taylor coefficients, and the coefficients of polynomials. The arithmetic primitives work on
  whole tracks. A word of a vector must therefore be brought onto a work track, at an index that
  is data.
- **Not done.**
  - writing a word back into a vector;
  - computing the offset `kL` from `k` on the machine (the multiplier can do it, but it is not
    composed here);
  - convolution, the Taylor recurrence and the evaluator (C6.5, C6.6, C7.5–C7.7, #99, which stays
    open).
- **Classical P versus NP remains unresolved.**

## 1. The machine

**Alphabet.** `ACell` has the shift tracks (work track `x` and counter `c`), the vector track `v`
and the mask track `mask`.

**Stages.**
1. A cellwise map copies `v` into `x`.
2. The right-shift loop `shrLoop` runs along a lens onto `(x, c)`.
   - *Test:* the counter test of `SweepLayout`.
   - *Body:* `seq shr dec`. Here `shr` is a single trip whose backward pass gives each cell the
     bit of the cell above it, so `x ↦ ⌊x/2⌋`; `dec` decrements the counter.
3. A cellwise map masks `x` with the mask track, which holds `2^L − 1`.

The stages are chained by `ProgOn.seq_reachFirst`. The shift loop never extends the tape
(`shrLoop_ext`), so the mask track is unchanged by frames.

## 2. Theorems

| Theorem | Statement |
|---|---|
| `fscan_idS`, `bscan_shr`, `bscan_shr_c`, `shr_first`, `shr_value` | the single-trip right shift: `x ↦ ⌊x/2⌋`, counter unchanged |
| `bodyR_first`, `bodyRStep_length`, `bodyRStep_x`, `bodyRStep_c` | the body: halve, then decrement |
| `iterR_spec`, `shift_right_by_counter` | **the right-shift loop**: `x = ⌊X/2^s⌋`, a zero counter, exactly `(3s + 1)(2n + 2)` transitions |
| `val_and_mask` | masking with `2^L − 1` keeps the residue modulo `2^L` |
| `pack_word` | `⌊pack L ws / 2^{kL}⌋ mod 2^L = ws[k]` for words below `2^L` |
| `shrLoop_ext`, `access_run` | the access machine on any tape: work track `⌊V/2^s⌋ mod 2^L` |
| `mkA_spec`, `access_tm` | **uniform word access on the compiled TM** |

## 3. Progress (registry)

```
C5   TM fixed-point, rational, signed and complex arithmetic; certified rounding  [####################] 100% (6/6)    90%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [###############.....]  73% (8/11)    70%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

- C7.11 is a new obligation, recorded as proved by `access_tm`. It is the "uniform input access"
  item of the restricted evaluator. It is infrastructure, like C7.8 (composition), C7.9 (track
  lenses) and C7.10 (loops).
- C7 moves from 7/10 to 8/11. C7.5 (the arithmetic library, which needs C6), C7.6 (the uniform
  evaluator) and C7.7 (its polynomial runtime) stay open.
- The ledger is unchanged. I-11 stays Restricted.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepAccess` compiles without warnings and uses no `sorry`, `admit`, `native_decide` or
  custom axiom. `access_tm`, `shift_right_by_counter` and `pack_word` depend only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `lake build PVNP` and the full transitive axiom audit (`audit/check_axioms.py`, all 1,561
  registered declarations) are run on this tree. The results are recorded below once complete.
