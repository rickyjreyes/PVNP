# Phase XXXII: finite Fourier convolution on the Turing machine by Kronecker substitution (28 November 2026)

New Lean module: `lean/PVNP/SweepConv.lean`, with 53 registered theorems. It builds on:
- the excess-packed vector format (`SweepPoly`, `SweepAccess`);
- the subtractor (`SweepArith`) and the multiplier (`SweepMul`), in first-arrival form;
- two's-complement codes (`SweepFixMul`);
- composition and track lenses (`SweepCompose`, `SweepLens`).

## Outcome

- **Proved (kernel-checked), registry C6.5.** The compiled single-tape TM computes the Fourier
  convolution of two finite coefficient arrays on a box of modes `[−R, R]² ⊂ ℤ²`. It does so for
  integer coefficients (`conv2_tm`) and for complex ones, given as pairs of integer arrays
  (`cconv2_tm`).
  - *Input:* the coefficients as `L`-bit words in excess `2^{L−1}`, packed on one track per part.
    The mode `p` sits at the index `ι(p) = (p₁ + R) + (4R + 1)(p₂ + R)`, and the padding positions
    hold zero coefficients.
  - *Output:* for every mode `k ∈ [−2R, 2R]²`, the accumulator's `L`-bit word at
    `κ(k) = (k₁ + 2R) + (4R + 1)(k₂ + 2R)` is `(a ⋆ b)(k) + 2^{L−1}`, with
    `(a ⋆ b)(k) = Σ_{j ∈ [−R, R]²} a(k − j) b(j)`. In the complex case there are two accumulators,
    for the real and the imaginary part.
  - *Hypotheses:* `0 < L`; the input coefficients lie in the `L`-bit range; the first factor is
    supported on the box; the values of `a ⋆ b` lie in the `L`-bit range; `(4R + 1)² L ≤ N`.
  - *Cost:* exactly `(trips + 3)(2N + 2) ≤ (N + 3)(2N + 2)` transitions for integer coefficients,
    and at most `(4N + 12)(2N + 2)` for complex ones. The machine is uniform in the number of
    modes.
- **One multiplication.** The convolution of two vectors is computed by one product of two
  integers. Evaluated at `2^L`, the coefficient polynomials multiply to the coefficient polynomial
  of the convolution (`kron_mul`). This is Kronecker substitution. When the convolution's
  coefficients fit in `L` bits, the `L`-bit words of the product are those coefficients.
- **Not done.**
  - truncation of the product to the Galerkin mode set, and repacking it in the input format;
  - the scaling of the product (`L⁻¹` in `TorusNonlin.pr`) and fixed-point rounding of the
    coefficients;
  - the constants and the Taylor recurrence (C6.2, C6.3, C6.6);
  - the evaluator (C7.5–C7.7, #99, which stays open).
- **Classical P versus NP remains unresolved.**

## 1. Kronecker substitution

`kron L a = Σ_i a_i 2^{iL}` is the coefficient polynomial `cpoly a = Σ_i a_i Xⁱ` evaluated at
`X = 2^L` (`cpoly_eval`).
- The convolution `conv a b`, with `(a ∗ b)_k = Σ_{i+j=k} a_i b_j`, has the coefficient
  polynomial `cpoly a · cpoly b` (`cpoly_conv`).
- Evaluating at `2^L` gives `kron L a · kron L b = kron L (a ∗ b)` (`kron_mul`).

**The excess format.** For words in the `L`-bit range, the packed excess codes are
`kron L c + Σ_k 2^{L−1} 2^{kL}` (`pack_excess`). This is the Kronecker value plus a packed
constant. The pack of `n` words below `2^L` is below `2^{nL}` (`pack_lt`).

## 2. The machine

**Alphabet.** `KCell` has the multiplier's tracks `x, y, acc`, the packed inputs `va, vb` and
their packed excess constants `ea, eb`.

**Stages** (`convProg`):
1. the subtractor, through a lens, writes `x := va − ea`. In two's complement this is the code of
   `kron L a` (`sub_tc_value`);
2. the subtractor writes `y := vb − eb`, the code of `kron L b`;
3. the multiplier adds `x·y` to `acc`, which holds the packed excess constant of the output.

Every stage is an exact code modulo `2^N` (`tc_fma`). The accumulator therefore becomes
`tc_N(E + kron L a · kron L b) = tc_N(E + kron L (a ∗ b))`, which is the packed excess codes of
`a ∗ b` (`conv_run`, `conv_tm`). The subtractors and the multiplier leave the input tracks
unchanged, and the frames come from the lens lemmas.

**Complex coefficients** (`cconvProg`). The alphabet `CKCell` holds both parts of both inputs and
two accumulators. The real machine runs four times through four lenses (`conv_lens`):
- `accR += A_R B_R`;
- `accR += (−A_I) B_I`. This lens swaps the roles of the vector and the excess constant, so the
  subtractor writes `ea − vaI = −A_I`;
- `accI += A_R B_I`;
- `accI += A_I B_R`.

The result is `Re = A_R B_R − A_I B_I` and `Im = A_R B_I + A_I B_R` (`cconv_run`,
`kron_cconvR`, `kron_cconvI`, `cconv_tm`).

## 3. Fourier convolution on a box of modes

The modes of `[−R, R]²` are packed in rows of width `W = 4R + 1` (`boxList`):
`ι(p) = (p₁ + R) + W(p₂ + R)`.
- The sum of two first digits is at most `4R < W`. So there is no carry, and
  `ι(p) + ι(q) = κ(k)` holds exactly when `p + q = k` (`bidx_add`, from `digits_eq`).
- Hence the packed convolution at `κ(k)` is the Fourier convolution `(a ⋆ b)(k)`
  (`convAt_box`). The proof compares the coefficients of the products of the polynomials
  `Σ_p a(p) X^{ι(p)}` (`cpoly_boxList`).
- Every index of the packed product, `n < W²`, is `κ(k)` for some `k ∈ [−2R, 2R]²`
  (`bidx2_decode`). So the range hypothesis on `a ⋆ b` covers every word of the product
  (`conv_boxList_range`).

## 4. Theorems

| Theorem | Statement |
|---|---|
| `cpoly_coeff`, `cpoly_eval`, `convAt_eq_zero`, `conv_getD`, `cpoly_conv`, `conv_length`, `cpoly_mul_coeff` | the coefficient polynomial of a list and of a convolution |
| `kron_mul` | **Kronecker substitution**: `kron L a · kron L b = kron L (a ∗ b)` |
| `excess_lt`, `pack_excess`, `pack_lt`, `excessCodes_lt`, `excessConst_lt` | the excess format and its bounds |
| `stk_sub`, `stk_mul`, `kv_congr`, `kmap_proj`, `tc_fma` | the stages on `KCell`, with their frames; multiply-add on codes |
| `conv_run` | **the convolution machine on any tape**: `acc = tc_N(C + (PA − QA)(PB − QB))`, inputs unchanged, exact cost |
| `mkK_spec`, `conv_tm` | the layout; **convolution on the compiled TM** |
| `mem_modeBox`, `digits_eq`, `bidx_inj`, `bidx_bound`, `bidx_decode`, `boxList_getD`, `boxList_length`, `cpoly_boxList` | the packing of a box of modes |
| `bidx_add`, `convAt_box` | **indices add exactly when modes add**; the packed convolution is the Fourier convolution |
| `blen_conv`, `bidx2_decode`, `bidx2_lt`, `boxList_ne_nil`, `boxList_range`, `conv_boxList_range` | the product box and the range of the packed product |
| `conv2_tm` | **Fourier convolution on the compiled TM** |
| `convProg_ext`, `conv_lens` | the convolution machine never extends the tape; a lifted convolution stage with its frame |
| `cv_congr`, `cmap_proj`, `tc_tc_add`, `cconv_run` | **the complex convolution machine on any tape** |
| `kron_cconvR`, `kron_cconvI`, `cconvR_length`, `cconvI_length` | the Kronecker identities for complex coefficients |
| `map_range_getD`, `mkCK_spec`, `cconv_tm` | the layout; **complex convolution on the compiled TM** |
| `cconv_boxList_range`, `cconv2_tm` | **complex Fourier convolution on the compiled TM** |

## 5. Progress (registry)

```
C6   Constants and series on the TM                                               [##########..........]  50% (3/6)    35%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [###############.....]  73% (8/11)    70%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

- C6.5 is proved, so C6 moves from 2/6 to 3/6. Its subjective estimate moves from 25% to 35%.
  The convolution covers the products in the nonlinearity. Truncation, scaling and the Taylor
  recurrence (C6.6) remain.
- C7 is unchanged at 8/11. C7.5, C7.6 and C7.7 stay open.
- The ledger is unchanged. I-11 stays Restricted.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `PVNP.SweepConv` compiles without warnings and uses no `sorry`, `admit`, `native_decide` or
  custom axiom. `conv2_tm`, `cconv2_tm`, `conv_tm`, `cconv_tm`, `kron_mul` and `convAt_box`
  depend only on `propext`, `Classical.choice` and `Quot.sound`.
- `lake build PVNP` passed (7,450 jobs).
- The full transitive axiom audit (`audit/check_axioms.py`) passed for all 1,635 registered
  declarations: the 1,582 earlier ones and the 53 new theorems. Each uses only `propext`,
  `Classical.choice` and `Quot.sound`, or none, and no `sorryAx` occurs. The audited file is the
  committed `lean/audit/AxiomAudit.lean`.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head.
