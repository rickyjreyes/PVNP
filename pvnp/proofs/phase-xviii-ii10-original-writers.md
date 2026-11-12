# II-10 at its original scope: the original polynomial-radius writers

**Date:** 12 November 2026
**Claim:** Part II, Theorem `thm:tm_to_wcc` (inventory row II-10)
**Outcome:** PROVED. Status changes from Restricted to Exact.
**Lean:** `lean/PVNP/TwoPhasePolynomialExec.lean`, `TwoPhasePolynomialState.lean`,
`TwoPhasePolynomialProgram.lean`, `TwoPhasePolynomialOutputs.lean`, `TwoPhasePolynomialFP.lean`
(namespace `PVNP.TwoPhasePolynomialWriter`)
**Verification record:** `pvnp/proofs/II10_VERIFICATION_LEDGER.md`

## 1. What was missing

`TwoPhaseUniform.originalUniform M p hWindow hEncoder` packages the author's two-phase machine
`W_M` as a uniform discrete WCC machine (`UWCC`), given two hypotheses:

```lean
hWindow  : FP (originalWindowCode p)
hEncoder : FP (originalInputCode M p)
```

`FP f` means: some single-tape machine of `def:tm` outputs `f x` on input `x`, at its **first**
halt, within a polynomial number of transitions, with the output on cells `0..|f x|-1` followed
by a blank (`MTM.Outputs`). Until now only fixed-radius writers were verified.

## 2. Result

For every `p : Polynomial ℕ`, every `M : MTM` and every input `x`:

| Theorem | Statement |
|---|---|
| `windowMTM_outputs` | `(windowMTM p).Outputs x (originalWindowCode p x) ((windowTime (coeffs p)).eval x.length)` |
| `inputMTM_outputs` | `(inputMTM M p).Outputs x (originalInputCode M p x) ((inputTime M (coeffs p)).eval x.length)` |
| `originalWindowCode_fp` | `FP (originalWindowCode p)` |
| `originalInputCode_fp` | `FP (originalInputCode M p)` |
| `originalWM` | `originalUniform M p` with both hypotheses supplied |
| `originalWM_first_answer` | if `M` first halts on `x` at `T ≤ p(|x|)`, the first non-`run` output of `W_M` is at update `2T` and equals the acceptance bit |
| `originalWM_decides` | `thm:tm_to_wcc`: `W_M` decides the language of `M` within `2·c·max(n,1)^k` updates |
| `originalWM_mem_P_disc`, `P_Turing_subset_P_disc_by_original` | `W_M` is itself the `P^disc` witness |

`windowMTM p` and `inputMTM M p` are the machines defined in
`TwoPhasePolynomialWriter.lean`. Their definitions are unchanged. The only edit to that file is
the removal of 18 `private` modifiers.

## 3. The machine

`build (entry, program)` is a single-tape machine with tape symbols `blank`, `leftEnd`, `raw b`
and `work c`. A work cell `c` carries an optional input bit, four marks (`acc`, `dest`, `outer`,
`inner`) and an optional output bit. Control states are `start`, `mark`, `normalize`, `done`,
and `ret pc`, `scan pc`, `neighbor pc` for a program counter `pc`. The program is an array of
instructions `finish | copy | take | nextInput | headInput | inc | emit`, produced by a small
assembler (`putI`, `setI`, `word`, `repeated`, `horner`, `assemble`).

A run has four parts.

1. **Normalization.** The head writes `leftEnd` at cell `-1`, converts the input cells into work
   cells, and returns. This takes `2|x| + 4` transitions (`normalize_steps`).
2. **Horner stages.** For the coefficients of `p`, highest first, one stage replaces the unary
   accumulator `a` (the `acc` marks on cells `0..a-1`) by `a·n + c`.
3. **Body.** `windowBody` or `inputBody M` writes the output bits into the work cells, using the
   accumulator `L = p(n)` as a loop counter.
4. **Finish.** One left-to-right scan converts each work cell into its raw output bit and halts
   on the first cell without an output bit, which leaves a blank after the word.

## 4. Proof

### 4.1 Instruction-level execution (`TwoPhasePolynomialExec.lean`)

`tapeOf l` is the tape with `leftEnd` at `-1`, the work cells `l` on `[0, |l|)` and blanks
elsewhere. `Steps P c c' k` says that `k` transitions lead from `c` to `c'` and that no
configuration strictly before step `k` is in the halting state. Every instruction has a lemma
with an exact transition count, starting and ending in `scan pc` at cell `0`:

| Instruction | Lemma | Transitions |
|---|---|---|
| return walk | `ret_walk` | `k + 1` from cell `k - 1` |
| `copy` | `exec_copy` | `2·len + 2` |
| `take`, mark found at `j` | `exec_take_hit` | `2j + 2` |
| `take`, no mark | `exec_take_miss` | `2·len + 2` |
| `inc` | `exec_inc_in`, `exec_inc_end` | `2j + 2` inside the work region; `2·len + 2` when the region is extended by one cell |
| `emit` | `exec_emit_in`, `exec_emit_end` | `2j + 2` inside the work region; `2·len + 2` when the region is extended by one cell |
| `nextInput` | `exec_next_hit`, `exec_next_miss` | `2j + 4`, `2·len + 2` |
| `headInput` | `exec_head` | `2` |
| `finish` | `exec_finish` | `|w| + 1`, ending in the halting state with `w` on the tape and a blank after it |

### 4.2 Abstract state (`TwoPhasePolynomialState.lean`)

In the configurations that occur, every mark is an initial segment or an interval, and the output
bits form an initial segment. The state is therefore

```lean
structure St where
  x : List Bool      -- input bits, on cells 0..|x|-1
  len : ℕ            -- length of the work region
  acc dst : ℕ        -- accumulator and destination, as initial segments
  oLo oHi iLo iHi : ℕ  -- outer and inner counters, as intervals
  out : List Bool    -- output bits written so far
```

with `cells s` the list of work cells it denotes. `Exec P pc s pc' s' m` says: from `scan pc` on
`tapeOf (cells s)`, the machine reaches `scan pc'` on `tapeOf (cells s')` without halting, in at
most `m·(2·s'.len + 4)` transitions, and well-formedness is preserved. Each instruction lifts to
`Exec` (`Exec.copy_acc_outer`, `Exec.clear_dest`, `Exec.copy_input_inner`, `Exec.copy_dest_acc`,
`Exec.take_outer_hit`, `Exec.take_outer_miss`, `Exec.take_inner_hit`, `Exec.take_inner_miss`,
`Exec.inc`, `Exec.emit`, `Exec.next_hit`, `Exec.next_miss`, `Exec.head`). Because the whole tape
is `tapeOf (cells s')`, these lemmas also say that every cell not named in the update is unchanged.

### 4.3 Assembler and Horner's rule (`TwoPhasePolynomialProgram.lean`)

`Emits f Q` says that running the assembler fragment `f` on any program prefix appends code, and
that `Q` holds for every final program containing that code at that offset. Fragments compose by
`Emits.bind`. The two back-patched loop heads (`setI`) are handled by an explicit list identity
(`set_mid`).

* `word_emits`: a word fragment appends its bits to the output.
* `repeated_emits`: `repeated bits next` appends `bits` once per `acc` unit, by an invariant on
  the outer counter.
* `inner_loop`: the inner loop adds `n` to `dst` (`2r + 1` instructions for `r` remaining marks).
* `outer_loop`: the outer loop runs the inner loop once per accumulator unit.
* `stage_sem`, `horner_emits`: one stage maps `acc` to `acc·n + c`, with output unchanged, in at
  most `acc·(2n + 3) + c + 4` instructions.
* `stages_emits`: after all stages, `acc = hv cs n`, where `hv` is the Horner value; `ic cs n`
  bounds the number of instructions and `hb cs n` the work-region growth.

`hv (coeffs p) n = p.eval n` (`hv_coeffs`).

### 4.4 Output words (`TwoPhasePolynomialOutputs.lean`)

* `windowBody_emits`: with `acc = R`, the body writes
  `1^R · 100 · (11)^R · 10` in at most `5R + 9` instructions.
* `inputBodyG_emits`: with `acc = R` and blocks of width `w`, the body writes `R` blank blocks,
  the head block for `x[0]?`, and the blocks for `x[1]?, …, x[R]?`, in at most
  `2R(w + 1) + w + 5` instructions.
* `assemble_outputs`: for any body with such a specification,
  `build (assemble cs body)` satisfies `Outputs x (W x (hv cs n)) B` with

  ```
  B = 2n + 4 + (ic cs n + cnt) · (2·(n + hb cs n + |W|) + 4) + (|W| + 1).
  ```

### 4.5 The canonical codes (`TwoPhasePolynomialFP.lean`)

* `winTail_eq_windowWord` and `TwoPhaseWindowWord.originalWindowCode_eq_windowWord` identify the
  window word with `originalWindowCode p x = latCode 1 (L + 1) (window L)`, `L = p(|x|)`.
* `inW_eq_originalInputCode` identifies the block word with
  `cfgCode (stateBits M) 1 (L + 1) (window L) (encM M L x)`. The blocks are the actual
  fixed-width codes `stateBits M (symbol, head, false)` of width `3 + 2·|S M|`. The left cells are
  blank, cell `0` carries `M.inputTape x 0` with the head in state `q0`, and cell `k + 1` carries
  the input bit `x[k + 1]` or a blank.
* `windowTime` and `inputTime` are polynomials in `ℕ[X]` that dominate the bound `B`
  (`hvP_eval`, `icP_eval`, `hb_le`).

## 5. Requirement checklist

| Requirement | Where |
|---|---|
| Input-presence marks, accumulator tracks, outer and inner counters, destination marks | `St`, `cells`, `Exec.*` |
| Every Horner iteration, coefficient sequencing, counter exhaustion | `inner_loop`, `outer_loop`, `stage_sem`, `stages_emits` |
| Preservation of unrelated cells | `Exec` is stated on the whole tape `tapeOf (cells s)` |
| `windowMTM p` writes exactly `originalWindowCode p x` | `windowMTM_outputs` |
| `inputMTM M p` writes exactly `originalInputCode M p x`, actual state encoding | `inputMTM_outputs`, `inW_eq_originalInputCode` |
| Counting actual `MTM.step` transitions, first halt, exact `MTM.Outputs` | `Steps`, `assemble_outputs` |
| Polynomial bound | `windowTime`, `inputTime` |
| `FP` for both, unconditional `UWCC` | `originalWindowCode_fp`, `originalInputCode_fp`, `originalWM` |

## 6. Scope

The manuscript lets `L(n)` be any polynomial bound on the space used by `M`, so `p` ranges over
all of `Polynomial ℕ` with the single hypothesis `c·max(n,1)^k ≤ p(n)` of `thm:tm_to_wcc`.
`radiusPoly c k = c·(X + 1)^k` is one such polynomial for every `c` and `k`.

Nothing here bears on classical P versus NP. The result is a uniformity statement about one
simulation of Turing machines by a cellular rule.

## 7. Checks before the proof

The real `step` and `assemble` definitions were executed on 371 window runs and 371 input runs:
13 coefficient lists of degree at most 3, every input of length at most 4 (length at most 3 for
the cubic lists), including radius 0 and the empty input. The input runs used stand-in blocks of
width 5 and tested the block structure. All 742 runs halted with the expected word. These runs
found no error before the proof was written; they are not part of the proof.
