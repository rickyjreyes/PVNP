# II-10 original two-phase W_M: verification and promotion record

Date: 2026-11-12. Supersedes the provisional pre-verification ledger.

## Claim and precise scope

The corrected Part II theorem `thm:tm_to_wcc` says that the author's
**original** two-phase finite discrete WCC machine W_M, whose radius
contains the ordinary single-tape TM's first-halt trajectory, makes its
first decision at exactly `2*T_M(x)` global update steps. The canonical
window writer, complete initial-configuration encoder, and decoder are
all polynomial-time transducers under `PartIIUniform.FP`. Consequently
the original machine provides the charged discrete inclusion
`P_Turing ⊆ P_disc`. The verified statement uses the corrected
polynomial bound `c*max(n,1)^k`, covering the empty input.

This is **not** a proof of physically realizable WCT computation,
physical class equivalence, or classical P ≠ NP.

## Source proof inventory

| File | Verified-source role |
| --- | --- |
| `lean/PVNP/TwoPhasePolynomialExec.lean` | Literal MTM transition traces and raw output at first halt |
| `lean/PVNP/TwoPhasePolynomialState.lean` | Abstract work-tape state, invariants, and instruction realization |
| `lean/PVNP/TwoPhasePolynomialProgram.lean` | Actual assembler semantics, charged Horner execution and polynomial value |
| `lean/PVNP/TwoPhasePolynomialOutputs.lean` | Exact output-body words, `assemble_spec`, `assemble_outputs` |
| `lean/PVNP/TwoPhasePolynomialFP.lean` | Canonical output equalities, time-polynomial evaluations, both original FP witnesses, original W_M, first-answer equality, and original-machine class inclusion |

The key Lean declarations in namespace `PVNP.TwoPhasePolynomialWriter` are:
`windowMTM_outputs`, `inputMTM_outputs`,
`originalWindowCode_fp`, `originalInputCode_fp`,
`originalWM`, `originalWM_decides`,
`originalWM_first_answer`, and
`P_Turing_subset_P_disc_by_original`. The root `lean/PVNP.lean`
imports the top-level FP module. The axiom audit prints these
declarations, and `.github/workflows/lean.yml` explicitly
builds all five new modules.

## External verification evidence and boundary

The producing session reported on 2026-11-12 that:

1. `lake build PVNP` succeeded with **7,386 build jobs**.
2. `lake env lean audit/AxiomAudit.lean`, followed by the repository's `audit/check_axioms.py`, passed with only the standard permitted Lean axioms.
3. `scripts/verify_ii10_original_wm.sh` completed on the **exact source commit**
   `df8824ca659b2e931eb4302251569d6c6c6140b3`, after incorporating the PR #72 integration and the exact-first-answer theorem.
4. Two concrete finite-reference sweeps covered **371 + 371 = 742 cases**, with no failures.

The build and audit successes above are **reported by the user's external
execution session**. This assistant inspected the matching source on
GitHub but did not independently execute Lean. GitHub-hosted Actions jobs
on this branch previously failed before assigning a runner, with no
executed steps; those job statuses are not proof failures, nor are they
independent attestations of the external pass.

The promotion changes in this PR affect **documentation, registry,
dashboard and manuscript sources**, not the Lean source tree. A
consistent full-run provenance should therefore pin the verified
**Lean tree** at `df8824c`, and keep the exact documentation-commit
status checks separate. For independently reproducible verification
run `bash scripts/verify_ii10_original_wm.sh` on the matching source
branch with Lean 4.23.0 and its pinned dependency cache.

## Mathematical proof sketch

1. Input normalization places input symbols into work cells, preserves
   a unique left-end sentinel and returns to the first instruction.
   This takes `2*|x|+4` transitions in the original machine.
2. The assembler emits finite literal instructions. An abstract
   well-formed work-state semantics is refined by real machine runs,
   with a polynomial step charge for every abstract transition.
3. Horner stages compute `hv (coeffs p) |x| = p.eval |x|`,
   carrying their counters in the actual tape/flags.
4. The window-body program constructs `windowWord (p.eval |x|)`.
   The input-body program constructs the exact flattened canonical
   state serializer `originalInputCode M p x` using fixed-width
   `stateBits M` blocks.
5. `assemble_outputs` proves `MTM.Outputs`, including **first halt**,
   all raw output symbols, the trailing blank, and a polynomial-time
   transition upper bound. It does not infer `FP` merely from
   polynomial output *length*.
6. These machine-level proofs yield unconditional
   `originalWindowCode_fp` and `originalInputCode_fp`.
   The existing `decM_fp` supplies the third preparation witness,
   giving the actual uniform W_M.
7. `originalWM_first_answer` imports the two-phase invariant and
   proves the original first-decision time identity at `2*T` with
   no earlier answer, provided `M.FirstHalt x T` and
   `T ≤ p.eval |x|`. With the polynomial radius bound,
   `P_Turing_subset_P_disc_by_original` completes the charged
   discrete inclusion.

## Classification after the author-reported verification

| Source | Exact | Restricted | Refuted | Open | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| Part I | 30 | 1 | 4 | 6 | 41 |
| Part II | 28 | 0 | 0 | 0 | 28 |
| Part III | 21 | 0 | 0 | 1 | 22 |
| **Total** | **79** | **1** | **4** | **7** | **91** |

The remaining Restricted entry is I-11. The universal SAT lower bound
I-16 and the continuum/PDE physical bridge remain unresolved. The
historical October 27 inventory snapshot must stay unchanged.

## Pull-request integration

- **PR #73:** original proof branch, stacked on PR #69; source tree
  containing the first-answer theorem and the merged PR #72 integration.
- **PR #72:** earlier integration draft, superseded for merging by the
  consolidated source in PR #73.
- **PR #70:** earlier first-instruction and final-scan proof
  candidates, with six Lean goals reportedly unresolved; not
  required for original II-10 closure.
- **This follow-up promotion:** documentary/editorial status promotion,
  stacked on PR #73. Merge in dependency order after review, without
  treating GitHub runner failures as kernel results.
