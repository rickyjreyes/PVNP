# II-10 original two-phase W_M: proof and release verification ledger

Date: 2026-11-12

## Exact claim and candidate theorem chain

Original Part II manuscript theorem `thm:tm_to_wcc` proves the two-phase W_M
first-decision time of 2T_M(x) for a machine whose polynomial radius contains
the simulated head trajectory. The 6 November amendment explicitly separates
this dynamic simulation from its original canonical writer uniformity.
The other single-cell uniform construction has always supplied a separate
class-inclusion proof, not a certificate for original W_M.

The recovered Phase XVIII source supplies the missing original-machine chain:

| File | Principal declaration / purpose |
| --- | --- |
| `TwoPhasePolynomialExec.lean` | Literal finite-control MTM instruction transitions, first halt and output scan |
| `TwoPhasePolynomialState.lean` | Well-formed abstract work tape and instruction-level trace realization |
| `TwoPhasePolynomialProgram.lean` | Assembler, repeated loops, Horner stages and charged execution |
| `TwoPhasePolynomialOutputs.lean` | Output bodies, assembled trace, `assemble_outputs` using original `MTM.Outputs` |
| `TwoPhasePolynomialFP.lean` | Canonical output-word equalities, polynomial bounds, original FP witnesses, original W_M construction and class inclusion |

In `PVNP.TwoPhasePolynomialWriter`, the intended top-level audit is:

- `windowMTM_outputs` and `inputMTM_outputs`: exact output word, trailing blank, first halt and polynomial transition budget of each actual machine.
- `originalWindowCode_fp` and `originalInputCode_fp`: witnesses of `FP` for the two actual canonical encoders.
- `originalWM`: explicit `UWCC` constructed from those writers without conditional FP assumptions.
- `originalWM_decides`: actual two-phase first-answer bound using the original W_M.
- `P_Turing_subset_P_disc_by_original`: class inclusion using the actual W_M rather than the separate single-cell construction.

## Independent verification gates

The exact commit being promoted must satisfy all of:

1. `lake build PVNP.TwoPhasePolynomialExec PVNP.TwoPhasePolynomialState PVNP.TwoPhasePolynomialProgram PVNP.TwoPhasePolynomialOutputs PVNP.TwoPhasePolynomialFP`.
2. `lake build PVNP`, with `import PVNP.TwoPhasePolynomialFP` in the root import tree.
3. `lake env lean audit/AxiomAudit.lean` followed by `python3 audit/check_axioms.py audit/AxiomAudit.lean <audit output>`. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Include the top-level original `FP`, `Outputs` and `W_M` declarations in the audit.
4. Python finite-reference tests and `python3 pvnp/phase_xvi/status.py --check`.
5. Manuscript-to-Lean statement audit: distinguish the original W_M from the one-cell construction; preserve the radius and first-halt hypotheses, the `2T_M` intrinsic runtime, and polynomial encoder/decoder charges.
6. Inspect the workflow run or an independent local build log **at the exact recorded source commit**. Absence of `sorry`, local single-file compilation, and an unassigned GitHub runner are not full-build certification.

Run `bash scripts/verify_ii10_original_wm.sh` from a working checkout for gates 1 through 4. This script does not modify research classifications.

## Manuscript promotion rule (executed on 12 November 2026, see the last section)

The current source-inventory classification is `Restricted` while full-build
confirmation is unavailable. Do not interpret the additional source theorems
as kernel verified solely from their presence.

**Only after all gates pass:**

- Change II-10 in the manuscript inventory from `Restricted` to `Exact` and cite the original `FP`/W_M declarations. Its exact mathematical scope is the corrected original manuscript statement, not a new lower bound for SAT.
- Change the count from **78 Exact, 2 Restricted, 4 Refuted, 7 Open** to **79 Exact, 1 Restricted, 4 Refuted, 7 Open**, with total still 91. Part II becomes 28 Exact, 0 Restricted.
- Update `pvnp/phase_xvi/targets.json` and `pvnp/phase_xvi/status.py` in the *same promotion change*. Keep registry and inventory status synchronized.
- Amend the Part II manuscript's conditional uniformity paragraph with the exact original-writer witnesses and remove the now-discharged conditional status. Retain separate runtime and complexity-class claims.
- Record the exact passing Lean toolchain version, commit SHA, audit report and test outcomes in the release verification report.
- Integrate this proof branch independently of the failing six-goal PR #70. Do not merge PR #70 as a prerequisite for these recovered modules.

## Gate result and promotion (12 November 2026)

The gate was run where the pinned toolchain is installed, on the commit that
merges the proof branch with the integration branch of PR #72.

| Item | Result |
| --- | --- |
| Commit | `df8824ca659b2e931eb4302251569d6c6c6140b3` |
| Toolchain | `leanprover/lean4:v4.23.0` |
| Unfinished-proof scan of the five modules | none found |
| Targeted build of the five modules | success, 7,260 jobs |
| `lake build PVNP` | success, 7,386 jobs |
| Axiom audit | 627 declarations, only `propext`, `Classical.choice`, `Quot.sound` |
| `test_two_phase_tape_writer.py` | 3 tests, OK |
| `test_phase_xvi_*.py` | 9 tests, OK |
| `test_phase_xvii_*.py` | 12 tests, OK |
| `status.py --check` | PASS (78/2/4/7 before promotion) |
| Script exit | `PASS: original II-10 source, exact-head Lean kernel, axioms and regressions` |

Gate 5 (statement audit). `originalWM M p` is `TwoPhaseUniform.originalUniform M p`
with its two `FP` arguments supplied, so it has the manuscript's alphabet
`S M`, rule `U M`, window `[-p(n), p(n)]`, encoder `encM` and decoder `decM`
(`original_window`, `original_step`, `original_initial`, `original_decoder`).
The radius hypothesis is `c·max(n,1)^k ≤ p(n)` and the first-halt hypothesis is
`M.HaltsWithin x (c·max(|x|,1)^k)`, as in `thm:tm_to_wcc`. The runtime is the
equality `T_{W_M}(x) = 2·T_M(x)` (`originalWM_first_answer`). The writers'
transition bounds are the polynomials `windowTime (coeffs p)` and
`inputTime M (coeffs p)`, and the decoder bound is `decM_fp`. The one-cell
construction `PartIIUniform.oneCell` is not used anywhere in this chain.

Gate 6. The log above is a local build at the recorded commit. GitHub-hosted
runners have not executed any step for this branch (issue #59), so there is no
hosted run to cite.

Promotion carried out in the commit that follows `df8824c` on
`research/phase-xviii-nine-claims-20261112` (PR #73):

- inventory row II-10 is `Exact`; counts are 79 Exact, 1 Restricted, 4 Refuted,
  7 Open; Part II is 28 Exact;
- `pvnp/phase_xvi/targets.json` and `status.py` carry the same counts;
- the dashboard registry lists II-10 as proved from `Restricted` by PR #73;
- Part II and the consolidated volume carry addenda dated 12 November 2026;
  the theorem keeps its conditional wording of 7 November;
- the Lean sources are identical in `df8824c` and the promotion commit, and the
  gate was run again on the promotion commit with the new counts.

PR #70 was not merged. Its head `a796133` was compiled separately and fails
with six `unsolved goals` errors (lines 421, 434, 436, 438, 481 and 791 of its
`TwoPhasePolynomialWriter.lean`).
