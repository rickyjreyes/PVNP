# Phase XVIII report: the nine outstanding claims

**Date:** 12 November 2026
**Pull requests:** [#73](https://github.com/rickyjreyes/PVNP/pull/73) (II-10, merged),
[#78](https://github.com/rickyjreyes/PVNP/pull/78) (I-31, merged),
[#79](https://github.com/rickyjreyes/PVNP/pull/79) (barriers, merged after #78)

## Strongest result: II-10 is proved at its original scope

For every polynomial radius `p`, every machine `M` and every input, the actual machines
`windowMTM p` and `inputMTM M p` write `originalWindowCode p x` and `originalInputCode M p x` at
their first halt within explicit polynomial transition bounds. Hence both `FP` hypotheses of the
original two-phase machine are theorems, the author's own `W_M` is a uniform discrete WCC machine
with no hypothesis, its first answer appears at exactly `2·T_M(x)`, and it is the `P^disc`
witness for every language of `P_Turing`. Merged in #73; proof note
`phase-xviii-ii10-original-writers.md`.

## The nine claims

| Claim | Original statement | Outcome | Strongest new result | Lean | Original claim closed? | Remaining obstruction |
|---|---|---|---|---|---|---|
| II-10 | `thm:tm_to_wcc`: `W_M` decides `L` in `2T_M`; uniform | **PROVED** (Exact) | `originalWindowCode_fp`, `originalInputCode_fp`, `originalWM`, `originalWM_first_answer` | 5 modules, #73 | Yes | none |
| I-31 | `lem:separator-price`: `Φ ≥ κ₀ 𝓗^{d−1}(∂𝓡)`, `κ₀` uniform | **REFUTED** for the frozen trajectory class (#78 merged; fixed-domain variant remains open) | exact plane waves of fixed contrast: `Φ` bounded, interface ≥ `L`; `no_uniform_separator_price`; corrected `layer_price` | `SeparatorFrozen`, 21 declarations | Yes, negatively | a fixed-domain variant is not decided |
| I-37 | §12.3: no toroidal lock ⟺ UNSAT | **OPEN** (not well posed) | frozen flow is time-reversible; no convergence to a stable conjugation-invariant lock from outside (`no_locking`) | `TorusNoLocking` | No | locking constraints undefined; a realization needs dissipative/forced dynamics |
| I-11 | `rem:infinite-compute`: within the rail `P_WCC = P_Turing` | **RESTRICTED** (unchanged) | — (discrete equality and diagonal countermodel already on `main`) | existing | No | certified polynomial simulation of the nonlinear PDE; TM realization with charged errors |
| I-32 | `prop:locked-expander-full`: separator `≥ c₀2^{γn}` for every decider | **OPEN**, equivalent to `P_TM ≠ NP_TM` in the charged constant class | `expanderGrowth_SAT_iff`, `expanderGrowth_implies_P_ne_NP` | `ExpanderInterfaceBarrier` | No | proving it proves `P ≠ NP` |
| I-3 | SAT ⟺ ∃ assignment with `∇φ → 0`, `|ψ|² → max` | **OPEN** | the frozen dynamics cannot supply the convergence (`no_locking_phaseOrbit`) | `TorusNoLocking` | No | formula-dependent dissipative dynamics and readout |
| I-2 | ∃ verifiable non-constructible target state | **OPEN** | explicit-state reading is false (`explicit_no_separation`) | `DepthBarrier` | No | a state notion the manuscript does not fix |
| I-16 | `conj:wcc_depth` for 3-SAT | **OPEN**, exactly `P_TM ≠ NP_TM` | `wccDepth_SAT_iff`, `wccdDepth_SAT_iff`, `uniform_depth_SAT_iff` | `DepthBarrier` | No | classical P versus NP |
| III-22 | §8: no equivalence with retrocausality | **OPEN** (interpretive) | backward evolution = conjugated forward evolution (`flow_neg`) | `TorusNoLocking` | No (no mathematical claim) | editorial |

## Inventory reconciliation (91 claims)

| Stage | Exact | Restricted | Refuted | Open |
|---|---|---|---|---|
| Phase XVII baseline | 78 | 2 | 4 | 7 |
| After #73 (II-10 Exact), on `main` | 79 | 1 | 4 | 7 |
| After #78 (I-31 Refuted) | 79 | 1 | 5 | 6 |
| After #79 | 79 | 1 | 5 | 6 |

Research percentages in `pvnp/phase_xvi/targets.json` changed only for II-10 (100, Exact) and
I-31 (100, Refuted). The barrier results of #79 change no percentage: they locate the remaining
obligations exactly but do not eliminate them.

## Verification

All local, Lean 4.23.0 with the pinned Mathlib:

| Head | `lake build PVNP` | Axiom audit | Other gates |
|---|---|---|---|
| `417c2d4` (#73) | 7,386 jobs | 627 declarations | `verify_ii10_original_wm.sh` PASS, 24 Python regressions |
| `7757f14` (#78) | 7,387 jobs | 648 declarations | dashboard, alignment, release-docs, status checks; PDFs build and verify |
| `0d3f56e` (#79) | 7,390 jobs | 678 declarations | same |

Every audited declaration depends only on `propext`, `Classical.choice` and `Quot.sound`; no
`sorry` or `admit`. GitHub-hosted jobs on this repository end before running any step (issue
#59), so there is no hosted run for these heads.

## What this phase does not do

It proves no classical separation. Two of the open claims are now kernel-checked to be as hard
as `P_TM ≠ NP_TM` (I-16 is equivalent to it; I-32 is equivalent to it in the charged constant
class and implies it in every larger class). Two (I-37, I-3) cannot be realized by the frozen
conservative dynamics. I-2 is false in its explicit-state reading and undetermined in the readings
the manuscript leaves open. III-22 is interpretation.
