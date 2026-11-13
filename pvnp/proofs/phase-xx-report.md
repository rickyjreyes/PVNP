# Phase XX report: interwoven-Ψ SAT on the frozen WCT torus

**Date:** 13 November 2026
**Pull requests:** [#89](https://github.com/rickyjreyes/PVNP/pull/89) (SAT readout bridge, merged),
[#90](https://github.com/rickyjreyes/PVNP/pull/90) (interwoven-Ψ model, torus SAT device, resource
barrier), [#91](https://github.com/rickyjreyes/PVNP/pull/91) (claim classification)
**Research note:** `wct-interwoven-sat-program-20261113.md`

## Three separate measures

| Measure | Value | What it does not mean |
|---|---|---|
| **Lean verification coverage** | 79 of 91 register entries are Exact (86.8%); 79 of the 90 mathematical claims (87.8%). 742 audited declarations, each using only `propext`, `Classical.choice`, `Quot.sound`. | Exact includes 21 conditional implications whose premises are open or modelled. |
| **Scientific completion of the manuscript claims** | 84 entries are settled by a proof or a counterexample (79 Exact + 5 Refuted). 2 are proved only for a narrower model (I-11, I-37), 4 are Open (I-2, I-3, I-16, I-32), 1 is Interpretive (III-22). | Restricted claims are not settled at the manuscript's scope; Open claims are not partially proved. |
| **Progress toward classical P versus NP** | None. I-16 and the Phase XX resource statement are each equivalent to `P_TM ≠ NP_TM` in their classes; I-32 and every superpolynomial physical bound over a class containing the charged zero-mode devices imply it. | No percentage is assigned. |

**The manuscript claims are not 100% complete:** four substantive claims remain Open.

## What Phase XX proved

| Question | Answer | Lean |
|---|---|---|
| PR #89 at its exact head | Seven declarations verified; four unused hypotheses removed; merged | `PhysicalSATReadout` |
| SAT ⟺ ground state, with coupling and curvature added | False for sign-sensitive terms (a satisfiable and an unsatisfiable formula both have ground energy 1/4; satisfying assignments are not ground states). True for sign-blind terms: `SAT ⟺ E_min = 0`, `UNSAT ⟺ E_min ≥ 1/8`. Exact criterion for every added energy `C ≥ 0`. | `InterwovenSAT` |
| "∃Ψ, E_F[Ψ] = E_min(F)" | False as a criterion: every formula attains its minimum | `min_formulation_vacuous` |
| Readout bound on the frozen torus | `(m − ρ − ε/2)⁴ ≤ G⁴T³(B_SAT + B_UNSAT)` without `Γ > 0`; `G` fixed by prepared mass and energy | `WCTSATDevice.device_pair_budget` |
| Can the encoder bypass transport? | Yes: exact zero-mode solutions read the answer at time zero with zero curvature budget | `preloaded_device` |
| Is initial blindness necessary? | Yes | `blindness_necessary` |
| Superpolynomial resources for every admissible solver | Equivalent to `P_TM ≠ NP_TM` in the charged zero-mode class; implies it in every class containing those devices | `WCTSATScaling` |
| Transfer to Turing machines | Physical ⟹ classical needs no simulation in such classes; classical ⟹ physical needs the missing I-11 bridge | `superpoly_SAT_implies_P_ne_NP` |

## Classification changes (PR #91)

| Claim | Before | After | Reason |
|---|---|---|---|
| I-37 | Open (not well posed) | **Restricted** | With the locking constraints defined on the configuration torus (clause penalties plus sign-blind coupling and curvature), "no locking configuration ⟺ unsatisfiable" is proved for every formula (`toroidal_locking_iff_unsat`); sign-sensitive constraints fail (`naive_toroidal_locking_fails`). Gap: the manuscript's spatial ψ–electron field and any dynamics that reaches the locks. |
| III-22 | Open | **Interpretive** | The remark states that no equivalence is proved and asserts no theorem. Supporting material (`Torus.flow_neg`) is unchanged. |

The register now reads **79 Exact, 2 Restricted, 5 Refuted, 4 Open, 1 Interpretive** (91 entries).
The new status Interpretive is supported by the inventory parser, the dashboard, the nine-claim
registry and both release gates; the historical 70/2/11/8 snapshot is parsed unchanged.

## Unresolved statements, reduced to the smallest missing obligation

| Claim | Status | Smallest missing obligation |
|---|---|---|
| I-16 `conj:wcc_depth` | Open | `P_TM ≠ NP_TM` (proved equivalent for dense SAT in every discrete model) |
| I-32 `prop:locked-expander-full` | Open | `P_TM ≠ NP_TM` (equivalent in the charged constant class; implied in every larger class) |
| I-3 phase-locking criterion | Open | A formula-dependent, non-conservative dynamics that drives the sign-blind energy below `1/8` from a state prepared by an encoder that does not itself decide SAT, with charged time. The static criterion and the readout are proved. |
| I-2 symbolic separation | Open | A state notion (input-indexed or physical families with a preparation model) under which the conjecture has complexity content; the explicit-state reading is false |
| I-11 physical ⇄ discrete | Restricted | A resource-preserving Turing simulation of the nonlinear PDE devices with charged encoders and robust measurement |
| I-37 toroidal locking | Restricted | A spatial-torus physical realization of the flux constraints with dynamics that reach the locks; the frozen dynamics cannot |
| Phase XX resource statement | Open (not a manuscript claim) | `P_TM ≠ NP_TM` in the zero-mode class |
| Blind constant-budget device | Not formalized | One exact frozen solution whose reading changes; the two-mode flux formula is checked numerically only |

Any proof of the first two rows, or of the resource statement, proves `P_TM ≠ NP_TM` and must
therefore overcome the relativization, natural-proofs and algebrization barriers. None of the
theorems here attempts that.

## Verification

| Head | `lake build PVNP` | Axiom audit | Other gates |
|---|---|---|---|
| `e87bf00` (#89) | 7,392 jobs (local, at `bf15f9b`) | 689 declarations | hosted `lean`, `dashboard`, `build`, `phase-iii-targeted` green |
| `9ed6535` (#90) | 7,395 jobs | 742 declarations | 76 Python tests; dashboard, alignment, release-docs, status checks |
| #91 head | no Lean change | unchanged | dashboard check (13 groups), alignment, release-docs, status checks, Python tests |

Every audited declaration depends only on `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, `admit` or `native_decide`.
