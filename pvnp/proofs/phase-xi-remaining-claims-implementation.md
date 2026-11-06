# PVNP remaining original claims: implementation and proof-status ledger

**Scope:** All ten referenced manuscript claims after the verified merge of PR #54.
This note makes no modifications to the official 91-claim status counts; those are
controlled by the manuscript inventory and the dashboard's registered amendments.

| Claim | Existing verified result or new work | What remains before the original claim is settled |
|---|---|---|
| II-10 | `PartIITwoPhase.tm_to_wcc_decides` proves step/time agreement; `PartIIUniform.P_Turing_subset_P_disc` gives an alternative uniform machine | Construct and prove polynomial-time transducers for the original `W_M` encoder, decoder, and `Λ_n` under the manuscript's exact encoding |
| I-11 | `P_disc_eq_P_TM` exact in uniform discrete model; **new** `PhysicalDiagonal.unrestricted_phys_ne_P_TM` proves failure of unrestricted constant-field physical equality | Identify charged physical model, stable output margins, certified PDE numerical simulation and resource accounting; no assertion of equality without the bridge |
| I-16 | Cook–Levin formalized; `SATLowerBound ↔ P_TM ≠ NP_TM`; recovered `PhaseXIQuadratic.sat_no_uniform_subquadratic` | An unconditional superpolynomial SAT lower bound for all deterministic deciders; quadratic is insufficient |
| I-31 | `PartISeparation.conditional_product_lower_bound` proves a product consequence from assumed interface/cost bounds | Derive a uniform separator-price lower bound for the actual, charged physical trajectory class |
| I-32 | `TseitinSAT.tseitin_mem_SAT_dense_iff_comp` demonstrates the polynomial parity bypass | Prove an algorithm-independent lower bound on a genuine hard family that survives algebraic simplification and alternate representations |
| I-2 | `PartISeparation.conditional_symbolic_separation` holds under an unproved nonconstructibility premise | Construct a specified WCT wavefield with polynomial-resource verification and prove it cannot be built under the same charged rails |
| I-3 | `PartIPsiSat.psi_sat_completeness` proves **SAT iff input-dependent `Elogic=0`**; new `PhaseLockScope.bare_phase_lock_not_sat` disproves formula-independent phase-zero characterization | Freeze physical gradient/amplitude limits and clause-aware encoding before asserting the analytic iff |
| I-37 | Recovered `ToroidalDiagonal.odd_encRing_not_SAT`, `even_encRing_mem_SAT` for a finite ring | Define the physical toroidal locking witness, prove nontrivial geometric realizability for every satisfying assignment, and soundness of the converse |
| III-22 | A qualitative remark that no equivalence with retrocausality is asserted | No formally stated iff or mathematical theorem to prove; should be classified as a remark, not silently given an Exact status |
| II-24 | **Already merged, PR #54:** `PartIIManuscript.conditional_np_safety` and `conditional_np_safety_all` | The theorem is Exact as an implication **conditional** on the stated rails and `P_Turing ≠ NP_Turing`; those premises remain unproved |

## Explicit classification rules

- A Lean-verified *conditional implication* is not a proof of its antecedent.
- A formal counterexample to the **unrestricted-encoder** physical model cannot
  refute a theorem scoped to charged polynomial-time encoders.
- Unsatisfiable instances with easy polynomial decision rules do not establish
  SAT hardness. A finite toroidal seam contradiction and a Tseitin parity test
  are examples.
- The exact target remains `CrossingSAT.SATLowerBound`; the repository has
  proved an equivalence to `P_TM ≠ NP_TM`, not either statement separately.
- The remaining original claims cannot honestly be marked completed solely
  because an auxiliary lemma or a scope countertest compiles.

## Integration

PR #55 imports and independently audits these four additions:

1. `PVNP.PhysicalDiagonal` (new explicit physical diagonal countermodel).
2. `PVNP.PhaseXIQuadratic` (preserved from the earlier Phase XI branch).
3. `PVNP.ToroidalDiagonal` (preserved from the finite-ring experiment).
4. `PVNP.PhaseLockScope` (new clause-independent phase-locking scope test).

Exact-head GitHub CI, axiom audit and merge are required before describing
these declarations as fully integrated into `main`.
