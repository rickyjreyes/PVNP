# Remaining original manuscript claims

The historical 91-row inventory and its original counterexamples are preserved. The conditional theorem II-24 is now Exact in the current inventory.

| Claim | Checked result | Remaining obligation |
|---|---|---|
| II-10 | `TwoPhaseDecoder.decM_fp` gives the original window decoder on all configurations. `PartIITwoPhase.tm_to_wcc_decides` gives two updates per TM step. | The original encoder and lattice writer as bit-output MTMs. |
| I-11 | `PhysicalAudit.unrestricted_phys_ne_P_TM` supplies an explicit diagonal language for uncharged encoders. Uniform discrete WCC equals classical P. | A fixed physical representation and a stable polynomial-cost simulation of its continuum decisions. |
| I-16 | `CrossingSATMatrix.quadratic_every_budget` gives quadratic first-answer time on a rejected word at every sufficiently large budget. `FiniteHorizon.fast_through_horizon` tests the reversed machine/length quantifiers. | For each fixed correct decider and each polynomial, arbitrarily long words exceeding that polynomial. |
| I-31 | `SeparatorPrice.mesh_price` charges measured faces with a common positive jump. `contrast_of_readout` obtains the jump from a Lipschitz readout and a threshold gap. | Establish those constants on the actual physical trajectories at every input length, or derive an alternative coercive estimate. |
| I-32 | `SeparatorPrice.binary_cut_price` bounds graph curvature above and below by the oriented cut on a bounded-degree two-level rail. Tseitin consistency admits a parity bypass. | Exhibit an encoding and prove every admissible decider incurs the requisite separator cost. |
| I-2 | `PartISeparation.conditional_symbolic_separation` checks the template. | Derive nonconstructibility and a decision-language obstruction from independently charged dynamics. |
| I-3 | `PartIPsiSat.roundPhase_satisfies` certifies an explicit assignment from energy below 1/8. Its strict threshold is sharp for this tie rule. | A formula-dependent trajectory and proof that the proposed phase/amplitude observation attains a sound readout. |
| I-37 | `ToroidalDiagonal.even_encRing_mem_SAT` and `odd_encRing_not_SAT` decide both seam signs of the finite ring. | A faithful physical lock for arbitrary inputs with completeness and soundness. |
| II-24 | `PartIIManuscript.conditional_np_safety_all` proves the original implication on every NP-complete language; the existential version uses dense SAT. | The physical resource, counting, and classical separation premises remain explicit. |
| III-22 | Section 8 presents the arrow-of-time passage as an interpretive remark. | The passage supplies no quantified proposition to check. |

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

The four modules entered main with PR #55 at `89058ccc`.
