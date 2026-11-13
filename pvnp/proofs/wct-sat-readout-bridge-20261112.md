# WCT physical SAT readout: a conditional robust bridge

**Base:** Draft PR #88, `research/wct-physical-readout-capacity-20261112`
**Extension:** `lean/PVNP/PhysicalSATReadout.lean`
**Status:** Mathematical and Lean proof candidates; **not kernel-certified** until the pinned 4.23.0 build succeeds.
**Inventory:** 79 Exact / 1 Restricted / 5 Refuted / 6 Open remains unchanged.

## What the new theorem proves

Let a single physical procedure assign each explicit 3-CNF `F` an exact solution `run F` of the *frozen* WCT torus PDE. The machine uses one fixed real localized-mass detector `Jdet`, a common observation time `T > 0`, and a common threshold `τ`.

For a satisfiable formula `F_yes` and an unsatisfiable formula `F_no`, suppose:

1. **Correctness of the entire physical procedure:** for *every* formula, the observed SAT output is at least `τ+m`, and every observed UNSAT output is at most `τ-m`. The margin `m > 0` is explicit.
2. **Finite measurement error:** each reported output differs from the exact WCT detector by at most `ρ ≥ 0`.
3. **Approximately blind initial detector:** `|J_yes(0)-J_no(0)| ≤ ε`, with `ε ≥ 0`.
4. **Nontrivial transport:** `ε ≤ 2(m-ρ)`.
5. **Charged dynamics:** each PDE solution satisfies the original regularity hypotheses, `Γ_yes, Γ_no > 0`, and integrated squared-Laplacian expenditures at most `B_yes, B_no`.

The terminal **true detector** contrast is at least `2(m-ρ)`, not necessarily `2m`. The triangle inequality yields a minimum change of

```text
d = (2(m-ρ)-ε)/2 = m-ρ-ε/2.
```

for at least one branch. Calling the PDE-derived inequality from PR #88 then gives:

```text
d^4 ≤ Γ_yes^4 T^3 B_yes  OR  d^4 ≤ Γ_no^4 T^3 B_no.
```

With `0 ≤ Γ_yes,Γ_no ≤ G`, and `B_yes,B_no ≥ 0`, the auxiliary
`combined_budget_of_disjunction` proves:

```text
d^4 ≤ G^4 T^3 (B_yes+B_no).
```

These are mathematically necessary resource floors **only in the specified physical readout class**, not universal SAT lower bounds.

## Lean declarations

* `margin_implies_contrast`: terminal margin gives exact readout separation.
* `noisy_margin_implies_contrast`: subtract absolute readout errors.
* `two_outcomes_with_initial_skew`: only the signal contrast not already present at the initial detector must be transported.
* `skewed_binary_readout_resource_disjunction`: apply the existing exact frozen-torus PDE flux theorem.
* `sat_pair_readout_resource_disjunction`: quantify over one SAT-correct solution family with physical detector margin.
* `noisy_sat_pair_readout_resource_disjunction`: robust SAT-correctness version with explicit measurement noise.
* `combined_budget_of_disjunction`: use common `G` to give a lower bound on summed curvature expenditure.

The module is imported from `lean/PVNP.lean` and all seven declarations are named in `lean/audit/AxiomAudit.lean`.

## What remains entirely open

* **`Elogic` vs actual WCT readout.** `PartIPsiSat.psi_sat_completeness` proves `SAT(F) ↔ ∃ψ, Elogic(ψ,F)=0` as a logical encoding. No theorem constructs the physical torus input state `run F 0` uniformly from that logical `ψ`, or shows the frozen PDE implements the SAT energy and reaches a satisfying phase state.
* **Input preparation and readout.** This theorem assumes the physical procedure is already SAT-correct. The encoder, construction cost, bandwidth, precision, and detector robustness remain unproved; no uncharged decision oracle may be hidden in initialization.
* **Initial blindness is restrictive.** It is not forced by SAT semantics; an encoder can present different initial detector values for different formulas. If `ε ≥ 2(m-ρ)`, the lower bound becomes trivial.
* **No WCT stable-lock convergence.** `TorusNoLocking` already shows why the frozen reversible dynamics cannot robustly converge from outside a stable lock set. The present readout model need not converge to a stable lock, and therefore does not bypass that obstruction.
* **No superpolynomial conclusion.** With constant `m>ρ+ε/2`, polynomially bounded `G,T` and polynomial total budget, the inequality is consistent: it provides at most an inverse-polynomial lower bound on budget. To prove superpolynomial SAT cost one needs a separate, algorithm-independent obstruction forcing `G,T,B` or some charged preparation/readout resource to scale superpolynomially. In particular, the number of interwoven `ψ_i` fields does not itself supply that result.
* **Same-length hard pairs.** The theorem applies to arbitrary SAT/UNSAT formulas; it does not assert a hard pair at each input length or a superpolynomial lower bound across lengths.

## Verification

The following are **required before changing this PR to ready-for-review**. They have not been run successfully for this exact new branch:

```bash
cd lean
lake build PVNP.PhysicalReadoutCapacity PVNP.PhysicalSATReadout
lake build PVNP
lake env lean audit/AxiomAudit.lean > audit-output.txt
python3 audit/check_axioms.py audit/AxiomAudit.lean audit-output.txt
cd ..
python3 -m unittest pvnp.tests.test_physical_sat_readout_algebra
```

The optional Python tests independently check real-number algebra on deterministic and adversarial examples; passing them is not kernel certification and not a PDE simulation.
