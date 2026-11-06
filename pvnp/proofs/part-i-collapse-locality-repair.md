# Part I I-10 and I-13 claim repair (6 November 2026)

## Provenance

This revision corrects two false or unproved propositions in the original October 27 Part I manuscript. It is **not** a proof of any general physical collapse, no-go theorem for all symbolic rules, superpolynomial decision-time lower bound, or `P != NP`. The original Lean counterexamples and the original Git revision are deliberately retained.

## I-10: common-successor mixing, not curvature-based grammar collapse

**Original claim (refuted / undefined):** crossing a curvature threshold allegedly forbade *any* finite invariant partition, forced the trajectory language to be either empty or universal, and made recovery of the local symbolic rule impossible even with unbounded computing. The literal first statement is contradicted by the invariant one-block partition (`trivial_partition_invariant`). The latter two statements do not follow without a defined word encoder, an observation channel and an identifiability criterion. The original *definition* of a collapsed state also bundled in the failure of every metastable partition, assuming part of the desired conclusion.

**Amended conditional theorem:** Fix an observable state space `X` and an allowed-transition relation `R : X -> X -> Prop`. Assume a **common successor** exists for each pair of states:

`forall x y, exists z, R x z and R y z.`

If a symbolic readout `sigma : X -> S` is pathwise invariant (`R x y -> sigma x = sigma y`), then `sigma` is constant. Therefore an `sigma` that takes at least two distinct values cannot be pathwise invariant.

**New Lean formalization:**
- `PVNP.PartISeparation.CommonSuccessor`
- `PVNP.PartISeparation.invariant_constant_of_common_successor`
- `PVNP.PartISeparation.no_nontrivial_invariant_of_common_successor`
- Retained counterexample `PVNP.PartISeparation.trivial_partition_invariant`

**Limits and outstanding implications:** common-successor mixing is a strong **additional** assumption on the *observable transition relation*. The curvature threshold does not imply it in the frozen WCT PDE. An invertible deterministic flow cannot simply be treated as a noisy transition relation. Also, a nonconstant time-dependent coding need not be *invariant* under each transition, so this theorem does not prohibit arbitrary computational symbolic dynamics or all nontrivial grammars. No theorem here establishes loss of identifiability or a particular language class. Those require separate definitions and proof obligations.

## I-13: correct finite-support growth in all dimensions

Let `U` be a radius-`r` local map on `Z^d` with quiescent background `s0`, and assume `A = supp(C0)` is finite. Then, for all `t`:

`supp(C_(t+1)) subset thickening_r(supp(C_t))`

`supp(C_t) subset thickening_(r*t)(A)`

`|supp(C_t)| <= |A| * (2*r*t+1)^d`.

**Existing Lean theorems:**
- `PVNP.PartILocality.supp_step_subset`
- `PVNP.PartILocality.supp_iterate_subset`
- `PVNP.PartILocality.support_poly_bound`

**Retained counterexamples:**
- `PVNP.PartILocality.local_growth_needs_quiescence`: locality without quiescence does not imply support containment.
- `PVNP.PartILocality.linear_growth_false_d2`: the quiescent radius-one OR rule with a single seed grows as `(2t+1)^2` in two dimensions.

The **radius** of causal propagation is linear in time; the **volume** of the active region has a dimension-dependent polynomial bound. The bound does not establish that every algorithm solving SAT needs superpolynomial time.

## Live manuscript inventory

| Snapshot | Exact | Restricted | Refuted | Open | Total |
|---|---:|---:|---:|---:|---:|
| Original October 27 source | 70 | 2 | 11 | 8 | 91 |
| After II-7 / II-8 / II-17 corrections | 73 | 2 | 8 | 8 | 91 |
| Amended I-10 / I-13 propositions | 75 | 2 | 6 | 8 | 91 |

I-10's **new conditional proposition** is counted as exact only as an implication with an explicit, unproved mixing hypothesis. The original physical and grammar-collapse conclusions are **not** counted as proved, and the original refutation remains valid against the superseded proposition.

## Validation

The amended manuscript must pass PDF CI. The new Lean declarations must pass the exact-head Lean build and axiom audit. Do not assert an exact-head CI success until the GitHub checks report it.
