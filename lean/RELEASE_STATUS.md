# Release-oriented Lean supplements

R03: finite Boolean CNF semantics and logically conditional separation.
R12: exact trajectory correspondence for a retract of a commuting state encoding.
R13: sign/density indistinguishability counterexample.

These are **additional scoped proofs** building on preexisting PVNP/PartI,
PartII and PartIII. They do not establish uniform polynomial simulations,
physical curvature lower bounds, classical P≠NP or that P vs NP is ill-posed.

Open issues: #10, #11, #12. Run `cd lean && lake build`.
Build status: unverified at authoring time. **2026-11-02:** these R03/R12/R13 modules build as part of `lake build PVNP` on the integration of `main` into the PR #14 branch. The uniform polynomial simulations and `P_WCC = P_TM`, `NP_WCC = NP_TM` are now proved in separate modules (see `formalization.yaml` → `current_status`), not in these supplements.
