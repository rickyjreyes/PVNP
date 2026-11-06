# Part II quantifier and empty-input repairs (6 November 2026)

This note records a correction to the *current manuscript statements*, not a retroactive claim that the original October 27 statements were true.

## II-7: `lem:invariant`

- **Originally refuted:** The invariant was quantified over every time `t >= 0`. Once the simulated head moves outside the finite window, the claim of a unique head cell in the window fails.
- **Amended statement:** For the finite window `Lambda_n = {-L(n),...,L(n)}` and every `0 <= t <= L(n)`, both the even and odd phase invariants hold. In the machine simulation, choose `L(n) >= T_M(n)+n` so this covers every step through the first halt.
- **Existing Lean proofs:** `PVNP.PartIITwoPhase.invariant_even`, `invariant_odd`.
- **Preserved counterexample:** `PVNP.PartIITwoPhase.invariant_literal_fails`.

## II-8: `lem:one_step`

- **Originally refuted:** The statement claimed head-in-window and correspondence for all `t >= 0`.
- **Amended statement:** `C_(2t)` encodes the simulated TM configuration for `0 <= t <= L(n)`. For `t < L(n)`, two further WCC updates give the next configuration with the head still in the window. The exact equality of window-restricted configurations is available even through `t = L(n)+1`, but it does **not** imply the head remains in the window at that endpoint.
- **Existing Lean proofs:** `PVNP.PartIITwoPhase.one_step`, `one_step_of_inWin`, `two_steps`.
- **Preserved counterexample:** `PVNP.PartIITwoPhase.one_step_literal_fails`.

## II-17: `def:pturing`

- **Originally refuted:** The worst-case time bound `T_M(n) <= c*n^k` with `k >= 1` for all `n >= 0` forces `T_M(0) = 0`, reducing the literal language class to `{empty language, all strings}`.
- **Amended statement:** `T_M(n) <= c*max(n,1)^k` for every `n >= 0`. The same bound is used downstream in `thm:tm_to_wcc`.
- **Existing Lean proof:** `PVNP.PartIITuring.P_Turing_eq_P_TM`, via explicit simulations.
- **Preserved counterexamples:** `PVNP.PartIITuring.P_Turing_lit_eq`, `P_Turing_lit_ne_P_TM`, `P_Turing_lit_ne_NP_Turing`.

## Coverage and limitations

| Manuscript snapshot | Exact | Restricted | Refuted | Open | Total |
|---|---:|---:|---:|---:|---:|
| Original October 27 source (audited November 5) | 70 | 2 | 11 | 8 | 91 |
| Amended Part II manuscript | 73 | 2 | 8 | 8 | 91 |

The historical counterexamples remain in Lean and the pre-repair Git revision. None of the three corrections changes a Lean theorem, resolves `CrossingSAT.SATLowerBound`, or proves classical `P != NP`. The corrected Part II is **26/28 Exact**, with II-10 restricted and II-24 open.

**Verification requirement:** The amended LaTeX must pass its PDF-build workflow and the existing Lean declarations must continue to pass CI on the exact pull-request head before this revision is described as CI-verified.
