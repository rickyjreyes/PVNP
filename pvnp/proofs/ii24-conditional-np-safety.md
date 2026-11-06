# II-24: conditional NP-safety — formalization (6 November 2026)

Part II, Theorem `thm:conditional_np_safety`. Module: `lean/PVNP/ConditionalNPSafety.lean`, with
the closure lemma in `lean/PVNP/FiniteModification.lean`. Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

## The statement and its hypotheses

The manuscript assumes three premises:

| Premise | In Lean |
|---|---|
| (i) WCT rails and the channel-capacity bound for a polynomial-resource device family | Real-valued `V`, `T`, `E`, `N_updates` with `V ≤ C_V n^a`, `T ≤ C_T n^b`, `E ≤ C_E n^c`, `N_updates ≤ K·V·T·E⁴`. These are the hypotheses of II-23 (`phys_step_ceiling`). |
| (ii) the computation is faithfully modelled by a uniform discrete WCC machine | A `UWCC` `W` (`def:wcc_machine`). Every input gets a first decision within `N_updates(|x|) + 1` rounds, the counting premise of `rounds_le_events`. The equivalences `P_WCC = P_Turing` and `NP_WCC = NP_Turing` are theorems (II-12, II-13), not assumptions. |
| (iii) `P_Turing ≠ NP_Turing` | A hypothesis, converted to `P_TM ≠ NP_TM` by `P_Turing_eq_P_TM` and `NP_Turing_eq_NP_TM`. |

The conclusions, with the manuscript's quantifiers:

* `conditional_np_safety`: there are an NP-complete `L` (namely `SAT_dense`) and `k ≥ 1` such
  that, for infinitely many `n` (`∀ N, ∃ n ≥ N`), some input of length `n` is not decided
  correctly by `W`. The constant `k` plays no role in the manuscript's statement or proof; `k = 1`.
* `conditional_np_safety_all`: the same for **every** NP-complete `L`, the manuscript's "in fact
  any NP-complete language".
* `no_np_complete_decider`: the equivalent form. Under (i)–(iii), `W` does not decide any
  NP-complete language on all inputs.

"`W` decides `x` for `L`" (`UDecidesAt`) means that `W`'s first decision on `x` is `[x ∈ L]`.

## NP-completeness

`NPCompleteDec L` means that `L ∈ NP_TM`, and `L ∈ P_TM` forces `NP_TM ⊆ P_TM`. This is the
property the manuscript's proof uses. `SAT_dense_npComplete` proves it for `SAT_dense` by the
uniform Cook–Levin theorem `NP_TM_subset_P_TM_of_SAT` (CL-1).

## The two closure facts

* `P^disc ⊆ P_TM` (II-11, `P_disc_subset_P_TM`). `W` decides its own language within a polynomial
  number of rounds, so that language is in `P_TM`.
* **Finite modification** (`P_TM_of_eventually_eq`). If `L'` is decided in polynomial time and
  `L` agrees with `L'` on every word of length at least `N`, then `L ∈ P_TM`. The decider is the
  sweep program `fmProg`, compiled by `Prog.toTM`:
  * its first round trip reads up to `N` input bits into a bounded buffer and places the input on
    a folded tape;
  * a short input is answered from a finite table;
  * otherwise it simulates a polynomial-time decider of `L'` one step per round trip.

`P_TM_of_wcc_eventually` combines the two: a uniform WCC machine that always decides within
polynomially many rounds, and is correct on all inputs of length at least `N`, puts `L` in
`P_TM`. The theorem follows by contradiction with (iii).

## Scope

The theorem is conditional. Premise (iii) is the open classical separation, and premises (i)
and (ii) are physical modelling assumptions. Lean proves only the implication. No physical
premise is proved and no separation is claimed.
