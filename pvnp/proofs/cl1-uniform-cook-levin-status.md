# CL-1: Cook–Levin for dense SAT — status (6 November 2026)

CL-1 is the statement that every language in `NP_TM` reduces to `SATV.SAT_dense` by a
polynomial-time many-one reduction computed by a Turing machine. With closure of `P_TM` under such
reductions it gives the converse transfer `P_TM ≠ NP_TM → CrossingSAT.SATLowerBound`, so that
`SATLowerBound` would be *equivalent* to classical `P_TM ≠ NP_TM`. It is also the missing premise
of Part II claim II-24.

## Part 1 (kernel-checked): the tableau reduction

Module: `lean/PVNP/CookLevinTableau.lean`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

* **Verifier normalization** (`Nrm.nrm`, `Nrm.nrm_answer`). A verifier `V` becomes a machine with
  fresh, injective, non-blank input symbols that halts at its first answer. If `V` decides `VL`
  within `P`, the normalized machine shows the answer `[y ∈ VL]` at every time `T ≥ P(|y|)`.
* **Tableau formula** (`phi M x Q T`). The space-time diagram of the radius-one automaton
  `M.toWCC` on the window `[−T−1, T+1]`, rows `0…T`. Group `k = t·W + c` (`W = 2T+3`) has one
  variable per cell symbol and one acceptance-chain variable. Each group contributes one clause per
  template:
  * at-least-one and at-most-one symbol;
  * one window clause per symbol triple;
  * a boundary or initial-row unit clause;
  * two witness clauses;
  * the acceptance chain.

  A template that does not apply contributes a tautology. Every clause mentions only groups
  `k−1, k, k+1, k+W`.
* **`phi_sat_iff`**. If `2|x| + 1 + Q ≤ T` and the input symbols are injective and non-blank,
  `phi M x Q T` is satisfiable iff `M` accepts some `pair x w` with `|w| ≤ Q` at time `T`. The
  proof decodes the witness from the initial row and shows, by induction on time, that every row
  of a satisfying assignment is the true diagram (`rows`, using `TM.toWCC_step_encode`). The
  converse assignment is read off the true diagram (`complete`).
* **`cookLevin`**. For every `L ∈ NP_TM` there are a machine `M` and polynomials `q`, `t` such
  that `x ∈ L ↔ inst x ∈ SAT_dense`, with
  `inst x = encDense (numVars M T) (phi M x q(|x|) T)` and `T = t(|x|)`.
  The instance has `3·numVars·|phi|` bits, which is polynomial in `|x|`.

## What part 1 does not prove

`cookLevin` defines the instance mathematically. It does **not** show that `x ↦ inst x` is
computed by a Turing machine in polynomial time. A non-uniform family of instances already
existed (`SATProjection.NP_projects_to_SAT`), so uniformity is the whole remaining content of
CL-1.

## Remaining parts

* **Part 2.** A machine that computes `inst x` in time polynomial in `|x|`. It will be built as a
  sweep program compiled by `Sweep.Prog.toTM`, using unary polynomial evaluation, a ruler of
  groups, and a block writer driven by the local template structure of `phi`.
* **Part 3.** Composition with a polynomial-time decider for `SAT_dense`, giving
  `SAT_dense ∈ P_TM → NP_TM ⊆ P_TM`. Hence `SATLowerBound ↔ P_TM ≠ NP_TM`, and the conditional
  NP-safety theorem II-24.

None of these parts bears on whether `SATLowerBound` itself holds. That remains open.
