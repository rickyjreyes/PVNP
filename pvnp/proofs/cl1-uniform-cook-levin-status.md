# CL-1: Cook–Levin for dense SAT — status (6 November 2026)

CL-1 is the statement that every language in `NP_TM` reduces to `SATV.SAT_dense` by a
polynomial-time reduction computed by a Turing machine, and that polynomial-time decidability is
preserved along it. It gives the converse transfer `P_TM ≠ NP_TM → CrossingSAT.SATLowerBound`, so
`SATLowerBound` becomes *equivalent* to classical `P_TM ≠ NP_TM`. It is also one of the two
premises Part II claim II-24 was missing.

**Status: complete and kernel-checked.** All modules below build with only `propext`,
`Classical.choice` and `Quot.sound` (axiom audit), with no `sorry`, `admit` or `native_decide`.

| Theorem | Statement |
|---|---|
| `CookLevin.Gen.NP_TM_subset_P_TM_of_SAT` | `SAT_dense ∈ P_TM → NP_TM ⊆ P_TM` |
| `CookLevin.Gen.SAT_mem_P_TM_iff` | `SAT_dense ∈ P_TM ↔ P_TM = NP_TM` |
| `CookLevin.Gen.satLowerBound_iff_P_ne_NP` | `CrossingSAT.SATLowerBound ↔ P_TM ≠ NP_TM` |

The last theorem *identifies* the two statements. It proves neither: `SATLowerBound` and
`P_TM ≠ NP_TM` both remain open.

## Part 1: the tableau reduction (`PVNP.CookLevinTableau`, PR #52)

* **Verifier normalization** (`Nrm.nrm`, `Nrm.nrm_answer`). A verifier `V` becomes a machine with
  fresh, injective, non-blank input symbols that halts at its first answer. If `V` decides `VL`
  within `P`, the normalized machine shows `[y ∈ VL]` at every time `T ≥ P(|y|)`.
* **Tableau formula** (`phi M x Q T`). The space-time diagram of the radius-one automaton
  `M.toWCC` on the window `[−T−1, T+1]`, rows `0…T`. Group `k = t·W + c` (`W = 2T+3`) has one
  variable per cell symbol and one acceptance-chain variable, and contributes one clause per
  template:
  * at-least-one and at-most-one symbol;
  * one window clause per symbol triple;
  * a boundary or initial-row unit clause;
  * two witness clauses;
  * the acceptance chain.

  Every clause mentions only groups `k−1, k, k+1, k+W`.
* **`phi_sat_iff`.** When `2|x| + 1 + Q ≤ T`, `phi M x Q T` is satisfiable iff `M` accepts some
  `pair x w` with `|w| ≤ Q` at time `T`.
* **`cookLevin`.** For every `L ∈ NP_TM` there are `M`, `q`, `t` with
  `x ∈ L ↔ inst x ∈ SAT_dense`, where `inst x = encDense (numVars M T) (phi M x q(|x|) T)` and
  `T = t(|x|)`.

## Part 2: the uniform generator

The map `x ↦ inst x` is computed by one fixed round-trip sweep program, `genCtrl d`, which
`Sweep.Prog.toTM` compiles into an ordinary single-tape Turing machine. The program carries
finitely many marker tracks, a column label and an output bit per cell.

| Module | Content |
|---|---|
| `PVNP.CookLevinKit` | Generic round trips: `grow`, `shift`, `first`, `clear`, `setM`, `setCl`, `setOut`, reads. Each has a cellwise effect lemma and frame lemmas. Sequential composition `seq`. |
| `PVNP.CookLevinHorner` | `HPar.horner_phase`: writes `horner cs n` unary marks on a track, using only its own tracks, within `|cs| · stepBound` trips. |
| `PVNP.CookLevinBits` | Bit locality. `slotBits_eq` and `inst_getElem` show that every bit of `inst x` is a function of the template, the group class `kcOf k`, the relative position `relOf k k'` and the slot. |
| `PVNP.CookLevinMain` | The main write loop `mainCtrl` and its invariant `TI`. `main_loop` writes all of `inst x` on the `out` track within `mainBound M T` trips. |
| `PVNP.CookLevinLabels` | `labCtrl` writes the column labels `labOf x Q T c` of the window, region by region. `label_phase` establishes `TI` within `8T + 21` trips. |
| `PVNP.CookLevinGen` | `genCtrl d = grow ; Horner(t+1) ; Horner(q) ; labels ; main loop`. `gen_run` proves that it writes `inst x` within `genBound d |x|` trips. `horner_hcoeffs` gives the coefficient lists of the polynomials. |

`genBound d n` is a polynomial expression in `n`. `CookLevinUniform.pG_eval` gives the
polynomial explicitly.

## Part 3: composition with a decider

| Module | Content |
|---|---|
| `PVNP.CookLevinDecide` | `decProg G S` pairs each generator cell with a folded tape cell of a manuscript machine `S` (`MTM`). It runs `G` (`dec_lift`), copies the `out` track onto `S`'s tape as its input with the head on cell `0` (`dec_conv`), and simulates `S` one step per trip via `simTrip_spec` (`dec_sim_loop`). `dec_halts` bounds the total cost. |
| `PVNP.CookLevinUniform` | Instantiates `S` with a polynomial-time decider of `SAT_dense` (`P_TM_subset_P_Turing`) and builds one polynomial `pFin` bounding the compiled machine's time. Proves the three theorems above. |

The decider for `L` is the single machine `Prog.toTM (decProg (genCtrl d) S)`, with the single
polynomial time bound `pFin d c e`. The construction is uniform. It is not the non-uniform
circuit projection `SATProjection.NP_projects_to_SAT`.

## Scope

* The reduction is computed in the round-trip sweep model and compiled to a single-tape machine
  with exact step counts (`Prog.toTM_firstAnswer`). The repository's transducer class `FP`
  (`MTM.ComputesIn`, output in the `Shows` format) is not used: there is no theorem that
  `x ↦ inst x ∈ FP` in that output convention. No current statement needs one.
* Closure is proved in the form the equivalence needs: composition with any polynomial-time
  decider of `SAT_dense`. A general lemma "`P_TM` is closed under `FP` reductions" is not stated.
* The 91-claim inventory is unchanged. II-24 still also needs closure of `P_TM` under finite
  modification.
