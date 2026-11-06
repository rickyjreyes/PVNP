# Phase X: direct attack on the universal SAT lower bound, and the circuit route

**Date:** 6 November 2026. **Base:** `main` at `6eb4634` (PR #42; Lean CI run 42151483811 passed).
**Lean modules:** `Circuits.lean`, `TMCircuit.lean`, `CircuitCookLevin.lean`.

**Historical scope.** This note records the alternative ranked-DAG formalization developed from PR #42. PR #43 independently established the circuit transfer on main. PR #53 subsequently verified uniform Cook–Levin, and PR #55 integrated the quadratic SAT corollary. Open-work descriptions below refer to the original Phase X snapshot.

**Result.**
- **Not proved.** `SATLowerBound` (`SAT_dense ∉ P_TM`) is not proved, and `P_TM ≠ NP_TM` is not
  derived. Classical P versus NP remains open.
- **Proved** (kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound`):
  - **`P_TM ⊆ Ppoly`**, with the explicit circuit size `(p(n)+1)(2p(n)+3)·c_M`.
  - **Non-uniform Cook–Levin for `SAT_dense`:** `SAT_dense ∈ Ppoly ↔ NP_TM ⊆ Ppoly`.
  - **Consequence:** if *any* language in `NP_TM` requires superpolynomial circuits, then
    `SATLowerBound` holds, and hence `P_TM ≠ NP_TM`.
- **Obligations closed.** This proves the universality half of the circuit route, which Phase IX
  §2.5 had left unformalized. It also closes the non-uniform half of obligation CL-1.

## 1. Direct attack: the attempts made in this phase

The attempts below are new. The invariant tests of Phase IX are not repeated.

1. **Diagonalization inside NP.**
   - *Aim.* For each polynomial-time machine `M`, build a formula `φ_M` with
     `φ_M ∈ SAT_dense ⟺ M rejects φ_M`.
   - *Exact failure.* `φ_M` must constrain a run of `M` on `φ_M` itself. The dense CNF of that
     tableau has at least `T_M(|φ_M|)` clauses, so `|φ_M| ≥ T_M(|φ_M|)`. That is impossible for
     every machine running in superlinear time.
   - *What diagonalization does give.* It separates `DTIME(t)` from slightly larger time classes
     (the time hierarchy), and the diagonal language lies outside the class it defeats. It cannot
     be placed in NP this way. It also relativizes, so Baker–Gill–Solovay excludes it as a proof of
     `P ≠ NP`.
2. **Padding ("hardness magnification") on one tape, and for circuits.** Let
   `SAT_pad = {x·1^{f(|x|)} : x ∈ SAT_dense}` with `f` superpolynomial.
   - *Cost decomposition.* Its single-tape time is `Θ(N log N)` for checking the padding plus
     `T_SAT(|x|)`. Its circuit size is `N + C_SAT(|x|)`, up to constants.
   - *Why it is circular.* "`SAT_pad` needs `ω(N log N)` time" or "`SAT_pad` needs `> 2N` gates"
     is therefore the original superpolynomial statement in disguise. The reduction is circular
     and is not pursued.
3. **Separator price and curvature on the decider's own trajectory.**
   - *Invariants of the trajectory.* An interface measure bounded by the trajectory's spacetime
     volume is polynomial for every polynomial-time decider. So "every decider incurs a
     superpolynomial interface" is equivalent to `SATLowerBound` (for curvature:
     `curvature_lower_bound_is_classical`).
   - *Invariants of the witness field.* Deciders that never build a witness avoid them (Phase IX,
     `tseitin_mem_SAT_dense_iff_comp`).
   - *Conclusion.* There is no invariant here that is weaker than the target.
4. **Circuit size, the route that survives every adversarial test.**
   - *Universality is proved.* Every correct decider, of any design, yields circuits of size
     `O(T²)` (§2, Theorem A). This covers Gaussian elimination, preprocessing, nonlocal or global
     strategies, algorithms that never search for a witness, and every polynomially equivalent
     machine model.
   - *Lower-bound strength is open.* That half is exactly a superpolynomial circuit lower bound
     for an NP language.

## 2. The new theorems

### Theorem A: polynomial-time machines have polynomial-size circuits

> For every ordinary single-tape machine `M`, every time bound `T`, input length `N` and input
> sources `src`, the explicit circuit `tableau M T N src` satisfies
> `eval = true ⟺ FirstAnswer (M.out (inputOf N src x)) T true` (`tableau_eval`), and has size at
> most `(T+1)(2T+3)·c_M` (`size_tableau`). Here
> `c_M = 6·|S|·(|S|³ + 1) + 12` and `S = Γ × (Λ ∪ {no head})`. Consequently
> **`P_TM ⊆ Ppoly`** (`P_TM_subset_Ppoly`).

**Proof.**
- **One step of the machine is a radius-one rule** on cell contents (symbol, head-state marker),
  derived from `TM.step`, including halted configurations (`content_next`).
- **The window is exact.** The head stays in `[-s, s]` up to time `s` (`abs_head_run`), so the
  window `[-T, T]` with blank edges is exact (`rule_congr_left`, `rule_congr_right`).
- **Row invariant.** The circuit holds one-hot wires for every cell of the window at every time.
  Each next-row wire is an OR over the `|S|³` neighbour patterns. By induction, row `s` holds the
  true contents (`val_cell`).
- **First-answer semantics.** These are computed by a "no answer before `s`" chain and an OR over
  `s ≤ T` (`val_nb`, `val_res`, `tableau_eval`).
- **The circuit model is standard.** Every gate has fan-in at most two (`const`, `inp`, `not`,
  `and`, `or`). A rank function makes the circuit acyclic. Every register outside the listed
  `regs` is the constant `false`, and size is `|regs|` (`Circuits.Circuit`). `Ppoly` uses one
  polynomial for all input lengths.

### Theorem B: the Cook–Levin embedding of `NP_TM`, non-uniform

> Let `L ∈ NP_TM`, with verifier machine `M_V` (time `p`) and witness bound `q`. For every `n`
> there is an explicit circuit `verCirc` of size at most
> `(q(n)+1)·(T+1)(2T+3)·c_{M_V} + q(n) + 2`, where `T = p(2n+1+q(n))` (`verCirc_size_le`), such
> that for `|x| = n`: `x ∈ L ⟺ ∃ W, verCirc(x, W) = 1` (`mem_iff_verCirc`).

Part I §11.1 states exactly this ("for any language `L ∈ NP` there exists a polynomial-size
Boolean circuit `C(x,w)` with `x ∈ L ⟺ ∃ w : C(x,w) = 1`"). It adds that "we do not yet supply a
complete Cook–Levin–style formal reduction". Theorem B supplies one in non-uniform form.

**Construction.**
- The circuit is the OR, over witness lengths `ℓ ≤ q(n)`, of the verifier tableaux on `pair x w`
  (`orComb`, `verCirc_eval`).
- `x` is read from inputs `0…n−1`, and the witness from inputs `n, n+1, …`
  (`vsrc`, `inputOf_vsrc`).

### Theorem C: `SAT_dense` is NP-complete under projections, non-uniformly

> **`SAT_dense ∈ Ppoly ↔ NP_TM ⊆ Ppoly`** (`SAT_dense_mem_Ppoly_iff`,
> `NP_TM_subset_Ppoly_of_SAT`).

**Proof.**
1. **Tseitin transformation** (`tseitin`, `gateCl_sat`, `tseitin_sat_iff`).
   - There is one CNF variable per listed register, a dummy `false` variable, and one variable per
     input bit.
   - Each gate becomes at most three clauses forcing its register to the gate's value.
   - The input bits of `x` are fixed by unit clauses. The CNF is then satisfiable iff some
     extension of `x` makes the circuit output `true`.
2. **Projection.** In the dense encoding `encDense`, only the unit clauses depend on `x`, and each
   of their bits is a constant, `xᵢ` or `¬xᵢ` (`encDense_full`, `fullProj_ok`). All variables lie
   below `|regs| + 1 + n + q(n)` (`tseitin_vars`, `verCirc_inp`).
3. **Closure of `Ppoly` under projections** (`projCirc`, `Ppoly_of_projection`). Composing with a
   projection costs at most `n` extra gates. The length of the projection is polynomial, at most
   `18·V(n)²`.

### Corollary D: the circuit route to the decisive premise

> **`(∃ L ∈ NP_TM, L ∉ Ppoly) → SATLowerBound`** (`satLowerBound_of_NP_not_Ppoly`), hence
> `P_TM ≠ NP_TM` (`P_ne_NP_of_NP_not_Ppoly`). Also `SAT_dense ∉ Ppoly → SATLowerBound`
> (`TMCircuit.satLowerBound_of_not_Ppoly`).

**Relationship to the unrestricted lower bound.**
- **Strictly stronger hypothesis.** Corollary D's hypothesis is non-uniform. Since `P_TM ⊆ Ppoly`,
  it implies `SATLowerBound`; the converse is not known.
- **More flexible target.** The hardness may be proved for *any* NP language, not only for SAT,
  and against *every* circuit. Every algorithm the repository can express is therefore covered
  automatically.

## 3. Adversarial elimination, applied to the circuit route

| Test | Outcome |
|---|---|
| Gaussian elimination, parity simplification | Polynomial-size circuits. A circuit lower bound already excludes them, by Theorem A. |
| Polynomial-time preprocessing, alternative encodings | Circuits are closed under composition and projection (Theorem C). |
| Deciders that never search for a witness | Covered: universality quantifies over all circuits. |
| Polynomial-time languages with large crossing information | Irrelevant: `V_SAT` has small circuits, and crossing information is not a circuit measure. |
| Nonlocal and global strategies, other machine models | Covered: every polynomially equivalent model has polynomial-size circuits. |
| Relativization (Baker–Gill–Solovay) | A proof of `P ≠ NP`, by this route or any other, must not relativize. |
| Natural proofs (Razborov–Rudich) | Applies to circuit lower-bound proofs that implicitly use a constructive and large property useful against `P/poly`. Conditional on pseudorandom function families secure against subexponential circuits. Such a proof of Corollary D's hypothesis would break those families. |
| Algebrization (Aaronson–Wigderson) | Arithmetization combined with diagonalization cannot prove `P ≠ NP`, so it cannot prove the hypothesis of Corollary D either. |

**What is known about the open half** (literature; not formalized here):
- For explicit functions, the best known lower bounds against general circuits are linear,
  about `3.1·n` (Find–Golovnev–Hirsch–Kulikov 2016; Li–Yang 2022).
- Superpolynomial circuit lower bounds are known only for classes far above NP, for example
  `MA_EXP ⊄ P/poly` (Buhrman–Fortnow–Thierauf 1998).
- For each fixed `k`, `Σ₂P ⊄ SIZE(n^k)` (Kannan 1982), which is a fixed-polynomial bound.

## 4. The original manuscript claims (Phase 3 classification)

| Claim | Category | Evidence | Status |
|---|---|---|---|
| `conj:wcc_depth` (I-16) | 3: equivalent to an unresolved classical statement | `satLowerBound_iff_wccDepth` (≡ `SAT_dense ∉ P_TM`); implied by `NP_TM ⊄ Ppoly` (Corollary D) | Open |
| `lem:separator-price` (I-31) | 4: useful but insufficient; not resolvable as stated | A schema over an unspecified functional `Φ`, interface `R_ψ` and machine class. Discrete curvature costs are vacuous rails (`P_TM_eq_curvature_rail`). | Open (hypothesis) |
| `prop:locked-expander-full` (I-32) | 3 for a genuinely hard family; 2 (false) for expander Tseitin families | Separator measure ≤ spacetime volume, so the claim implies an exponential lower bound for every decider. On Tseitin families every algorithm can avoid it (`tseitin_mem_SAT_dense_iff_comp`). The family is unspecified. | Open (hypothesis) |
| Symbolic Separation Program (I-2) | 4 at the state level; 3 at the language level | `conditional_symbolic_separation` (state level); the language level needs `SATLowerBound` | Open (conjecture) |

No original claim changes status. The ledger stays at **70 Exact, 11 Refuted, 2 Restricted,
8 Open**. Theorem B supplies the Cook–Levin embedding that Part I §11.1 uses, which is not a
numbered inventory claim.

## 5. Remaining mathematical obstructions (updated)

| Item | Status after Phase X |
|---|---|
| `SATLowerBound` (`SAT_dense ∉ P_TM` ≡ `SATSuperpolynomial` ≡ `WCCDepth SAT_dense`) | **Open.** The decisive premise. |
| Sufficient condition: `∃ L ∈ NP_TM, L ∉ Ppoly` | **Open.** Proved to imply `SATLowerBound` (Corollary D). |
| CL-1, non-uniform part: every `NP_TM` language reduces to `SAT_dense` by projections | **Closed** (Theorem C). |
| CL-1, uniform part: a polynomial-time machine computing the reduction, and closure of `P_TM` under it | Open. It would give `P_TM ≠ NP_TM → SATLowerBound` and, with closure under finite modification, II-24. |
| M1, M3-C, physical class identifications | Unchanged (see `remaining-obstructions.md`). |

## 6. What would still be required to prove `P ≠ NP`

One of the following would suffice:
- a proof of `SATLowerBound` itself, in any of its proved-equivalent forms;
- a superpolynomial circuit lower bound for any single language in `NP_TM`. Corollary D then turns
  it into `SATLowerBound` and `P_TM ≠ NP_TM`.

Any such proof must:
- be non-relativizing and non-algebrizing;
- if it argues through a property of Boolean functions, avoid the natural-proofs barrier;
- go beyond crossing information alone, constraint-graph expansion or proof-system cost alone, and
  curvature alone (Phase IX).

None of Phases VIII–X supplies such a lower bound. The strongest unconditional lower bound for
`SAT_dense` in the repository is fixed-polynomial: `Ω(N²/(log N · log|Λ|))` for single-tape
machines.

## 7. Lean declarations

- **`PVNP.Circuits`:** `Gate`, `Circuit` (gate function, rank, `wf`, `regs`, `triv`, `out`),
  `Circuit.val_eq`, `Circuit.val_embed`, `Gate.map`, `Ppoly`, `DecidesLen`, `poly_eval_mono`.
- **`PVNP.TMCircuit`:** `content`, `rule`, `content_next`, `abs_head_run`, `rule_congr_left/right`,
  `tableau`, `val_cell`, `tableau_eval`, `size_tableau`, `gate_eq_inp`, `firstAnswer_true_iff`,
  `P_TM_subset_Ppoly`, `satLowerBound_of_not_Ppoly`, `P_ne_NP_of_not_Ppoly`.
- **`PVNP.CircuitCookLevin`:** `orComb`, `orComb_eval`, `tseitin`, `units`, `gateCl_sat`,
  `tseitin_sat_iff`, `tseitin_vars`, `Proj`, `encDense_full`, `projCirc`, `projCirc_eval`,
  `Ppoly_of_projection`, `vsrc`, `verCirc`, `inputOf_vsrc`, `verCirc_eval`, `mem_iff_verCirc`,
  `verCirc_inp`, `verCirc_size_le`, `NP_TM_subset_Ppoly_of_SAT`, `SAT_dense_mem_Ppoly_iff`,
  `satLowerBound_of_NP_not_Ppoly`, `P_ne_NP_of_NP_not_Ppoly`, `satLowerBound_of_not_subset`.

## References

- S. A. Cook, The complexity of theorem-proving procedures, STOC 1971; L. Levin, Universal
  sequential search problems, 1973.
- G. S. Tseitin, On the complexity of derivation in propositional calculus, 1968.
- J. E. Savage, Computational work and time on finite machines, J. ACM 19 (1972) (machines to
  circuits).
- T. Baker, J. Gill, R. Solovay, SIAM J. Comput. 4 (1975); A. Razborov, S. Rudich, J. Comput.
  Syst. Sci. 55 (1997); S. Aaronson, A. Wigderson, ACM TOCT 1 (2009).
- R. Kannan, Circuit-size lower bounds and non-reducibility to sparse sets, Inform. Control 55
  (1982); H. Buhrman, L. Fortnow, T. Thierauf, Nonrelativizing separations, CCC 1998.
- M. G. Find, A. Golovnev, E. A. Hirsch, A. S. Kulikov, FOCS 2016; J. Li, T. Yang, STOC 2022.
