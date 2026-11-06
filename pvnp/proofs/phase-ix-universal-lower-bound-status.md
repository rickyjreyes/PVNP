# Phase IX: the universal computational lower bound — exact target, invariant tests, outcome

**Date:** 6 November 2026. **Base:** `main` at `bc06e72` (PR #41). Lean CI on that commit passed (run
42144788341). PR #41 changed documentation only; its parent `888296e` (PR #40) also passed (run
42143237058). **Lean modules:** `SATTarget.lean`, `TseitinSAT.lean`, `VerifierCrossing.lean`.

**Result.**
- **Proved (kernel-checked):**
  - The Phase IX target, a per-input statement of the form `∀ M ∃ x`, is *equivalent* to
    `SATLowerBound`. It is also equivalent to Part I `conj:wcc_depth` for `SAT_dense`.
  - Two candidate invariants fail one of the two required implications, each by an explicit
    counterexample.
- **Not proved:** `SATLowerBound` (`SAT_dense ∉ P_TM`). Consequently `P_TM ≠ NP_TM` is **not**
  derived, and classical P versus NP remains open.

## 1. The exact target (stated and proved equivalent; not proved)

`T_M(x)` is the first-answer time `CrossingSAT.ftime M x`, the step at which `M` first displays an
answer. This is exactly the quantity that `TM.Decides` bounds. `SATTarget.Correct M L` means that
on every input `M` eventually displays the correct membership bit, with no time bound imposed.

```lean
-- PVNP.SATTarget
def SATSuperpolynomial : Prop :=
  ∀ M : TM, Correct M SAT_dense → ∀ k C N₀ : ℕ, 0 < C →
    ∃ x : List Bool, N₀ ≤ x.length ∧ C * x.length ^ k < ftime M x
theorem satLowerBound_iff_superpolynomial : SATLowerBound ↔ SATSuperpolynomial
theorem satLowerBound_iff_superpolynomialReal : SATLowerBound ↔ SATSuperpolynomialReal  -- C : ℝ, C > 0
theorem satLowerBound_iff_wccDepth : SATLowerBound ↔ PartISeparation.WCCDepth SAT_dense
theorem satLowerBound_iff_wccdDepth (d : ℕ) : SATLowerBound ↔ PartISeparation.WCCDDepth d SAT_dense
theorem P_ne_NP_of_superpolynomial (h : SATSuperpolynomial) : P_TM ≠ NP_TM
```

**Proof.**
- **(⇒)** Suppose some correct `M` has `T_M(x) ≤ C|x|^k` for all `|x| ≥ N₀`. There are only finitely
  many shorter inputs (`List.finite_length_lt`), so their first-answer times have a maximum `K`.
  `mem_P_TM_of_eventually_le` then gives `M.Decides SAT_dense (C·n^k + K)`, so `SAT_dense ∈ P_TM`.
  The machine itself is not modified.
- **(⇐)** If `M` decides `SAT_dense` within a polynomial `p`, then `p(n) ≤ p(1)·n^{deg p} ≤ n^{deg p + 1}`
  for `n > p(1)` (`eval_le_pow_succ`). Hence `k = deg p + 1`, `C = 1` and `N₀ = p(1) + 1` violate
  the target.
- **Real constants.** Use `⌈C⌉₊` for real `C`.

**Coverage.** The quantifier ranges over every ordinary single-tape `PVNP.Discrete.TM`. That class
is every algorithm in the repository's model. By `P_WCC_eq_P_TM`, `P_WCCD_eq_P_TM` and
`P_disc_eq_P_TM` it is also every polynomial-time uniform discrete WCC/WCCD machine.

## 2. Testing candidate invariants

An invariant `I` yields `SATLowerBound` only if two things are proved:

- **(A)** every correct `SAT_dense` decider incurs `I`;
- **(B)** incurring `I` forces superpolynomial time.

Neither may be assumed. The table records which half fails for each candidate source in the request.

| Source | Candidate invariant | (A) | (B) | Decisive fact |
|---|---|---|---|---|
| 1. Unavoidable constraint dependencies | resolution width/size, DPLL/CDCL search | **fails** | holds for resolution proofs (literature) | `TseitinSAT.tseitin_mem_SAT_dense_iff_comp` (§2.1) |
| 2. Global consistency | expansion / treewidth of the constraint graph | **fails** | not established, and not needed | `TseitinSAT.tseitin_connected_iff` (§2.2) |
| — (Phase VIII invariant) | crossing information, "many distinguishable states" | holds (Phase VIII) | **fails** | `VerifierCrossing.crossingInfo_not_superpolynomial` (§2.3) |
| 3. Structural transformations | invariants of instance structure | **fails** in general | — | §2.4 (no new Lean) |
| 4. Representation-invariant costs | circuit size of `SAT_n` | holds (standard tableau simulation; not formalized here) | **open**, and strictly stronger than the target | §2.5 |
| 5. Part I curvature confinement | discrete curvature / depth | ≡ classical | ≡ classical | `curvature_lower_bound_is_classical`, `satLowerBound_iff_wccDepth` (§2.6) |

### 2.1 Unavoidable constraint dependencies — (A) fails, with a kernel-checked decision side

**Strongest meaningful lemma.** These are literature results, not formalized here.
- Let `G` be a bounded-degree expander on `m` vertices with odd total charge. Every resolution
  refutation of its Tseitin formula has width at least the boundary expansion of `G` and size
  `2^{Ω(m)}` (Tseitin 1968; Urquhart 1987; Ben-Sasson–Wigderson 2001).
- Any decider whose run yields a resolution refutation on rejected inputs therefore takes `2^{Ω(m)}`
  steps on this family. This covers DPLL and CDCL without extension rules.

**Crucial inference tested.** The candidate claims that *every* correct decider incurs this cost.
That is **false**, as the following kernel-checked theorem shows (`TseitinSAT`).

> For every loopless multigraph `E` on `Fin m`, every charge `χ`, and every `n` with
> `1 ≤ n` and `|E| ≤ n`:
> `encDense n (tseitinCNF E χ (finRange m)) ∈ SAT_dense ↔ ∀ v, Σ_{u ∈ comp E v} χ(u) = 0 (mod 2)`.

Here `comp E v` is `|V|` rounds of explicit neighbour expansion from `{v}`. Checking the criterion
takes `O(m²·|E|)` elementary set operations, which is polynomial in the input length.

A decider that computes component parities never produces a resolution refutation. The missing
hypothesis is: "every polynomial-time decider can be converted into a polynomial-size resolution
refutation on unsatisfiable inputs." This hypothesis is *false*. The theorem above gives the
decision side, and the resolution side is the cited lower bound.

**Proof structure.**
- `solvable_iff_parityOK`: the GF(2) system `Σ_{e ∋ v} x_e = χ(v)` is solvable iff every
  edge-closed vertex set (union of components) has even charge.
  - Necessity: every edge is counted twice over a closed set (`sum_degSum_closed`).
  - Sufficiency: induction on the edge list. The first edge `(a, b)` must take the common charge
    of the closed sets of the remaining graph that separate `a` from `b`. Any two such sets have the
    same charge because their symmetric difference is closed in the whole graph (`sum_symm`).
- `parityOK_iff_comp`:
  - `|V|` expansion rounds stabilize (`grow_comp`);
  - each `comp E v` is the least closed set containing `v` (`closed_comp`, `comp_subset`);
  - every closed set is a disjoint union of such components (strong induction on the cardinality).
- `evalFormula_xorCNF`: the CNF of an XOR constraint is exact. It has one clause per wrong-parity
  pattern, so a degree-3 vertex gives 4 clauses of width 3.
- `tseitin_mem_SAT_dense_iff`: everything is transferred to `SAT_dense` through
  `encDense_mem_SAT_iff`.

The earlier module `Tseitin.lean` proved only the obstruction direction, and the ledger
(`physical-model-freeze.md`) recorded the Gaussian-elimination bypass as analytic. The bypass is now
kernel-checked, as a polynomial criterion for the repository's own SAT language.

### 2.2 Global consistency — (A) fails: on connected graphs global consistency is one parity bit

**Candidate.** On an expander, every balanced cut of the constraint graph is crossed by `Ω(m)`
constraints. The candidate concludes that every decider must transport `Ω(m)` bits of consistency
information across every cut, and that this costs `2^{Ω(m)}` in total.

**Failure.** The inference fails twice.
- **The step from per-cut information to exponential cost is invalid.** Counting per-cut
  information certifies at most `G·I ≤ (N+1)·N` steps for `G` cuts carrying `I` bits each, never
  an exponential bound (Phase VIII §4). By §2.3, even that much is carried by a polynomial-time
  language.
- **The premise is false for Tseitin instances.** On a connected multigraph, membership is the
  parity of the total charge (`tseitin_connected_iff`). One bit summarizes all global consistency,
  and it is computable in linear time, whatever the expansion.

Expansion, treewidth and global coupling are therefore not invariants that every algorithm must pay
for.

### 2.3 Distinguishable states / crossing information — (B) fails, kernel-checked

The Phase VIII invariant is formalized as
`CrossingInfo L N F G`. It says: there are `G` distinct cuts, and at each of them every decider of
`L` has injective decision traces on a family of `F` inputs of length `N`.
- **(A) holds.** `crossingInfo_SAT_dense` gives
  `CrossingInfo SAT_dense (3n(2·2ⁿ+g)) (2^{2ⁿ}) (3ng+1)`.
- **Conversion to time.** `time_of_crossingInfo` gives `G·ℓ ≤ 2T(N)` whenever
  `2(|Λ×Dir|+1)^ℓ ≤ F`.

**(B) fails** (`VerifierCrossing`). Take the verification language `V_SAT` (Part III `L_check`).
- **It is in `P_TM`.** `satTM` decides it within `2(N+3)²` steps.
- **It carries quadratic crossing information.** `CrossingInfo V_SAT (13n+1) (2ⁿ) (6n+1)` holds for
  every `n ≥ 1`, and `(13n+1)² ≤ 30·(6n+1)·n`.
  - The family is the formula `exC(a) ∧ (z₀ ∨ ¬z₀ ∨ ¬z₀)` paired with the witness `b`. It is accepted
    iff `b ≠ a`.
  - Rejection splicing at any of the `6n+1` cuts in the doubled padding makes the decision traces
    injective on all `2ⁿ` rejected diagonal instances (`vsat_mixed`).
- **It is quadratically hard on a single tape.** Every single-tape decider of `V_SAT` needs
  `T(13n+1) ≥ (6n+1)⌊(n−1)/L⌋/2` with `L = ⌊log₂(3|Λ|+1)⌋+1` (`vsat_time_lower_bound_sq`).
  - That is `Ω(N²/log|Λ|)`, and `satTM` matches it up to the `log|Λ|` factor.
  - Phase VIII certifies only `Ω(N²/(log N·log|Λ|))` for `SAT_dense`.

`crossingInfo_not_superpolynomial` states the conclusion: some `L ∈ P_TM` carries, at every length,
a constant fraction of the maximal crossing information. Hence no argument that uses *only*
crossing information about `L` can show `L ∉ P_TM`. The near-quadratic SAT bound of Phase VIII
reflects single-tape information transport, which polynomial-time verification also requires. It
does not reflect NP-hardness.

### 2.4 Structural transformations — no invariant survives membership-preserving preprocessing

**Candidate.** Use an invariant of instance structure as the cost. Examples: number of solutions,
symmetry group, treewidth, kernel size, or the self-reduction tree.

**Test.** A universal lower bound must be preserved by every polynomial-time map that preserves
`SAT_dense` membership, because a decider may apply any such map first. Polynomial-time
preprocessing changes all of the structural quantities listed:
- Gaussian elimination collapses Tseitin instances to a parity bit (§2.1);
- unit propagation and the 2-SAT implication-graph algorithm solve their fragments outright.

An invariant that *is* preserved by all such maps is a property of the polynomial-time degree of
`SAT_dense`. Proving it superpolynomial is `SATLowerBound` restated.

Downward self-reducibility relates the cost of decision to the cost of search. It gives no lower
bound on either.

**Missing hypothesis.** A preprocessing-invariant quantity that is provably superpolynomial for
`SAT_dense`. No such quantity is known other than the target itself. No Lean declaration is added,
because formalizing a restatement is excluded by the request.

### 2.5 Representation-invariant costs — (B) is open and strictly stronger than the target

**Candidate.** The minimum Boolean-circuit size of `SAT_dense` on inputs of length `N`.

**(A) holds**, and is standard but not formalized here. A single-tape machine running `T` steps
unrolls into circuits of size `O(T²)`, since a tableau has `T` rows of `O(T)` cells, each computed by
a constant-size gate block. A time bound therefore yields a circuit bound.

**(B) is the claim "`SAT_dense` needs superpolynomial circuits", i.e. `SAT ∉ P/poly`.**
- It implies `SATLowerBound` and is strictly stronger, because it is a non-uniform statement.
- It is open. For explicit functions, even ones in P, the best known general circuit lower bounds
  are linear, about `3.1·N` (Find–Golovnev–Hirsch–Kulikov 2016; Li–Yang 2022).

Description-complexity costs face similar limits.
- The Kolmogorov complexity of an instance is at most its length, so it can force only linear time.
- Time-bounded variants such as MINKT and MCSP have hardness tied to one-way functions
  (Liu–Pass 2020). It is not unconditional.

### 2.6 Part I curvature confinement — equivalent to the classical statement

Earlier kernel-checked theorems settle this source.
- For NP languages, every discrete curvature or depth lower bound is *equivalent* to the classical
  time bound (`Discrete.curvature_lower_bound_is_classical`, `P_TM_eq_curvature_rail`).
- Phase IX adds `satLowerBound_iff_wccDepth` and `satLowerBound_iff_wccdDepth`: Part I
  `conj:wcc_depth` for `SAT_dense` is exactly the target.

A curvature bridge therefore cannot be easier than `SATLowerBound`. No new rigorous bridge exists.

## 3. Universal separation lemma: the Part I claims revisited

| Claim | Phase IX finding | Status |
|---|---|---|
| `conj:wcc_depth` (I-16) | It is exactly `SATLowerBound` for `SAT_dense` (`satLowerBound_iff_wccDepth`). | Open |
| `lem:separator-price` (I-31) | It is a hypothesis over unspecified admissible fields. Discrete curvature costs are vacuous rails (`P_TM_eq_curvature_rail`). | Open (hypothesis) |
| `prop:locked-expander-full` (I-32) | Its expander motivation fails for every algorithm on Tseitin families, where component parity decides membership without paying a separator cost. As a hypothesis quantified over "every permitted decider" of an unspecified hard family, it would imply a `SATLowerBound`-type statement. | Open (hypothesis) |
| Symbolic Separation Program (I-2) | The state-level schema is formal (`conditional_symbolic_separation`). The language-level content needs the target. | Open (conjecture) |

**Survival of each obstruction against the tests required in Phase 3:**
- **Crossing information**
  - fails under *alternative representations*: the cut layout is encoding-specific;
  - fails under *polynomially equivalent machine models*: on multitape machines it gives only
    `Ω̃(N)` (Phase VIII §4);
  - fails against *algorithms unrelated to WCC*: `V_SAT ∈ P_TM` carries it.
- **Resolution, expansion and global consistency** fail against *algebraic simplification* (GF(2)
  elimination) and against *avoidance of witness search* (parity never searches).
- **Curvature** is classical by equivalence.
- **Circuit size** survives all seven tests: preprocessing, alternative representations,
  simplification, nonlocal computation, witness strategies, model changes and unrelated algorithms.
  It is, however, unproved and stronger than the target.

## 4. Barriers: exactly which hypotheses they address

None of these is an impossibility theorem for `P ≠ NP`. Each excludes a class of proofs.

- **Relativization** (Baker–Gill–Solovay 1975). There are oracles `A`, `B` with `P^A = NP^A` and
  `P^B ≠ NP^B`.
  - *Addresses:* any argument that remains valid verbatim when every machine, decider and verifier
    alike, gets the same arbitrary oracle. This covers pure simulation and diagonalization. In this
    repository, the class equalities and transfer theorems are arguments of this kind: they move a
    separation between models but cannot create one.
  - *Does not address:* arguments that use the internal structure of computations, such as
    tableaux, arithmetization or circuit structure, in an oracle-sensitive way.
- **Natural proofs** (Razborov–Rudich 1997).
  - *Addresses:* lower-bound proofs against `P/poly` that implicitly supply a property of Boolean
    functions that is *constructive* (decidable in time `2^{O(n)}` from the truth table), *large*
    (true of a `2^{−O(n)}` fraction of functions) and *useful* (false for all small circuits).
  - *Conditional on:* pseudorandom function families secure against subexponential-size circuits,
    which follow from sufficiently strong one-way functions.
  - *Does not address:* non-constructive or non-large properties, uniform-machine arguments that
    do not yield circuit lower bounds, or diagonalization.
  - *Relevance here:* it bears on the circuit route of §2.5. Crossing information at a cut is
    constructive and large (random languages have full-rank cut matrices), so a circuit version of
    it would be natural. This is moot, because §2.3 refutes (B) unconditionally.
- **Algebrization** (Aaronson–Wigderson 2008/2009).
  - *Addresses:* separation proofs that stay valid when the class being separated out gets a
    low-degree extension `Ã` of an oracle `A` while the other class gets `A`. Some `A` and some
    extension `Ã` satisfy `NP^Ã ⊆ P^A`, so no algebrizing argument proves `P ≠ NP`. This covers
    arithmetization combined with diagonalization, the techniques behind `IP = PSPACE`.
  - *Does not address:* non-algebrizing techniques. None are currently known to suffice.

The Phase IX negative results are of a different kind. They are explicit counterexamples to
specific inferences (§2.1–2.3), proved unconditionally.

## 5. The smallest remaining implication

`SATLowerBound`, in any of its proved-equivalent forms:
`SAT_dense ∉ P_TM` ⟺ `SATSuperpolynomial` ⟺ `SATSuperpolynomialReal` ⟺
`WCCDepth SAT_dense` ⟺ `WCCDDepth d SAT_dense`.
- **What it would give.** `P_TM ≠ NP_TM` (`P_ne_NP_of_satLowerBound`, `P_ne_NP_of_superpolynomial`).
  Through `P_disc_eq_P_TM` and `NP_disc_eq_NP_TM`, it would also give the discrete separation.
- **What it is not.** No proper weakening of it is known to suffice.
- **The converse.** `P_TM ≠ NP_TM → SATLowerBound` needs Cook–Levin (CL-1), which is not formalized.

Any future proof must avoid the routes this phase shows to be dead:
- crossing information alone (§2.3);
- constraint-graph expansion or proof-system cost alone (§2.1–2.2);
- curvature alone (§2.6).

If it goes through circuits, it must be non-natural. In any case it must be non-relativizing and
non-algebrizing.

## 6. Ledger

No manuscript claim changes status: **70 Exact, 11 Refuted, 2 Restricted, 8 Open**.

- The `TseitinSAT` theorem kernel-checks the bypass behind an already-recorded refutation (the
  expander-to-hardness inference: Part III WIN-18, `physical-model-freeze.md`).
- The `SATTarget` equivalences sharpen I-16 without resolving it.
- `VerifierCrossing` is a supporting no-go for the Phase VIII method.

## 7. Lean declarations (all kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound`)

- `PVNP.SATTarget`: `Correct`, `SATSuperpolynomial`, `SATSuperpolynomialReal`, `decidesAt_ftime`,
  `mem_P_TM_of_eventually_le`, `eval_le_pow_succ`, `satLowerBound_iff_superpolynomial`,
  `superpolynomial_iff_real`, `satLowerBound_iff_superpolynomialReal`,
  `satLowerBound_iff_wccDepth`, `satLowerBound_iff_wccdDepth`, `P_ne_NP_of_superpolynomial`.
- `PVNP.TseitinSAT`: `solvable_iff_parityOK` (`parityOK_of_solvable`, `solvable_of_parityOK`),
  `grow_comp`, `closed_comp`, `comp_subset`, `parityOK_iff_comp`, `parityOK_iff_total`,
  `evalFormula_xorCNF`, `satisfiable_tseitinCNF_iff`, `tseitin_mem_SAT_dense_iff`,
  `tseitin_mem_SAT_dense_iff_comp`, `tseitin_connected_iff`.
- `PVNP.VerifierCrossing`: `CrossingInfo`, `time_of_crossingInfo`, `crossingInfo_SAT_dense`,
  `vInst_mem_iff`, `vsat_mixed`, `dtraceV_injective`, `crossingInfo_V_SAT`, `vsat_info_quadratic`,
  `vsat_time_lower_bound`, `vsat_time_lower_bound_sq`, `crossingInfo_not_superpolynomial`.

## References

- G. S. Tseitin, On the complexity of derivation in propositional calculus (1968).
- A. Urquhart, Hard examples for resolution, J. ACM 34 (1987).
- E. Ben-Sasson, A. Wigderson, Short proofs are narrow — resolution made simple, J. ACM 48 (2001).
- F. C. Hennie, One-tape, off-line Turing machine computations, Inform. Control 8 (1965).
- T. Baker, J. Gill, R. Solovay, Relativizations of the P =? NP question, SIAM J. Comput. 4 (1975).
- A. Razborov, S. Rudich, Natural proofs, J. Comput. Syst. Sci. 55 (1997).
- S. Aaronson, A. Wigderson, Algebrization: a new barrier in complexity theory, ACM TOCT 1 (2009).
- M. G. Find, A. Golovnev, E. A. Hirsch, A. S. Kulikov, A better-than-3n lower bound for the circuit
  complexity of an explicit function, FOCS 2016; J. Li, T. Yang, 3.1n − o(n) circuit lower bounds
  for explicit functions, STOC 2022.
- Y. Liu, R. Pass, On one-way functions and Kolmogorov complexity, FOCS 2020.
