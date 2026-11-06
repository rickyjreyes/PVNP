# Faithful Lean formalization of the three PVNP manuscripts: report (5 November 2026)

The source of truth is the three manuscripts in `pvnp/papers/*/main.tex` (revised 27 October 2026),
read in full. The claim-by-claim table, with Lean names and statuses, is
`pvnp/proofs/manuscript-lean-inventory.md`. This report summarizes it.

Toolchain: Lean 4.23.0 / Mathlib v4.23.0 (unchanged). Every listed theorem is kernel-checked. The
axiom audit admits only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`,
`admit` or custom axiom.

## A. Part I (*P vs NP in Curvature-Bounded Wave Computation*)

41 claims: 26 Exact, 1 Restricted, 8 Refuted, 6 Open.

* **Verified skeleton.** Each separation statement is formalized with its own hypotheses and
  universal quantifiers over admissible machines. The implications are proved:
  * complexity schema;
  * conditional symbolic separation;
  * WIN-05;
  * `thm:np-type-conditional`;
  * `lem:lower`;
  * `thm:curv-bdd-sep`;
  * `cor:P-neq-NP-conditional` (`PartISeparation`).
* **Verified mathematics.**
  * `thm:psi-sat-completeness`: both forms (`PartIPsiSat`).
  * WIN-03: a zero-penalty field that is not stationary for any λ.
  * Uniform symbolic verification.
  * `lem:clause_flip` and its remark (`PartILocality`).
  * WIN-04: the Gaussian on `ℝ⁴` with Mathlib's Laplacian (`PartIDimLock`).
  * The telescoping bound in quotient form; conditional additive padding
    (`ManuscriptRemarks`).
* **`conj:wcc_depth`** is proved *equivalent* to `L ∉ P_TM`, both in 1-D and on `ℤ^(1+d)`
  (`WCCDepth_iff_not_P_TM`, `WCCDDepth_iff_not_P_TM`). Hence `prop:internal_sep_conditional`
  holds, and its premise for 3-SAT is the classical problem itself.
* **Refuted steps.** Each has a Lean counterexample satisfying the claim's own hypotheses.
  * **State-level routes (I-25 to I-28):** they infer language separation from the
    non-constructibility of a state, and that inference is invalid.
  * **`lem:local_growth` (I-13):** an implicit quiescence hypothesis is needed, and the linear
    growth bound fails for `d = 2`. The corrected bound `|supp C_t| ≤ |supp C_0|(2rt+1)^d` is
    proved.
  * **§6.4 physical barrier (I-12):** it fails under P = NP with charged encoders, and the claim
    itself implies `P_TM ≠ NP_TM`.
  * **Dimensional-lock hypothesis (1) (I-20):** it is incompatible with polynomial witnesses.
  * **`prop:collapse-grammar` (1) (I-10):** false as literally stated.
* **Open.**
  * The conjectures and hypotheses themselves: `conj:wcc_depth`, the Symbolic Separation
    Program, `lem:separator-price`, `prop:locked-expander-full`.
  * Two informal statements that are not well posed: the phase-locking criterion and the
    toroidal locking configuration.
* **Discrete class equivalences (I-38, I-39): Exact.** `thm:P-equivalence` and
  `thm:NP-equivalence` concern Part I's *uniform discrete WCC machine*. That model is
  `PartIIUniform.UWCC`: any dimension `d ≥ 1` and radius `r ≥ 0`, a poly-time lattice algorithm,
  encoder and readout, all charged. `P_disc_eq_P_TM` and `NP_disc_eq_NP_TM` prove both theorems
  (Milestone 5).
* **Restricted (I-11).** `rem:infinite-compute` asserts the equality *within the physical rail*.
  The discrete equality is proved, but that the rail induces a uniform discrete machine is a
  physical premise, which Part I itself (`rem:physical-bridge`) leaves unproved.

## B. Part II correspondence audit (*Discrete WCC and Classical Complexity*)

28 claims: 23 Exact, 1 Restricted, 3 Refuted, 1 Open.

* **Machine model.**
  * The manuscript's Turing machine (`def:tm`: total `δ`, moves `L`/`R`, `q_acc`/`q_rej`) is
    `PartIITuring.MTM`.
  * **Finding:** the literal `def:pturing` ("`T_M(n) ≤ c nᵏ` for all `n`, `c, k ≥ 1`") forces
    `T_M(0) = 0`. Therefore `P_Turing^lit = {∅, Σ*}`, and literally `P_Turing ≠ NP_Turing`; this
    is an artefact of the boundary case.
  * With the clearly distinguished correction `c·max(n,1)ᵏ`, `P_Turing = P_TM` (explicit
    simulations both ways).
  * `NP_Turing = NP_TM` holds as defined.
* **The author's construction `W_M`.** It is formalized exactly as written:
  * alphabet `Γ × (Q' ∪ {⊥}) × {0,1}`;
  * phase-1 cases in the manuscript's order;
  * window `Λ_n` with background, `enc_M`, `dec_M`.

  Results:
  * `prop:local-tm` and `lem:runtime` are proved. The first output appears at time
    **exactly** `2·T_M(x)`, and `|Λ_n| = 2L+1`.
  * `lem:one_step` and `lem:invariant` hold for every `t ≤ L(n)`, hence every `t ≤ T_M(n)`.
  * Their literal "for all `t ≥ 0`" fails once the head leaves `Λ_n`: `rightMTM`, with the
    manuscript's own `L(n) = T_M(n) + n`.
* **Uniform model (`def:wcc_machine`).** Formalized as `PartIIUniform.UWCC`:
  * poly-time computable functions on the manuscript's machine;
  * lattice description as a box bitmap with margin `r`;
  * canonical configuration codes;
  * a poly-time decoder in `n`.

  `P_TM ⊆ P^disc` is proved by an explicit answer-writing machine (II-26). The status
  paragraph's phrase "the equality also holds for this trivial reason" is right only for this
  inclusion.
* **The reverse simulation (`thm:wcc_to_tm`, Milestone 5).** `PartIIUniform.wcc_to_tm` gives,
  for every uniform machine `W`, an ordinary single-tape machine `M_W` and a polynomial `q_W`.
  Whenever the decoder of `W` first outputs `some b` at time `T_W(x)`, `M_W` first answers `b`
  within `q_W(|x| + T_W(x) + 1)` steps. `M_W` is compiled by `Prog.toTM` from an explicit
  round-trip sweep program (`UniformSim.Spec.prog`), which works as follows.
  * The lattice algorithm, the encoder and the decoder of `W` run as simulated manuscript
    machines on folded tracks, one round trip per step (`simTrip_spec`). Their cost is charged
    through the FP time bounds.
  * The box bitmap `1^R 0 b` is parsed, a ruler of `B = 2R+1` cells is built, and `C_0` is loaded
    from the encoder's code (`pre_round`).
  * Each round writes the decoder input `1^n 0 cfgCode(C_t)` (`decode_phase`), reads the first
    decision (`round_halt`), and otherwise computes `C_{t+1} = UWCC.step n C_t` on the box
    (`round_spec`).
  * The windows come from cyclic rotations by `δ_v = Σ_k (v_k − r) B^k`, nested over the ruler
    (`rot_level`, `tasks_shift`). The flattened-index geometry is proved (`nbr_idx`,
    `member_nbr`), not assumed.

  Hence `P_disc_eq_P_TM`. The verifier class of `def:wcc_verifier` is `NP_disc`, and
  `NP_disc_eq_NP_TM` holds (II-13; reading of the definition in the inventory).
* **Capacity section.** `lem:bandlimit`, `lem:spatial_capacity` (a genuine lattice-point count,
  `C₂ = 27/(8π³)`), `lem:lane_update_bound`, `thm:spacetime_capacity` and
  `prop:phys_step_ceiling` are proved. Their physical premises are explicit hypotheses, as in
  the manuscript.
* **Wave–symbol correspondence.** Both directions of `thm:wave-symbol-isomorphism` and the
  manuscript's counterexample are proved.
* **Exact (II-11, II-12, II-13, II-15).** `thm:wcc_to_tm`, `cor:pwcc_equals_pturing`,
  `thm:np_equiv` and `thm:uniform-discrete-bijection` hold for the uniform model. `P_Turing` is
  read with the corrected `def:pturing`; with the literal one the right side is `{∅, Σ*}` (II-17).
* **Restricted (II-10).** Both conclusions of `thm:tm_to_wcc` are proved. What is not formalized
  is that the author's own `W_M` is uniform, i.e. that `enc_M`, `dec_M` and `Λ_n` are computable
  in polynomial time.
* **Open (II-24, `thm:conditional_np_safety`).** It needs an NP-complete language (Cook–Levin)
  and closure of `P` under poly-time reductions.

## C. Part III (*Physical Complexity Reassessment*)

22 claims: 21 Exact (including III-6, `thm:disc-equiv`, via `P_disc_eq_P_TM` and
`NP_disc_eq_NP_TM`), 0 Restricted, 1 Open (III-22, a remark without mathematical content).
New in earlier passes:
* WIN-13;
* `thm:p-in-np`, for any model whose verifiers may ignore witnesses under the same rails;
* WIN-16.

## D. Coverage

| Paper | Claims | Exact | Restricted | Refuted | Open |
|---|---|---|---|---|---|
| I | 41 | 26 | 1 | 8 | 6 |
| II | 28 | 23 | 1 | 3 | 1 |
| III | 22 | 21 | 0 | 0 | 1 |
| **Total** | **91** | **70** | **2** | **11** | **8** |

* Exact coverage is 70/91 ≈ 77% (63/91 before Milestone 5).
* The proportion determined (Exact + Refuted) is 81/91 ≈ 89%.
* "Exact" includes conditional implications whose premises are open. No conditional theorem is
  counted as verifying an unconditional claim.

## E. Smallest missing lemmas

1. **Discrete separation route.** `conj:wcc_depth` for 3-SAT, which is equivalent in Lean to
   `3-SAT ∉ P_TM`, the classical open problem.
2. **Physical route.**
   * `lem:separator-price` and `prop:locked-expander-full` for every admissible decider;
   * a physical-to-discrete class identification.

   Even then, a physical SAT lower bound under poly-time encoders already implies
   `P_TM ≠ NP_TM` (`physical_SAT_lower_bound_is_classical`).
3. **Done in Milestone 5:** the uniform model's `P^disc ⊆ P_TM`, hence `P_disc_eq_P_TM` and
   `NP_disc_eq_NP_TM` (about 4,950 lines in `UniformSim*` and `PartIIUniformEquiv`).
4. **II-24.** An NP-complete language and closure of `P_TM` under poly-time reductions and finite
   modification.
5. **Uniformity of the author's `W_M`.** A poly-time machine computing `enc_M` on
   `Λ_n = {−L(n)…L(n)}`, which needs unary evaluation of `L(n)`.

## F. Paths, declarations, PRs, CI, audit

**Modules** (under `lean/PVNP/`):
* `PartIPsiSat`, `PartISeparation`, `PartILocality`, `PartIDimLock`;
* `PartIIManuscript`, `ManuscriptRemarks`;
* `PartIITuringModel`, `PartIITwoPhase`, `PartIIUniform`;
* Milestone 5: `UniformSimLib`, `UniformSimProg`, `UniformSimSem`, `UniformSimMath`,
  `UniformSimPre`, `UniformSimGrow`, `UniformSimLoad`, `UniformSimInit`, `UniformSimPack`,
  `UniformSimRot`, `UniformSimApply`, `UniformSimRound`, `UniformSimMain`, `PartIIUniformEquiv`;
* the earlier D-1 modules: `SweepTM`, `WCCDCyclic`, `WCCDSweep*`.

**PRs, merged once CI (`lean`, `build`, `phase-iii-targeted`) was green on the exact head:**

| PR | Content | Head | Merge commit |
|---|---|---|---|
| #25 | D-1 | — | `1a2c3c1` |
| #27 | Milestone 1 | `529058b` | `ccd2c51` |
| #28 | Milestone 2 | `1f56405` | `6c4f537` |
| #30 | Milestone 3 | `c5454af` | `2d3a8ee` |
| #31 | Milestone 4 (uniform model, `P_TM ⊆ P^disc`) | — | `ad18b6a` |
| #32 | Milestone 5 checkpoint (simulator library and program) | — | `08899d7` |

Milestone 5 (`P_disc_eq_P_TM`, `NP_disc_eq_NP_TM`) is submitted as its own PR.

**Axiom audit:** `lean/audit/AxiomAudit.lean`, 311 principal declarations, checked by
`audit/check_axioms.py`. CI also builds each manuscript module explicitly.

## G. Conclusion on P versus NP

**No proof of P ≠ NP (or P = NP) is contained in the three manuscripts, and none is claimed
here.**

* Every route in Part I to `P_WCC ≠ NP_WCC` or `P ≠ NP` passes through an unproved premise:
  * `conj:wcc_depth`, which is equivalent to `3-SAT ∉ P_TM`;
  * the interface/expander hypotheses;
  * the non-constructibility premises.
* The state-level routes contain an inference refuted in Lean.
* The discrete equivalences that are verified (`P_WCC = P_TM`, `NP_WCC = NP_TM` on `ℤ^(1+d)`;
  `P_disc = P_TM` and `NP_disc = NP_TM` for the uniform model of `def:wcc_machine`; the
  manuscript's own Turing model with the corrected bound) show only that the discrete WCC
  question is *exactly* the classical one.
* The entire chain is not verified, because its decisive premise is the open problem itself.

### Phase VIII addendum (6 November 2026)

The crossing-sequence route of Part I is now formalized for the ordinary single-tape
`PVNP.Discrete.TM` (`CrossingHennie`, `CrossingSAT`, `CrossingSATSets`).

- **Splicing.** The complete multi-segment splicing theorem is proved: `CrossingHennie.hennie`.
- **SAT mixed acceptance.** It is derived for an explicit, spatially separated `SAT_dense` encoding:
  `CrossingSAT.diag_mixed` and `hmixed_of_halting`.
- **Time lower bounds.** The resulting single-tape bounds go up to
  `T(N) = Ω(N²/(log N · log|Λ|))`: `CrossingSATSets.sat_time_lower_bound_near_sq`.

These are fixed-polynomial bounds, and they are the ceiling of crossing-sequence counting. The
decisive premise is unchanged. It is now stated as `CrossingSAT.SATLowerBound`
(`SAT_dense ∉ P_TM`), with the proved transfer `P_ne_NP_of_satLowerBound`, and it remains open.

No claim changes status: 70 Exact, 11 Refuted, 2 Restricted, 8 Open. See
`phase-viii-separation-status.md`.

