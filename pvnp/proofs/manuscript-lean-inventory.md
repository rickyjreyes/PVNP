# Manuscript-to-Lean inventory (Parts I–III), live checklist

Started 5 November 2026. The source of truth is the three manuscripts in
`pvnp/papers/*/main.tex` (revised 27 October 2026), read in full. Each mathematically
substantive claim is listed with its source, the Lean declaration that matches it (if any), and
its status. Pure definitions, purely empirical sections and research-direction remarks without
mathematical content are not counted.

**Status vocabulary**

| Status | Meaning |
|---|---|
| **Exact** | The manuscript claim, with its own hypotheses and quantifiers, is a kernel-checked Lean theorem. For a claim stated as an implication, the implication itself is what is verified; its premises are not thereby proved. |
| **Restricted** | Lean proves the statement for a narrower model or encoding than the manuscript states. The gap is named. |
| **Refuted** | The claim as stated is false, and a Lean counterexample satisfies the claim's own hypotheses. A corrected statement is proved where possible. |
| **Open** | A conjecture or hypothesis stated as such in the manuscript, or a claim that is not well posed or not yet formalized. The missing piece is named. |

Lean paths are relative to `lean/`. "(new)" marks declarations added in this pass.

## Coverage table

| Paper | Claims | Exact | Restricted | Refuted | Open |
|---|---|---|---|---|---|
| Part I | 41 | 24 | 3 | 8 | 6 |
| Part II | 28 | 19 | 5 | 3 | 1 |
| Part III | 22 | 20 | 1 | 0 | 1 |
| **Total** | **91** | **63** | **9** | **11** | **8** |

* Exact verification coverage = Exact / Total = 63/91 ≈ 69%.
* Status conclusively determined by a proof or a counterexample (Exact + Refuted) = 74/91 ≈ 81%.
* Milestone history:
  * Milestone 1 (PR #27): 44 Exact, 8 Refuted.
  * Milestone 2 (PR #28): adds I-8, I-22, I-23, II-4, II-5, II-18 to II-23, II-27, III-5, III-7
    and III-8.
  * Milestone 3 (PR #30): adds the manuscript's Turing-machine model and two-phase
    construction (II-2, II-7, II-8, II-9, II-17, new row II-28).
  * Milestone 4: adds the uniform model of `def:wcc_machine` and `P_TM ⊆ P^disc` (II-26).

**What the "Exact" count does not mean.** It includes conditional propositions whose
implications are verified while their premises remain open, for example
`prop:internal_sep_conditional`, whose premise is `conj:wcc_depth`. No exact entry asserts
classical `P ≠ NP`.

## Part I — *P vs NP in Curvature-Bounded Wave Computation*

| # | Label / location | Claim (short) | Lean | Status |
|---|---|---|---|---|
| I-1 | Prop. "Curvature-Confinement Complexity Schema" §2.2 | (1) C(ψ*) above every poly-time bound + (2) verifiable ⇒ ψ* ∈ NP\P (states) | `PartISeparation.complexity_schema` (new) | Exact; premise (1) open |
| I-2 | Conj. "Symbolic Separation Program" §4 | ∃ verifiable non-constructible ψ* under WCT rails | — | Open (conjecture) |
| I-3 | §2.3/§4.1 phase-locking criterion "SAT ⟺ ∃xᵢ: ∇φ→0, \|ψ\|²→max" | informal limits, encoding unspecified | — | Open (not well posed; superseded by I-6) |
| I-4 | Thm. "Conditional Symbolic Separation" §4.2 | verifiable ∧ not constructible ⇒ ψ* ∈ NP\P, P≠NP (states) | `PartISeparation.conditional_symbolic_separation` (new) | Exact; premise (2) open |
| I-5 | "Conditional Classical Corollary" §4.4 | TM⇄WCC^∞ ⇒ P^∞=P, NP^∞=NP; separation ⇒ P≠NP | `P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM`, `p_vs_np_discrete_transfer`, `PartISeparation.conditional_bridge_WCC/WCCD` (new) | Exact (premises proved for the discrete model) |
| I-6 | Thm. `thm:psi-sat-completeness` §5.4 | 3-CNF F sat ⟺ ∃ binary-phase ψ, E_logic=0 ⟺ ∃ nonzero-amplitude ψ, E_logic=0 | `PartIPsiSat.psi_sat_completeness`, `psi_sat_completeness_field` (new) | Exact |
| I-7 | Remark WIN-03 | E_logic=0 ⇏ δ(E_geom+λE_logic)=0 | `PartIPsiSat.zero_penalty_not_stationary` (new) | Exact |
| I-8 | Prop. WIN-04 `lem:dim-lock` | Gaussian on ℝ⁴ has finite ‖∇ψ‖² and ‖Θ_ε‖² | `PartIDimLock.win04_gaussian`, `laplacian_ψ` (new) | Exact (Mathlib's Laplacian; Δψ = (4‖x‖²−8)e^{−‖x‖²} proved; integrability of ψ, ‖∇ψ‖², Θ_ε² for every ε > 0, α ≥ 0) |
| I-9 | Prop. WIN-05 `thm:pwcc-neq-npwcc` | verifier + every decider exceeds a rail i.o. ⇒ P^phys≠NP^phys | `PartISeparation.win05` (new) | Exact |
| I-10 | Prop. `prop:collapse-grammar` | (1) no finite invariant partition; (2) L(ψ)∈{∅,Σ*}; (3) rule unrecoverable | `PartISeparation.trivial_partition_invariant` (new) | Refuted ((1) as literally stated; (2),(3) undefined) |
| I-11 | Remark `rem:infinite-compute` | within the rail, P_WCC = P_Turing | `P_WCC_eq_P_TM` | Restricted (discrete model) |
| I-12 | §6.4 "even if P=NP, any SAT algorithm would violate the rails" | physical barrier claim | `PartISeparation.PNP_SAT_physically_constant`, `category_error_claim_implies_classical` (new) | Refuted under P=NP in the frozen model with charged poly-time encoders; the claim implies `P_TM ≠ NP_TM` |
| I-13 | Lemma `lem:local_growth` | supp(C_{t+1}) ⊆ supp(C_t)^{+r}; \|supp C_t\| ≤ \|supp C_0\| + O(rt\|∂supp C_0\|) | `PartILocality.supp_step_subset`, `local_growth_needs_quiescence`, `linear_growth_false_d2`, `support_poly_bound` (new) | Refuted (needs quiescence; linear bound false for d=2); corrected (2rt+1)^d bound proved |
| I-14 | Lemma `lem:clause_flip` | local signature change needs local activity; k ≤ Tb | `PartILocality.clause_flip_local`, `clause_flip_rounds`, `clause_flip_ceil` (new) | Exact |
| I-15 | Remark after `lem:clause_flip` | locality alone gives no T ≥ k | `PartILocality.parallel_flips` (new) | Exact |
| I-16 | Conj. `conj:wcc_depth` | every uniform discrete WCC decider of 3-SAT is superpolynomial i.o. | `PartISeparation.WCCDepth` (statement) | Open (≡ 3-SAT ∉ P) |
| I-17 | "precisely as difficult as P≠NP via 3-SAT ∉ P" | conj(L) ⟺ L ∉ P | `PartISeparation.WCCDepth_iff_not_P_TM`, `WCCDDepth_iff_not_P_TM` (new) | Exact |
| I-18 | Prop. `prop:internal_sep_conditional` | conj ⇒ L* ∈ NP_WCC\P_WCC, P_WCC ⊊ NP_WCC | `PartISeparation.internal_sep_conditional`, `internal_sep_SAT` (new) | Exact (L* = dense CNF-SAT; 3-CNF restriction not encoded) |
| I-19 | "any proof of conj would yield P≠NP" | conj ⇒ P≠NP | `internal_sep_conditional` (3rd component) | Exact |
| I-20 | Conj. "Dimensional-Lock Hypothesis (Physical)" §7 | K(ψ*) > poly ∧ slow descent ⇒ ψ* ∈ NP^phys\P^phys | `PartISeparation.high_K_not_poly_witness` (new) | Refuted (hypothesis (1) forces \|ψ*\| > every polynomial bound q, so ψ* is no polynomial-size witness) |
| I-21 | Prop. `thm:separator_curvature` | substitution of two lower bounds | `conditional_interface_bound` | Exact |
| I-22 | Prop. `thm:mass_complexity` | T ≥ (C_T − C_0)_+/Δ_max | `ManuscriptRemarks.valid_telescoping` (new), `telescoping_bound` | Exact (the manuscript's quotient form) |
| I-23 | Prop. `thm:padding_stability` + remark | additive padding with zero padding energy; superlinear padding loses 2^{Ω(N)} | `ManuscriptRemarks.padding_stability`, `superlinear_padding` (new) | Exact (functional = integral of a local density, no interface term) |
| I-24 | Prop. `thm:np-type-conditional` | verifier ∧ no decider ⇒ L ∈ NP^phys\P^phys | `PartISeparation.np_type_conditional` (new) | Exact |
| I-25 | Prop. "Model-Relative Separation in Ideal WCC" §8.4 | state-level separation; + P^∞=P, NP^∞=NP ⇒ P≠NP | `conditional_symbolic_separation`; `state_separation_not_language_separation` (new) | Refuted (the state-to-language step: a verifiable unreachable state exists in a model whose language classes are equal) |
| I-26 | Prop. "Formal Model-Theoretic Separation in WCT" §9.4 | family in NP_WCT\P_WCT ⇒ P_WCT≠NP_WCT ⇒ (with identifications) P≠NP | same | Refuted (same step) |
| I-27 | Prop. "Conditional Turing Reduction Template" §10.4 | ... ⇒ L ∈ NP\P | `PartISeparation.accepted_language_not_in_NP_diff_P` (new) | Refuted (under hyp. (2) the accepted language is in P) |
| I-28 | §11.2 "Universal scope" | ∀M ∃ instance whose solution M misses ⇒ ψ* ∉ P ⇒ P≠NP | `PartISeparation.universal_scope_counterexample` (new) | Refuted (holds for a language in P) |
| I-29 | App. A Prop. "Uniform symbolic verification" | 𝟏{E_logic[a]=0} decidable in poly time | `PartIPsiSat.uniform_symbolic_verification` (new), `SATV.V_SAT_mem_P_TM` | Exact (the "≤ 3m literal checks" count is algorithm-specific, not formalized) |
| I-30 | App. A.2–A.3 limitation statements | verifier efficiency / diagonalization give no NP\P language | `universal_scope_counterexample` | Exact |
| I-31 | Hyp. `lem:separator-price` | uniform interface price | — | Open (hypothesis) |
| I-32 | Hyp. `prop:locked-expander-full` | encoding-uniform interface growth 2^{γn} | — | Open (hypothesis; Part III WIN-18) |
| I-33 | Prop. `lem:lower` | the two hypotheses ⇒ C_Θ(L,n) ≥ κ₀c₀2^{γn} | `PartISeparation.conditional_product_lower_bound` (new) | Exact |
| I-34 | Remark WIN-06 | direct clause evaluation needs no enumeration | `SATV.V_SAT_mem_P_TM`, `uniform_symbolic_verification` | Exact |
| I-35 | Prop. `cor:P-neq-NP-conditional` (1) | same-class identifications ⇒ separation gives P≠NP | `conditional_bridge_WCC/WCCD` (new) | Exact |
| I-36 | Prop. `cor:P-neq-NP-conditional` (2) | restricted separation does not give P≠NP | `PartISeparation.restricted_separation_schema_iff` (new) | Exact (the schema is equivalent to P≠NP) |
| I-37 | §12.3 "nonexistence of a toroidal locking configuration ⟺ unsatisfiability" | informal | — | Open (not well posed) |
| I-38 | Thm. `thm:P-equivalence` | P^disc_WCC = P | `P_WCC_eq_P_TM`, `P_WCCR_eq_P_TM`, `P_WCCD_eq_P_TM` | Restricted (fixed origin-marked encoding; 1-D any radius, ℤ^(1+d) radius one; the manuscript allows radius r in ℤ^d and poly-time enc/readout) |
| I-39 | Thm. `thm:NP-equivalence` | NP^disc_WCC = NP | `NP_WCC_eq_NP_TM`, `NP_WCCR_eq_NP_TM`, `NP_WCCD_eq_NP_TM` | Restricted (same gaps) |
| I-40 | Thm. `thm:supplied-assignment-in-P` | L* (uniform F_n) ∈ P; explicit (F,a) ∈ P | `SATV.V_SAT_mem_P_TM` (explicit version) | Exact for explicit (F,a); uniform-family version needs TM composition (counted Exact for the explicit claim) |
| I-41 | Prop. `thm:curv-bdd-sep` + remark | conditional physical separation; fixed-n impossibility | `PartISeparation.curv_bdd_sep`, `fixed_n_impossible` (new) | Exact |

Counts:
* Exact (24): I-1, 4, 5, 6, 7, 8, 9, 14, 15, 17, 18, 19, 21, 22, 23, 24, 29, 30, 33, 34, 35, 36,
  40, 41.
* Restricted (3): I-11, 38, 39.
* Refuted (8): I-10, 12, 13, 20, 25, 26, 27, 28.
* Open (6): I-2, 3, 16, 31, 32, 37.

### Status of the Part I separation argument

1. Part I proves the logical skeleton of each separation statement, now kernel-checked: I-1, I-4,
   I-9, I-24, I-33, I-35, I-36 and I-41.
2. Every route to P_WCC ≠ NP_WCC, or to P ≠ NP, passes through one of these premises, none of
   which is proved:
   * Conjecture `conj:wcc_depth`, which is exactly 3-SAT ∉ P_TM (I-17);
   * Hypotheses `lem:separator-price` and `prop:locked-expander-full` (I-31, I-32);
   * the non-constructibility premises of I-1, I-4 and I-20.
3. The state-level routes (I-25 to I-28) contain an invalid inference from state
   non-constructibility to language-class separation. Lean gives counterexamples.
4. The physical-barrier claim (I-12) cannot be established without proving `P_TM ≠ NP_TM`.

## Part II — *Discrete Wave-Constrained Computation and Classical Complexity*

| # | Label | Claim | Lean | Status |
|---|---|---|---|---|
| II-1 | Lemma `lem:precision-stability` | local rule keeps ⌈log₂\|S\|⌉ bits | typing of `WCC.step` | Exact (by construction) |
| II-2 | Prop. `prop:local-tm` | TM transitions realizable by a radius-1 rule (two-phase encoding) | `PartIITwoPhase.two_steps` (new; the manuscript's own S = Γ × (Q' ∪ {⊥}) × {0,1} and phase rules), `TM.toWCC_step_encode` | Exact |
| II-3 | Prop. `prop:deterministic-replay` | trajectory determined by C₀ and U | `WCC.run` is a function | Exact (by construction) |
| II-4 | Thm. `thm:wave-symbol-isomorphism` | quantization compatibility ⇒ exact symbolic update; converse construction | `PartIIManuscript.wave_symbol_forward`, `wave_symbol_converse` (new) | Exact (abstract neighbourhood map; covers the background-extended lattice) |
| II-5 | Remark `rem:wave-symbol-obstruction` | counterexample without compatibility | `PartIIManuscript.compatibility_necessary` (new) | Exact (the manuscript's Z = {−1, ½, 1}) |
| II-6 | Prop. `prop:gandy-wcc` + Cor. | Gandy axioms | `WCC.step` definition | Exact (by construction) |
| II-7 | Lemma `lem:invariant` | two-phase invariant, "for all t ≥ 0" | `PartIITwoPhase.invariant_even`, `invariant_odd`, `invariant_literal_fails` (new) | Refuted (quantifier range only: the head can leave Λ_n after halting; `rightMTM` with the manuscript's L(n) = T_M(n)+n has no head cell at time 2). Corrected statement for all t ≤ L(n), hence all t ≤ T_M(n), proved |
| II-8 | Lemma `lem:one_step` | one TM step = two WCC steps; C_{2t} encodes the TM configuration "for all t ≥ 0" | `PartIITwoPhase.two_steps`, `one_step`, `one_step_of_inWin`, `one_step_literal_fails` (new) | Refuted (quantifier range only, same counterexample). Corrected statement for all t ≤ L(n)+1, and for every t while the head stays in Λ_n, proved |
| II-9 | Lemma `lem:runtime` | acceptance ⟺ q_acc; T_{W_M} = 2T_M; \|Λ_n\| = 2L(n)+1 | `PartIITwoPhase.runtime`, `runtime_accepts`, `card_window` (new) | Exact (first output of dec_M at time exactly 2T_M(x), when T_M(x) ≤ L(n)) |
| II-10 | Thm. `thm:tm_to_wcc` | W_M decides L in time 2T_M ≤ 2cn^k; P_Turing ⊆ P_WCC | `PartIITwoPhase.tm_to_wcc_decides`, `PartIIUniform.P_Turing_subset_P_disc` (new), `TM.toWCC_decides`, `P_TM_subset_P_WCC` | Restricted. Both conclusions are verified: the decision-and-time statement for the author's W_M, and P_Turing ⊆ P^disc in the uniform model of `def:wcc_machine`, via the one-cell machine whose encoder computes the decision bit. Not formalized: that W_M itself is uniform, i.e. that enc_M, dec_M and Λ_n are computable in polynomial time |
| II-11 | Thm. `thm:wcc_to_tm` | P_WCC ⊆ P_Turing | `WCC.toTM_decides`, `WCCR.toTM_decides`, `WCCDSweep.toTM_decides` | Restricted (radius r > 1 in ℤ^d, d ≥ 2, and poly-time enc/dec composition missing) |
| II-12 | Cor. `cor:pwcc_equals_pturing` | P_WCC = P_Turing | `P_WCC_eq_P_TM`, …; `PartIITuring.P_Turing_eq_P_TM` (new, corrected def:pturing) | Restricted (repository WCC models; uniform model not formalized; with the literal def:pturing the right side is {∅, Σ*}, see II-17) |
| II-13 | Thm. `thm:np_equiv` | NP_WCC = NP_Turing | `NP_WCC_eq_NP_TM`, …; `PartIITuring.NP_Turing_eq_NP_TM` (new) | Restricted (repository WCC models; uniform model not formalized) |
| II-14 | Lemma `lem:verifier-encoding` | preservation of verifier outcomes | `TM.toWCC_decides` on `pair x w` | Exact |
| II-15 | Thm. `thm:uniform-discrete-bijection` | P, NP equalities | as II-12/13 | Restricted |
| II-16 | Prop. `prop:conditional-classical-lift` | L ∈ NP^disc\P^disc ⇒ P≠NP | `p_vs_np_discrete_transfer` | Exact |
| II-17 | Def. `def:pturing` (T_M(n) ≤ cn^k for all n, c,k ≥ 1) as the classical class P | the manuscript's P_Turing is P | `PartIITuring.P_Turing_lit_eq`, `P_Turing_lit_ne_P_TM`, `P_Turing_lit_ne_NP_Turing`, `P_Turing_eq_P_TM` (new) | Refuted (literal: n = 0 forces T_M(0) = 0, so P_Turing^lit = {∅, Σ*}; literally then P_Turing ≠ NP_Turing, a meaningless artefact). Corrected bound c·max(n,1)^k: P_Turing = P_TM proved, via explicit simulations in both directions (manuscript TM: total δ, moves L/R, q_acc/q_rej) |
| II-18 | Lemma `lem:bandlimit` | k_eff ≤ C₁E_max/(ħc); conditional k_max bound | `PartIIManuscript.bandlimit_eff`, `bandlimit_sharp` (new) | Exact (physical identities as explicit hypotheses, as in the manuscript) |
| II-19 | Lemma `lem:spatial_capacity` | N_lanes ≤ C₂Vk_max³ | `PartIIManuscript.spatial_capacity`, `spatial_capacity_energy` (new) | Exact (periodic cube of side ℓ, explicit C₂ = 27/(8π³); genuine lattice-point count) |
| II-20 | Lemma `lem:lane_update_bound` | ≤ Tck_max/C₃ transitions per lane | `PartIIManuscript.lane_update_bound` (new) | Exact |
| II-21 | Thm. `thm:spacetime_capacity` | N_updates ≤ C₄VTk_max⁴ ≤ KVTE⁴ | `PartIIManuscript.spacetime_capacity` (new) | Exact (C₄ = C₂c/C₃, K = C₄C₁⁴/(ħc)⁴; independent-lane premise explicit) |
| II-22 | Thm. `thm:channel_capacity` | restatement | `PartIIManuscript.spacetime_capacity` (new) | Exact |
| II-23 | Prop. `prop:phys_step_ceiling` | N_updates(n) ≤ C'n^d; T_W polynomial | `PartIIManuscript.phys_step_ceiling`, `rounds_le_events` (new) | Exact (C' = KC_VC_TC_E⁴, d = a+b+4c; T_W ≤ N_updates + 1 under the counting premise) |
| II-24 | Thm. `thm:conditional_np_safety` | (i)–(iii) ⇒ no poly-resource WCT AGI decides an NP-complete L | — | Open (needs Cook–Levin (CL-1) and closure of P_TM under finite modification) |
| II-25 | Remark `rem:compatibility` and the Part II formal-status paragraph | encoder triviality statements | `unrestricted_encoder_trivializes_WCC`, `advice_bit_trivializes`, `P_WCC_enc_id` | Exact |
| II-26 | Formal-status paragraph: "P^disc = P also for the trivial reason that a poly-time encoder can compute the answer" | P_TM ⊆ P^disc via encoder | `PartIIUniform.P_TM_subset_P_disc`, `MTM.answerWriter`, `answerWriter_outputs` (new; uniform model `UWCC`, `FP`) | Exact for the inclusion P_TM ⊆ P^disc. The trivial reason gives only this inclusion; the reverse inclusion P^disc ⊆ P_TM needs the simulation of `thm:wcc_to_tm` and is not formalized for the uniform model |
| II-27 | Remark `rem:poly_resources` | poly resources ⇒ poly updates | `PartIIManuscript.phys_step_ceiling` (new) | Exact |
| II-28 | Defs. `def:tm_verifier`, `def:npturing` vs Lean `NP_TM` | the manuscript's verifier class is NP | `PartIITuring.NP_Turing_eq_NP_TM`, `MTM.guard` (new) | Exact (binary input and witness alphabets, pair format `pair`; time bound p(\|x\|+\|y\|) required only on well-formed pairs, as in the manuscript) |

Counts:
* Exact (19): II-1, 2, 3, 4, 5, 6, 9, 14, 16, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28.
* Restricted (5): II-10, 11, 12, 13, 15.
* Refuted (3): II-7, 8, 17. In each, only the literal quantifier or boundary case fails; the
  corrected statement is proved.
* Open (1): II-24.

### Status of the Part II correspondence

1. **Machine models.**
   * The manuscript's Turing machine (`def:tm`) is formalized as `PartIITuring.MTM`, and
     simulations in both directions connect it to the repository model.
   * Its literal `def:pturing` is degenerate (II-17). With the boundary case corrected,
     `P_Turing = P_TM` and `NP_Turing = NP_TM` (II-28).
2. **The author's construction.** The two-phase simulation `W_M` (`def:local_state`, `def:wm`)
   is formalized as written: alphabet, phase rules in the manuscript's order, finite window
   with background, `enc_M` and `dec_M`. Lemmas `prop:local-tm`, `lem:one_step`,
   `lem:invariant` and `lem:runtime` are proved, the first two on their correct range.
3. **The uniform model** (`def:wcc_machine`) is formalized as `PartIIUniform.UWCC`.
   * Poly-time computable functions (`FP`) are those computed by the manuscript's own Turing
     machine.
   * Its lattice description is the box bitmap with margin `r`; its configuration code lists
     member states in flattened order.
   * `P_TM ⊆ P^disc` is proved (II-26).
4. **What remains** is the inclusion `P^disc ⊆ P_TM` for the uniform model. It needs a
   Turing-machine simulation of the radius-`r` rule on canonical codes over `ℤ^d`, composed with
   the encoder and the decoder. It would complete II-10 to II-13, II-15, I-11, I-38, I-39 and
   III-6. II-24 additionally needs an NP-complete language (Cook–Levin).

## Part III — *Classical Complexity and Curvature-Bounded Physical Computation*

| # | Label | Claim | Lean | Status |
|---|---|---|---|---|
| III-1 | Prop. `prop:zero_cost` | distinct H¹ states, zero curvature cost | `PartIIIAnalytic.zero_cost_counterexample` | Exact |
| III-2 | Remark WIN-12 | original lemma false | same | Exact |
| III-3 | Prop. "Conditional additive storage" | E_store ≥ nc₀ | `conditional_additive_storage` | Exact |
| III-4 | Lemma `lem:h2bound` | C_Θ ≤ ‖Δψ‖²/(4ε²) | `PartIIIAnalytic.curvature_cost_le` | Exact |
| III-5 | Remark WIN-13 | ψ=−ε violates \|ψ+ε\| ≥ ε | `ManuscriptRemarks.win13_counterexample` (new) | Exact |
| III-6 | Thm. `thm:disc-equiv` | P^disc=P, NP^disc=NP | as II-12/13 | Restricted |
| III-7 | Thm. `thm:p-in-np` | P^phys ⊆ NP^phys when verifiers may ignore witnesses | `ManuscriptRemarks.p_in_np_phys` (new), `P_TM_subset_NP_TM`, `P_WCC_subset_NP_WCC` | Exact (any model whose verifiers may ignore witnesses under the same rails) |
| III-8 | Remark WIN-16 | NP^phys = ∅ contradicts nonempty P^phys | `ManuscriptRemarks.win16` (new) | Exact |
| III-9 | Prop. "No logical conflict" | inclusions compatible with = and ≠ | `inclusions_do_not_determine` | Exact |
| III-10 | Remark WIN-17 | classical P vs NP is well posed | `classical_question_well_posed` | Exact |
| III-11 | Prop. `prop:interface` | C_Θ ≥ κA_n | `conditional_interface_bound` | Exact |
| III-12 | Prop. `prop:assignment-P` | L_check ∈ P | `SATV.V_SAT_mem_P_TM` (all CNF, dense encoding) | Exact (counted; the 3-CNF format check is a sublanguage) |
| III-13 | Thm. `thm:constructibility` | C_T ≤ p₀ + p_T K | `telescoping_bound` | Exact |
| III-14 | Remarks §7 (ECT) | P=NP ⇏ physical equality; physical separation ⇏ classical | `restricted_separation_schema_iff`, `inclusions_do_not_determine` | Exact |
| III-15 | Prop. `prop:highfreq` | high-frequency counterexample on (0,2π)³ | `PartIIIHighFreq3D.cube_gradient_energy`, `cube_curvature_lower` | Exact |
| III-16 | Thm. `thm:capacity` | uniform H² ⇒ C_Θ ≤ q²/(4ε²) | `PartIIIAnalytic.capacity_law` | Exact |
| III-17 | Lemma `lem:boundary_variation` | B→ = 2ⁿVar, B_und = 2ⁿ⁻¹Var | `directed_boundary_eq` | Exact |
| III-18 | Thm. `thm:influence` | 0 ≤ Var ≤ n | `variation_class_vacuous` | Exact |
| III-19 | Cor. `cor:var` | P_var is vacuous | `variation_class_vacuous` | Exact |
| III-20 | Remark WIN-21 | parity: Var=n, B→=n2ⁿ | `parity_total_influence`, `parity_directed_boundary` | Exact |
| III-21 | Decoder-uniformity paragraph | fixed sign code, unrestricted decoder | `DecoderUniformity.*` | Exact |
| III-22 | §8 arrow-of-time remark | no equivalence with retrocausality | — | Open (no mathematical content to formalize) |

Counts:
* Exact (20): III-1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21.
* Restricted (1): III-6.
* Open (1): III-22.

## Smallest missing lemmas (for the P-versus-NP conclusion)

* **Discrete route.** `conj:wcc_depth`, which is equivalent in Lean to `3-SAT ∉ P_TM`. This is the
  classical open problem itself.
* **Physical route.**
  * Hypotheses `lem:separator-price` and `prop:locked-expander-full`, for every admissible
    decider;
  * a physical-to-discrete class identification.

  Even with both, `physical_SAT_lower_bound_is_classical` shows that a physical SAT lower bound
  under poly-time encoders already implies `P_TM ≠ NP_TM`.
* **State-level routes.** Not repairable as stated. A language-level formulation (I-9, I-24,
  I-41) is required, and these reduce to the two items above.
