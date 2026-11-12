# Manuscript-to-Lean inventory (Parts I–III), live checklist

Started 5 November 2026. The source of truth is the three manuscripts in
`pvnp/papers/*/main.tex` (October 27 source, with Part I I-10/I-12/I-13/I-20 and Part II II-7/II-8/II-17 corrections on November 6, 2026), read in full. Each mathematically
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
| Part I | 41 | 30 | 1 | 4 | 6 |
| Part II | 28 | 28 | 0 | 0 | 0 |
| Part III | 22 | 21 | 0 | 0 | 1 |
| **Total** | **91** | **79** | **1** | **4** | **7** |

* Exact verification coverage for the amended manuscripts = Exact / Total = 79/91 ≈ 86.8% (78/91 before II-10, 77/91 before II-24, 75/91 after I-10/I-13, 73/91 after II-7/II-8/II-17, 70/91 original).
* Status conclusively determined by a proof or a counterexample (Exact + Refuted) = 83/91 ≈ 91.2%.
* **Phase XVIII, II-10 at its original scope (12 November 2026):** the actual machines `windowMTM p` and `inputMTM M p` are proved to write `originalWindowCode p x` and `originalInputCode M p x` at their first halt within explicit polynomial transition bounds, for every polynomial `p`, machine `M` and input. Both `FP` hypotheses of the original uniform machine are therefore theorems, and II-10 is Exact. The exact-head gate `scripts/verify_ii10_original_wm.sh` passed on commit `df8824c` (Lean 4.23.0, 7,386 jobs, 627 audited declarations). See `pvnp/proofs/II10_VERIFICATION_LEDGER.md`.
* **Provenance:** The original October 27 manuscript inventory was 70 Exact, 2 Restricted, 11 Refuted, 8 Open. Claims II-7, II-8 and II-17 were false as written in that version. Their original Lean counterexamples remain in the repository. In the amended manuscript, their statements are restricted/corrected to match the already-proved Lean theorems; the historical count is not retroactively overwritten.
* **I-12/I-20 scope:** I-12 now states an exact **conditional counterargument** in the frozen WCT submodel with charged polynomial-time indicator encoders: under the *hypothetical* P_TM = NP_TM, dense SAT is implementable; an unconditional barrier in that submodel would imply P_TM != NP_TM. This does not prove either equality or inequality. I-20 now states the proved **explicit-state description-size obstruction** K_D(s) <= |s|+c. A separate physical cost model distinguishes preparation from verification of a *succinct* certificate and from decision; its claimed lower-bound premises remain open, and the original state-as-short-witness inference is withdrawn.
* **I-10/I-13 scope:** I-10 is now a new *conditional* obstruction to exact nonconstant symbolic readouts under an explicit common-successor transition-relation hypothesis. Curvature collapse is **not** proved to imply this hypothesis. The original language triviality and unique-rule non-identifiability assertions are no longer claimed as theorems. I-13 now states the quiescent finite-support bound already proved in Lean. All original counterexamples are preserved.
* Milestone history:
  * Milestone 1 (PR #27): 44 Exact, 8 Refuted.
  * Milestone 2 (PR #28): adds I-8, I-22, I-23, II-4, II-5, II-18 to II-23, II-27, III-5, III-7
    and III-8.
  * Milestone 3 (PR #30): adds the manuscript's Turing-machine model and two-phase
    construction (II-2, II-7, II-8, II-9, II-17, new row II-28).
  * Milestone 4: adds the uniform model of `def:wcc_machine` and `P_TM ⊆ P^disc` (II-26).
  * Milestone 5 (5 November 2026): adds the reverse simulation for the uniform model,
    `P^disc ⊆ P_TM`, hence `P_disc_eq_P_TM`, and the uniform verifier class with
    `NP_disc_eq_NP_TM` (`PVNP.PartIIUniformEquiv`, simulator `PVNP.UniformSim*`). Upgrades
    I-38, I-39, II-11, II-12, II-13, II-15 and III-6 to Exact; I-11 and II-10 stay Restricted.
  * Manuscript correction (6 November 2026): II-7, II-8 and II-17 now match the existing corrected Lean statements.
  * Part I correction (6 November 2026): I-10 is re-scoped to a conditional common-successor theorem with a new Lean proof; I-13 now matches the existing quiescent finite-support bound. Neither proves WCT-induced mixing nor complexity-class separation.
  * Phase XVIII (12 November 2026, PR #73): II-10 moves from Restricted to Exact. The original polynomial-radius window and input writers are verified as polynomial-time single-tape transducers (`PVNP.TwoPhasePolynomialExec`, `State`, `Program`, `Outputs`, `FP`), which removes the two writer hypotheses of `thm:tm_to_wcc`.
  * Part I computational-model clarification (6 November 2026): I-12 is replaced with the previously kernel-proved conditional charged-encoder compatibility statement; I-20 is replaced by the existing explicit-state description-length obstruction, with preparation and certificate verification separated. Original counterarguments remain in Lean.

**What the "Exact" count does not mean.** It includes conditional propositions whose
implications are verified while their premises remain open, for example
`prop:internal_sep_conditional`, whose premise is `conj:wcc_depth`. No exact entry asserts
classical `P ≠ NP`.

## Part I — *P vs NP in Curvature-Bounded Wave Computation*

| # | Label / location | Claim (short) | Lean | Status |
|---|---|---|---|---|
| I-1 | Prop. "Curvature-Confinement Complexity Schema" §2.2 | (1) C(ψ*) above every poly-time bound + (2) verifiable ⇒ ψ* ∈ NP\P (states) | `PartISeparation.complexity_schema` (new) | Exact; premise (1) open |
| I-2 | Conj. "Symbolic Separation Program" §4 | ∃ verifiable non-constructible ψ* under WCT rails | — | Open (conjecture) |
| I-3 | §2.3/§4.1 phase-locking criterion "SAT ⟺ ∃xᵢ: ∇φ→0, \|ψ\|²→max" | informal limits, encoding unspecified | `PartIPsiSat.roundPhase_satisfies`, `PartIPsiSat.eventually_satisfies_of_energy_tendsto`, `PhaseLockScope.bare_phase_lock_not_sat` | Open. Logical energy below 1/8 certifies a rounded witness. The manuscript still needs formula-dependent dynamics, initial conditions and a readout theorem. |
| I-4 | Thm. "Conditional Symbolic Separation" §4.2 | verifiable ∧ not constructible ⇒ ψ* ∈ NP\P, P≠NP (states) | `PartISeparation.conditional_symbolic_separation` (new) | Exact; premise (2) open |
| I-5 | "Conditional Classical Corollary" §4.4 | TM⇄WCC^∞ ⇒ P^∞=P, NP^∞=NP; separation ⇒ P≠NP | `P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM`, `p_vs_np_discrete_transfer`, `PartISeparation.conditional_bridge_WCC/WCCD` (new) | Exact (premises proved for the discrete model) |
| I-6 | Thm. `thm:psi-sat-completeness` §5.4 | 3-CNF F sat ⟺ ∃ binary-phase ψ, E_logic=0 ⟺ ∃ nonzero-amplitude ψ, E_logic=0 | `PartIPsiSat.psi_sat_completeness`, `psi_sat_completeness_field` (new) | Exact |
| I-7 | Remark WIN-03 | E_logic=0 ⇏ δ(E_geom+λE_logic)=0 | `PartIPsiSat.zero_penalty_not_stationary` (new) | Exact |
| I-8 | Prop. WIN-04 `lem:dim-lock` | Gaussian on ℝ⁴ has finite ‖∇ψ‖² and ‖Θ_ε‖² | `PartIDimLock.win04_gaussian`, `laplacian_ψ` (new) | Exact (Mathlib's Laplacian; Δψ = (4‖x‖²−8)e^{−‖x‖²} proved; integrability of ψ, ‖∇ψ‖², Θ_ε² for every ε > 0, α ≥ 0) |
| I-9 | Prop. WIN-05 `thm:pwcc-neq-npwcc` | verifier + every decider exceeds a rail i.o. ⇒ P^phys≠NP^phys | `PartISeparation.win05` (new) | Exact |
| I-10 | Prop. `prop:collapse-grammar` (amended) | Under common-successor mixing of an observable transition relation, no nonconstant symbolic readout is invariant on every allowed transition | `PartISeparation.invariant_constant_of_common_successor`, `no_nontrivial_invariant_of_common_successor`; original `trivial_partition_invariant` preserved | Exact (conditional on an **unproved** observable mixing hypothesis). Original curvature ⇒ collapse, language triviality, and rule non-identifiability are not derived or counted as verified |
| I-11 | Remark `rem:infinite-compute` | within the rail, P_WCC = P_Turing | `P_WCC_eq_P_TM`; `PartIIUniform.P_disc_eq_P_TM` (new), `PhysicalAudit.unrestricted_phys_ne_P_TM` | Restricted. The discrete uniform equality is exact. The constant-field class with arbitrary encoders contains a diagonal language outside P_TM. Charged physical encoders, robust measurement and polynomial numerical simulation still require a bridge. |
| I-12 | Prop. `prop:charged-encoder-barrier` (amended) | In the charged polynomial-time indicator-encoder frozen WCT model, P_TM = NP_TM implies dense SAT has an admissible constant-evolution-cost implementation; any barrier forbidding it even in that case entails P_TM != NP_TM | `PartISeparation.PNP_SAT_physically_constant`, `category_error_claim_implies_classical`, `PhysicalAudit.PhysConst_polyEnc_eq_P_TM` | Exact **conditional implication in the explicitly restricted model**. The hypothetical equality is NOT proved, no universal WCT physical barrier is established, and the encoder computation remains charged |
| I-13 | Lemma `lem:local_growth` (amended) | Quiescent radius-r local updates, finite initial support: supp(C_t) ⊆ supp(C_0)^{+rt} and |supp C_t| ≤ |supp C_0|(2rt+1)^d | `PartILocality.supp_step_subset`, `supp_iterate_subset`, `support_poly_bound`; original `local_growth_needs_quiescence`, `linear_growth_false_d2` preserved | Exact (amended assumptions and dimension-dependent bound); locality alone does not imply superpolynomial time |
| I-14 | Lemma `lem:clause_flip` | local signature change needs local activity; k ≤ Tb | `PartILocality.clause_flip_local`, `clause_flip_rounds`, `clause_flip_ceil` (new) | Exact |
| I-15 | Remark after `lem:clause_flip` | locality alone gives no T ≥ k | `PartILocality.parallel_flips` (new) | Exact |
| I-16 | Conj. `conj:wcc_depth` | every uniform discrete WCC decider of 3-SAT is superpolynomial i.o. | `PartISeparation.WCCDepth` (statement), `CrossingSATMatrix.quadratic_every_budget`, `FiniteHorizon.fast_through_horizon` | Open. For every sufficiently large budget H and every fixed correct one-tape decider there is a rejected input of length at most H requiring quadratic time in H. Superpolynomial time for one fixed machine remains open. |
| I-17 | "precisely as difficult as P≠NP via 3-SAT ∉ P" | conj(L) ⟺ L ∉ P | `PartISeparation.WCCDepth_iff_not_P_TM`, `WCCDDepth_iff_not_P_TM` (new) | Exact |
| I-18 | Prop. `prop:internal_sep_conditional` | conj ⇒ L* ∈ NP_WCC\P_WCC, P_WCC ⊊ NP_WCC | `PartISeparation.internal_sep_conditional`, `internal_sep_SAT` (new) | Exact (L* = dense CNF-SAT; 3-CNF restriction not encoded) |
| I-19 | "any proof of conj would yield P≠NP" | conj ⇒ P≠NP | `internal_sep_conditional` (3rd component) | Exact |
| I-20 | Prop. `prop:explicit-state-witness-size` (amended; original dimensional-lock conjecture withdrawn) | With literal-description overhead c, K_D(s) <= |s|+c; if K_D(s)>q(n)+c, then the explicit state s is longer than the witness budget q(n) | `PartISeparation.Kc_le`, `high_K_not_poly_witness` (original incompatibility proof preserved) | Exact **negative size obstruction**, not a construction lower bound or physical NP/P separation. The separate succinct-certificate verification and universal-decider lower-bound program remains open |
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
| I-31 | Hyp. `lem:separator-price` | uniform interface price | `SeparatorPrice.mesh_price`, `SeparatorPrice.contrast_of_readout`, `SeparatorPrice.binary_cut_price` | Open. Verified for mesh faces with a fixed readout contrast and on a two-level graph rail. A uniform price for the physical trajectory class remains open. |
| I-32 | Hyp. `prop:locked-expander-full` | encoding-uniform interface growth 2^{γn} | `SeparatorPrice.binary_cut_price`, `CurvatureBarrier.graphStorageCost_le_n_mul_d_sq` | Open. Bounded-degree binary graph storage costs at most a constant times the cut size. Every-decider exponential growth still needs an independent theorem. |
| I-33 | Prop. `lem:lower` | the two hypotheses ⇒ C_Θ(L,n) ≥ κ₀c₀2^{γn} | `PartISeparation.conditional_product_lower_bound` (new) | Exact |
| I-34 | Remark WIN-06 | direct clause evaluation needs no enumeration | `SATV.V_SAT_mem_P_TM`, `uniform_symbolic_verification` | Exact |
| I-35 | Prop. `cor:P-neq-NP-conditional` (1) | same-class identifications ⇒ separation gives P≠NP | `conditional_bridge_WCC/WCCD` (new) | Exact |
| I-36 | Prop. `cor:P-neq-NP-conditional` (2) | restricted separation does not give P≠NP | `PartISeparation.restricted_separation_schema_iff` (new) | Exact (the schema is equivalent to P≠NP) |
| I-37 | §12.3 "nonexistence of a toroidal locking configuration ⟺ unsatisfiability" | informal | `ToroidalDiagonal.even_encRing_mem_SAT`, `ToroidalDiagonal.odd_encRing_not_SAT` | Open. Both seam signs are settled for the finite equality ring. An arbitrary-formula map to physical toroidal locks and both directions of the readout are missing. |
| I-38 | Thm. `thm:P-equivalence` | P^disc_WCC = P | `PartIIUniform.P_disc_eq_P_TM` (new); also `P_WCC_eq_P_TM`, `P_WCCR_eq_P_TM`, `P_WCCD_eq_P_TM` | Exact (uniform model `PartIIUniform.UWCC`: any d ≥ 1 and radius r ≥ 0, poly-time lattice algorithm, encoder and readout, all charged) |
| I-39 | Thm. `thm:NP-equivalence` | NP^disc_WCC = NP | `PartIIUniform.NP_disc_eq_NP_TM` (new); also `NP_WCC_eq_NP_TM`, `NP_WCCR_eq_NP_TM`, `NP_WCCD_eq_NP_TM` | Exact (polynomial-size witness strings, uniform poly-time WCC verifiers: `PartIIUniform.NP_disc`) |
| I-40 | Thm. `thm:supplied-assignment-in-P` | L* (uniform F_n) ∈ P; explicit (F,a) ∈ P | `SATV.V_SAT_mem_P_TM` (explicit version) | Exact for explicit (F,a); uniform-family version needs TM composition (counted Exact for the explicit claim) |
| I-41 | Prop. `thm:curv-bdd-sep` + remark | conditional physical separation; fixed-n impossibility | `PartISeparation.curv_bdd_sep`, `fixed_n_impossible` (new) | Exact |

Counts:
* Exact (30): I-1, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 29, 30, 33, 34, 35, 36,
  38, 39, 40, 41.
* Restricted (1): I-11.
* Refuted (4): I-25, 26, 27, 28. Original I-10, I-12, I-13 and I-20 counterarguments/counterexamples remain preserved against superseded statements.
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
| II-7 | Lemma `lem:invariant` | two-phase invariant for 0 ≤ t ≤ L(n), including all t ≤ T_M(n) | `PartIITwoPhase.invariant_even`, `invariant_odd`; historical counterexample `invariant_literal_fails` | Exact (amended statement); original “all t ≥ 0” refuted by `rightMTM` when the head leaves Λ_n |
| II-8 | Lemma `lem:one_step` | C_{2t} encodes the TM configuration for 0 ≤ t ≤ L(n); the two-step identity holds while the head stays in Λ_n | `PartIITwoPhase.two_steps`, `one_step`, `one_step_of_inWin`; historical counterexample `one_step_literal_fails` | Exact (amended statement); Lean also proves equality of restricted configurations through t ≤ L(n)+1, without head-in-window at the endpoint |
| II-9 | Lemma `lem:runtime` | acceptance ⟺ q_acc; T_{W_M} = 2T_M; \|Λ_n\| = 2L(n)+1 | `PartIITwoPhase.runtime`, `runtime_accepts`, `card_window` (new) | Exact (first output of dec_M at time exactly 2T_M(x), when T_M(x) ≤ L(n)) |
| II-10 | Thm. `thm:tm_to_wcc` | W_M decides L in time 2T_M ≤ 2c·max(n,1)^k; P_Turing ⊆ P_WCC | `PartIITwoPhase.tm_to_wcc_decides`, `TwoPhaseDecoder.decM_fp`, `TwoPhasePolynomialWriter.originalWindowCode_fp`, `TwoPhasePolynomialWriter.originalInputCode_fp`, `TwoPhasePolynomialWriter.originalWM`, `TwoPhasePolynomialWriter.originalWM_first_answer`, `TwoPhasePolynomialWriter.originalWM_decides`, `TwoPhasePolynomialWriter.P_Turing_subset_P_disc_by_original` (Phase XVIII) | Exact. The author's own `W_M` (alphabet, two-phase rule, window `[-L, L]`, encoder, decoder) is a uniform machine of `def:wcc_machine` for every polynomial radius: its lattice writer and its encoder are the actual single-tape machines `windowMTM p` and `inputMTM M p`, which output the canonical codes at their first halt in polynomially many transitions. The first answer of `W_M` appears at update exactly 2T_M(x) whenever T_M(x) ≤ L(\|x\|), and `W_M` itself places every language of P_Turing in P^disc. |
| II-11 | Thm. `thm:wcc_to_tm` | P_WCC ⊆ P_Turing | `PartIIUniform.wcc_to_tm`, `P_disc_subset_P_TM` (new); also `WCC.toTM_decides`, `WCCR.toTM_decides`, `WCCDSweep.toTM_decides` | Exact (uniform model, every d ≥ 1 and r ≥ 0: an explicit single-tape machine M_W, compiled from a sweep program, first answers within q_W(\|x\| + T_W(x) + 1) steps, lattice algorithm, encoder and decoder simulated and charged; P_Turing read with the corrected def:pturing, see II-17) |
| II-12 | Cor. `cor:pwcc_equals_pturing` | P_WCC = P_Turing | `PartIIUniform.P_disc_eq_P_TM` (new), `PartIITuring.P_Turing_eq_P_TM` (corrected def:pturing) | Exact (uniform model of def:wcc_machine; the original, superseded def:pturing was degenerate, see II-17) |
| II-13 | Thm. `thm:np_equiv` | NP_WCC = NP_Turing | `PartIIUniform.NP_disc_eq_NP_TM` (new), `PartIITuring.NP_Turing_eq_NP_TM` | Exact (verifier class `NP_disc` of def:wcc_verifier with binary alphabets: input word `pair x y`; \|Λ\| ≤ p(N) for \|y\| ≤ q(\|x\|), N = \|x\|+\|y\|; first decision within p(N) on every pair, the runtime scaling of def:tm_verifier; acceptance = first decision 1, the first-output convention of def:pwcc) |
| II-14 | Lemma `lem:verifier-encoding` | preservation of verifier outcomes | `TM.toWCC_decides` on `pair x w` | Exact |
| II-15 | Thm. `thm:uniform-discrete-bijection` | P, NP equalities | `PartIIUniform.P_disc_eq_P_TM`, `NP_disc_eq_NP_TM` (new) | Exact |
| II-16 | Prop. `prop:conditional-classical-lift` | L ∈ NP^disc\P^disc ⇒ P≠NP | `p_vs_np_discrete_transfer` | Exact |
| II-17 | Def. `def:pturing` (T_M(n) ≤ c·max(n,1)^k for all n ≥ 0, c,k ≥ 1) | the amended manuscript's P_Turing is classical P | `PartIITuring.P_Turing_eq_P_TM`; historical counterexamples `P_Turing_lit_eq`, `P_Turing_lit_ne_P_TM`, `P_Turing_lit_ne_NP_Turing` | Exact (amended definition); original cn^k bound forced T_M(0)=0 and degenerated to {∅, Σ*}; the corrected equivalence is proved by explicit simulations |
| II-18 | Lemma `lem:bandlimit` | k_eff ≤ C₁E_max/(ħc); conditional k_max bound | `PartIIManuscript.bandlimit_eff`, `bandlimit_sharp` (new) | Exact (physical identities as explicit hypotheses, as in the manuscript) |
| II-19 | Lemma `lem:spatial_capacity` | N_lanes ≤ C₂Vk_max³ | `PartIIManuscript.spatial_capacity`, `spatial_capacity_energy` (new) | Exact (periodic cube of side ℓ, explicit C₂ = 27/(8π³); genuine lattice-point count) |
| II-20 | Lemma `lem:lane_update_bound` | ≤ Tck_max/C₃ transitions per lane | `PartIIManuscript.lane_update_bound` (new) | Exact |
| II-21 | Thm. `thm:spacetime_capacity` | N_updates ≤ C₄VTk_max⁴ ≤ KVTE⁴ | `PartIIManuscript.spacetime_capacity` (new) | Exact (C₄ = C₂c/C₃, K = C₄C₁⁴/(ħc)⁴; independent-lane premise explicit) |
| II-22 | Thm. `thm:channel_capacity` | restatement | `PartIIManuscript.spacetime_capacity` (new) | Exact |
| II-23 | Prop. `prop:phys_step_ceiling` | N_updates(n) ≤ C'n^d; T_W polynomial | `PartIIManuscript.phys_step_ceiling`, `rounds_le_events` (new) | Exact (C' = KC_VC_TC_E⁴, d = a+b+4c; T_W ≤ N_updates + 1 under the counting premise) |
| II-24 | Thm. `thm:conditional_np_safety` | (i)–(iii) ⇒ no poly-resource WCT AGI decides an NP-complete L | `PartIIManuscript.conditional_np_safety_all`, `PartIIManuscript.conditional_np_safety` | Exact, conditional on the stated polynomial physical resources and capacity, uniform simulation and counted updates, and P_Turing ≠ NP_Turing (#54). |
| II-25 | Remark `rem:compatibility` and the Part II formal-status paragraph | encoder triviality statements | `unrestricted_encoder_trivializes_WCC`, `advice_bit_trivializes`, `P_WCC_enc_id` | Exact |
| II-26 | Formal-status paragraph: "P^disc = P also for the trivial reason that a poly-time encoder can compute the answer" | P_TM ⊆ P^disc via encoder | `PartIIUniform.P_TM_subset_P_disc`, `MTM.answerWriter`, `answerWriter_outputs` (new; uniform model `UWCC`, `FP`) | Exact for the inclusion P_TM ⊆ P^disc. The trivial reason gives only this inclusion; the reverse inclusion P^disc ⊆ P_TM needs the simulation of `thm:wcc_to_tm`, now kernel-checked (II-11) |
| II-27 | Remark `rem:poly_resources` | poly resources ⇒ poly updates | `PartIIManuscript.phys_step_ceiling` (new) | Exact |
| II-28 | Defs. `def:tm_verifier`, `def:npturing` vs Lean `NP_TM` | the manuscript's verifier class is NP | `PartIITuring.NP_Turing_eq_NP_TM`, `MTM.guard` (new) | Exact (binary input and witness alphabets, pair format `pair`; time bound p(\|x\|+\|y\|) required only on well-formed pairs, as in the manuscript) |

Counts:
* Exact (28): II-1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28.
* Restricted (0). II-10 was Restricted until Phase XVIII.
* Refuted (0) in the amended Part II manuscript. Historical refutations (3): II-7, II-8, II-17, retained with their original counterexamples.
* Open (0) in Part II. II-24 verifies an implication with its classical separation premise explicit.

### Status of the Part II correspondence

1. **Machine models.**
   * The manuscript's Turing machine (`def:tm`) is formalized as `PartIITuring.MTM`, and
     simulations in both directions connect it to the repository model.
   * Its original `def:pturing` was degenerate (II-17). With the now-amended boundary case,
     `P_Turing = P_TM` and `NP_Turing = NP_TM` (II-28).
2. **The author's construction.** The two-phase simulation `W_M` (`def:local_state`, `def:wm`)
   is formalized as written: alphabet, phase rules in the manuscript's order, finite window
   with background, `enc_M` and `dec_M`. Lemmas `prop:local-tm`, `lem:one_step`,
   `lem:invariant` and `lem:runtime` are proved with the finite-window ranges now stated in the amended manuscript.
3. **The uniform model** (`def:wcc_machine`) is formalized as `PartIIUniform.UWCC`.
   * Poly-time computable functions (`FP`) are those computed by the manuscript's own Turing
     machine.
   * Its lattice description is the box bitmap with margin `r`; its configuration code lists
     member states in flattened order.
   * `P_TM ⊆ P^disc` is proved (II-26).
   * `P^disc ⊆ P_TM` is proved (Milestone 5, II-11): `PartIIUniform.wcc_to_tm` compiles an
     explicit sweep program (`UniformSim.Spec.prog`) into a single-tape machine. The program runs
     the lattice algorithm, the encoder and the decoder of `W` as simulated manuscript machines,
     parses the box bitmap, loads `C_0`, and per round writes the decoder input
     `1^n 0 cfgCode(C_t)` (`decode_phase`) and computes `C_{t+1} = UWCC.step n C_t` on the box
     (`round_spec`). The windows are gathered by cyclic rotations by
     `δ_v = Σ_k (v_k − r)(2R+1)^k` (`tasks_shift`, `member_nbr`). Hence `P_disc_eq_P_TM` and,
     for the verifier class `NP_disc`, `NP_disc_eq_NP_TM`.
4. **What remains.** Nothing in Part II is Restricted or Open. II-10 is proved for the author's own `W_M`: `TwoPhasePolynomialWriter.originalWindowCode_fp` and `originalInputCode_fp` supply the lattice and encoder witnesses, and `TwoPhaseDecoder.decM_fp` the decoder. II-24 follows under its original premises by #54; its classical separation premise is still open.

## Part III — *Classical Complexity and Curvature-Bounded Physical Computation*

| # | Label | Claim | Lean | Status |
|---|---|---|---|---|
| III-1 | Prop. `prop:zero_cost` | distinct H¹ states, zero curvature cost | `PartIIIAnalytic.zero_cost_counterexample` | Exact |
| III-2 | Remark WIN-12 | original lemma false | same | Exact |
| III-3 | Prop. "Conditional additive storage" | E_store ≥ nc₀ | `conditional_additive_storage` | Exact |
| III-4 | Lemma `lem:h2bound` | C_Θ ≤ ‖Δψ‖²/(4ε²) | `PartIIIAnalytic.curvature_cost_le` | Exact |
| III-5 | Remark WIN-13 | ψ=−ε violates \|ψ+ε\| ≥ ε | `ManuscriptRemarks.win13_counterexample` (new) | Exact |
| III-6 | Thm. `thm:disc-equiv` | P^disc=P, NP^disc=NP | `PartIIUniform.P_disc_eq_P_TM`, `NP_disc_eq_NP_TM` (new) | Exact (uniform finite-state fixed-radius model `UWCC`) |
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
* Exact (21): III-1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21.
* Restricted (0).
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
* **Crossing-sequence route (Phase VIII, 6 November 2026).** Formalized completely for single-tape
  machines: `CrossingHennie.hennie`, `CrossingSAT.diag_mixed`,
  `CrossingSATSets.sat_time_lower_bound_near_sq`. It yields only fixed-polynomial bounds, at most
  `Ω(N²/(log N · log|Λ|))`, which is the ceiling of the method. The missing lemma is
  `CrossingSAT.SATLowerBound` (`SAT_dense ∉ P_TM`). Counts unchanged.
* **Phase IX (6 November 2026).** The decisive premise is now stated in the per-input `∀ M ∃ x`
  form and proved equivalent to `SATLowerBound` and to I-16 `conj:wcc_depth` for `SAT_dense`
  (`SATTarget.satLowerBound_iff_superpolynomial`, `satLowerBound_iff_wccDepth`).
  - Two candidate invariants are refuted as separation routes, by kernel-checked counterexamples:
    - expander/Tseitin instances are decided by component parity
      (`TseitinSAT.tseitin_mem_SAT_dense_iff_comp`);
    - the polynomial-time language `V_SAT` carries quadratic crossing information
      (`VerifierCrossing.crossingInfo_not_superpolynomial`).
  - I-16, I-31 and I-32 remain Open. Counts unchanged.
* **State-level routes.** Not repairable as stated. A language-level formulation (I-9, I-24,
  I-41) is required, and these reduce to the two items above.
