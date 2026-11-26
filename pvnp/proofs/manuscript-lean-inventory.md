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
| **Interpretive** | A manuscript passage kept in the register for traceability that makes no independently quantified mathematical assertion (for example, a remark that states that no equivalence is proved). It is neither a theorem nor an unresolved conjecture, and no proof obligation is attached. |

Lean paths are relative to `lean/`. "(new)" marks declarations added in this pass.

## Coverage table

| Paper | Claims | Exact | Restricted | Refuted | Open | Interpretive |
|---|---|---|---|---|---|---|
| Part I | 41 | 30 | 3 | 5 | 3 | 0 |
| Part II | 28 | 28 | 0 | 0 | 0 | 0 |
| Part III | 22 | 21 | 0 | 0 | 0 | 1 |
| **Total** | **91** | **79** | **3** | **5** | **3** | **1** |

* Exact verification coverage for the amended manuscripts = Exact / Total = 79/91 ≈ 86.8% (80/91 before the Phase XXIII scope correction, 78/91 before II-10, 77/91 before II-24, 75/91 after I-10/I-13, 73/91 after II-7/II-8/II-17, 70/91 original).
* Status conclusively determined by a proof or a counterexample (Exact + Refuted) = 84/91 ≈ 92.3% (85/91 before the Phase XXIII scope correction, 83/91 before I-31).
* The register has 91 entries; 90 are mathematical claims and one (III-22) is Interpretive. Of the 90 mathematical claims, 79 (87.8%) are Exact, 3 Restricted, 5 Refuted and 3 Open. Lean verification coverage is not scientific completion: Exact includes conditional implications whose premises are open, and none of the counts measures progress toward classical P versus NP.
* **Phase XXVII (26 November 2026):** no status change. Exact finite-bit form of the exponential partial sum for rational arguments with polynomial integer sizes, dyadic rounding and an end-to-end relative bound (`ExpTaylorBits`); see `pvnp/proofs/phase-xxvii-bit-complexity.md`. No Turing-machine implementation, nonlinear time-analyticity bound or new separation mechanism; P versus NP remains unresolved.
* **Phase XXVI (26 November 2026):** no status change. The original separation mechanism was re-examined; no valid mechanism was found and classical P versus NP remains unresolved (I-2, I-16, I-32 Open). Each candidate invariant (history depth, time-bounded description complexity, causal interfaces, crossing sequences, compression, finite-horizon uniformity) either reduces to the running time, relativizes, or is a restricted-model bound; see `pvnp/proofs/phase-xxvi-separation.md`. New: `ExpTaylor.taylor_terms_for_precision` (exponential sensitivity is not exponential cost for the linearized sideband flow).
* **Phase XXV (26 November 2026, PR #104):** no status change; I-11 stays Restricted (55% → 65%). Kernel-checked: effective weak-norm Fourier tails, Galerkin mass and Hamiltonian conservation with global existence, a cutoff-independent radius, an end-to-end detector error bound 4 Cdet R_B² e^{LF(R_B)T}/K, a certified rounded Euler envelope, exact finite nonlinear residuals and finite detector sums, and exponential constant-background sideband modes together with a stable regime that has a uniform-in-time bound. See `pvnp/proofs/phase-xxv-finite-residual.md`.
* **Phase XXIV (15 November 2026, PR #98):** no status change. `TorusGalerkin.frozen_galerkin_approximation`: actual frozen-PDE solutions are approximated uniformly in H² on every finite forward interval by trajectories of the finite Fourier (Galerkin) ODE, built with a radius cutoff, Picard–Lindelöf, compactness of the trajectory and Gronwall. The cutoff set is not computable from these proofs, so I-11 stays Restricted at 55%. See `pvnp/proofs/phase-xxiv-progress.md`.
* **Phase XXIII (14 November 2026):** I-37 is Restricted at original scope; the revised reference-component theorem remains proved. New supporting results: `SATDynamics.readout_requires_energy_excursion`, `SATDynamics.bounded_forcing_cannot_readout`, `TorusGalerkin.galerkin_consistent`, `TorusGalerkin.residual_certificate`, `TorusGalerkin.no_uniform_H2_cutoff`. No classical separation or polynomial simulation is proved. See `phase-xxiii-progress.md`.
* **Phase XXII, final six-claim closure (14 November 2026, PRs #95 and this classification PR):** I-37 moves from Restricted to Exact and I-3 from Open to Restricted. I-37 is realized on the spatial torus of the frozen equation (`SpatialLocking.sat_iff_locked`): locks exist iff the formula is satisfiable, they are exact solutions of the frozen flow, and no frozen trajectory approaches one from outside (`SpatialLocking.no_attracting_locks`). I-3: the static criterion and the exhaustive corner device are proved, and energy descent is refuted as a test (`SATDynamics.energy_monotone_trapped`, `SATDynamics.no_corner_preparation_decides`). I-11 stays Restricted (robust readout and the zero-mode class equality are proved; certified simulation of the nonlinear evolution is missing). I-2, I-16 and I-32 stay Open: each reading of I-2 is false, vacuous or exactly `P_TM ≠ NP_TM`, and the non-vacuous reading is equivalent to I-16 and, in the charged constant class, to I-32 (`NonconstructibleFamily.npFamily_iff_wccDepth`, `NonconstructibleFamily.npFamily_iff_expanderGrowth`). See `pvnp/proofs/phase-xxii-six-claim-closure-20261114.md`.
* **Phase XX, interwoven-Ψ SAT and the frozen-torus SAT device (13 November 2026, PRs #90 and this classification PR):** I-37 moves from Open to Restricted and III-22 from Open to Interpretive. With the locking constraints defined on the configuration torus `|ψᵢ| = 1` (clause penalties plus sign-blind coupling and curvature), "no locking configuration ⟺ unsatisfiable" is proved (`InterwovenSAT.toroidal_locking_iff_unsat`); with sign-sensitive coupling it fails (`InterwovenSAT.naive_toroidal_locking_fails`); for any added energy `C ≥ 0` the exact criterion is `InterwovenSAT.locks_iff_sat_iff`. III-22 makes no mathematical assertion (it states that no equivalence is proved). No other status changes: the SAT readout bound on the frozen torus is proved in device form, its initial-blindness hypothesis is necessary (`WCTSATDevice.blindness_necessary`), and a superpolynomial physical-resource bound for SAT over any class containing the charged zero-mode devices is equivalent to, or implies, `P_TM ≠ NP_TM` (`WCTSATScaling.zeroSuperpoly_SAT_iff`, `WCTSATScaling.superpoly_SAT_implies_P_ne_NP`). See `pvnp/proofs/wct-interwoven-sat-program-20261113.md`.
* **Phase XVIII, barriers for the remaining open claims (12 November 2026, PR #79):** no status changes. I-32 is equivalent to P_TM ≠ NP_TM for dense SAT in the charged constant model; I-16 is P_TM ≠ NP_TM in each discrete model; the frozen flow is time-reversible and cannot lock into a stable lock set from outside it (I-37, I-3); the explicit-state reading of I-2 is false; III-22's physical sentence has an exact frozen-model form. See `pvnp/proofs/phase-xviii-barriers.md`.
* **Phase XVIII, I-31 refuted for the frozen trajectory class (12 November 2026):** `lem:separator-price` asks for `Φ(ψ) ≥ κ₀ 𝓗^{d−1}(∂𝓡_ψ)` with `κ₀` independent of the input length. On the torus of side `L_n` the exact plane waves of fixed amplitude keep `Φ` bounded while the interface has length at least `L_n`, so no `κ₀ > 0` works. See `pvnp/proofs/phase-xviii-i31-separator-counterexample.md`.
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
  * Phase XVIII (12 November 2026, PR #78): I-31 moves from Open to Refuted. `PVNP.SeparatorFrozen` gives exact frozen-PDE fields of fixed readout contrast whose curvature functional stays bounded while their decision interface grows linearly with the torus side; the corrected, width-dependent price is proved.
  * Part I computational-model clarification (6 November 2026): I-12 is replaced with the previously kernel-proved conditional charged-encoder compatibility statement; I-20 is replaced by the existing explicit-state description-length obstruction, with preparation and certificate verification separated. Original counterarguments remain in Lean.

**What the "Exact" count does not mean.** It includes conditional propositions whose
implications are verified while their premises remain open, for example
`prop:internal_sep_conditional`, whose premise is `conj:wcc_depth`. No exact entry asserts
classical `P ≠ NP`.

## Part I — *P vs NP in Curvature-Bounded Wave Computation*

| # | Label / location | Claim (short) | Lean | Status |
|---|---|---|---|---|
| I-1 | Prop. "Curvature-Confinement Complexity Schema" §2.2 | (1) C(ψ*) above every poly-time bound + (2) verifiable ⇒ ψ* ∈ NP\P (states) | `PartISeparation.complexity_schema` (new) | Exact; premise (1) open |
| I-2 | Conj. "Symbolic Separation Program" §4 | ∃ verifiable non-constructible ψ* under WCT rails | `NonconstructibleFamily.unrestricted_family_separation`, `NonconstructibleFamily.npFamily_separation_iff`, `NonconstructibleFamily.npFamily_SAT_iff`, `NonconstructibleFamily.wavefield_separation_iff`, `NonconstructibleFamily.npFamily_iff_wccDepth` (Phase XXII); `DepthBarrier.explicit_no_separation`, `DepthBarrier.explicit_state_constructible` (Phase XVIII) | Open (conjecture). The specified formalized readings are false, vacuous or equivalent to the classical separation; other models remain open. Explicit states: false, since a fixed machine of `def:tm` writes any word in \|s\|+1 transitions on every input, so `NPst \ Pst = ∅` for every verifier. Input-indexed families `x ↦ ψ_x` with unrestricted verification: true for the vacuous reason that a diagonal language outside P_TM is verified by the trivial predicate. NP-verified families, and physical wavefield families prepared by charged zero-mode torus devices: `NPst \ Pst ≠ ∅` iff P_TM ≠ NP_TM, which is `conj:wcc_depth` (I-16) for dense SAT. Missing: P_TM ≠ NP_TM. |
| I-3 | §2.3/§4.1 phase-locking criterion "SAT ⟺ ∃xᵢ: ∇φ→0, \|ψ\|²→max" | informal limits, encoding unspecified | `SATDynamics.sat_iff_corner_sweep`, `SATDynamics.energy_monotone_trapped`, `SATDynamics.corner_trapped`, `SATDynamics.no_corner_preparation_decides`, `SATDynamics.efficient_device_and_simulation_imply_P_eq_NP`, `SATFalseWell.signblind_false_local_well` (Phase XXII); `InterwovenSAT.sat_iff_EminSB_eq_zero`, `InterwovenSAT.measure_satisfies`, `InterwovenSAT.naive_Emin`, `InterwovenSAT.satisfying_not_ground` (Phase XX); `PartIPsiSat.roundPhase_satisfies`, `PartIPsiSat.eventually_satisfies_of_energy_tendsto`, `PhaseLockScope.bare_phase_lock_not_sat`, `Torus.no_locking_phaseOrbit`, `Torus.no_locking_realStates` (Phase XVIII) | Restricted (Phase XXII). As a static criterion in the sign-blind interwoven encoding it holds: SAT ⟺ ground energy 0, UNSAT ⟺ ground energy at least 1/8, and the sign readout of any field below 1/8 satisfies the formula; preparing the `2^n` corner fields and reading `E < 1/8` decides SAT for every formula (`sat_iff_corner_sweep`). As a dynamical test it fails: the bare lock (gradient and intensity only) does not detect SAT; with the literal sign-sensitive gradient the satisfiable `F_xor` and the unsatisfiable `G` have the same ground energy 1/4; a satisfiable formula has a false well that traps every energy-nonincreasing evolution of unit fields for all time (`energy_monotone_trapped`), so for every formula-independent corner preparation some satisfiable formula is never read as satisfiable by energy descent (`no_corner_preparation_decides`); the frozen dynamics cannot supply the convergence (time reversibility). Not covered: non-monotone dynamics from formula-dependent polynomial-time preparations. With polynomial resources and a resource-preserving simulation such a device would put SAT in P_TM.  Phase XXIII: `SATDynamics.readout_requires_energy_excursion` requires a peak-energy increase of at least 1/16 for any continuous admissible forced trajectory from the false corner reaching readout; no monotonicity assumption.  `SATDynamics.escape_energy_bound` and `readout_requires_sharp_peak` match at peak 32/25 on the fixed false-well instance; the prescribed path reaches zero energy at time one with zero graph curvature. |
| I-4 | Thm. "Conditional Symbolic Separation" §4.2 | verifiable ∧ not constructible ⇒ ψ* ∈ NP\P, P≠NP (states) | `PartISeparation.conditional_symbolic_separation` (new) | Exact; premise (2) open |
| I-5 | "Conditional Classical Corollary" §4.4 | TM⇄WCC^∞ ⇒ P^∞=P, NP^∞=NP; separation ⇒ P≠NP | `P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM`, `p_vs_np_discrete_transfer`, `PartISeparation.conditional_bridge_WCC/WCCD` (new) | Exact (premises proved for the discrete model) |
| I-6 | Thm. `thm:psi-sat-completeness` §5.4 | 3-CNF F sat ⟺ ∃ binary-phase ψ, E_logic=0 ⟺ ∃ nonzero-amplitude ψ, E_logic=0 | `PartIPsiSat.psi_sat_completeness`, `psi_sat_completeness_field` (new) | Exact |
| I-7 | Remark WIN-03 | E_logic=0 ⇏ δ(E_geom+λE_logic)=0 | `PartIPsiSat.zero_penalty_not_stationary` (new) | Exact |
| I-8 | Prop. WIN-04 `lem:dim-lock` | Gaussian on ℝ⁴ has finite ‖∇ψ‖² and ‖Θ_ε‖² | `PartIDimLock.win04_gaussian`, `laplacian_ψ` (new) | Exact (Mathlib's Laplacian; Δψ = (4‖x‖²−8)e^{−‖x‖²} proved; integrability of ψ, ‖∇ψ‖², Θ_ε² for every ε > 0, α ≥ 0) |
| I-9 | Prop. WIN-05 `thm:pwcc-neq-npwcc` | verifier + every decider exceeds a rail i.o. ⇒ P^phys≠NP^phys | `PartISeparation.win05` (new) | Exact |
| I-10 | Prop. `prop:collapse-grammar` (amended) | Under common-successor mixing of an observable transition relation, no nonconstant symbolic readout is invariant on every allowed transition | `PartISeparation.invariant_constant_of_common_successor`, `no_nontrivial_invariant_of_common_successor`; original `trivial_partition_invariant` preserved | Exact (conditional on an **unproved** observable mixing hypothesis). Original curvature ⇒ collapse, language triviality, and rule non-identifiability are not derived or counted as verified |
| I-11 | Remark `rem:infinite-compute` | within the rail, P_WCC = P_Turing | `P_WCC_eq_P_TM`; `PartIIUniform.P_disc_eq_P_TM` (new), `PhysicalAudit.unrestricted_phys_ne_P_TM`, `WCTSATScaling.superpoly_SAT_implies_P_ne_NP`, `WCTSATScaling.torus_superpoly_implies_P_ne_NP` (Phase XX), `ContinuumPrecision.zeroDev_languages_eq_P_TM`, `ContinuumPrecision.decision_robust`, `ContinuumPrecision.precision_suffices`, `ContinuumPrecision.approx_readout` (Phase XXII), `TorusGalerkin.frozen_galerkin_approximation`, `TorusGalerkin.exists_convergent_galerkin` (Phase XXIV), `TorusGalerkin.weak_projection_tail`, `TorusGalerkin.weak_galerkin_global_error`, `TorusGalerkin.galerkin_conserved`, `TorusGalerkin.exists_certified_galerkin_readout`, `TorusGalerkin.rounded_galerkin_euler`, `SidebandAmplification.actual_field_first_variation`, `SidebandAmplification.stable_sideband_ratio_bound` (Phase XXV), `ExpTaylor.taylor_terms_for_precision`, `ExpTaylor.sideband_growth_taylor` (Phase XXVI), `ExpTaylorBits.partial_sum_eq`, `ExpTaylorBits.num_le_pow`, `ExpTaylorBits.exp_dyadic_approx` (Phase XXVII) | Restricted. The discrete uniform equality is exact. The constant-field class with arbitrary encoders contains a diagonal language outside P_TM. Phase XX: transfer from a physical lower bound to a classical one needs no simulation in any class containing the charged zero-mode torus devices. Phase XXII: that charged class decides exactly P_TM (`zeroDev_languages_eq_P_TM`), and robust measurement is proved: the detector is Lipschitz on bounded sets, and initial data known to precision δ with log(1/δ) = LF·T + log(4RC_χ/m) fix the decision of a margin-m readout at time T (`precision_suffices`); an approximate trajectory with residual ε stays within a Gronwall bound of the solution and fixes the readout (`approx_readout`). Missing: a polynomial-time finite-dimensional scheme with a certified residual (truncation of the solution, time discretization, arithmetic cost) for the full device class.  Phase XXIII: `TorusGalerkin.galerkin_consistent`, `consistency_bound`, `residual_certificate`, `no_uniform_H2_cutoff` establish finite-vector-field consistency and the failure of a uniform H² cutoff from an H² bound alone. No trajectory convergence rate or bit complexity is established. Phase XXIV: for every frozen solution, every T ≥ 0 and every ε > 0 there is an actual trajectory of the finite Fourier (Galerkin) system, started at the truncated data, with uniform H² error below ε on [0, T] (`frozen_galerkin_approximation`). The mode set comes from compactness of the trajectory and is not computed from the data; no rate, time discretization or bit complexity is established. Phase XXV: in the physical L² (weak) norm the detector uses, the Fourier tail is effective, ‖P_S v − v‖ ≤ ‖v‖/K when every omitted weight is at least K (`weak_projection_tail`). The Galerkin flow conserves the PDE's mass and Hamiltonian (`galerkin_conserved`), which gives a cutoff-independent radius R_B from the initial H² bound alone, and the readout error is at most 4 Cdet R_B² e^{LF(R_B)T}/K (`exists_certified_galerkin_readout`). A rounded Euler scheme has an explicit error envelope, given checked per-step update defects (`rounded_galerkin_euler`). The sufficient mode and step counts are polynomial only when LF(R_B)·T = O(log n). The constant-background sideband linearization has genuine exponential modes λ² = −H(H+2c) (`SidebandAmplification`), so this amplification is not a Gronwall artifact; it is a sensitivity, not a proved runtime lower bound. Missing: a formal bit-complexity (Turing-machine) implementation, and any polynomial simulation, or lower bound, outside the logarithmic-amplification regime. Phase XXVI: the exponential sideband sensitivity does not force exponential computation for the linearized flow; ⌈2x⌉ + p + 1 Taylor terms give e^x to relative precision 2^{-p} (`taylor_terms_for_precision`), linear in the growth exponent and the precision bits. The nonlinear time-analyticity radius and propagated spatial decay remain open. Phase XXVII: for x = a/b the partial sum is an exact integer fraction whose numerator and denominator have at most γ + m(β+γ) bits (`num_le_pow`, `den_le_pow`), and p-bit dyadic rounding gives e^x within 2^{1−p}e^x (`exp_dyadic_approx`); no Turing-machine implementation is given. |
| I-12 | Prop. `prop:charged-encoder-barrier` (amended) | In the charged polynomial-time indicator-encoder frozen WCT model, P_TM = NP_TM implies dense SAT has an admissible constant-evolution-cost implementation; any barrier forbidding it even in that case entails P_TM != NP_TM | `PartISeparation.PNP_SAT_physically_constant`, `category_error_claim_implies_classical`, `PhysicalAudit.PhysConst_polyEnc_eq_P_TM` | Exact **conditional implication in the explicitly restricted model**. The hypothetical equality is NOT proved, no universal WCT physical barrier is established, and the encoder computation remains charged |
| I-13 | Lemma `lem:local_growth` (amended) | Quiescent radius-r local updates, finite initial support: supp(C_t) ⊆ supp(C_0)^{+rt} and |supp C_t| ≤ |supp C_0|(2rt+1)^d | `PartILocality.supp_step_subset`, `supp_iterate_subset`, `support_poly_bound`; original `local_growth_needs_quiescence`, `linear_growth_false_d2` preserved | Exact (amended assumptions and dimension-dependent bound); locality alone does not imply superpolynomial time |
| I-14 | Lemma `lem:clause_flip` | local signature change needs local activity; k ≤ Tb | `PartILocality.clause_flip_local`, `clause_flip_rounds`, `clause_flip_ceil` (new) | Exact |
| I-15 | Remark after `lem:clause_flip` | locality alone gives no T ≥ k | `PartILocality.parallel_flips` (new) | Exact |
| I-16 | Conj. `conj:wcc_depth` | every uniform discrete WCC decider of 3-SAT is superpolynomial i.o. | `PartISeparation.WCCDepth` (statement), `PartISeparation.WCCDepth_iff_not_P_TM`, `DepthBarrier.wccDepth_SAT_iff`, `DepthBarrier.wccdDepth_SAT_iff`, `DepthBarrier.uniform_depth_SAT_iff` (Phase XVIII), `CrossingSATMatrix.quadratic_every_budget`, `FiniteHorizon.fast_through_horizon`, `WCTSATScaling.zeroSuperpoly_SAT_iff` (Phase XX), `NonconstructibleFamily.npFamily_iff_wccDepth` (Phase XXII) | Open. For dense SAT the conjecture is exactly P_TM ≠ NP_TM in the radius-one, `ℤ^(1+d)` and uniform models. For every sufficiently large budget H and every fixed correct one-tape decider there is a rejected input of length at most H requiring quadratic time in H. Superpolynomial time for one fixed machine remains open. Phase XX: the same holds for the charged zero-mode devices of the frozen torus model, with machine time, evolution time, curvature budget, mass and inverse margin charged. Phase XXII: equivalent to the NP-verified reading of I-2 (`npFamily_iff_wccDepth`). Diagonalization, crossing sequences (quadratic, one tape), causal-cone bounds (linear) and the physical-resource routes (I-31 refuted; the charged zero-mode class equals P_TM) give no superpolynomial bound, and no route here is shown to avoid the relativization, natural-proofs or algebrization barriers. |
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
| I-31 | Hyp. `lem:separator-price` | uniform interface price | `SeparatorFrozen.no_uniform_separator_price`, `SeparatorFrozen.separator_price_hypothesis_false`, `SeparatorFrozen.no_uniform_price_modulus`, `SeparatorFrozen.stripe_device_violates`, `SeparatorFrozen.layer_price` (Phase XVIII); `SeparatorPrice.mesh_price`, `SeparatorPrice.contrast_of_readout`, `SeparatorPrice.binary_cut_price` | Refuted for the frozen physical trajectory class. On the torus of side L, the exact plane-wave solution of amplitude A (fixed, so the readout contrast is fixed) has Φ = ∫(\|∇ψ\|² + \|Θψ\|²) ≤ 4π²\|A\|² + 16π⁴c²\|A\|²/L² for every curvature operator with \|Θψ\| ≤ c\|Δψ\| (Δ itself, the Θ_ε of Part III), while the Euclidean 𝓗¹ of the frontier of its decision region {Re ψ > 0} is at least L, at every time. Every κ₀ > 0 fails once L is large. The fields are used by an admissible decider (`stripe_device_decides`), and a modulus readout fails in the same way. Corrected statements: a transition of width w costs at least 4η²/w per unit length (`layer_price`, sharp), and the mesh price holds for sharp interfaces. |
| I-32 | Hyp. `prop:locked-expander-full` | encoding-uniform interface growth 2^{γn} | `ExpanderInterface.expanderGrowth_SAT_iff`, `ExpanderInterface.expanderGrowth_implies_P_ne_NP`, `ExpanderInterface.expanderGrowth_const_iff`, `ExpanderInterface.sep_const` (Phase XVIII); `SeparatorPrice.binary_cut_price`, `CurvatureBarrier.graphStorageCost_le_n_mul_d_sq`, `WCTSATScaling.superpoly_SAT_implies_P_ne_NP` (Phase XX); `NonconstructibleFamily.npFamily_iff_expanderGrowth` (Phase XXII) | Open. The charged constant devices of the frozen model have no decision interface. Hence, for dense SAT in the class of charged constant devices, the hypothesis is equivalent to P_TM ≠ NP_TM, and in any device class containing them it implies P_TM ≠ NP_TM; for every language in P_TM it is false. Bounded-degree binary graph storage costs at most a constant times the cut size. Phase XX: any superpolynomial physical-resource lower bound for SAT over such a class implies P_TM ≠ NP_TM. Phase XXII: for dense SAT in the charged constant class it is equivalent to the NP-verified reading of I-2 and to I-16. The manuscript turns interface growth into an energy bound through `lem:separator-price` (I-31), which is refuted for the frozen class, so a proof of I-32 would not by itself give that bound. |
| I-33 | Prop. `lem:lower` | the two hypotheses ⇒ C_Θ(L,n) ≥ κ₀c₀2^{γn} | `PartISeparation.conditional_product_lower_bound` (new) | Exact |
| I-34 | Remark WIN-06 | direct clause evaluation needs no enumeration | `SATV.V_SAT_mem_P_TM`, `uniform_symbolic_verification` | Exact |
| I-35 | Prop. `cor:P-neq-NP-conditional` (1) | same-class identifications ⇒ separation gives P≠NP | `conditional_bridge_WCC/WCCD` (new) | Exact |
| I-36 | Prop. `cor:P-neq-NP-conditional` (2) | restricted separation does not give P≠NP | `PartISeparation.restricted_separation_schema_iff` (new) | Exact (the schema is equivalent to P≠NP) |
| I-37 | §12.3 "nonexistence of a toroidal locking configuration ⟺ unsatisfiability" | informal | `SpatialLocking.sat_iff_locked`, `SpatialLocking.no_locked_iff_unsat`, `SpatialLocking.locked_iff`, `SpatialLocking.locked_frozen_flow`, `SpatialLocking.frozen_flow_preserves_locks`, `SpatialLocking.no_attracting_locks` (Phase XXII); `InterwovenSAT.toroidal_locking_iff_unsat`, `InterwovenSAT.locks_iff_sat_iff`, `InterwovenSAT.naive_toroidal_locking_fails` (Phase XX); `Torus.no_locking`, `Torus.unstable_or_unreachable`, `Torus.isSolution_reverse`, `Torus.no_locking_phaseOrbit` (Phase XVIII); `ToroidalDiagonal.even_encRing_mem_SAT`, `ToroidalDiagonal.odd_encRing_not_SAT` | Restricted (Phase XXIII original-scope audit). Exact only for the revised reference-component definition; no ψ-electron identification theorem is provided. The structure is realized on the spatial torus `T_L²` of the frozen equation: a field `Ψ = (ψ₀, ψ₁, …)` of frozen-torus `H²` states, `ψ₀` the reference (ψ–electron) component and `ψ_{i+1}` carrying variable `i`. A locking configuration has `\|ψᵢ\| = 1` at every point, zero local density of the clause penalties plus the sign-blind coupling and curvature of the relative field `ψ_{i+1}·conj ψ₀` at every point, and zero gradient energy. For every formula, every `L > 0` and all `λ, μ ≥ 0` such a configuration exists iff the formula is satisfiable. The locks are the constant fields with satisfying relative phases; under the frozen flow they stay locked with vanishing Laplacian for all times, and for `κ ≤ 0, β ≤ 0 < γ` no frozen trajectory approaches one from outside (the zero mode is the strict Hamiltonian minimizer at fixed mass). The sentence asks for constraints that correspond to the satisfaction of all clauses: sign-sensitive coupling does not (it fails on the satisfiable `F_xor`), and `locks_iff_sat_iff` characterizes the flux energies for which the equivalence holds. "ψ–electron" occurs only in this sentence and is read as the reference component. Both seam signs are settled for the finite equality ring. |
| I-38 | Thm. `thm:P-equivalence` | P^disc_WCC = P | `PartIIUniform.P_disc_eq_P_TM` (new); also `P_WCC_eq_P_TM`, `P_WCCR_eq_P_TM`, `P_WCCD_eq_P_TM` | Exact (uniform model `PartIIUniform.UWCC`: any d ≥ 1 and radius r ≥ 0, poly-time lattice algorithm, encoder and readout, all charged) |
| I-39 | Thm. `thm:NP-equivalence` | NP^disc_WCC = NP | `PartIIUniform.NP_disc_eq_NP_TM` (new); also `NP_WCC_eq_NP_TM`, `NP_WCCR_eq_NP_TM`, `NP_WCCD_eq_NP_TM` | Exact (polynomial-size witness strings, uniform poly-time WCC verifiers: `PartIIUniform.NP_disc`) |
| I-40 | Thm. `thm:supplied-assignment-in-P` | L* (uniform F_n) ∈ P; explicit (F,a) ∈ P | `SATV.V_SAT_mem_P_TM` (explicit version) | Exact for explicit (F,a); uniform-family version needs TM composition (counted Exact for the explicit claim) |
| I-41 | Prop. `thm:curv-bdd-sep` + remark | conditional physical separation; fixed-n impossibility | `PartISeparation.curv_bdd_sep`, `fixed_n_impossible` (new) | Exact |

Counts:
* Exact (30): I-1, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 29, 30, 33, 34, 35, 36,
  38, 39, 40, 41.
* Restricted (3): I-3 (Phase XXII), I-11, I-37 (Phase XXIII scope audit).
* Refuted (5): I-25, 26, 27, 28, 31. Original I-10, I-12, I-13 and I-20 counterarguments/counterexamples remain preserved against superseded statements.
* Open (3): I-2, 16, 32.

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
| III-22 | §8 arrow-of-time remark | no equivalence with retrocausality | `Torus.backward_eq_forward_conj`, `Torus.flow_neg` (Phase XVIII, supporting) | Interpretive (Phase XX). The remark states that no equivalence `P^phys = NP^phys ⟺ retrocausality` is proved and keeps the section as a research direction; it asserts no theorem, so no proof obligation is attached. Its sentence "inverse dynamics need not efficiently solve SAT" has a precise frozen-model form, proved as supporting material: the state at time −t is the conjugate of the forward evolution of the conjugated state, so backward evolution is forward evolution composed with conjugation. |

Counts:
* Exact (21): III-1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21.
* Restricted (0).
* Open (0).
* Interpretive (1): III-22 (Phase XX; Open until then).

## Smallest missing lemmas (for the P-versus-NP conclusion)

* **Discrete route.** `conj:wcc_depth`, which is equivalent in Lean to `3-SAT ∉ P_TM`. This is the
  classical open problem itself.
* **Physical route.**
  * Hypotheses `lem:separator-price` and `prop:locked-expander-full`, for every admissible
    decider;
  * a physical-to-discrete class identification.

  Even with both, `physical_SAT_lower_bound_is_classical` shows that a physical SAT lower bound
  under poly-time encoders already implies `P_TM ≠ NP_TM`. Phase XX (13 November 2026) proves the
  same for the frozen torus equation itself: in every device class that contains the charged
  zero-mode devices, a superpolynomial resource bound for SAT implies `P_TM ≠ NP_TM`, and in the
  zero-mode class it is equivalent to it (`WCTSATScaling`). The transport bound of the SAT readout
  (`WCTSATDevice.device_pair_budget`) is at best inverse-polynomial and needs initial blindness.
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
