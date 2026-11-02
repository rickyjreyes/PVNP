# Theorem ↔ manuscript map (ASTRA v2, 2 November 2026)

Every numbered statement of the three PVNP manuscripts is listed here with its Lean counterpart, the
assumptions the Lean statement actually uses, its domain or dimension, its status, and how the formal
statement differs from the manuscript.

**Status vocabulary**

| Status | Meaning |
|---|---|
| **PROVED** | Kernel-checked with no premise that restates the conclusion. |
| **PROVED-R** | Proved for a restricted scope, stated in the row. |
| **COND** | Kernel-checked implication; its premises are explicit and unproved. |
| **REFUTED** | A Lean counterexample to the statement as written. |
| **ANALYTIC** | Paper proof only, not formalized. |
| **OPEN** | Neither proved nor refuted. |

All Lean names are relative to `lean/PVNP/`. "Audit" means the name is listed in
`lean/audit/AxiomAudit.lean`: 111 declarations, each using only `propext`, `Classical.choice` or
`Quot.sound`.

## Part III — *Physical complexity reassessment* (`pvnp/papers/part-iii-physical-complexity-reassessment`)

| Statement | Lean declaration | Lean assumptions | Domain / dimension | Status | Differences |
|---|---|---|---|---|---|
| Prop. `prop:zero_cost` (no universal positive separation cost) | `PartIIIAnalytic.zero_cost_counterexample` | none | arbitrary measure space; Mathlib Laplacian | **REFUTED** (the universal claim) | none |
| Prop. (conditional additive storage) | `Discrete.conditional_additive_storage` | additivity and per-cell bound as premises | `n` disjoint cells | **COND** | algebraic core only |
| Lemma `lem:h2bound` | `PartIIIAnalytic.curvature_cost_le` | integrability of `‖Δψ‖²` | any measure space | **PROVED** | more general than `H²(Ω)` |
| Thm. `thm:disc-equiv` | `Discrete.P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM`, `P_WCCR_eq_P_TM`, `NP_WCCR_eq_NP_TM`; for `d ≥ 2` only `P_TM_subset_P_WCCD` | radius `r ≥ 1`, origin-marked encoding | `ℤ` with quiescent blank (all fixed radii); `ℤ^(1+d)` inclusion only | **PROVED-R** | finite `Λ_n` with background symbol replaced by `ℤ` with quiescent blank; reverse inclusion for `d ≥ 2` not formalized |
| Thm. `thm:p-in-np` | `Discrete.P_TM_subset_NP_TM`, `P_WCC_subset_NP_WCC` | **none**: the closure premise is eliminated | discrete | **PROVED** (stronger) | explicit pair-parsing verifier machine |
| Prop. (no logical conflict between semantics) | `Discrete.inclusions_do_not_determine` | `NPd` nonempty | abstract classes | **PROVED** | set-theoretic form |
| Prop. `prop:interface` | `Discrete.conditional_interface_bound` | area lower bound and cost/area premise | abstract | **COND** | no geometric measure theory |
| Prop. `prop:assignment-P` | `Discrete.SATV.V_SAT_mem_P_TM` (also `SAT_dense_mem_NP_TM`) | dense CNF encoding | discrete TM | **PROVED** | dense encoding is fixed |
| Thm. `thm:constructibility` | `Discrete.telescoping_bound` | increment bound `K` is a premise | sequences | **COND** | the PDE never supplies `K` |
| Prop. `prop:highfreq` | `PartIIIHighFreq3D.cube_gradient_energy`, `cube_curvature_lower`; 1-D: `PartIIIAnalytic.highfreq_*` | none | periodic cube `(0,2π)³` | **PROVED** | the manuscript's constants |
| Thm. `thm:capacity` | `PartIIIAnalytic.capacity_law` | uniform second-derivative bound | any measure space | **COND** | none |
| Lemma `lem:boundary_variation` | `PartIII.directed_boundary_eq` (+ `PartIIIExtended.*`) | none | Boolean cube | **PROVED** | none |
| Thm. `thm:influence` | `PartIII.total_influence_le_dimension`, `PartIIIExtended.normalized_total_influence_le_n`; sharpness `PartIII.parity_total_influence` | none | Boolean cube | **PROVED** | none |
| Cor. `cor:var` | `PartIII.variation_class_vacuous` | none | Boolean cube | **PROVED** | none |
| Formal-status paragraph: encoder/decoder audit | `PhysicalAudit.unrestricted_encoder_trivializes`, `unrestricted_decoder_trivializes`, `PhysConst_polyEnc_eq_P_TM`, `physical_SAT_lower_bound_is_classical` | exact plane-wave solutions of the frozen PDE | 2-D box | **PROVED** | new in ASTRA v2 |
| Formal-status paragraph: flux inequality, continuum | premise of `TransportCalculus.curvature_time_lower_bound` | flux inequality assumed | continuum | **ANALYTIC** (`wct-pde-transport-bound.md` §3) | not derived in Lean |
| Formal-status paragraph: flux inequality, lattice | `WCTLattice.hasDerivAt_flux`, `flux_bound`, `lattice_flux_inequality`, `lattice_curvature_time_bound` | solution of the lattice ODE; `γ > 0` | discrete torus `ℤ/Nℤ`, any `N, h` | **PROVED** (derived) | `D = ‖(Δ_h+κ)z‖`; constant `Γ` explicit and uniform in `N` |
| Formal-status paragraph: well-posedness | external `ReyesMath.Sobolev.global_wellposed`, `continuous_dependence`, `conservation`; bridge `lean/bridge/MathBridge.lean` | `γ > 0`, data in `H²(ℝ²)` | whole plane `ℝ²` | **PROVED** (external, verified) | not the torus model; see M3-T |
| Formal-status paragraph: uniform constants | `SpectralGap.no_uniform_poincare`, `wirtinger_sharp`; `WCTLattice.bandpass_le_ham`, `TransportCalculus.hamiltonian_controls_bandpass` | none | circles of length `L`; any `N` | **REFUTED** (uniform Poincaré); **PROVED** (uniform bandpass coercivity) | sharp constant `(2π/L)²` |

## Part II — *Discrete WCC ⇄ Turing equivalence* (`pvnp/papers/part-ii-discrete-wcc-turing-equivalence`)

| Statement | Lean declaration | Lean assumptions | Domain / dimension | Status | Differences |
|---|---|---|---|---|---|
| Def. `def:wcc_machine` | three models: `Discrete.WCC` (r = 1), `WCCR` (any `r ≥ 1`), `WCCD d` (`ℤ^(1+d)`) | — | 1-D; `(1+d)`-D | — | infinite quiescent lattice instead of finite `Λ_n`; identity encoding instead of polynomial-time `enc`; global accept/reject flags instead of `dec_n`. Radius 0 is excluded (`P_WCCR_zero`). |
| Lemma `lem:precision-stability` | — | — | — | **ANALYTIC** | — |
| Prop. `prop:local-tm` | `Discrete.TM.toWCC_step_encode` | none | 1-D | **PROVED** | real time (overhead factor 1) |
| Prop. `prop:deterministic-replay` | definitional (`WCC.run` is a function) | — | — | **PROVED** | — |
| Thm. `thm:wave-symbol-isomorphism` | — | compatibility hypothesis | — | **ANALYTIC/COND** | — |
| Prop. `prop:gandy-wcc`, Cor. `cor:gandy-wcc-correspondence` | — | — | — | **ANALYTIC** | — |
| Lemmas `lem:invariant`, `lem:one_step`, `lem:runtime`; Thm. `thm:tm_to_wcc` | `Discrete.TM.toWCC_step_encode`, `TM.toWCC_decides` | none | 1-D, radius 1 | **PROVED** | the Lean simulation is real time, stronger than two WCC steps per TM step |
| Thm. `thm:wcc_to_tm` | `WCC.toTM_decides` (r = 1, time `1+(T+1)(n+2T+5)`); `WCCR.toTM_decides` (any `r`, time `1+(T+1)(n+2r(T+1)+2r+1)`) | none | 1-D only | **PROVED-R** | `d ≥ 2` is the paper's sketch only (obligation D-1) |
| Cor. `cor:pwcc_equals_pturing` | `Discrete.P_WCC_eq_P_TM`, `P_WCCR_eq_P_TM`, `P_WCCR_radius_invariant` | `r ≥ 1` | 1-D | **PROVED-R** | new Remark `rem:verified-scope` restricts the claim |
| Thm. `thm:np_equiv` | `Discrete.NP_WCC_eq_NP_TM`, `NP_WCCR_eq_NP_TM`, `NP_TM_verifier_to_WCC`, `NP_WCC_verifier_to_TM` | explicit witness polynomial, self-delimiting pairing | 1-D | **PROVED-R** | — |
| Lemmas `lem:bandlimit`, `lem:spatial_capacity`, `lem:lane_update_bound`; Thms. `thm:spacetime_capacity`, `thm:channel_capacity`; Prop. `prop:phys_step_ceiling`; Thm. `thm:conditional_np_safety` | counting core: `Packing.complex_receiver_packing`, `FourierTorus.torus2_bandlimited_packing`, `FourierReceiver.receiver_mode_count`, `Packing.capacity_bits_le` | declared receiver class; rest-energy and dimensional-lock hypotheses | bounded cavity / torus | **COND** | "bandwidth preserved" **REFUTED** (`FourierReceiver.cubic_quintic_generates_new_modes`); "packing ⇒ decision bound" **REFUTED** (`DecisionVsEncoding.promoted_bound_false`) |
| Lemma `lem:verifier-encoding` | `Discrete.NP_TM_verifier_to_WCC` | none | 1-D | **PROVED** | — |
| Thm. `thm:uniform-discrete-bijection` | `P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM` (+ radius-r) | fixed origin-marked encoding | 1-D | **PROVED-R** | for polynomial-time encoders the ⊇ inclusion is trivial (`unrestricted_encoder_trivializes_WCC`, `P_WCC_enc_id`) |
| Prop. `prop:conditional-classical-lift` | `Discrete.p_vs_np_discrete_transfer`, `lower_bound_transfer`, `p_vs_np_radius_transfer` | none | discrete | **PROVED** | — |
| Formal-status paragraph: encoders and advice | `Discrete.unrestricted_encoder_trivializes_WCC`, `advice_bit_trivializes` | none | 1-D | **PROVED** | new in ASTRA v2 |

## Part I — *Curvature-bounded wave computation* (`pvnp/papers/part-i-curvature-bounded-wave-computation`)

| Statement | Lean declaration | Lean assumptions | Domain | Status | Differences |
|---|---|---|---|---|---|
| Prop. (curvature-confinement schema, l. 327); Conj. (symbolic separation, l. 431); Thm. (conditional symbolic separation, l. 510) | `Discrete.curvature_lower_bound_is_classical`, `SATV.SAT_curvature_transfer` | — | discrete | **COND / OPEN** | any discrete curvature lower bound is a classical one |
| Thm. `thm:psi-sat-completeness` | `SATV.encDense_mem_SAT_iff`, `R03.unsatisfied_clause_has_penalty` | dense encoding | finite | **PROVED-R** | penalty-functional form |
| Prop. `lem:dim-lock` (WIN-04) | — | — | `d = 4` | **ANALYTIC** | — |
| Prop. `thm:pwcc-neq-npwcc` (WIN-05) | `Discrete.p_vs_np_discrete_transfer`, `PhysicalAudit.physical_SAT_lower_bound_is_classical` | — | — | **COND** | proved to be at least as hard as P vs NP |
| Prop. `prop:collapse-grammar` | — | — | — | **ANALYTIC** | — |
| Hyp. `hyp:dimensional-lock` | refuted variants: `DecisionVsEncoding.promoted_bound_false`, `PartIIIAnalytic.zero_cost_counterexample` | — | — | **OPEN** (as stated); **REFUTED** (packing form) | — |
| Lemma `lem:local_growth` | `MultiStageCausality.multistage_required_causal_coverage` | none | 1-D, radius `r` | **PROVED** | — |
| Lemma `lem:clause_flip` | — | — | — | **ANALYTIC** | — |
| Conj. `conj:wcc_depth` | `Discrete.lower_bound_transfer`, `SATV.SAT_dense_mem_NP_TM` | — | discrete | **OPEN** | the conjecture implies `P ≠ NP`; it is equivalent to `P ≠ NP` given Cook–Levin (CL-1) |
| Prop. `prop:internal_sep_conditional` | `Discrete.p_vs_np_discrete_transfer` | conjecture `conj:wcc_depth` | discrete | **COND** | — |
| Props. `thm:separator_curvature`, `thm:mass_complexity`, `thm:padding_stability` | `Discrete.conditional_interface_bound`, `telescoping_bound`, `conditional_additive_storage` | explicit premises | abstract | **COND** | — |
| Prop. `thm:np-type-conditional` | `Discrete.curvature_lower_bound_is_classical` | — | — | **COND** | — |
| Prop. `cor:P-neq-NP-conditional` | `Discrete.p_vs_np_discrete_transfer` | — | — | **PROVED** (bridge); no separation | — |
| Thms. `thm:P-equivalence`, `thm:NP-equivalence` | `Discrete.P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM`, radius-r versions | — | 1-D | **PROVED-R** | — |
| Thm. `thm:supplied-assignment-in-P` | `Discrete.SATV.V_SAT_mem_P_TM` | dense encoding | discrete | **PROVED** | — |
| Prop. `thm:curv-bdd-sep` | `PhysicalAudit.physical_SAT_lower_bound_is_classical` | — | — | **COND** | — |

## Not claimed anywhere

Classical `P ≠ NP`, a physical `P ≠ NP`, any universal SAT lower bound, and any
curvature-preserving physical realization of the discrete WCC.
