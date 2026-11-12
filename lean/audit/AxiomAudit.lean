import PVNP
/-! Axiom audit for the principal ASTRA theorems (run with `lake env lean audit/AxiomAudit.lean`).
Every listed declaration must depend only on `propext`, `Classical.choice`, `Quot.sound`. -/
-- Issue #11
#print axioms PVNP.Discrete.TM.toWCC_step_encode
#print axioms PVNP.Discrete.TM.toWCC_decides
#print axioms PVNP.Discrete.WCC.phase_step
#print axioms PVNP.Discrete.WCC.toTM_decides
#print axioms PVNP.Discrete.P_WCC_eq_P_TM
#print axioms PVNP.Discrete.NP_WCC_eq_NP_TM
#print axioms PVNP.Discrete.p_vs_np_discrete_transfer
#print axioms PVNP.Discrete.encodeTable_decodeTable
#print axioms PVNP.Discrete.decodeTable_sound
#print axioms PVNP.Discrete.encodeTable_length_le
#print axioms PVNP.Discrete.TM.normalize_decides
#print axioms PVNP.Discrete.P_TM_eq_tables
-- Issue #15
#print axioms PVNP.Packing.packing_card_le
#print axioms PVNP.Packing.finrank_real_euclideanSpace_complex
#print axioms PVNP.Packing.complex_receiver_packing
#print axioms PVNP.Packing.subspace_receiver_packing
#print axioms PVNP.Packing.capacity_bits_le
#print axioms PVNP.Packing.mass_lower_bound
#print axioms PVNP.FourierReceiver.receiver_mode_count
#print axioms PVNP.FourierReceiver.cubic_quintic_generates_new_modes
#print axioms PVNP.DecisionVsEncoding.robust_decision_readout
#print axioms PVNP.DecisionVsEncoding.promoted_bound_false
-- Issues #10 / #12
#print axioms PVNP.Discrete.P_TM_eq_curvature_rail
#print axioms PVNP.Discrete.curvature_lower_bound_is_classical
#print axioms PVNP.Discrete.WCC.relabel_decides
#print axioms PVNP.Discrete.curvature_not_representation_invariant
#print axioms PVNP.PartIIIAnalytic.curvature_cost_le
#print axioms PVNP.PartIIIAnalytic.capacity_law
#print axioms PVNP.PartIIIAnalytic.zero_cost_counterexample
#print axioms PVNP.PartIIIAnalytic.highfreq_gradient_energy
#print axioms PVNP.PartIIIAnalytic.highfreq_curvature_lower
#print axioms PVNP.PartIIIAnalytic.no_gradient_energy_control
#print axioms PVNP.PartIII.directed_boundary_eq
#print axioms PVNP.PartIII.parity_total_influence
#print axioms PVNP.Discrete.NP_TM_verifier_to_WCC
#print axioms PVNP.Discrete.NP_WCC_verifier_to_TM
#print axioms PVNP.FourierTorus.receiver_bessel
#print axioms PVNP.FourierTorus.torus_receiver_packing
#print axioms PVNP.FourierTorus.torus2_bandlimited_packing
#print axioms PVNP.Discrete.TM.unpair_decides
#print axioms PVNP.Discrete.P_TM_subset_NP_TM
#print axioms PVNP.Discrete.P_WCC_subset_NP_WCC
#print axioms PVNP.SpectralGap.fourierCoeff_of_deriv
#print axioms PVNP.SpectralGap.wirtinger
#print axioms PVNP.SpectralGap.wirtinger_sharp
#print axioms PVNP.SpectralGap.no_uniform_poincare
#print axioms PVNP.WCTPlaneWave.plane_wave_solves
#print axioms PVNP.WCTPlaneWave.classical_derivatives
#print axioms PVNP.WCTPlaneWave.expanding_domain_countermodel
#print axioms PVNP.WCTPlaneWave.curvature_energy_vanishes
#print axioms PVNP.Discrete.SATV.rounds
#print axioms PVNP.Discrete.SATV.satTM_decides
#print axioms PVNP.Discrete.SATV.V_SAT_mem_P_TM
#print axioms PVNP.Discrete.SATV.SAT_dense_mem_NP_TM
#print axioms PVNP.Discrete.SATV.SAT_dense_mem_NP_WCC
#print axioms PVNP.Discrete.SATV.encDense_mem_SAT_iff
#print axioms PVNP.Discrete.SATV.SAT_curvature_transfer
#print axioms PVNP.PartIIIHighFreq3D.lap3_psi
#print axioms PVNP.PartIIIHighFreq3D.cube_gradient_energy
#print axioms PVNP.PartIIIHighFreq3D.cube_curvature_lower
#print axioms PVNP.Discrete.conditional_additive_storage
#print axioms PVNP.TransportCalculus.power_mean_four
#print axioms PVNP.TransportCalculus.transport_tradeoff
#print axioms PVNP.TransportCalculus.curvature_time_lower_bound
#print axioms PVNP.TransportCalculus.hamiltonian_controls_bandpass
#print axioms PVNP.AnalogSplitSAT.scalar_level_count
#print axioms PVNP.AnalogSplitSAT.analog_split_sat_capacity
#print axioms PVNP.PhysicalAudit.device_physics
#print axioms PVNP.PhysicalAudit.unrestricted_encoder_trivializes
#print axioms PVNP.PhysicalAudit.unrestricted_decoder_trivializes
#print axioms PVNP.PhysicalAudit.P_TM_subset_PhysConst
#print axioms PVNP.PhysicalAudit.PhysConst_polyEnc_eq_P_TM
#print axioms PVNP.PhysicalAudit.physical_SAT_lower_bound_is_classical
#print axioms PVNP.PhysicalAudit.two_states_suffice
#print axioms PVNP.Discrete.WCCR.rsweep_run
#print axioms PVNP.Discrete.WCCR.lsweep_run
#print axioms PVNP.Discrete.WCCR.phase_step
#print axioms PVNP.Discrete.WCCR.global
#print axioms PVNP.Discrete.WCCR.toTM_decides
#print axioms PVNP.Discrete.WCC.toR_decides
#print axioms PVNP.Discrete.P_WCCR_subset_P_TM
#print axioms PVNP.Discrete.P_WCCR_eq_P_TM
#print axioms PVNP.Discrete.NP_WCCR_eq_NP_TM
#print axioms PVNP.Discrete.P_WCCR_radius_invariant
#print axioms PVNP.Discrete.p_vs_np_radius_transfer
#print axioms PVNP.Discrete.explicit_radius_simulations

-- Fixed, language-independent robust encoding / unrestricted receiver countermodel
#print axioms PVNP.DecoderUniformity.signDecode_signCode
#print axioms PVNP.DecoderUniformity.signCode_mass
#print axioms PVNP.DecoderUniformity.signCode_injective
#print axioms PVNP.DecoderUniformity.signDecode_noise
#print axioms PVNP.DecoderUniformity.arbitrary_predicate_has_robust_decoder
#print axioms PVNP.DecoderUniformity.number_of_labels
-- Part II generality: (1+d)-dimensional lattices, encoders, advice
#print axioms PVNP.Discrete.WCC.toD_run
#print axioms PVNP.Discrete.WCC.toD_decides
#print axioms PVNP.Discrete.P_TM_subset_P_WCCD
#print axioms PVNP.Discrete.NP_TM_subset_NP_WCCD
#print axioms PVNP.Discrete.P_WCC_enc_id
#print axioms PVNP.Discrete.unrestricted_encoder_trivializes_WCC
#print axioms PVNP.Discrete.advice_bit_trivializes
-- D-1 finite propagation on higher-dimensional Moore lattices
#print axioms PVNP.Discrete.WCCD.off_bounds
#print axioms PVNP.Discrete.WCCD.init_blank_outside
#print axioms PVNP.Discrete.WCCD.run_blank_outside
#print axioms PVNP.Discrete.WCCD.run_blank_left
#print axioms PVNP.Discrete.WCCD.run_blank_right
#print axioms PVNP.Discrete.WCCD.run_blank_transverse
-- D-1 exact finite snapshot interpreter: coordinates, updates, blank-aware output
#print axioms PVNP.Discrete.WCCD.point_inCone
#print axioms PVNP.Discrete.WCCD.point_index
#print axioms PVNP.Discrete.WCCD.index_point
#print axioms PVNP.Discrete.WCCD.box_card
#print axioms PVNP.Discrete.WCCD.read_point
#print axioms PVNP.Discrete.WCCD.read_snapshot
#print axioms PVNP.Discrete.WCCD.advance_snapshot
#print axioms PVNP.Discrete.WCCD.hasWitness_iff
#print axioms PVNP.Discrete.WCCD.hasWitness_correct
#print axioms PVNP.Discrete.WCCD.finiteOutput_snapshot
#print axioms PVNP.Discrete.WCCD.replay_correct
#print axioms PVNP.Discrete.WCCD.replay_output
#print axioms PVNP.Discrete.WCCD.firstAnswer_replay
-- D-1 concrete ordinary single-tape scan subroutine
#print axioms PVNP.Discrete.TMStackScan.scan_return
-- D-1 completion: round-trip sweep programs compiled to ordinary single-tape TMs
#print axioms PVNP.Discrete.Sweep.Prog.reach_run
#print axioms PVNP.Discrete.Sweep.Prog.halts_run
#print axioms PVNP.Discrete.Sweep.Prog.toTM_firstAnswer
-- D-1 completion: exact cyclic flattening of WCCD runs
#print axioms PVNP.Discrete.WCCD.flat_inj
#print axioms PVNP.Discrete.WCCD.cyclic_exact
#print axioms PVNP.Discrete.WCCD.cyclic_out
-- D-1 completion: the explicit WCCD-simulating sweep program
#print axioms PVNP.Discrete.WCCDSweep.step_chk
#print axioms PVNP.Discrete.WCCDSweep.loopL
#print axioms PVNP.Discrete.WCCDSweep.loopR
#print axioms PVNP.Discrete.WCCDSweep.axis_step
#print axioms PVNP.Discrete.WCCDSweep.axes_run
#print axioms PVNP.Discrete.WCCDSweep.round
#print axioms PVNP.Discrete.WCCDSweep.inner_loop
#print axioms PVNP.Discrete.WCCDSweep.outer_loop
#print axioms PVNP.Discrete.WCCDSweep.build_axes
#print axioms PVNP.Discrete.WCCDSweep.xfin_inv
#print axioms PVNP.Discrete.WCCDSweep.arrAns_eq
#print axioms PVNP.Discrete.WCCDSweep.restart
#print axioms PVNP.Discrete.WCCDSweep.enter
#print axioms PVNP.Discrete.WCCDSweep.init_phase
#print axioms PVNP.Discrete.WCCDSweep.halts_of_first
#print axioms PVNP.Discrete.WCCDSweep.final_arith
#print axioms PVNP.Discrete.WCCDSweep.toTM_decides
#print axioms PVNP.Discrete.P_WCCD_subset_P_TM
#print axioms PVNP.Discrete.P_WCCD_eq_P_TM
#print axioms PVNP.Discrete.NP_WCCD_eq_NP_TM
-- Manuscript Part I, claim by claim (pvnp/proofs/manuscript-lean-inventory.md)
#print axioms PVNP.PartIPsiSat.psi_sat_completeness
#print axioms PVNP.PartIPsiSat.psi_sat_completeness_field
#print axioms PVNP.PartIPsiSat.zero_penalty_not_stationary
#print axioms PVNP.PartIPsiSat.uniform_symbolic_verification
#print axioms PVNP.PartISeparation.univ_mem_P_TM
#print axioms PVNP.PartISeparation.empty_mem_P_TM
#print axioms PVNP.PartISeparation.complexity_schema
#print axioms PVNP.PartISeparation.conditional_symbolic_separation
#print axioms PVNP.PartISeparation.win05
#print axioms PVNP.PartISeparation.np_type_conditional
#print axioms PVNP.PartISeparation.curv_bdd_sep
#print axioms PVNP.PartISeparation.fixed_n_impossible
#print axioms PVNP.PartISeparation.WCCDepth_iff_not_P_TM
#print axioms PVNP.PartISeparation.WCCDDepth_iff_not_P_TM
#print axioms PVNP.PartISeparation.internal_sep_conditional
#print axioms PVNP.PartISeparation.internal_sep_SAT
#print axioms PVNP.PartISeparation.conditional_product_lower_bound
#print axioms PVNP.PartISeparation.conditional_bridge_WCC
#print axioms PVNP.PartISeparation.conditional_bridge_WCCD
#print axioms PVNP.PartISeparation.restricted_separation_schema_iff
#print axioms PVNP.PartISeparation.state_separation_not_language_separation
#print axioms PVNP.PartISeparation.accepted_language_not_in_NP_diff_P
#print axioms PVNP.PartISeparation.universal_scope_counterexample
#print axioms PVNP.PartISeparation.PNP_SAT_physically_constant
#print axioms PVNP.PartISeparation.category_error_claim_implies_classical
#print axioms PVNP.PartISeparation.high_K_not_poly_witness
#print axioms PVNP.PartISeparation.trivial_partition_invariant
#print axioms PVNP.PartISeparation.invariant_constant_of_common_successor
#print axioms PVNP.PartISeparation.no_nontrivial_invariant_of_common_successor
#print axioms PVNP.PartILocality.supp_step_subset
#print axioms PVNP.PartILocality.local_growth_needs_quiescence
#print axioms PVNP.PartILocality.support_poly_bound
#print axioms PVNP.PartILocality.linear_growth_false_d2
#print axioms PVNP.PartILocality.clause_flip_local
#print axioms PVNP.PartILocality.clause_flip_rounds
#print axioms PVNP.PartILocality.clause_flip_ceil
#print axioms PVNP.PartILocality.parallel_flips
#print axioms PVNP.PartIDimLock.fderiv_fderiv_ψ
#print axioms PVNP.PartIDimLock.laplacian_ψ
#print axioms PVNP.PartIDimLock.integrable_ψ
#print axioms PVNP.PartIDimLock.win04_gaussian
#print axioms PVNP.PartIIManuscript.wave_symbol_forward
#print axioms PVNP.PartIIManuscript.wave_symbol_converse
#print axioms PVNP.PartIIManuscript.compatibility_necessary
#print axioms PVNP.PartIIManuscript.bandlimit_eff
#print axioms PVNP.PartIIManuscript.bandlimit_sharp
#print axioms PVNP.PartIIManuscript.spatial_capacity
#print axioms PVNP.PartIIManuscript.spatial_capacity_energy
#print axioms PVNP.PartIIManuscript.lane_update_bound
#print axioms PVNP.PartIIManuscript.spacetime_capacity
#print axioms PVNP.PartIIManuscript.phys_step_ceiling
#print axioms PVNP.PartIIManuscript.rounds_le_events
#print axioms PVNP.ManuscriptRemarks.valid_telescoping
#print axioms PVNP.ManuscriptRemarks.padding_stability
#print axioms PVNP.ManuscriptRemarks.superlinear_padding
#print axioms PVNP.ManuscriptRemarks.win13_counterexample
#print axioms PVNP.ManuscriptRemarks.p_in_np_phys
#print axioms PVNP.ManuscriptRemarks.win16
#print axioms PVNP.PartIITuring.P_Turing_lit_eq
#print axioms PVNP.PartIITuring.P_Turing_subset_P_TM
#print axioms PVNP.PartIITuring.P_TM_subset_P_Turing
#print axioms PVNP.PartIITuring.P_Turing_eq_P_TM
#print axioms PVNP.PartIITuring.NP_Turing_subset_NP_TM
#print axioms PVNP.PartIITuring.NP_TM_subset_NP_Turing
#print axioms PVNP.PartIITuring.NP_Turing_eq_NP_TM
#print axioms PVNP.PartIITuring.P_Turing_lit_ne_P_TM
#print axioms PVNP.PartIITuring.P_Turing_lit_ne_NP_Turing
#print axioms PVNP.PartIITuring.MTM.guard_valid
#print axioms PVNP.PartIITuring.OfTM.ofTM_decides
#print axioms PVNP.PartIITwoPhase.encM_eq
#print axioms PVNP.PartIITwoPhase.two_steps
#print axioms PVNP.PartIITwoPhase.one_step_of_inWin
#print axioms PVNP.PartIITwoPhase.one_step
#print axioms PVNP.PartIITwoPhase.invariant_even
#print axioms PVNP.PartIITwoPhase.invariant_odd
#print axioms PVNP.PartIITwoPhase.runtime
#print axioms PVNP.PartIITwoPhase.runtime_accepts
#print axioms PVNP.PartIITwoPhase.card_window
#print axioms PVNP.PartIITwoPhase.tm_to_wcc_decides
#print axioms PVNP.PartIITwoPhase.one_step_literal_fails
#print axioms PVNP.PartIITwoPhase.invariant_literal_fails
#print axioms PVNP.PartIITuring.MTM.aw_sim
#print axioms PVNP.PartIITuring.MTM.answerWriter_outputs
#print axioms PVNP.PartIIUniform.latMTM_outputs
#print axioms PVNP.PartIIUniform.decMTM_outputs
#print axioms PVNP.PartIIUniform.P_Turing_subset_P_disc
#print axioms PVNP.PartIIUniform.P_TM_subset_P_disc
-- D-1 polynomial finite-array work accounting (does not imply TM-time bound)
#print axioms PVNP.Discrete.WCCD.boxCells_card
#print axioms PVNP.Discrete.WCCD.boxCells_mono
#print axioms PVNP.Discrete.WCCD.totalCells_le
#print axioms PVNP.Discrete.WCCD.totalCells_polynomial_bound
#print axioms PVNP.Discrete.WCCD.neighborhood_card
#print axioms PVNP.Discrete.WCCD.totalNeighborReads_polynomial_bound
#print axioms PVNP.Discrete.WCCD.workPoly_eval
#print axioms PVNP.Discrete.WCCD.totalCells_le_workPoly
#print axioms PVNP.Discrete.WCCD.neighborWorkPoly_eval
#print axioms PVNP.Discrete.WCCD.totalNeighborReads_le_workPoly
-- Lattice WCT system: conservation, coercivity, derived flux inequality, transport bound
#print axioms PVNP.WCTLattice.ip_Aop
#print axioms PVNP.WCTLattice.hasDerivAt_mass
#print axioms PVNP.WCTLattice.hasDerivAt_ham
#print axioms PVNP.WCTLattice.mass_conserved
#print axioms PVNP.WCTLattice.ham_conserved
#print axioms PVNP.WCTLattice.exists_local_solution
#print axioms PVNP.WCTLattice.local_conservation
#print axioms PVNP.WCTLattice.bandpass_le_ham
#print axioms PVNP.WCTLattice.hasDerivAt_flux
#print axioms PVNP.WCTLattice.flux_bound
#print axioms PVNP.WCTLattice.lattice_flux_inequality
#print axioms PVNP.WCTLattice.lattice_curvature_time_bound
-- M3-G: quantitative mass bounds along local solutions
#print axioms PVNP.WCTLattice.coordinate_norm_sq_le_mass
#print axioms PVNP.WCTLattice.coordinate_norm_le_sqrt_mass
#print axioms PVNP.WCTLattice.solution_uniform_coordinate_bound
#print axioms PVNP.WCTLattice.exists_local_solution_bounded
-- M3-C: flux prefactor mesh-refinement limitation
#print axioms PVNP.WCTLattice.mesh_flux_prefactor
#print axioms PVNP.WCTLattice.mesh_flux_prefactor_unit


-- M3-G: constructed global flow, uniqueness and degenerate cases
#print axioms PVNP.BoundedODE.exists_global
#print axioms PVNP.BoundedODE.lipschitz_retract
#print axioms PVNP.WCTLattice.vf_locallyLipschitz
#print axioms PVNP.WCTLattice.vf_lipschitz_ball
#print axioms PVNP.WCTLattice.truncated_bounded_lipschitz
#print axioms PVNP.WCTLattice.sum_inner_truncated
#print axioms PVNP.WCTLattice.exists_global_solution
#print axioms PVNP.WCTLattice.global_solution_unique
#print axioms PVNP.WCTLattice.global_wellposed
#print axioms PVNP.WCTLattice.exists_global_conserved_bounded
#print axioms PVNP.WCTLattice.local_global_agree
#print axioms PVNP.WCTLattice.zero_initial_stationary
#print axioms PVNP.WCTLattice.zero_coefficients_stationary

-- F-1 static budget reduction; PDE identity remains separate
#print axioms PVNP.ContinuumFlux.grad_le_sqrt
#print axioms PVNP.ContinuumFlux.static_to_sqrt
#print axioms PVNP.ContinuumFlux.transport_from_static
#print axioms PVNP.ContinuumFlux.curvature_lower_from_static

-- WCT minimal dependency closure, exactly conditional on physical/computational hypotheses
#print axioms PVNP.WCTDependencyClosure.physical_hardness_plus_TM_realization
#print axioms PVNP.WCTDependencyClosure.interface_growth_implies_hardness
#print axioms PVNP.WCTDependencyClosure.full_interface_route
#print axioms PVNP.WCTDependencyClosure.no_route_under_classical_collapse
#print axioms PVNP.WCTDependencyClosure.indicator_physical_barrier_iff_TM

-- Milestone 5: the uniform simulator (`UniformSim*`) and the uniform class equalities
#print axioms PVNP.UniformSim.simTrip_spec
#print axioms PVNP.UniformSim.RN.reach
#print axioms PVNP.UniformSim.nbr_idx
#print axioms PVNP.UniformSim.Spec.sim_loop
#print axioms PVNP.UniformSim.Spec.pre_machines
#print axioms PVNP.UniformSim.Spec.parse_trip
#print axioms PVNP.UniformSim.Spec.rul_loop
#print axioms PVNP.UniformSim.Spec.grow_loop
#print axioms PVNP.UniformSim.Spec.load_loop
#print axioms PVNP.UniformSim.Spec.pre_round
#print axioms PVNP.UniformSim.Spec.pack_loop
#print axioms PVNP.UniformSim.Spec.packSym_eq_inputTape
#print axioms PVNP.UniformSim.Spec.rotU_trip
#print axioms PVNP.UniformSim.Spec.rot_level
#print axioms PVNP.UniformSim.Spec.tasks_shift
#print axioms PVNP.UniformSim.Spec.tasks_loop
#print axioms PVNP.UniformSim.Spec.offset_loop
#print axioms PVNP.UniformSim.Spec.member_nbr
#print axioms PVNP.UniformSim.Spec.decode_phase
#print axioms PVNP.UniformSim.Spec.round_halt
#print axioms PVNP.UniformSim.Spec.round_spec
#print axioms PVNP.UniformSim.Spec.rounds
#print axioms PVNP.UniformSim.Spec.sim_halts
#print axioms PVNP.UniformSim.Spec.sim_invalid
#print axioms PVNP.UniformSim.Spec.toTM_firstAnswer_of_dec
#print axioms PVNP.PartIIUniform.wcc_to_tm
#print axioms PVNP.PartIIUniform.P_disc_subset_P_TM
#print axioms PVNP.PartIIUniform.P_disc_eq_P_TM
#print axioms PVNP.PartIIUniform.NP_disc_subset_NP_TM
#print axioms PVNP.PartIIUniform.NP_TM_subset_NP_disc
#print axioms PVNP.PartIIUniform.NP_disc_eq_NP_TM

-- Spatial F-1 identities on the periodic square.
#print axioms PVNP.ContinuumFlux.I2_lap_symm
#print axioms PVNP.ContinuumFlux.flux_static
#print axioms PVNP.ContinuumFlux.flux_split
#print axioms PVNP.ContinuumFlux.I2_bound
#print axioms PVNP.ContinuumFlux.norm_Gd_le

-- Part I: bounded crossing-record capacity and finite-control TM locality.
#print axioms PVNP.CrossingCapacity.bounded_crossing_record_capacity
#print axioms PVNP.CrossingCapacity.no_short_crossing_record
#print axioms PVNP.CrossingCapacity.same_scanned_symbol_same_instruction
#print axioms PVNP.CrossingCapacity.one_tape_head_speed
#print axioms PVNP.CrossingCapacity.right_crossing_is_adjacent

-- Phase VII: crossing events extracted from actual TM steps and local tape splicing.
#print axioms PVNP.CrossingTrace.event_right
#print axioms PVNP.CrossingTrace.event_left
#print axioms PVNP.CrossingTrace.left_crossing_adjacent
#print axioms PVNP.CrossingTrace.right_crossing_adjacent
#print axioms PVNP.CrossingTrace.trace_length_le
#print axioms PVNP.CrossingTrace.inputTrace_length_le
#print axioms PVNP.CrossingTrace.actual_trace_split_sat_capacity
#print axioms PVNP.CrossingSplice.update_mix_left
#print axioms PVNP.CrossingSplice.update_mix_right
#print axioms PVNP.CrossingSplice.next_splice_left
#print axioms PVNP.CrossingSplice.next_splice_right
#print axioms PVNP.CrossingSplice.run_splice_left
#print axioms PVNP.CrossingSplice.answer_splice_left
#print axioms PVNP.CrossingDiagonal.diagonal_trace_injective
#print axioms PVNP.CrossingDiagonal.diagonal_trace_capacity
#print axioms PVNP.CrossingSplice.run_splice_right
#print axioms PVNP.CrossingSplice.answer_splice_right

-- Phase VIII: complete crossing-sequence splicing theorem and the SAT application
#print axioms PVNP.CrossingHennie.run_splice_side
#print axioms PVNP.CrossingHennie.run_offSide_tape
#print axioms PVNP.CrossingHennie.cross_of_event
#print axioms PVNP.CrossingHennie.trace_cons_events
#print axioms PVNP.CrossingHennie.splice_core
#print axioms PVNP.CrossingHennie.init_append_mix
#print axioms PVNP.CrossingHennie.hennie
#print axioms PVNP.CrossingHennie.splice_mem
#print axioms PVNP.CrossingSAT.splitFormula_sat_iff
#print axioms PVNP.CrossingSAT.encSplit_mem_iff
#print axioms PVNP.CrossingSAT.encSplit_layout
#print axioms PVNP.CrossingSAT.length_encSplit
#print axioms PVNP.CrossingSAT.diag_mixed
#print axioms PVNP.CrossingSAT.dtrace_injective
#print axioms PVNP.CrossingSAT.hmixed_of_halting
#print axioms PVNP.CrossingSAT.diagonal_capacity_halting
#print axioms PVNP.CrossingSAT.diagonal_capacity
#print axioms PVNP.CrossingSAT.sum_trace_length_le
#print axioms PVNP.CrossingSAT.sat_time_lower_bound
#print axioms PVNP.CrossingSAT.sat_time_lower_bound_sq
#print axioms PVNP.CrossingSAT.sat_not_linear_time
#print axioms PVNP.CrossingSAT.satLowerBound_iff
#print axioms PVNP.CrossingSAT.P_ne_NP_of_satLowerBound
#print axioms PVNP.CrossingSATSets.fooling_time_bound
#print axioms PVNP.CrossingSATSets.splice_nmem
#print axioms PVNP.CrossingSATSets.setFormula_sat_iff
#print axioms PVNP.CrossingSATSets.encSet_mem_iff
#print axioms PVNP.CrossingSATSets.length_encSet
#print axioms PVNP.CrossingSATSets.set_mixed
#print axioms PVNP.CrossingSATSets.dtraceSet_injective
#print axioms PVNP.CrossingSATSets.sat_time_lower_bound_sets
#print axioms PVNP.CrossingSATSets.sat_time_lower_bound_near_sq

-- Phase VI: periodic torus H2 and F-1 flux, checked in full import tree.
#print axioms PVNP.Torus.global_wellposed
#print axioms PVNP.Torus.conservation
#print axioms PVNP.Torus.apriori
#print axioms PVNP.Torus.continuous_dependence
#print axioms PVNP.Torus.flux_identity
#print axioms PVNP.Torus.flux_static
#print axioms PVNP.Torus.flux_inequality
#print axioms PVNP.Torus.curvature_time_bound
#print axioms PVNP.Torus.flux_inequality_explicit

-- Phase IX: exact target statement (equivalent to SATLowerBound; not proved).
#print axioms PVNP.SATTarget.decidesAt_ftime
#print axioms PVNP.SATTarget.mem_P_TM_of_eventually_le
#print axioms PVNP.SATTarget.eval_le_pow_succ
#print axioms PVNP.SATTarget.satLowerBound_iff_superpolynomial
#print axioms PVNP.SATTarget.superpolynomial_iff_real
#print axioms PVNP.SATTarget.satLowerBound_iff_superpolynomialReal
#print axioms PVNP.SATTarget.satLowerBound_iff_wccDepth
#print axioms PVNP.SATTarget.satLowerBound_iff_wccdDepth
#print axioms PVNP.SATTarget.P_ne_NP_of_superpolynomial
-- Phase IX no-go: Tseitin instances of SAT_dense are decided by component parity.
#print axioms PVNP.TseitinSAT.parityOK_of_solvable
#print axioms PVNP.TseitinSAT.solvable_of_parityOK
#print axioms PVNP.TseitinSAT.solvable_iff_parityOK
#print axioms PVNP.TseitinSAT.grow_comp
#print axioms PVNP.TseitinSAT.parityOK_iff_comp
#print axioms PVNP.TseitinSAT.parityOK_iff_total
#print axioms PVNP.TseitinSAT.evalFormula_xorCNF
#print axioms PVNP.TseitinSAT.satisfiable_tseitinCNF_iff
#print axioms PVNP.TseitinSAT.tseitin_mem_SAT_dense_iff
#print axioms PVNP.TseitinSAT.tseitin_mem_SAT_dense_iff_comp
#print axioms PVNP.TseitinSAT.tseitin_connected_iff
-- Phase IX no-go: crossing information is attained by V_SAT ∈ P_TM.
#print axioms PVNP.VerifierCrossing.time_of_crossingInfo
#print axioms PVNP.VerifierCrossing.crossingInfo_SAT_dense
#print axioms PVNP.VerifierCrossing.vInst_mem_iff
#print axioms PVNP.VerifierCrossing.vsat_mixed
#print axioms PVNP.VerifierCrossing.crossingInfo_V_SAT
#print axioms PVNP.VerifierCrossing.vsat_info_quadratic
#print axioms PVNP.VerifierCrossing.vsat_time_lower_bound
#print axioms PVNP.VerifierCrossing.vsat_time_lower_bound_sq
#print axioms PVNP.VerifierCrossing.crossingInfo_not_superpolynomial

#print axioms PVNP.TMBooleanTableau.circuit_first
#print axioms PVNP.TMBooleanTableau.circuit_size
#print axioms PVNP.TMBooleanTableau.P_TM_subset_PPoly
#print axioms PVNP.CircuitCNF.circuit_good
#print axioms PVNP.VerifierCircuits.closed_under_projections
#print axioms PVNP.VerifierCircuits.verifier_family
#print axioms PVNP.SATProjection.project_circuit
#print axioms PVNP.SATProjection.NP_projects_to_SAT
#print axioms PVNP.SATProjection.NP_subset_PPoly_of_SAT
#print axioms PVNP.SATProjection.SAT_circuit_lower_iff
#print axioms PVNP.SATProjection.SATLowerBound_of_NP_circuit_lower
#print axioms PVNP.CrossingSATMatrix.instanceWord_mem
#print axioms PVNP.CrossingSATMatrix.matrix_time
#print axioms PVNP.CrossingSATMatrix.quadratic_diagonal
#print axioms PVNP.CrossingSATMatrix.quadratic_arbitrarily_large
#print axioms PVNP.CrossingSATMatrix.matrix_promise_circuit

-- CL-1, part 1: Cook–Levin tableau formula and the mathematical reduction NP_TM → SAT_dense.
#print axioms PVNP.CookLevin.head_le
#print axioms PVNP.CookLevin.tape_far
#print axioms PVNP.CookLevin.Nrm.nrm_answer
#print axioms PVNP.CookLevin.phi_bounded
#print axioms PVNP.CookLevin.truth_step
#print axioms PVNP.CookLevin.rows
#print axioms PVNP.CookLevin.sound
#print axioms PVNP.CookLevin.complete
#print axioms PVNP.CookLevin.phi_sat_iff
#print axioms PVNP.CookLevin.nrm_acc_iff
#print axioms PVNP.CookLevin.cookLevin

-- CL-1, parts 2–3: the uniform generator, the generator-plus-decider program and the equivalence.
#print axioms PVNP.CookLevin.Gen.HPar.horner_phase
#print axioms PVNP.CookLevin.Gen.slotBits_eq
#print axioms PVNP.CookLevin.Gen.inst_getElem
#print axioms PVNP.CookLevin.Gen.TI.bit
#print axioms PVNP.CookLevin.Gen.main_loop
#print axioms PVNP.CookLevin.Gen.label_phase
#print axioms PVNP.CookLevin.Gen.horner_hcoeffs
#print axioms PVNP.CookLevin.Gen.gen_run
#print axioms PVNP.CookLevin.Gen.dec_lift
#print axioms PVNP.CookLevin.Gen.dec_conv
#print axioms PVNP.CookLevin.Gen.dec_sim_loop
#print axioms PVNP.CookLevin.Gen.dec_halts
#print axioms PVNP.CookLevin.Gen.NP_TM_subset_P_TM_of_SAT
#print axioms PVNP.CookLevin.Gen.SAT_mem_P_TM_iff
#print axioms PVNP.CookLevin.Gen.satLowerBound_iff_P_ne_NP

-- Part II, II-24: finite modification and conditional NP-safety.
#print axioms PVNP.CookLevin.Gen.gsim_halts
#print axioms PVNP.CookLevin.Gen.scan_short
#print axioms PVNP.CookLevin.Gen.fm_first
#print axioms PVNP.CookLevin.Gen.fm_long
#print axioms PVNP.CookLevin.Gen.P_TM_of_eventually_eq
#print axioms PVNP.PartIIManuscript.SAT_dense_npComplete
#print axioms PVNP.PartIIManuscript.P_TM_of_wcc_eventually
#print axioms PVNP.PartIIManuscript.conditional_np_safety_all
#print axioms PVNP.PartIIManuscript.conditional_np_safety
#print axioms PVNP.PartIIManuscript.no_np_complete_decider

-- I-11 unrestricted-encoder diagonal scope countermodel.
#print axioms PVNP.PhysicalAudit.firstAnswer_value_unique
#print axioms PVNP.PhysicalAudit.tableFirstAccept_iff_mem
#print axioms PVNP.PhysicalAudit.diagonal_on_code
#print axioms PVNP.PhysicalAudit.diagonal_not_mem_P_TM
#print axioms PVNP.PhysicalAudit.unrestricted_phys_ne_P_TM

-- Consolidated Phase XI quadratic bound and finite toroidal consistency proof.
#print axioms PVNP.PhaseXIQuadratic.sat_no_uniform_subquadratic
#print axioms PVNP.ToroidalDiagonal.edge_chain_constant
#print axioms PVNP.ToroidalDiagonal.odd_ring_no_state
#print axioms PVNP.ToroidalDiagonal.even_ring_has_state
#print axioms PVNP.ToroidalDiagonal.odd_ring_unsat
#print axioms PVNP.ToroidalDiagonal.even_ring_sat
#print axioms PVNP.ToroidalDiagonal.odd_encRing_not_SAT
#print axioms PVNP.ToroidalDiagonal.even_encRing_mem_SAT
#print axioms PVNP.ToroidalDiagonal.encRing_length

-- I-3 phase-locking logical sufficiency test.
#print axioms PVNP.PhaseLockScope.contradictory_unsat
#print axioms PVNP.PhaseLockScope.all_phases_zero_exists
#print axioms PVNP.PhaseLockScope.contradiction_phase_locked_but_not_logical
#print axioms PVNP.PhaseLockScope.bare_phase_lock_not_sat

-- Phase X: Boolean circuits and P_TM ⊆ Ppoly (tableau circuits for single-tape machines).
#print axioms PVNP.Circuits.Circuit.val_eq
#print axioms PVNP.Circuits.Circuit.val_embed
#print axioms PVNP.Circuits.poly_eval_mono
#print axioms PVNP.TMCircuit.content_next
#print axioms PVNP.TMCircuit.abs_head_run
#print axioms PVNP.TMCircuit.rule_congr_left
#print axioms PVNP.TMCircuit.val_cell
#print axioms PVNP.TMCircuit.tableau_eval
#print axioms PVNP.TMCircuit.size_tableau
#print axioms PVNP.TMCircuit.gate_eq_inp
#print axioms PVNP.TMCircuit.firstAnswer_true_iff
#print axioms PVNP.TMCircuit.P_TM_subset_Ppoly
#print axioms PVNP.TMCircuit.satLowerBound_of_not_Ppoly
#print axioms PVNP.TMCircuit.P_ne_NP_of_not_Ppoly
-- Phase X: non-uniform Cook–Levin for SAT_dense (Tseitin transformation, projections).
#print axioms PVNP.CircuitCookLevin.orComb_eval
#print axioms PVNP.CircuitCookLevin.gateCl_sat
#print axioms PVNP.CircuitCookLevin.tseitin_sat_iff
#print axioms PVNP.CircuitCookLevin.tseitin_vars
#print axioms PVNP.CircuitCookLevin.encDense_full
#print axioms PVNP.CircuitCookLevin.projCirc_eval
#print axioms PVNP.CircuitCookLevin.Ppoly_of_projection
#print axioms PVNP.CircuitCookLevin.inputOf_vsrc
#print axioms PVNP.CircuitCookLevin.verCirc_eval
#print axioms PVNP.CircuitCookLevin.mem_iff_verCirc
#print axioms PVNP.CircuitCookLevin.verCirc_size_le
#print axioms PVNP.CircuitCookLevin.NP_TM_subset_Ppoly_of_SAT
#print axioms PVNP.CircuitCookLevin.SAT_dense_mem_Ppoly_iff
#print axioms PVNP.CircuitCookLevin.satLowerBound_of_NP_not_Ppoly
#print axioms PVNP.CircuitCookLevin.P_ne_NP_of_NP_not_Ppoly
#print axioms PVNP.CircuitCookLevin.satLowerBound_of_not_subset

-- Phase XI original decoder and quantitative Part I results.
#print axioms PVNP.TwoPhaseDecoder.reader_outputs
#print axioms PVNP.TwoPhaseDecoder.stateBits_injective
#print axioms PVNP.TwoPhaseDecoder.stateBits_length
#print axioms PVNP.TwoPhaseDecoder.decM_outputs
#print axioms PVNP.TwoPhaseDecoder.decM_fp
#print axioms PVNP.PartIPsiSat.failed_clause_margin
#print axioms PVNP.PartIPsiSat.roundPhase_satisfies
#print axioms PVNP.PartIPsiSat.eventually_satisfies_of_energy_tendsto
#print axioms PVNP.PartIPsiSat.rounding_threshold_attained
#print axioms PVNP.SeparatorPrice.mesh_price
#print axioms PVNP.SeparatorPrice.contrast_of_readout
#print axioms PVNP.SeparatorPrice.binary_cut_price
#print axioms PVNP.FiniteHorizon.fast_through_horizon
#print axioms PVNP.FiniteHorizon.no_common_hard_horizon
#print axioms PVNP.CrossingSATMatrix.quadratic_every_budget

-- Phase XII: the original two-phase W_M construction in the uniform interface.
-- This bridge *assumes* FP writers for the original encoder and lattice window.
-- Its existence does not establish II-10 uniformity until those hypotheses are discharged.
#print axioms PVNP.TwoPhaseUniform.original_window
#print axioms PVNP.TwoPhaseUniform.original_decoder
#print axioms PVNP.TwoPhaseUniform.original_initial
#print axioms PVNP.TwoPhaseUniform.original_step
#print axioms PVNP.TwoPhaseUniform.original_cfg
#print axioms PVNP.TwoPhaseUniform.original_output
#print axioms PVNP.TwoPhaseUniform.original_uniform_decides
#print axioms PVNP.TwoPhaseUniform.original_state_bits_length
#print axioms PVNP.TwoPhaseUniform.original_state_bits_injective
#print axioms PVNP.TwoPhaseUniform.originalWindowCode_length
#print axioms PVNP.TwoPhaseUniform.originalInputCode_eq_encCfg
#print axioms PVNP.TwoPhaseUniform.stateBits_flatMap_length
#print axioms PVNP.TwoPhaseUniform.originalInputCode_length_le
#print axioms PVNP.TwoPhaseUniform.originalWindowCode_polynomial_length
#print axioms PVNP.TwoPhaseUniform.originalInputCode_polynomial_length

-- Reuse the verified finite-control Horner program to write unary W_M radius.
#print axioms PVNP.CookLevin.Gen.twoPhase_unary_radius

-- Phase XIII logical-energy certification theorems.
#print axioms PVNP.PartIPsiSat.unsat_logical_energy_gap
#print axioms PVNP.PartIPsiSat.sat_iff_exists_energy_lt_eighth
#print axioms PVNP.PartIPsiSat.noisy_energy_readout_certifies_sat
#print axioms PVNP.PartIPsiSat.unsat_rejects_low_energy_certificate

-- Phase XIII original W_M lattice-window bit shape.
#print axioms PVNP.TwoPhaseWindowShape.site_one_coordinate
#print axioms PVNP.TwoPhaseWindowShape.original_window_membership_iff
#print axioms PVNP.TwoPhaseWindowShape.original_window_bit

-- Phase XIV complete window word equivalence and length checks.
#print axioms PVNP.TwoPhaseWindowWord.bitmap_eq_interior
#print axioms PVNP.TwoPhaseWindowWord.windowWord_eq_latCode
#print axioms PVNP.TwoPhaseWindowWord.originalWindowCode_eq_windowWord
#print axioms PVNP.TwoPhaseWindowWord.windowWord_length
#print axioms PVNP.TwoPhaseWindowWord.originalWindowCode_length_from_word

-- Phase XIV, original W_M zero-radius explicit MTM writer.
#print axioms PVNP.TwoPhaseConstantWindow.zeroWindowMTM_outputs
#print axioms PVNP.TwoPhaseConstantWindow.originalWindowCode_zero
#print axioms PVNP.TwoPhaseConstantWindow.zeroWindowCode_fp

-- Phase XIV: finite-control literal-output machine and fixed-radius FP witness.
#print axioms PVNP.TwoPhaseFixedWord.literal_run_prefix
#print axioms PVNP.TwoPhaseFixedWord.literalMTM_outputs
#print axioms PVNP.TwoPhaseFixedWord.constantWindowCode_fp
-- Phase XVI finite toroidal CNF lock: kernel-checked logical equivalence and obstruction.
#print axioms PVNP.ToroidalCNFLock.rows_constant
#print axioms PVNP.ToroidalCNFLock.lock_iff_satisfiable
#print axioms PVNP.ToroidalCNFLock.bare_ring_lock_not_sat_classifier
-- Phase XVI: abstract quadratic amplitude-scaling obstruction.
#print axioms PVNP.SeparatorAmplitude.no_uniform_quadratic_price

-- Phase XVII: finite-row logical torus and normalized contrast theorems.
#print axioms PVNP.ToroidalFiniteRows.rowLock_iff_satisfiable
#print axioms PVNP.ToroidalFiniteRows.finiteTrace_length
#print axioms PVNP.SeparatorNormalizedRay.contrast_forces_quadratic_price
#print axioms PVNP.SeparatorNormalizedRay.price_is_sharp
#print axioms PVNP.TwoPhasePolynomialWriter.writer_clock_eq_polynomial
#print axioms PVNP.TwoPhasePolynomialWriter.writer_coeffs_length
#print axioms PVNP.TwoPhasePolynomialWriter.writer_clock_poly_bound
#print axioms PVNP.TwoPhasePolynomialWriter.expected_window_length_from_writer_clock
#print axioms PVNP.ToroidalFiniteRows.lock_rows_constant
#print axioms PVNP.TwoPhasePolynomialWriter.partially_normalized_current_input
#print axioms PVNP.TwoPhasePolynomialWriter.partially_normalized_extend
#print axioms PVNP.TwoPhasePolynomialWriter.normalize_raw_rule
#print axioms PVNP.TwoPhasePolynomialWriter.normalization_cfg_step
#print axioms PVNP.TwoPhasePolynomialWriter.timePoly_eval
#print axioms PVNP.TwoPhasePolynomialWriter.initialized_sentinel_tape
#print axioms PVNP.TwoPhasePolynomialWriter.start_to_mark
#print axioms PVNP.TwoPhasePolynomialWriter.mark_to_normalize
#print axioms PVNP.TwoPhasePolynomialWriter.run_normalizes_input
#print axioms PVNP.TwoPhasePolynomialWriter.windowMTM_normalization
#print axioms PVNP.TwoPhasePolynomialWriter.inputMTM_normalization

-- Phase XVIII: actual machine return sweep and first assembled instruction.
#print axioms PVNP.TwoPhasePolynomialWriter.normalized_end_blank
#print axioms PVNP.TwoPhasePolynomialWriter.normalized_nonnegative_not_sentinel
#print axioms PVNP.TwoPhasePolynomialWriter.return_step_non_sentinel
#print axioms PVNP.TwoPhasePolynomialWriter.return_step_sentinel
#print axioms PVNP.TwoPhasePolynomialWriter.return_walk
#print axioms PVNP.TwoPhasePolynomialWriter.normalization_end_step
#print axioms PVNP.TwoPhasePolynomialWriter.return_dispatch_after_normalization
#print axioms PVNP.TwoPhasePolynomialWriter.run_to_first_instruction
-- Phase XVIII continuation: complete pre-dispatch nonhalting interval.
#print axioms PVNP.TwoPhasePolynomialWriter.return_walk_prefix
#print axioms PVNP.TwoPhasePolynomialWriter.run_return_prefix
#print axioms PVNP.TwoPhasePolynomialWriter.normalization_not_halting
#print axioms PVNP.TwoPhasePolynomialWriter.return_not_halting
#print axioms PVNP.TwoPhasePolynomialWriter.not_halting_before_first_instruction
#print axioms PVNP.TwoPhasePolynomialWriter.windowMTM_not_halting_before_entry
#print axioms PVNP.TwoPhasePolynomialWriter.inputMTM_not_halting_before_entry
#print axioms PVNP.TwoPhasePolynomialWriter.outputs_of_assembled_body
-- Phase XVIII exact terminal scan and original MTM.Outputs composition.
#print axioms PVNP.TwoPhasePolynomialWriter.finish_run_prefix
#print axioms PVNP.TwoPhasePolynomialWriter.finish_scan_first_halt
#print axioms PVNP.TwoPhasePolynomialWriter.outputs_of_prepared_finish
-- Phase XVIII actual-machine certificate interface for original II-10 FP.
#print axioms PVNP.TwoPhasePolynomialWriter.fp_of_finish_certificate
#print axioms PVNP.TwoPhasePolynomialWriter.originalWindowCode_fp_of_finish_certificate
#print axioms PVNP.TwoPhasePolynomialWriter.originalInputCode_fp_of_finish_certificate
#print axioms PVNP.TwoPhasePolynomialWriter.originalUniform_of_finish_certificates
