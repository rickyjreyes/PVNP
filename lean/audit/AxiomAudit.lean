import PVNP
/-! Axiom audit for the principal PVNP theorems (run with `lake env lean audit/AxiomAudit.lean`).
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

-- Phase XVIII: II-10 at its original scope. The actual polynomial-radius writers
-- `windowMTM p` and `inputMTM M p` are polynomial-time transducers for the original codes.
#print axioms PVNP.TwoPhasePolynomialWriter.ret_walk
#print axioms PVNP.TwoPhasePolynomialWriter.exec_copy
#print axioms PVNP.TwoPhasePolynomialWriter.exec_take_hit
#print axioms PVNP.TwoPhasePolynomialWriter.exec_take_miss
#print axioms PVNP.TwoPhasePolynomialWriter.exec_inc_in
#print axioms PVNP.TwoPhasePolynomialWriter.exec_inc_end
#print axioms PVNP.TwoPhasePolynomialWriter.exec_emit_in
#print axioms PVNP.TwoPhasePolynomialWriter.exec_emit_end
#print axioms PVNP.TwoPhasePolynomialWriter.exec_next_hit
#print axioms PVNP.TwoPhasePolynomialWriter.exec_next_miss
#print axioms PVNP.TwoPhasePolynomialWriter.exec_head
#print axioms PVNP.TwoPhasePolynomialWriter.exec_finish
#print axioms PVNP.TwoPhasePolynomialWriter.Exec.trans
#print axioms PVNP.TwoPhasePolynomialWriter.Exec.inc
#print axioms PVNP.TwoPhasePolynomialWriter.Exec.emit
#print axioms PVNP.TwoPhasePolynomialWriter.Exec.next_hit
#print axioms PVNP.TwoPhasePolynomialWriter.Exec.head
#print axioms PVNP.TwoPhasePolynomialWriter.word_emits
#print axioms PVNP.TwoPhasePolynomialWriter.repeated_emits
#print axioms PVNP.TwoPhasePolynomialWriter.inner_loop
#print axioms PVNP.TwoPhasePolynomialWriter.outer_loop
#print axioms PVNP.TwoPhasePolynomialWriter.stage_sem
#print axioms PVNP.TwoPhasePolynomialWriter.horner_emits
#print axioms PVNP.TwoPhasePolynomialWriter.stages_emits
#print axioms PVNP.TwoPhasePolynomialWriter.windowBody_emits
#print axioms PVNP.TwoPhasePolynomialWriter.inputBodyG_emits
#print axioms PVNP.TwoPhasePolynomialWriter.normalize_steps
#print axioms PVNP.TwoPhasePolynomialWriter.assemble_outputs
#print axioms PVNP.TwoPhasePolynomialWriter.hv_coeffs
#print axioms PVNP.TwoPhasePolynomialWriter.winTail_eq_windowWord
#print axioms PVNP.TwoPhasePolynomialWriter.inW_eq_originalInputCode
#print axioms PVNP.TwoPhasePolynomialWriter.windowMTM_outputs
#print axioms PVNP.TwoPhasePolynomialWriter.inputMTM_outputs
-- Also registered by the integration branch of PR #72 (literal original machines).
#print axioms PVNP.TwoPhasePolynomialWriter.Steps.trans
#print axioms PVNP.TwoPhasePolynomialWriter.StagesSpec
#print axioms PVNP.TwoPhasePolynomialWriter.assemble_spec
#print axioms PVNP.TwoPhasePolynomialWriter.originalWindowCode_fp
#print axioms PVNP.TwoPhasePolynomialWriter.originalInputCode_fp
#print axioms PVNP.TwoPhasePolynomialWriter.originalWM
#print axioms PVNP.TwoPhasePolynomialWriter.originalWM_decides
#print axioms PVNP.TwoPhasePolynomialWriter.originalWM_first_answer
#print axioms PVNP.TwoPhasePolynomialWriter.P_Turing_subset_P_disc_original
#print axioms PVNP.TwoPhasePolynomialWriter.originalWM_mem_P_disc
#print axioms PVNP.TwoPhasePolynomialWriter.P_Turing_subset_P_disc_by_original

-- Phase XVIII, I-31: no uniform separator price for the frozen trajectory class.
#print axioms PVNP.SeparatorFrozen.traj_solves
#print axioms PVNP.SeparatorFrozen.traj_periodic
#print axioms PVNP.SeparatorFrozen.traj_norm
#print axioms PVNP.SeparatorFrozen.traj_contrast
#print axioms PVNP.SeparatorFrozen.segment_subset
#print axioms PVNP.SeparatorFrozen.hausdorff_segment
#print axioms PVNP.SeparatorFrozen.interface_ge
#print axioms PVNP.SeparatorFrozen.Phi_wave_le
#print axioms PVNP.SeparatorFrozen.Phi_traj_le
#print axioms PVNP.SeparatorFrozen.no_uniform_separator_price
#print axioms PVNP.SeparatorFrozen.separator_price_hypothesis_false
#print axioms PVNP.SeparatorFrozen.thetaEps_dominated
#print axioms PVNP.SeparatorFrozen.separator_price_false_thetaEps
#print axioms PVNP.SeparatorFrozen.stripe_device_decides
#print axioms PVNP.SeparatorFrozen.stripe_device_violates
#print axioms PVNP.SeparatorFrozen.Phi_bump_le
#print axioms PVNP.SeparatorFrozen.bump_interface_ge
#print axioms PVNP.SeparatorFrozen.no_uniform_price_modulus
#print axioms PVNP.SeparatorFrozen.sq_integral_le
#print axioms PVNP.SeparatorFrozen.layer_price
#print axioms PVNP.SeparatorFrozen.layer_price_sharp

-- Phase XVIII, I-32: expander interface growth is as hard as P_TM ≠ NP_TM.
#print axioms PVNP.ExpanderInterface.expanderGrowth_of_every_length
#print axioms PVNP.ExpanderInterface.sep_of_const
#print axioms PVNP.ExpanderInterface.sep_const
#print axioms PVNP.ExpanderInterface.constDecides_mem_P_TM
#print axioms PVNP.ExpanderInterface.expanderGrowth_const_iff
#print axioms PVNP.ExpanderInterface.expanderGrowth_false_of_mem_P
#print axioms PVNP.ExpanderInterface.expanderGrowth_SAT_iff
#print axioms PVNP.ExpanderInterface.expanderGrowth_implies_P_ne_NP
-- Phase XVIII, I-37, I-3, III-22: time reversal and no locking for the frozen flow.
#print axioms PVNP.Torus.conjH_conjH
#print axioms PVNP.Torus.conjH_isometry
#print axioms PVNP.Torus.fnl_conj
#print axioms PVNP.Torus.fc_conj
#print axioms PVNP.Torus.isSolution_reverse
#print axioms PVNP.Torus.isSolution_shift
#print axioms PVNP.Torus.backward_eq_forward_conj
#print axioms PVNP.Torus.flow_neg
#print axioms PVNP.Torus.infDist_conjH_le
#print axioms PVNP.Torus.no_locking
#print axioms PVNP.Torus.unstable_or_unreachable
#print axioms PVNP.Torus.realStates_conj
#print axioms PVNP.Torus.field_real_of_realState
#print axioms PVNP.Torus.phaseOrbit_conj
#print axioms PVNP.Torus.no_locking_phaseOrbit
#print axioms PVNP.Torus.no_locking_realStates
-- Phase XVIII, I-16 and I-2.
#print axioms PVNP.DepthBarrier.wccDepth_SAT_iff
#print axioms PVNP.DepthBarrier.wccdDepth_SAT_iff
#print axioms PVNP.DepthBarrier.uniform_depth_SAT_iff
#print axioms PVNP.DepthBarrier.explicit_state_constructible
#print axioms PVNP.DepthBarrier.no_separation_of_all_constructible
#print axioms PVNP.DepthBarrier.explicit_no_separation

-- Physical readout capacity: conditional, PDE-derived, two-outcome contrast.
#print axioms PVNP.PhysicalReadoutCapacity.detector_contrast_budget
#print axioms PVNP.PhysicalReadoutCapacity.two_outcomes_require_change
#print axioms PVNP.PhysicalReadoutCapacity.binary_readout_resource_disjunction
#print axioms PVNP.PhysicalReadoutCapacity.no_binary_readout_below_both_budgets

-- Conditional WCT SAT physical readout. These do not prove a SAT time lower bound.
#print axioms PVNP.PhysicalSATReadout.margin_implies_contrast
#print axioms PVNP.PhysicalSATReadout.noisy_margin_implies_contrast
#print axioms PVNP.PhysicalSATReadout.two_outcomes_with_initial_skew
#print axioms PVNP.PhysicalSATReadout.skewed_binary_readout_resource_disjunction
#print axioms PVNP.PhysicalSATReadout.sat_pair_readout_resource_disjunction
#print axioms PVNP.PhysicalSATReadout.noisy_sat_pair_readout_resource_disjunction
#print axioms PVNP.PhysicalSATReadout.combined_budget_of_disjunction

-- Interwoven-Ψ SAT energy model (Phase B). Energy landscapes only: no dynamics, no time bound.
#print axioms PVNP.InterwovenSAT.sat_iff_zero_energySB
#print axioms PVNP.InterwovenSAT.unsat_energySB_gap
#print axioms PVNP.InterwovenSAT.sat_iff_energySB_lt_eighth
#print axioms PVNP.InterwovenSAT.measure_satisfies
#print axioms PVNP.InterwovenSAT.xor_energy_pos
#print axioms PVNP.InterwovenSAT.xor_energy_ge_quarter
#print axioms PVNP.InterwovenSAT.xor_energy_at_I
#print axioms PVNP.InterwovenSAT.single_var_energy
#print axioms PVNP.InterwovenSAT.naive_ground_energy_blind
#print axioms PVNP.InterwovenSAT.naive_zero_energy_fails
#print axioms PVNP.InterwovenSAT.naive_threshold_fails
#print axioms PVNP.InterwovenSAT.min_formulation_vacuous
#print axioms PVNP.InterwovenSAT.satisfying_not_ground
#print axioms PVNP.InterwovenSAT.sat_iff_EminSB_eq_zero
#print axioms PVNP.InterwovenSAT.unsat_iff_EminSB_ge
#print axioms PVNP.InterwovenSAT.naive_Emin
#print axioms PVNP.InterwovenSAT.sat_of_locks
#print axioms PVNP.InterwovenSAT.locks_iff_sat_iff
#print axioms PVNP.InterwovenSAT.unsat_gap_general
#print axioms PVNP.InterwovenSAT.toroidal_locking_iff_unsat
#print axioms PVNP.InterwovenSAT.naive_toroidal_locking_fails

-- Frozen-torus SAT device bound and preloaded-answer countermodel (Phase C). No SAT lower bound.
#print axioms PVNP.WCTSATDevice.Gam_nonneg
#print axioms PVNP.WCTSATDevice.Jdet_const_of_Gam_eq_zero
#print axioms PVNP.WCTSATDevice.change_budget
#print axioms PVNP.WCTSATDevice.device_pair_budget
#print axioms PVNP.WCTSATDevice.budget_mono
#print axioms PVNP.WCTSATDevice.Gam_le_of_bounds
#print axioms PVNP.WCTSATDevice.device_pair_budget_of_preparation
#print axioms PVNP.WCTSATDevice.co_mode
#print axioms PVNP.WCTSATDevice.fc_const
#print axioms PVNP.WCTSATDevice.zeroMode_isSolution
#print axioms PVNP.WCTSATDevice.Dc_zeroMode
#print axioms PVNP.WCTSATDevice.budget_zeroMode
#print axioms PVNP.WCTSATDevice.mass_zeroMode
#print axioms PVNP.WCTSATDevice.Jdet_mode_zero
#print axioms PVNP.WCTSATDevice.rev_dco
#print axioms PVNP.WCTSATDevice.aW_dco_pos
#print axioms PVNP.WCTSATDevice.Jdet_zeroMode_detector
#print axioms PVNP.WCTSATDevice.Gam_zeroMode_pos
#print axioms PVNP.WCTSATDevice.preloaded_device
#print axioms PVNP.WCTSATDevice.preloaded_skew_eq_contrast
#print axioms PVNP.WCTSATDevice.oneClause_sat
#print axioms PVNP.WCTSATDevice.blindness_necessary

-- Superpolynomial-resource barrier (Phase D): such a bound for SAT proves P_TM ≠ NP_TM.
#print axioms PVNP.WCTSATScaling.not_superpoly_of_poly
#print axioms PVNP.WCTSATScaling.superpoly_implies_not_mem_P
#print axioms PVNP.WCTSATScaling.superpoly_SAT_implies_P_ne_NP
#print axioms PVNP.WCTSATScaling.zdecides_iff
#print axioms PVNP.WCTSATScaling.ZeroDev.res_le
#print axioms PVNP.WCTSATScaling.zero_charges_P
#print axioms PVNP.WCTSATScaling.zdecides_mem_P
#print axioms PVNP.WCTSATScaling.zeroSuperpoly_iff
#print axioms PVNP.WCTSATScaling.zeroSuperpoly_SAT_iff
#print axioms PVNP.WCTSATScaling.torus_superpoly_implies_P_ne_NP

-- Blind frozen-torus SAT device with one fixed budget (Phase XX). Its encoder is a SAT decider.
#print axioms PVNP.WCTSATBlind.co_twoMode
#print axioms PVNP.WCTSATBlind.pr_dco_tc
#print axioms PVNP.WCTSATBlind.inner_eq_tsum
#print axioms PVNP.WCTSATBlind.Jdet_twoMode
#print axioms PVNP.WCTSATBlind.qf_e1v
#print axioms PVNP.WCTSATBlind.Jdot_twoMode
#print axioms PVNP.WCTSATBlind.flux_condition_of_nonpos
#print axioms PVNP.WCTSATBlind.exists_pos_ne_of_hasDerivAt
#print axioms PVNP.WCTSATBlind.blind_pair_exists
#print axioms PVNP.WCTSATBlind.blind_device

-- WCT sign-blind SAT-energy gap under arbitrary charged finite-radius stages.
#print axioms PVNP.WCTLocalSATEnergy.distalFormula_sat_iff
#print axioms PVNP.WCTLocalSATEnergy.distalFormula_energy_gap_iff
#print axioms PVNP.WCTLocalSATEnergy.distalFormula_ground_energy_iff
#print axioms PVNP.WCTLocalSATEnergy.sat_energy_requires_causal_coverage
#print axioms PVNP.WCTLocalSATEnergy.sat_ground_energy_requires_causal_coverage
#print axioms PVNP.WCTLocalSATEnergy.no_sat_energy_decider_below_cone
#print axioms PVNP.WCTLocalSATEnergy.last_site_sat_energy_linear_bound

-- Phase XXI: n-bit distributed 3-CNF, SAT truth, and charged light-cone lower bounds.
#print axioms PVNP.WCTDistributedSAT.sourceFormula_length
#print axioms PVNP.WCTDistributedSAT.formulaOfBits_sat_iff
#print axioms PVNP.WCTDistributedSAT.sourceFormula_sat_iff
#print axioms PVNP.WCTDistributedSAT.allTrue_sat
#print axioms PVNP.WCTDistributedSAT.oneFalse_unsat
#print axioms PVNP.WCTDistributedSAT.sources_agree_before
#print axioms PVNP.WCTDistributedSAT.no_distributed_sat_decider_below_cone
#print axioms PVNP.WCTDistributedSAT.distributed_sat_requires_causal_coverage
#print axioms PVNP.WCTDistributedSAT.distributed_energy_requires_causal_coverage
#print axioms PVNP.WCTDistributedSAT.distributed_ground_energy_requires_causal_coverage
#print axioms PVNP.WCTDistributedSAT.distributed_energy_last_site_linear
-- Part I I-3: explicit satisfiable 3-CNF with a nonglobal sign-blind local well.
#print axioms PVNP.SATFalseWell.trapFormula_sat
#print axioms PVNP.SATFalseWell.sPos_nonneg
#print axioms PVNP.SATFalseWell.Elogic_trapFormula
#print axioms PVNP.SATFalseWell.trapEnergy_local_lower
#print axioms PVNP.SATFalseWell.trapEnergy_false
#print axioms PVNP.SATFalseWell.trapEnergy_true
#print axioms PVNP.SATFalseWell.false_score_is_local_min
#print axioms PVNP.SATFalseWell.false_phase_energy
#print axioms PVNP.SATFalseWell.true_phase_energy
#print axioms PVNP.SATFalseWell.signblind_false_local_well

-- Part II: quantitative high-frequency tail from the actual torus Fourier weights.
#print axioms PVNP.TorusSpectralTail.finite_high_frequency_mass_bound
#print axioms PVNP.TorusSpectralTail.finite_tail_mass_from_curvature_budget

-- Part III: conservation-derived frozen-torus regularized curvature majorant.
#print axioms PVNP.WCTRegularizedCeiling.lapBudget_nonneg
#print axioms PVNP.WCTRegularizedCeiling.frozen_torus_laplacian_ceiling
#print axioms PVNP.WCTRegularizedCeiling.frozen_torus_laplacian_squared_ceiling
#print axioms PVNP.WCTRegularizedCeiling.regularized_laplacian_envelope_ceiling

-- Part II: complete infinite torus Fourier tail control via H² and summability.
#print axioms PVNP.TorusSpectralTail.infinite_high_frequency_mass_bound
#print axioms PVNP.TorusSpectralTail.infinite_tail_mass_from_curvature_budget

-- Phase XXII, I-37: locking configurations of a field on the spatial torus T_L².
#print axioms PVNP.SpatialLocking.rel_admissible
#print axioms PVNP.SpatialLocking.qf_pos
#print axioms PVNP.SpatialLocking.summable_grad2
#print axioms PVNP.SpatialLocking.grad2_nonneg
#print axioms PVNP.SpatialLocking.grad2_mode_zero
#print axioms PVNP.SpatialLocking.eq_mode_of_grad2_eq_zero
#print axioms PVNP.SpatialLocking.pt_mode
#print axioms PVNP.SpatialLocking.dens_nonneg
#print axioms PVNP.SpatialLocking.rel_bitField
#print axioms PVNP.SpatialLocking.norm_bitField
#print axioms PVNP.SpatialLocking.sat_iff_locked
#print axioms PVNP.SpatialLocking.no_locked_iff_unsat
#print axioms PVNP.SpatialLocking.locked_iff
#print axioms PVNP.SpatialLocking.rel_phase
#print axioms PVNP.SpatialLocking.locked_frozen_flow
#print axioms PVNP.SpatialLocking.frozen_flow_preserves_locks
#print axioms PVNP.SpatialLocking.summable_mass
#print axioms PVNP.SpatialLocking.norm_Ac_sq
#print axioms PVNP.SpatialLocking.kin_eq
#print axioms PVNP.SpatialLocking.summable_kin
#print axioms PVNP.SpatialLocking.eq_mode_of_coeff
#print axioms PVNP.SpatialLocking.kin_ge
#print axioms PVNP.SpatialLocking.eq_mode_of_kin_eq
#print axioms PVNP.SpatialLocking.box_real_univ
#print axioms PVNP.SpatialLocking.bound_field
#print axioms PVNP.SpatialLocking.pot_ge
#print axioms PVNP.SpatialLocking.ham_ge
#print axioms PVNP.SpatialLocking.eq_mode_of_ham_eq
#print axioms PVNP.SpatialLocking.ham_mode
#print axioms PVNP.SpatialLocking.approach_zeroMode
#print axioms PVNP.SpatialLocking.mode_apply_zero
#print axioms PVNP.SpatialLocking.no_attracting_locks

-- Phase XXII, I-3: the false well traps every energy-monotone evolution.
#print axioms PVNP.SATDynamics.sPos_eq
#print axioms PVNP.SATDynamics.energy_lower_in_box
#print axioms PVNP.SATDynamics.energy_monotone_trapped
#print axioms PVNP.SATDynamics.false_corner_in_box
#print axioms PVNP.SATDynamics.false_corner_energy
#print axioms PVNP.SATDynamics.flipLit_flipLit
#print axioms PVNP.SATDynamics.flipF_flipF
#print axioms PVNP.SATDynamics.flipField_flipField
#print axioms PVNP.SATDynamics.admissible_flipField
#print axioms PVNP.SATDynamics.sq_flipField
#print axioms PVNP.SATDynamics.score_flip
#print axioms PVNP.SATDynamics.clausePen_flip
#print axioms PVNP.SATDynamics.Elog_flip
#print axioms PVNP.SATDynamics.edges_flipF
#print axioms PVNP.SATDynamics.hyperedges_flipF
#print axioms PVNP.SATDynamics.vars_flipF
#print axioms PVNP.SATDynamics.glap_flipF
#print axioms PVNP.SATDynamics.energySB_flip
#print axioms PVNP.SATDynamics.litVal_flip
#print axioms PVNP.SATDynamics.sat_flipF
#print axioms PVNP.SATDynamics.flipField_false_corner
#print axioms PVNP.SATDynamics.corner_trapped
#print axioms PVNP.SATDynamics.no_corner_preparation_decides
#print axioms PVNP.SATDynamics.le_foldr_max
#print axioms PVNP.SATDynamics.var_lt_nvar
#print axioms PVNP.SATDynamics.sat_iff_corner_sweep
#print axioms PVNP.SATDynamics.corner_sweep_card
#print axioms PVNP.SATDynamics.efficient_device_and_simulation_imply_P_eq_NP

-- Phase XXII, I-2: readings of the symbolic separation conjecture; links to I-16 and I-32.
#print axioms PVNP.NonconstructibleFamily.familyModel_Pst
#print axioms PVNP.NonconstructibleFamily.familyModel_NPst
#print axioms PVNP.NonconstructibleFamily.unrestricted_family_separation
#print axioms PVNP.NonconstructibleFamily.npFamily_separation_iff
#print axioms PVNP.NonconstructibleFamily.npFamily_SAT_iff
#print axioms PVNP.NonconstructibleFamily.mode_zero_apply
#print axioms PVNP.NonconstructibleFamily.zeroMode_zero
#print axioms PVNP.NonconstructibleFamily.wavefield_injective
#print axioms PVNP.NonconstructibleFamily.wavefield_constructible_iff
#print axioms PVNP.NonconstructibleFamily.wavefield_separation_iff
#print axioms PVNP.NonconstructibleFamily.npFamily_iff_wccDepth
#print axioms PVNP.NonconstructibleFamily.npFamily_iff_expanderGrowth

-- Phase XXII, I-11: zero-mode class equality and readout precision.
#print axioms PVNP.ContinuumPrecision.zeroDev_languages_eq_P_TM
#print axioms PVNP.ContinuumPrecision.Cdet_nonneg
#print axioms PVNP.ContinuumPrecision.Jdet_lipschitz
#print axioms PVNP.ContinuumPrecision.readout_precision
#print axioms PVNP.ContinuumPrecision.decision_robust
#print axioms PVNP.ContinuumPrecision.precision_suffices
#print axioms PVNP.ContinuumPrecision.approx_trajectory_close
#print axioms PVNP.ContinuumPrecision.approx_readout

-- Phase XXIII: forced barrier and finite Fourier certificates
#print axioms PVNP.SATDynamics.energy_cap_trapped
#print axioms PVNP.SATDynamics.readout_requires_energy_excursion
#print axioms PVNP.SATDynamics.bounded_forcing_cannot_readout
#print axioms PVNP.TorusGalerkin.trunc_norm_le
#print axioms PVNP.TorusGalerkin.trunc_sub
#print axioms PVNP.TorusGalerkin.galerkin_support
#print axioms PVNP.TorusGalerkin.galerkin_lipschitz
#print axioms PVNP.TorusGalerkin.consistency_bound
#print axioms PVNP.TorusGalerkin.galerkin_consistent
#print axioms PVNP.TorusGalerkin.residual_certificate
#print axioms PVNP.TorusGalerkin.no_uniform_H2_cutoff
#print axioms PVNP.TorusGalerkin.higher_regularity_tail
#print axioms PVNP.TorusGalerkin.certified_readout
#print axioms PVNP.SATDynamics.every_corner_requires_excursion
#print axioms PVNP.SATDynamics.escape_admissible
#print axioms PVNP.SATDynamics.escape_continuous
#print axioms PVNP.SATDynamics.escape_start
#print axioms PVNP.SATDynamics.escape_end
#print axioms PVNP.SATDynamics.escape_curvature
#print axioms PVNP.SATDynamics.escape_energy
#print axioms PVNP.SATDynamics.escape_energy_bound
#print axioms PVNP.SATDynamics.escape_readout
#print axioms PVNP.SATDynamics.trapEnergy_decomposition
#print axioms PVNP.SATDynamics.trapEnergy_mean_lower
#print axioms PVNP.SATDynamics.trapEnergy_before_saddle
#print axioms PVNP.SATDynamics.trapEnergy_saddle
#print axioms PVNP.SATDynamics.readout_requires_sharp_peak

-- Phase XXIV: finite Fourier trajectory convergence
#print axioms PVNP.TorusGalerkin.trunc_lipschitz
#print axioms PVNP.TorusGalerkin.compact_uniform_tail
#print axioms PVNP.TorusGalerkin.clipped_support
#print axioms PVNP.TorusGalerkin.clipped_lipschitz
#print axioms PVNP.TorusGalerkin.clipped_bound
#print axioms PVNP.TorusGalerkin.clipped_continuous_time
#print axioms PVNP.TorusGalerkin.clipped_eq_galerkin
#print axioms PVNP.TorusGalerkin.clipped_uniform_consistency
#print axioms PVNP.TorusGalerkin.exists_local_clipped
#print axioms PVNP.TorusGalerkin.exists_global_clipped
#print axioms PVNP.TorusGalerkin.clipped_trajectory_support
#print axioms PVNP.TorusGalerkin.gronwall_diagonal_scale
#print axioms PVNP.TorusGalerkin.gronwall_diagonal_mono
#print axioms PVNP.TorusGalerkin.clipped_trajectory_error
#print axioms PVNP.TorusGalerkin.exists_convergent_clipped
#print axioms PVNP.TorusGalerkin.exists_convergent_galerkin
#print axioms PVNP.TorusGalerkin.frozen_galerkin_approximation

-- Phase XXV: exact finite residual evaluation
#print axioms PVNP.TorusGalerkin.trunc_supported
#print axioms PVNP.TorusGalerkin.supported_trunc_eq
#print axioms PVNP.TorusGalerkin.support_mono
#print axioms PVNP.TorusGalerkin.support_U
#print axioms PVNP.TorusGalerkin.support_smul
#print axioms PVNP.TorusGalerkin.support_add
#print axioms PVNP.TorusGalerkin.support_conj
#print axioms PVNP.TorusGalerkin.support_mulH
#print axioms PVNP.TorusGalerkin.support_Fnl
#print axioms PVNP.TorusGalerkin.support_Gf
#print axioms PVNP.TorusGalerkin.finite_nonlinear_field
#print axioms PVNP.TorusGalerkin.finite_residual_sq
#print axioms PVNP.TorusGalerkin.finite_pr

-- Phase XXV: time-slab certification
#print axioms PVNP.TorusGalerkin.finite_U_increment
#print axioms PVNP.TorusGalerkin.finite_U_time_modulus
#print axioms PVNP.TorusGalerkin.finite_Gf_time_modulus
#print axioms PVNP.TorusGalerkin.affine_slab_residual

-- Effective weak-norm consistency
#print axioms PVNP.TorusGalerkin.weak_projection_tail
#print axioms PVNP.TorusGalerkin.weak_detector_lipschitz
#print axioms PVNP.TorusGalerkin.weak_detector_cutoff
#print axioms PVNP.TorusGalerkin.weak_mulH_comm
#print axioms PVNP.TorusGalerkin.weak_mul_bound
#print axioms PVNP.TorusGalerkin.weak_conj_norm
#print axioms PVNP.TorusGalerkin.weak_lip_mul
#print axioms PVNP.TorusGalerkin.weak_Fnl_sub_le
#print axioms PVNP.TorusGalerkin.weak_Gf_sub_le
#print axioms PVNP.TorusGalerkin.weak_consistency_bound

-- Finite Galerkin conservation and global existence
#print axioms PVNP.TorusGalerkin.trunc_co
#print axioms PVNP.TorusGalerkin.trunc_comm_U
#print axioms PVNP.TorusGalerkin.trunc_smul
#print axioms PVNP.TorusGalerkin.supported_inner_Lc
#print axioms PVNP.TorusGalerkin.supported_inner_Ac
#print axioms PVNP.TorusGalerkin.projected_inner_Lc_self
#print axioms PVNP.TorusGalerkin.U_galerkin
#print axioms PVNP.TorusGalerkin.galerkin_mass_deriv
#print axioms PVNP.TorusGalerkin.galerkin_ham_deriv
#print axioms PVNP.TorusGalerkin.galerkin_conserved
#print axioms PVNP.TorusGalerkin.galerkin_apriori
#print axioms PVNP.TorusGalerkin.exists_global_galerkin

-- Effective global weak comparison
#print axioms PVNP.TorusGalerkin.Lc_injective
#print axioms PVNP.TorusGalerkin.weakLift_Lc
#print axioms PVNP.TorusGalerkin.weakField_Lc
#print axioms PVNP.TorusGalerkin.weakField_lipschitz
#print axioms PVNP.TorusGalerkin.weak_trajectory_error
#print axioms PVNP.TorusGalerkin.weak_galerkin_residual
#print axioms PVNP.TorusGalerkin.weak_galerkin_global_error

-- Cutoff-independent radius and detector error
#print axioms PVNP.TorusGalerkin.kinetic_norm_bound
#print axioms PVNP.TorusGalerkin.potBudget_nonneg
#print axioms PVNP.TorusGalerkin.potential_zero
#print axioms PVNP.TorusGalerkin.potential_upper
#print axioms PVNP.TorusGalerkin.initial_energy_upper
#print axioms PVNP.TorusGalerkin.uniformRadius_nonneg
#print axioms PVNP.TorusGalerkin.initial_radius_upper
#print axioms PVNP.TorusGalerkin.exists_uniform_galerkin
#print axioms PVNP.TorusGalerkin.weak_readout_error
#print axioms PVNP.TorusGalerkin.gronwall_proportional_le
#print axioms PVNP.TorusGalerkin.exists_certified_galerkin_readout
#print axioms PVNP.TorusGalerkin.detector_margin_from_cutoff
#print axioms PVNP.TorusGalerkin.detector_decision_preserved

-- Rounded Euler resource and radius certificates
#print axioms PVNP.TorusGalerkin.stepEnvelope_nonneg
#print axioms PVNP.TorusGalerkin.stepEnvelope_mono
#print axioms PVNP.TorusGalerkin.stepEnvelope_succ
#print axioms PVNP.TorusGalerkin.rounded_step_bootstrap
#print axioms PVNP.TorusGalerkin.rounded_step_budget
#print axioms PVNP.TorusGalerkin.galerkin_time_modulus
#print axioms PVNP.TorusGalerkin.galerkin_speed
#print axioms PVNP.TorusGalerkin.galerkin_euler_defect
#print axioms PVNP.TorusGalerkin.rounded_galerkin_euler

-- Exact finite detector
#print axioms PVNP.TorusGalerkin.finite_detector_sum
#print axioms PVNP.TorusGalerkin.finite_detector_dependence
#print axioms PVNP.TorusGalerkin.finite_detector_free_sum

-- Restricted resource envelopes and promise totality
#print axioms PVNP.RestrictedResourceBudget.cutoff_weight_lower
#print axioms PVNP.RestrictedResourceBudget.spatial_budget
#print axioms PVNP.RestrictedResourceBudget.step_count_budget
#print axioms PVNP.RestrictedResourceBudget.interval_decision_total
#print axioms PVNP.RestrictedResourceBudget.expanded_interval_width
#print axioms PVNP.RestrictedResourceBudget.expanded_interval_sound

-- Sideband amplification algebra
#print axioms PVNP.SidebandAmplification.growing_rate
#print axioms PVNP.SidebandAmplification.eigenvector
#print axioms PVNP.SidebandAmplification.explicit_growing_sideband
#print axioms PVNP.SidebandAmplification.exponential_solution
#print axioms PVNP.SidebandAmplification.rotated_fnl_deriv
#print axioms PVNP.SidebandAmplification.actual_field_first_variation
#print axioms PVNP.SidebandAmplification.sideband_energy_deriv
#print axioms PVNP.SidebandAmplification.sideband_energy_conserved
#print axioms PVNP.SidebandAmplification.stable_sideband_bound
#print axioms PVNP.SidebandAmplification.stable_sideband_ratio_bound
#print axioms PVNP.SidebandAmplification.stable_background_coefficients
#print axioms PVNP.SidebandAmplification.unstable_sideband_iff
#print axioms PVNP.SidebandAmplification.detector_directional_expansion
#print axioms PVNP.SidebandAmplification.detector_directional_deriv

-- Phase XXVI: exponential sensitivity is not exponential computational cost.
#print axioms PVNP.ExpTaylor.exp_eq_tsum
#print axioms PVNP.ExpTaylor.term_succ
#print axioms PVNP.ExpTaylor.term_shift_le
#print axioms PVNP.ExpTaylor.exp_sub_partial_eq
#print axioms PVNP.ExpTaylor.exp_tail_le
#print axioms PVNP.ExpTaylor.exp_partial_sum_error
#print axioms PVNP.ExpTaylor.taylor_terms_for_precision
#print axioms PVNP.ExpTaylor.sideband_growth_taylor

-- Phase XXVII: finite-bit exponential partial sum.
#print axioms PVNP.ExpTaylorBits.fallQ_mul
#print axioms PVNP.ExpTaylorBits.fallQ_le
#print axioms PVNP.ExpTaylorBits.taylorDen_pos
#print axioms PVNP.ExpTaylorBits.partial_sum_eq
#print axioms PVNP.ExpTaylorBits.num_le_pow
#print axioms PVNP.ExpTaylorBits.den_le_pow
#print axioms PVNP.ExpTaylorBits.round_error
#print axioms PVNP.ExpTaylorBits.exp_dyadic_approx
#print axioms PVNP.ExpTaylorBits.dyadic_num_le

-- Phase XXVIII: cubic–quintic Taylor majorant.
#print axioms PVNP.TaylorMajorant.wt_pos
#print axioms PVNP.TaylorMajorant.wt_zero
#print axioms PVNP.TaylorMajorant.cauchy_nonneg
#print axioms PVNP.TaylorMajorant.sum_wt_le
#print axioms PVNP.TaylorMajorant.sum_wt_le_two
#print axioms PVNP.TaylorMajorant.wt_mul_le
#print axioms PVNP.TaylorMajorant.weighted_conv_le
#print axioms PVNP.TaylorMajorant.cauchy_bound
#print axioms PVNP.TaylorMajorant.powers_bound
#print axioms PVNP.TaylorMajorant.wt_step
#print axioms PVNP.TaylorMajorant.majorant
#print axioms PVNP.TaylorMajorant.taylor_term_le
#print axioms PVNP.TaylorMajorant.taylor_tail_le

-- Phase XXVIII: norm reduction of the actual nonlinearity to the Taylor majorant.
#print axioms PVNP.GalerkinTaylor.cauchy_comm
#print axioms PVNP.GalerkinTaylor.cauchy_mono
#print axioms PVNP.GalerkinTaylor.cauchy_smul_left
#print axioms PVNP.GalerkinTaylor.norm_cauchyH_le
#print axioms PVNP.GalerkinTaylor.norm_conjSeq
#print axioms PVNP.GalerkinTaylor.nseq_nonneg
#print axioms PVNP.GalerkinTaylor.cauchyH_step
#print axioms PVNP.GalerkinTaylor.norm_fnlCoeff_le
#print axioms PVNP.GalerkinTaylor.galerkin_taylor_majorant

-- Phase XXVIII: identification of the actual Galerkin trajectory with its Taylor series.
#print axioms PVNP.GalerkinTaylor.hasSum_mulH
#print axioms PVNP.GalerkinTaylor.real_smul_eq
#print axioms PVNP.GalerkinTaylor.mulH_real_smul
#print axioms PVNP.GalerkinTaylor.hasSum_mulH_pow
#print axioms PVNP.GalerkinTaylor.conjH_add
#print axioms PVNP.GalerkinTaylor.conjH_real_smul
#print axioms PVNP.GalerkinTaylor.hasSum_conjSeq
#print axioms PVNP.GalerkinTaylor.sum_range_wt_le_two
#print axioms PVNP.GalerkinTaylor.summable_wt
#print axioms PVNP.GalerkinTaylor.tsum_wt_le_two
#print axioms PVNP.GalerkinTaylor.norm_pow_smul_le
#print axioms PVNP.GalerkinTaylor.Dom.summable
#print axioms PVNP.GalerkinTaylor.Dom.hasSum
#print axioms PVNP.GalerkinTaylor.Dom.cprod
#print axioms PVNP.GalerkinTaylor.Dom.conj
#print axioms PVNP.GalerkinTaylor.hasSum_Fnl
#print axioms PVNP.GalerkinTaylor.om_nonneg
#print axioms PVNP.GalerkinTaylor.omSum_nonneg
#print axioms PVNP.GalerkinTaylor.om_le_omSum
#print axioms PVNP.GalerkinTaylor.norm_omMul_le
#print axioms PVNP.GalerkinTaylor.Aop_apply
#print axioms PVNP.GalerkinTaylor.norm_Aop_le
#print axioms PVNP.GalerkinTaylor.hasDerivAt_phys
#print axioms PVNP.GalerkinTaylor.pre_eq_coeff
#print axioms PVNP.GalerkinTaylor.coeff_zero
#print axioms PVNP.GalerkinTaylor.cauchyH_congr
#print axioms PVNP.GalerkinTaylor.fnlCoeff_congr
#print axioms PVNP.GalerkinTaylor.rhs_congr
#print axioms PVNP.GalerkinTaylor.coeff_succ
#print axioms PVNP.GalerkinTaylor.coeff_recursion
#print axioms PVNP.GalerkinTaylor.coeff_dom
#print axioms PVNP.GalerkinTaylor.rate_nonneg
#print axioms PVNP.GalerkinTaylor.nat_mul_wt_le
#print axioms PVNP.GalerkinTaylor.trunc_add
#print axioms PVNP.GalerkinTaylor.truncL_apply
#print axioms PVNP.GalerkinTaylor.real_smul_comm_I
#print axioms PVNP.GalerkinTaylor.hasSum_rhs
#print axioms PVNP.GalerkinTaylor.norm_deriv_term_le
#print axioms PVNP.GalerkinTaylor.hasDerivAt_series
#print axioms PVNP.GalerkinTaylor.series_zero
#print axioms PVNP.GalerkinTaylor.norm_series_le
#print axioms PVNP.GalerkinTaylor.series_solves
#print axioms PVNP.GalerkinTaylor.physField_lipschitz
#print axioms PVNP.GalerkinTaylor.galerkin_taylor_series
#print axioms PVNP.GalerkinTaylor.taylor_poly_error
#print axioms PVNP.GalerkinTaylor.radius_admissible
#print axioms PVNP.GalerkinTaylor.actual_galerkin_taylor
#print axioms PVNP.GalerkinTaylor.galerkin_trajectory_taylor

-- Phase XXVIII: certified multi-step Taylor integrator.
#print axioms PVNP.GalerkinTaylor.tail_of_dom
#print axioms PVNP.GalerkinTaylor.tail_bound
#print axioms PVNP.GalerkinTaylor.flowSeries_zero
#print axioms PVNP.GalerkinTaylor.flowSeries_lipschitz
#print axioms PVNP.GalerkinTaylor.step_error
#print axioms PVNP.GalerkinTaylor.gronE_succ
#print axioms PVNP.GalerkinTaylor.gronE_mono
#print axioms PVNP.GalerkinTaylor.gronE_le
#print axioms PVNP.GalerkinTaylor.integrator_error
#print axioms PVNP.GalerkinTaylor.certified_integrator

-- Phase XXVIII: spatial mode counts.
#print axioms PVNP.TorusGalerkin.weighted_tail
#print axioms PVNP.TorusGalerkin.analytic_tail
#print axioms PVNP.TorusGalerkin.gronwallBound_le
#print axioms PVNP.TorusGalerkin.analytic_mode_count
#print axioms PVNP.TorusGalerkin.sobolev_count_lower
#print axioms PVNP.TorusGalerkin.galerkin_error_of_tail

-- Phase XXIX: cutoff-independent analytic norms and the analytic Banach algebra.
#print axioms PVNP.Analytic.size_nonneg
#print axioms PVNP.Analytic.size_add_le
#print axioms PVNP.Analytic.size_neg
#print axioms PVNP.Analytic.size_le_sub_add
#print axioms PVNP.Analytic.aw_pos
#print axioms PVNP.Analytic.aw_le_mul
#print axioms PVNP.Analytic.aw_neg
#print axioms PVNP.Analytic.aw_zero
#print axioms PVNP.Analytic.asq_nonneg
#print axioms PVNP.Analytic.anorm_nonneg
#print axioms PVNP.Analytic.anorm_sq
#print axioms PVNP.Analytic.asq_zero_radius
#print axioms PVNP.Analytic.asum_zero_radius
#print axioms PVNP.Analytic.asum_of_supported
#print axioms PVNP.Analytic.lift_apply
#print axioms PVNP.Analytic.norm_lift_sq
#print axioms PVNP.Analytic.norm_lift
#print axioms PVNP.Analytic.co_lift
#print axioms PVNP.Analytic.norm_co_lift
#print axioms PVNP.Analytic.aw_mulH_le
#print axioms PVNP.Analytic.asum_mulH
#print axioms PVNP.Analytic.anorm_mulH_le
#print axioms PVNP.Analytic.asum_conjH
#print axioms PVNP.Analytic.asq_conjH
#print axioms PVNP.Analytic.anorm_conjH
#print axioms PVNP.Analytic.asum_trunc
#print axioms PVNP.Analytic.asq_trunc_le
#print axioms PVNP.Analytic.asum_smul
#print axioms PVNP.Analytic.asq_smul
#print axioms PVNP.Analytic.anorm_smul
#print axioms PVNP.Analytic.anorm_add_le
#print axioms PVNP.Analytic.asq_U
#print axioms PVNP.Analytic.asum_U
#print axioms PVNP.Analytic.anorm_Fnl_le
#print axioms PVNP.Analytic.asq_interp
#print axioms PVNP.Analytic.asq_mono
#print axioms PVNP.Analytic.tail_le

-- Phase XXIX: propagation of analytic regularity, uniform over Galerkin truncations.
#print axioms PVNP.Analytic.asq_eq_sum
#print axioms PVNP.Analytic.hasDerivAt_asq
#print axioms PVNP.Analytic.inner_disp_zero
#print axioms PVNP.Analytic.inner_physField_le
#print axioms PVNP.Analytic.deriv_asq_le
#print axioms PVNP.Analytic.grate_pos
#print axioms PVNP.Analytic.tstep_pos
#print axioms PVNP.Analytic.exp_half_le_two
#print axioms PVNP.Analytic.local_propagation
#print axioms PVNP.Analytic.global_propagation
#print axioms PVNP.Analytic.radius_at

-- Phase XXIX: end-to-end simulation of the frozen flow from analytic data.
#print axioms PVNP.Analytic.pde_apriori
#print axioms PVNP.Analytic.supported_U
#print axioms PVNP.Analytic.galerkin_analytic
#print axioms PVNP.Analytic.radius_mono
#print axioms PVNP.Analytic.analytic_galerkin_pde_error
#print axioms PVNP.Analytic.analytic_end_to_end

-- Phase XXIX: verified binary addition, subtraction and comparison on the compiled TM.
#print axioms PVNP.Discrete.SweepArith.val_append
#print axioms PVNP.Discrete.SweepArith.val_lt
#print axioms PVNP.Discrete.SweepArith.bscan_id
#print axioms PVNP.Discrete.SweepArith.fadd_spec
#print axioms PVNP.Discrete.SweepArith.fscan_add_ab
#print axioms PVNP.Discrete.SweepArith.fscan_add
#print axioms PVNP.Discrete.SweepArith.add_reach
#print axioms PVNP.Discrete.SweepArith.add_value
#print axioms PVNP.Discrete.SweepArith.addCost_le
#print axioms PVNP.Discrete.SweepArith.add_tm
#print axioms PVNP.Discrete.SweepArith.fsub_spec
#print axioms PVNP.Discrete.SweepArith.fscan_sub
#print axioms PVNP.Discrete.SweepArith.sub_reach
#print axioms PVNP.Discrete.SweepArith.sub_value
#print axioms PVNP.Discrete.SweepArith.sub_tm
#print axioms PVNP.Discrete.SweepArith.cmpOf_step
#print axioms PVNP.Discrete.SweepArith.fscan_cmp
#print axioms PVNP.Discrete.SweepArith.cmp_halts
#print axioms PVNP.Discrete.SweepArith.cmp_tm

-- Phase XXX: verified shift-and-add multiplication on the compiled TM.
#print axioms PVNP.Discrete.SweepArith.fscan_shift_x
#print axioms PVNP.Discrete.SweepArith.fscan_keep_y
#print axioms PVNP.Discrete.SweepArith.fscan_fr
#print axioms PVNP.Discrete.SweepArith.fscan_fA_acc
#print axioms PVNP.Discrete.SweepArith.fscan_fS_acc
#print axioms PVNP.Discrete.SweepArith.fscan_fP
#print axioms PVNP.Discrete.SweepArith.decide_ne_zero
#print axioms PVNP.Discrete.SweepArith.decide_odd
#print axioms PVNP.Discrete.SweepArith.bscan_bP
#print axioms PVNP.Discrete.SweepArith.bscan_bR
#print axioms PVNP.Discrete.SweepArith.val_tail_append_false
#print axioms PVNP.Discrete.SweepArith.mnext_eq
#print axioms PVNP.Discrete.SweepArith.trips_zero
#print axioms PVNP.Discrete.SweepArith.trips_pos
#print axioms PVNP.Discrete.SweepArith.trips_le
#print axioms PVNP.Discrete.SweepArith.trip_eq
#print axioms PVNP.Discrete.SweepArith.step_core
#print axioms PVNP.Discrete.SweepArith.step_trip
#print axioms PVNP.Discrete.SweepArith.tripCost_mul
#print axioms PVNP.Discrete.SweepArith.mod_add_mul
#print axioms PVNP.Discrete.SweepArith.mul_loop
#print axioms PVNP.Discrete.SweepArith.mul_reach
#print axioms PVNP.Discrete.SweepArith.mul_exact
#print axioms PVNP.Discrete.SweepArith.mul_tm

-- Phase XXX: resonance structure of the frozen dispersion (no small divisors, nontrivial resonances).
#print axioms PVNP.FrozenResonance.qf_two_pi
#print axioms PVNP.FrozenResonance.om_two_pi
#print axioms PVNP.FrozenResonance.om_cast
#print axioms PVNP.FrozenResonance.phase_int
#print axioms PVNP.FrozenResonance.no_small_divisors
#print axioms PVNP.FrozenResonance.doubly_resonant_trivial
#print axioms PVNP.FrozenResonance.radial_vanish
#print axioms PVNP.FrozenResonance.nontrivial_resonance
#print axioms PVNP.FrozenResonance.nontrivial_resonance_real

-- Phase XXXI: verified long division (SweepDiv)
#print axioms PVNP.Discrete.SweepArith.cmpOf_msb
#print axioms PVNP.Discrete.SweepArith.gscan_q
#print axioms PVNP.Discrete.SweepArith.gscan_keep
#print axioms PVNP.Discrete.SweepArith.gscan_fr
#print axioms PVNP.Discrete.SweepArith.gscan_sub
#print axioms PVNP.Discrete.SweepArith.gscan_gP
#print axioms PVNP.Discrete.SweepArith.hscan_hP
#print axioms PVNP.Discrete.SweepArith.hscan_hR
#print axioms PVNP.Discrete.SweepArith.cmpOf_lt_iff
#print axioms PVNP.Discrete.SweepArith.dnext_eq
#print axioms PVNP.Discrete.SweepArith.trip_eq_div
#print axioms PVNP.Discrete.SweepArith.tripCost_div
#print axioms PVNP.Discrete.SweepArith.dstep_core
#print axioms PVNP.Discrete.SweepArith.dstep
#print axioms PVNP.Discrete.SweepArith.div_arith
#print axioms PVNP.Discrete.SweepArith.mod_shift
#print axioms PVNP.Discrete.SweepArith.div_loop
#print axioms PVNP.Discrete.SweepArith.div_reach
#print axioms PVNP.Discrete.SweepArith.div_tm
#print axioms PVNP.Discrete.SweepArith.bitsOf_length
#print axioms PVNP.Discrete.SweepArith.val_bitsOf
#print axioms PVNP.Discrete.SweepArith.mkCells_spec
#print axioms PVNP.Discrete.SweepArith.divInput_spec
#print axioms PVNP.Discrete.SweepArith.div_exact
#print axioms PVNP.Discrete.SweepArith.div_exact_tm
#print axioms PVNP.Discrete.SweepArith.fixdiv_certified
#print axioms PVNP.Discrete.SweepArith.fixdiv_tm

-- Phase XXXI: detector-specific quadratic truncation bound (DetectorQuadratic)
#print axioms PVNP.DetectorQuadratic.co_trunc
#print axioms PVNP.DetectorQuadratic.co_mulH_eq_zero
#print axioms PVNP.DetectorQuadratic.co_mulH_congr
#print axioms PVNP.DetectorQuadratic.inner_layer_left
#print axioms PVNP.DetectorQuadratic.inner_layer_right
#print axioms PVNP.DetectorQuadratic.detector_split
#print axioms PVNP.DetectorQuadratic.detector_layer_bound
#print axioms PVNP.DetectorQuadratic.layer_le
#print axioms PVNP.DetectorQuadratic.detector_static_quadratic
#print axioms PVNP.DetectorQuadratic.size_sub_comm
#print axioms PVNP.DetectorQuadratic.isLayer_of_band
#print axioms PVNP.DetectorQuadratic.layer_size
#print axioms PVNP.DetectorQuadratic.detector_band_quadratic
#print axioms PVNP.DetectorQuadratic.device_band
#print axioms PVNP.DetectorQuadratic.device_real
#print axioms PVNP.DetectorQuadratic.device_detector_quadratic
