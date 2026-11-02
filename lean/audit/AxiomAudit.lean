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
