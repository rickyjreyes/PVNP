import PVNP.PhasePenaltyMargin

/-!
# Phase XIII: uniform logical-energy separation for 3-CNF SAT

The previously verified phase-score formalization proves that if the
input-dependent logical energy of a phase field is strictly below 1/8,
sign rounding yields a satisfying assignment.

This module states the corresponding quantitative separation directly:
* every UNSAT 3-CNF has logical energy at least 1/8 at *every* phase field;
* every SAT 3-CNF has a phase field with logical energy exactly zero;
* consequently SAT is equivalent to the existence of a phase field whose
  logical energy is strictly below 1/8;
* a rigorously bounded absolute measurement error can certify SAT.

All statements refer to the **formula-dependent logical penalty** `Elogic`,
not to the physical PDE evolution or to a costed algorithm for minimizing it.
The existence of a low-energy field does not provide a polynomial-time way
of finding that field, and the results do not prove P != NP.
-/

namespace PVNP.PartIPsiSat

/-- Unconditional, formula-independent soundness gap for UNSAT formulas:
all real phase fields have logical energy at least one eighth. -/
theorem unsat_logical_energy_gap (F : CNF3) (hF : ¬ Sat F)
    (θ : ℕ → ℝ) : (1 : ℝ) / 8 ≤ Elogic θ F := by
  by_contra h
  have hlt : Elogic θ F < (1 : ℝ) / 8 := lt_of_not_ge h
  exact hF ⟨roundPhase θ, roundPhase_satisfies F θ hlt⟩

/-- SAT iff an arbitrary phase field crosses the universal logical-energy
readout threshold. This is strictly a certificate criterion, not a
polynomial-time procedure to prepare or discover the field. -/
theorem sat_iff_exists_energy_lt_eighth (F : CNF3) :
    Sat F ↔ ∃ θ : ℕ → ℝ, Elogic θ F < (1 : ℝ) / 8 := by
  constructor
  · intro hF
    obtain ⟨θ, hzero⟩ := (psi_sat_completeness F).2.mp hF
    refine ⟨θ, ?_⟩
    rw [hzero]
    norm_num
  · rintro ⟨θ, hθ⟩
    exact ⟨roundPhase θ, roundPhase_satisfies F θ hθ⟩

/-- A measured logical energy `observed` with certified absolute
error at most `eps` produces a sound SAT certificate whenever its
upper error bar lies strictly below 1/8. -/
theorem noisy_energy_readout_certifies_sat
    (F : CNF3) (θ : ℕ → ℝ) (observed eps : ℝ)
    (hError : |observed - Elogic θ F| ≤ eps)
    (hBelow : observed + eps < (1 : ℝ) / 8) : Sat F := by
  have hLower := (abs_le.mp hError).1
  have hEnergy : Elogic θ F < (1 : ℝ) / 8 := by linarith
  exact (sat_iff_exists_energy_lt_eighth F).2 ⟨θ, hEnergy⟩

/-- Conversely, a formula known to be unsatisfiable cannot have a
certified upper error bar below the SAT threshold. -/
theorem unsat_rejects_low_energy_certificate
    (F : CNF3) (hUnsat : ¬ Sat F) (θ : ℕ → ℝ)
    (observed eps : ℝ)
    (hError : |observed - Elogic θ F| ≤ eps) :
    (1 : ℝ) / 8 ≤ observed + eps := by
  have hLower := (abs_le.mp hError).1
  have hGap := unsat_logical_energy_gap F hUnsat θ
  linarith

end PVNP.PartIPsiSat
