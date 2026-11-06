import PVNP.PartIPsiSat

/-!
# I-3: logical constraints cannot be discarded from the phase-locking criterion

This narrow scope test works in the frozen finite three-CNF phase encoding.
It demonstrates a contradiction formula for which every site may have
constant phase zero, even though no phase field has `Elogic = 0`.
The original analytic gradient/max-amplitude phrase is not a defined
machine predicate here, so this result is **not** an exact counterexample
to that full phrase. It shows why phase coherence alone is insufficient.

The exact formula-dependent statement remains
`PartIPsiSat.psi_sat_completeness`.
-/

namespace PVNP.PhaseLockScope

open PVNP.PartIPsiSat

/-- Two contradictory three-literal clauses, one demanding the first variable
be true and one demanding that it be false. -/
def contradictory : CNF3 :=
  [fun _ => ⟨0, true⟩, fun _ => ⟨0, false⟩]

/-- No assignment satisfies both uniform-sign clauses. -/
theorem contradictory_unsat : ¬ Sat contradictory := by
  rintro ⟨a, ha⟩
  have hpos : clauseVal a (fun _ => ⟨0, true⟩) = true :=
    ha _ (by simp [contradictory])
  have hneg : clauseVal a (fun _ => ⟨0, false⟩) = true :=
    ha _ (by simp [contradictory])
  cases h : a 0 with
  | false => simp [clauseVal, litVal, h] at hpos
  | true => simp [clauseVal, litVal, h] at hneg

/-- A purely phase-coherent condition, independent of formula clauses. -/
def AllPhasesZero (θ : ℕ → ℝ) : Prop := ∀ i, θ i = 0

theorem all_phases_zero_exists : ∃ θ : ℕ → ℝ, AllPhasesZero θ :=
  ⟨fun _ => 0, fun _ => rfl⟩

/-- The contradiction formula admits the constant-zero phase configuration,
but its logical penalty is strictly nonzero. -/
theorem contradiction_phase_locked_but_not_logical :
    ∃ θ : ℕ → ℝ, AllPhasesZero θ ∧ Elogic θ contradictory ≠ 0 := by
  refine ⟨fun _ => 0, (fun _ => rfl), ?_⟩
  intro hz
  exact contradictory_unsat
    ((psi_sat_completeness contradictory).2.mpr ⟨fun _ => 0, hz⟩)

/-- No formula-independent phase-zero test characterizes three-CNF SAT. -/
theorem bare_phase_lock_not_sat :
    ¬ ∀ F : CNF3, Sat F ↔ ∃ θ : ℕ → ℝ, AllPhasesZero θ := by
  intro h
  exact contradictory_unsat ((h contradictory).mpr all_phases_zero_exists)

end PVNP.PhaseLockScope
