import PVNP.WCTLattice

/-!
# M3-G: non-blowup bounds for finite lattice solutions

The vector field of the frozen lattice WCT equation already has local
existence and exact mass conservation.  The following unconditional
coordinate bounds are the quantitative a priori estimates needed for a
future global ODE continuation theorem.  They do NOT themselves assert that
a global solution exists.
-/

namespace PVNP.WCTLattice

variable {N : ℕ} [NeZero N]

/-- Each lattice coordinate has squared amplitude at most the total mass. -/
theorem coordinate_norm_sq_le_mass (u : Fld N) (j : ZMod N) :
    ‖u j‖ ^ 2 ≤ mass u := by
  unfold mass nsq
  exact Finset.single_le_sum
    (fun k _ => sq_nonneg (‖u k‖)) (Finset.mem_univ j)

/-- Each coordinate is bounded by the square root of the total mass. -/
theorem coordinate_norm_le_sqrt_mass (u : Fld N) (j : ZMod N) :
    ‖u j‖ ≤ Real.sqrt (mass u) := by
  calc
    ‖u j‖ = Real.sqrt (‖u j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (mass u) := Real.sqrt_le_sqrt (coordinate_norm_sq_le_mass u j)

/-- A global solution, if given, cannot exhibit finite-time coordinate
blowup: its pointwise amplitude is uniformly controlled by initial mass. -/
theorem solution_uniform_coordinate_bound {a b β γ : ℝ}
    {z : ℝ → Fld N} (hz : IsSol a b β γ z) (t : ℝ) (j : ZMod N) :
    ‖z t j‖ ≤ Real.sqrt (mass (z 0)) := by
  calc
    ‖z t j‖ ≤ Real.sqrt (mass (z t)) :=
      coordinate_norm_le_sqrt_mass (z t) j
    _ = Real.sqrt (mass (z 0)) := by rw [mass_conserved hz t]

/-- The existing Picard-Lindelöf local solution can be chosen with an
explicit pointwise bound on its entire (nonempty) existence interval. -/
theorem exists_local_solution_bounded (a b β γ : ℝ) (u₀ : Fld N) :
    ∃ z : ℝ → Fld N, z 0 = u₀ ∧
      ∃ ε > (0 : ℝ),
        (∀ t ∈ Set.Ioo (-ε) ε, ∀ j,
          HasDerivAt (fun s => z s j) (vf a b β γ (z t) j) t) ∧
        (∀ t ∈ Set.Ioo (-ε) ε, ∀ j,
          ‖z t j‖ ≤ Real.sqrt (mass u₀)) := by
  obtain ⟨z, hz0, ε, hε, hz⟩ := exists_local_solution a b β γ u₀
  refine ⟨z, hz0, ε, hε, hz, ?_⟩
  intro t ht j
  have hmass := (local_conservation hz ht).1
  calc
    ‖z t j‖ ≤ Real.sqrt (mass (z t)) :=
      coordinate_norm_le_sqrt_mass (z t) j
    _ = Real.sqrt (mass u₀) := by rw [hmass, hz0]

end PVNP.WCTLattice
