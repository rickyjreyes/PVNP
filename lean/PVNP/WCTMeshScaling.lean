import PVNP.WCTLatticeGlobalBounds

/-!
# M3-C: an explicit mesh-scaling limitation of the *current* flux estimate

The general lattice flux bound contains a factor `4 * |a| * ω`,
with nearest-neighbour coefficient `a = 1/h²`.
If a detector weight has discrete variation `ω = h`, the prefactor
is `4/h`.  On a unit interval with `h = 1/n` it becomes `4n`.

This is an algebraic diagnosis of the currently proved estimate,
NOT a no-go theorem for a sharper mesh-uniform estimate and
NOT a proof of convergence or divergence of a numerical scheme.
-/

namespace PVNP.WCTLattice

/-- Under `a = h⁻²` and detector variation `ω = h`, the raw
commutator prefactor in `flux_bound` scales as `4/h`. -/
theorem mesh_flux_prefactor (h : ℝ) (hh : 0 < h) :
    4 * |(1 : ℝ) / h ^ 2| * h = 4 / h := by
  have hn : h ≠ 0 := ne_of_gt hh
  rw [abs_of_nonneg (div_nonneg (by positivity) (sq_nonneg h))]
  field_simp
  ring

/-- On the unit mesh `h = 1/n`, the same coefficient is `4n` for
every positive integer number of intervals. -/
theorem mesh_flux_prefactor_unit (n : ℕ) (hn : 0 < n) :
    4 * |(1 : ℝ) / ((1 : ℝ) / (n : ℝ)) ^ 2| *
        ((1 : ℝ) / (n : ℝ)) = 4 * (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh : 0 < (1 : ℝ) / (n : ℝ) := by positivity
  rw [mesh_flux_prefactor _ hh]
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  field_simp

end PVNP.WCTLattice
