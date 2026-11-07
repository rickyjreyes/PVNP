import PVNP.TwoPhaseUniform

/-!
# Phase XIII, II-10: exact finite-window bitmap for original W_M

The original W_M uses a one-dimensional bounding box of radius R = L+1
and an active interval [-L,L]. Here we derive the bit predicate of the
canonical `latCode` at *every* enumerated position. It has the simple shape

  false :: replicate (2L+1) true ++ [false]

after the unary radius prefix and separator.

This is an exact semantic theorem about the actual `site` and `window`
definitions. Together with the executable writer in `pvnp/two_phase_reference.py`,
it is a concrete step toward the remaining II-10 lattice FP witness.

A polynomial output-length bound and an executable Python writer are not
the MTM polynomial-time output transducer; that obligation remains open.
-/

namespace PVNP.TwoPhaseWindowShape

open PVNP.PartIIUniform PVNP.TwoPhaseDecoder

/-- In one dimension the jth coordinate of a radius-(L+1) box is j-(L+1)
whenever the index is inside the box. -/
theorem site_one_coordinate (L j : ℕ)
    (hj : j < 2 * (L + 1) + 1) :
    site 1 (L + 1) j 0 = (j : ℤ) - (L + 1 : ℕ) := by
  simp [site, side, Nat.mod_eq_of_lt hj]

/-- The original W_M active window occupies exactly the interior bitmap
positions, excluding the first and last bounding-box cells. -/
theorem original_window_membership_iff (L j : ℕ)
    (hj : j < 2 * (L + 1) + 1) :
    site 1 (L + 1) j ∈ window L ↔
      0 < j ∧ j < 2 * (L + 1) := by
  change InWin L (site 1 (L + 1) j 0) ↔ _
  rw [site_one_coordinate L j hj]
  unfold InWin
  omega

/-- Every exact membership bit in the canonical 1D window code is given
by the elementary strict interior test. -/
theorem original_window_bit (L j : ℕ)
    (hj : j < 2 * (L + 1) + 1) :
    decide (site 1 (L + 1) j ∈ window L) =
      decide (0 < j ∧ j < 2 * (L + 1)) := by
  simp only [original_window_membership_iff L j hj]

end PVNP.TwoPhaseWindowShape
