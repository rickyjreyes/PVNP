import Mathlib

/-!
# Geometric cut-capacity and metastable escape test

Area bound assumes a 2D square footprint, an explicit maximum number of
simultaneous crossing channels per unit cut length, and no free
time-multiplexing. The metastable calculation assumes a one-step
memoryless escape probability; it is not a theorem about arbitrary PDEs.
-/

namespace PVNP.PhysicalBounds

/-- Finite-bandwidth cut: if n obligations must cross a cut and
only B messages per round cross for T rounds, then n ≤ B*T. -/
theorem communication_time_tradeoff
    (obligations bandwidth rounds : Nat)
    (hcapacity : obligations ≤ bandwidth * rounds) :
    obligations ≤ bandwidth * rounds := hcapacity

/-- With square side L and at most k*L simultaneous channels across
a balanced cut, a bisection requirement b implies b² ≤ k²*A. -/
theorem planar_cut_area_bound
    (b k L area : ℝ) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hL : 0 ≤ L)
    (hcut : b ≤ k * L)
    (harea : L ^ 2 ≤ area) :
    b ^ 2 ≤ k ^ 2 * area := by
  have hcut_sq : b ^ 2 ≤ (k * L) ^ 2 := by
    have hleft : 0 ≤ k * L - b := sub_nonneg.mpr hcut
    have hright : 0 ≤ k * L + b := by positivity
    nlinarith [mul_nonneg hleft hright]
  have harea_mul : k ^ 2 * L ^ 2 ≤ k ^ 2 * area :=
    mul_le_mul_of_nonneg_left harea (sq_nonneg k)
  nlinarith

/-- The mean escape time of a memoryless two-state trap satisfies
E = 1 + (1-p)*E and hence equals 1/p for nonzero p. -/
theorem geometric_escape_mean
    (p E : ℝ) (hp : 0 < p)
    (hrec : E = 1 + (1 - p) * E) :
    E = 1 / p := by
  have hpe : p * E = 1 := by nlinarith [hrec]
  apply (eq_div_iff (ne_of_gt hp)).2
  nlinarith [hpe]

/-- If one-step escape probability is at most q, mean escape time is
at least 1/q. An exponential result follows only from an independently
proved exponentially small escape probability. -/
theorem mean_escape_lower_bound
    (p q E : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q)
    (hrec : E = 1 + (1 - p) * E) :
    1 / q ≤ E := by
  rw [geometric_escape_mean p E hp hrec]
  apply (div_le_div_iff₀ hq hp).2
  nlinarith [hpq]

/-- Merely having an arbitrary number of states does not imply slow
convergence: a deterministic map can reach its target in one step. -/
theorem many_states_can_converge_in_one_step
    {State : Type*} (target : State) :
    ∃ F : State → State, ∀ x, F x = target :=
  ⟨fun _ => target, by intro x; rfl⟩

end PVNP.PhysicalBounds
