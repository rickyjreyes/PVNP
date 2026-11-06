import PVNP.CrossingSATMatrix

/-!
# Phase XI: quantified consequence of the matrix lower bound

This module packages the kernel-checked Phase X matrix lower bound as a
no-uniform-subquadratic-time theorem for correct single-tape SAT deciders.
It does not improve the exponent and does not prove a superpolynomial bound.
-/

namespace PVNP.PhaseXIQuadratic

open PVNP.Discrete PVNP.Discrete.SATV PVNP.CrossingSAT PVNP.CrossingSATMatrix

/-- Time is uniformly little-o of the squared input length: for every positive
integer multiplier C, eventually C times the first-answer time is strictly
less than the squared length on *every* input. -/
def UniformSubquadratic (M : TM) : Prop :=
  ∀ C : ℕ, 0 < C →
    ∃ N₀ : ℕ, ∀ x : List Bool, N₀ ≤ x.length →
      C * ftime M x < x.length ^ 2

/-- No correct single-tape dense-SAT decider has uniformly o(N²)
first-answer time. This is an exact corollary of
`CrossingSATMatrix.quadratic_arbitrarily_large`, not a superpolynomial bound. -/
theorem sat_no_uniform_subquadratic {M : TM} {T : ℕ → ℕ}
    (hM : M.Decides SAT_dense T) : ¬ UniformSubquadratic M := by
  intro h
  let C : ℕ := 384 * symbolBits M
  obtain ⟨N₀, hfast⟩ := h C (by
    dsimp [C, symbolBits]
    positivity)
  obtain ⟨x, hlarge, _, hslow⟩ := quadratic_arbitrarily_large hM N₀
  have hfastx := hfast x hlarge
  dsimp only [C] at hfastx
  omega

end PVNP.PhaseXIQuadratic
