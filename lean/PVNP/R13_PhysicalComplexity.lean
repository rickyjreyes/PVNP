import PVNP.PartIII

/-! R13 (DOI 10.5281/zenodo.17783074).
A phase/sign counterexample to inferring distinguishability from the
squared density alone. Classical P vs NP remains mathematically defined. -/
namespace PVNP.R13

theorem opposite_sign_same_density (x : ℝ) (hx : x ≠ 0) :
    x ≠ -x ∧ x ^ 2 = (-x) ^ 2 := by
  constructor
  · intro h
    apply hx
    linarith
  · ring

theorem shifted_denominator_counterexample (epsilon : ℝ) (he : 0 < epsilon) :
    ¬ (∀ x : ℝ, epsilon ≤ |x + epsilon|) :=
  PVNP.PartIII.shifted_denominator_no_uniform_gap epsilon he

end PVNP.R13
