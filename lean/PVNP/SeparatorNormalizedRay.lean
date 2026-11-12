import PVNP.SeparatorAmplitude

/-!
# Phase XVII: sharp contrast price on a normalized amplitude ray (I-31)

For a ray with quadratic energy `a² e` and linearly homogeneous
receiver contrast `a r`, a prescribed contrast `δ ≤ a r` implies
`δ² e ≤ r² (a² e)` for nonnegative e, a, δ, r.

This excludes the small-amplitude counterexamples under a charged
readout margin. It does NOT establish that frozen WCT devices possess a
uniform positive e/r², nor does it prove the original continuum theorem.
-/
namespace PVNP.SeparatorNormalizedRay

/-- Scale-invariant lower bound on the ray energy from a nonzero detector
contrast. The inequality is sharp at `δ = a*r`. -/
theorem contrast_forces_quadratic_price
    (a e r δ : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e) (hr : 0 ≤ r)
    (hδ : 0 ≤ δ) (hgap : δ ≤ a * r) :
    δ ^ 2 * e ≤ a ^ 2 * (r ^ 2 * e) := by
  have hprod : 0 ≤ (a * r - δ) * (a * r + δ) := by
    apply mul_nonneg (sub_nonneg.mpr hgap)
    exact add_nonneg (mul_nonneg ha hr) hδ
  have hsq : δ ^ 2 ≤ (a * r) ^ 2 := by
    nlinarith [hprod]
  calc
    δ ^ 2 * e ≤ (a * r) ^ 2 * e := mul_le_mul_of_nonneg_right hsq he
    _ = a ^ 2 * (r ^ 2 * e) := by ring

/-- The price is attained at equality in the detector margin: there is
no stronger ray-uniform coefficient without extra assumptions. -/
theorem price_is_sharp (a e r : ℝ) :
    (a * r) ^ 2 * e = a ^ 2 * (r ^ 2 * e) := by ring

end PVNP.SeparatorNormalizedRay
