import PVNP.SeparatorPrice
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Part I's normal-gradient cost on an observed continuum interface. On
disjoint normal fibers, the trace contrast and physical width control the
Dirichlet energy. Identifying these fibers on general WCT trajectories is
a separate geometric hypothesis. -/
namespace PVNP.ContinuumSeparator
open MeasureTheory Set

/-- Sharp one-dimensional chord estimate on a physical interval. -/
theorem chord {w : ℝ} (hw : 0 < w) (u v : ℝ → ℝ) (hv : Continuous v)
    (hd : ∀ t ∈ uIcc 0 w, HasDerivAt u (v t) t) :
    (u w - u 0)^2 / w ≤ ∫ t in (0:ℝ)..w, (v t)^2 := by
  let a := (u w-u 0)/w
  have hmean : w*a = u w - u 0 := by dsimp [a]; field_simp
  have hvint := hv.intervalIntegrable (μ := volume) 0 w
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hvint
  have hpos := intervalIntegral.integral_nonneg_of_forall (μ := volume) hw.le (fun t => sq_nonneg (v t-a))
  have he : (fun t => (v t-a)^2) = fun t => (v t)^2 - (2*a)*v t + a^2 := by
    funext t; ring
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, hft, intervalIntegral.integral_const] at hpos
  · simp only [sub_zero, smul_eq_mul] at hpos
    apply (div_le_iff₀ hw).mpr
    rw [← hmean] at hpos ⊢
    nlinarith [mul_nonneg hw.le hpos]
  · exact (hv.pow 2).intervalIntegrable ..
  · exact (continuous_const.mul hv).intervalIntegrable ..
  · exact ((hv.pow 2).sub (continuous_const.mul hv)).intervalIntegrable ..
  · exact intervalIntegrable_const

/-- With a finite physical area measure on the interface, an upper bound on
normal widths, and a uniform contrast, the price is independent of mesh size.
The left factor is the area of the *observed* interface. -/
theorem interface_price {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (u v : S → ℝ → ℝ) (w : S → ℝ) (W δ : ℝ) (hδ : 0 ≤ δ)
    (hw : ∀ s, 0 < w s ∧ w s ≤ W) (hv : ∀ s, Continuous (v s))
    (hd : ∀ s t, t ∈ uIcc 0 (w s) → HasDerivAt (u s) (v s t) t)
    (contrast : ∀ s, δ ≤ |u s (w s) - u s 0|)
    (hi : Integrable (fun s => ∫ t in (0:ℝ)..w s, (v s t)^2) μ) :
    (μ.real univ) * (δ^2/W) ≤ ∫ s, (∫ t in (0:ℝ)..w s, (v s t)^2) ∂μ := by
  have hpoint (s : S) : δ^2/W ≤ ∫ t in (0:ℝ)..w s, (v s t)^2 := by
    have hs := pow_le_pow_left₀ hδ (contrast s) 2
    rw [sq_abs] at hs
    calc δ^2/W ≤ δ^2/w s := div_le_div_of_nonneg_left (sq_nonneg _) (hw s).1 (hw s).2
         _ ≤ (u s (w s)-u s 0)^2/w s := div_le_div_of_nonneg_right hs (hw s).1.le
         _ ≤ _ := chord (hw s).1 _ _ (hv s) (hd s)
  simpa [MeasureTheory.integral_const, smul_eq_mul] using
    (integral_mono (μ := μ) (integrable_const (δ^2/W)) hi hpoint)

/-- Without an upper bound on physical width, smooth ramps of fixed contrast
have arbitrarily small normal gradient energy. -/
theorem ramp_below {δ κ : ℝ} (hκ : 0 < κ) :
    ∃ w : ℝ, 0 < w ∧ (fun t : ℝ => δ*t/w) w - (fun t : ℝ => δ*t/w) 0 = δ ∧
      (∫ _t in (0:ℝ)..w, (δ/w)^2) < κ := by
  let w := δ^2/κ+1
  have hw : 0 < w := by dsimp [w]; positivity
  refine ⟨w,hw,by field_simp; ring,?_⟩
  rw [intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul]
  have he : w*(δ/w)^2 = δ^2/w := by field_simp
  rw [he,div_lt_iff₀ hw]
  dsimp [w]
  field_simp
  nlinarith

end PVNP.ContinuumSeparator
