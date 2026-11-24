import PVNP.WeakNormApproximation
import PVNP.GalerkinConservation

/-!
# Global comparison in the physical L² norm

The physical coefficient map is injective but its inverse need not be
bounded. We use the weak Lipschitz estimate only on the image of the
H² radius ball, not on arbitrary L² states.
-/
open Set
open scoped NNReal
namespace PVNP.TorusGalerkin
open PVNP.Torus

theorem Lc_injective (L : ℝ) : Function.Injective (Lc L) := by
  intro v w h
  ext k
  have hc : co L v k = co L w k := by
    have hk := congrArg (fun z : ℓ2 => z k) h
    simpa only [Lc_apply] using hk
  rw [← wt_mul_co L v k, ← wt_mul_co L w k, hc]

/-- A set-theoretic inverse on the range; no resource or continuity
property of this inverse is asserted or used. -/
noncomputable def weakLift (L : ℝ) (z : ℓ2) : ℓ2 := by
  classical
  exact if h : ∃ v : ℓ2, Lc L v = z then Classical.choose h else 0

theorem weakLift_Lc (L : ℝ) (v : ℓ2) : weakLift L (Lc L v) = v := by
  classical
  unfold weakLift
  let h : ∃ w : ℓ2, Lc L w = Lc L v := ⟨v, rfl⟩
  rw [dif_pos h]
  exact Lc_injective L (Classical.choose_spec h)

noncomputable def weakField (L κ β γ t : ℝ) (z : ℓ2) : ℓ2 :=
  Lc L (Gf L κ β γ t (weakLift L z))

theorem weakField_Lc (L κ β γ t : ℝ) (v : ℓ2) :
    weakField L κ β γ t (Lc L v) = Lc L (Gf L κ β γ t v) := by
  rw [weakField, weakLift_Lc]

theorem weakField_lipschitz {L κ β γ R : ℝ} (hL : 0 < L) (t : ℝ) :
    LipschitzOnWith ⟨LF L β γ R, LF_nonneg L β γ R⟩
      (weakField L κ β γ t) (Lc L '' Metric.closedBall (0 : ℓ2) R) := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz y hy => ?_
  obtain ⟨v, hv, rfl⟩ := hz
  obtain ⟨w, hw, rfl⟩ := hy
  rw [Metric.mem_closedBall, dist_zero_right] at hv hw
  rw [dist_eq_norm, weakField_Lc, weakField_Lc, dist_eq_norm, ← map_sub, ← map_sub]
  exact weak_Gf_sub_le hL t hv hw

/-- Quantitative global L² error under certified H² radius bounds on
both the numerical and exact trajectories. -/
theorem weak_trajectory_error {L κ β γ R : ℝ} (hL : 0 < L)
    {W w : ℝ → ℓ2} {W' : ℝ → ℓ2} {T δ η : ℝ}
    (hW : ∀ t, HasDerivAt W (W' t) t)
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t)
    (hballW : ∀ t ∈ Ico 0 T, ‖W t‖ ≤ R)
    (hballw : ∀ t ∈ Ico 0 T, ‖w t‖ ≤ R)
    (hres : ∀ t ∈ Ico 0 T, ‖Lc L (W' t - Gf L κ β γ t (W t))‖ ≤ η)
    (h0 : ‖Lc L (W 0 - w 0)‖ ≤ δ) :
    ∀ t ∈ Icc 0 T, ‖Lc L (W t - w t)‖ ≤ gronwallBound δ (LF L β γ R) η t := by
  have hDW : ∀ t, HasDerivAt (fun s => Lc L (W s)) (Lc L (W' t)) t :=
    fun t => hasDerivAt_Lc (hW t)
  have hDw : ∀ t, HasDerivAt (fun s => Lc L (w s)) (Lc L (Gf L κ β γ t (w t))) t :=
    fun t => hasDerivAt_Lc (hw t)
  have hcW : Continuous fun s => Lc L (W s) :=
    continuous_iff_continuousAt.2 fun t => (hDW t).continuousAt
  have hcw : Continuous fun s => Lc L (w s) :=
    continuous_iff_continuousAt.2 fun t => (hDw t).continuousAt
  have key := dist_le_of_approx_trajectories_ODE_of_mem
    (v := weakField L κ β γ)
    (s := fun _ => Lc L '' Metric.closedBall (0 : ℓ2) R)
    (K := ⟨LF L β γ R, LF_nonneg L β γ R⟩) (a := 0) (b := T)
    (f := fun t => Lc L (W t)) (g := fun t => Lc L (w t))
    (f' := fun t => Lc L (W' t)) (g' := fun t => Lc L (Gf L κ β γ t (w t)))
    (εf := η) (εg := 0) (δ := δ)
    (fun t _ => weakField_lipschitz hL t)
    hcW.continuousOn (fun t _ => (hDW t).hasDerivWithinAt)
    (fun t ht => by rw [weakField_Lc, dist_eq_norm, ← map_sub]; exact hres t ht)
    (fun t ht => ⟨W t, by rw [Metric.mem_closedBall, dist_zero_right]; exact hballW t ht, rfl⟩)
    hcw.continuousOn (fun t _ => (hDw t).hasDerivWithinAt)
    (fun t _ => by rw [weakField_Lc, dist_self])
    (fun t ht => ⟨w t, by rw [Metric.mem_closedBall, dist_zero_right]; exact hballw t ht, rfl⟩)
    (by rw [dist_eq_norm, ← map_sub]; exact h0)
  intro t ht
  have h := key t ht
  simpa only [dist_eq_norm, ← map_sub, NNReal.coe_mk, add_zero, sub_zero] using h

/-- An actual projected solution needs only the omitted output tail,
since its input is already supported on S. -/
theorem weak_galerkin_residual {L κ β γ R K : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hK : 0 < K) (S : Finset Z2)
    (hcut : ∀ k ∉ S, K ≤ wt L k) (t : ℝ)
    {v : ℓ2} (hv : Supported S v) (hr : ‖v‖ ≤ R) :
    ‖Lc L (galerkin S L κ β γ t v - Gf L κ β γ t v)‖ ≤ LF L β γ R * R / K := by
  unfold galerkin
  rw [supported_trunc_eq hv]
  exact (weak_projection_tail L S _ hK hcut).trans
    (div_le_div_of_nonneg_right (norm_Gf_le hL hR t hr) hK.le)

theorem weak_galerkin_global_error {L κ β γ R K T : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hK : 0 < K) (S : Finset Z2)
    (hcut : ∀ k ∉ S, K ≤ wt L k)
    {W w : ℝ → ℓ2} (hW0 : W 0 = trunc S (w 0))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t)
    (hs : ∀ t, Supported S (W t))
    (hbW : ∀ t, ‖W t‖ ≤ R) (hbw : ∀ t, ‖w t‖ ≤ R) :
    ∀ t ∈ Icc 0 T, ‖Lc L (W t - w t)‖ ≤
      gronwallBound (R/K) (LF L β γ R) (LF L β γ R * R/K) t := by
  apply weak_trajectory_error hL hW hw (fun t _ => hbW t) (fun t _ => hbw t)
  · intro t _
    exact weak_galerkin_residual hL hR hK S hcut t (hs t) (hbW t)
  · rw [hW0]
    exact (weak_projection_tail L S _ hK hcut).trans
      (div_le_div_of_nonneg_right (hbw 0) hK.le)

end PVNP.TorusGalerkin
