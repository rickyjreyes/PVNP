import PVNP.TorusGalerkinTrajectory

/-!
# Exact finite residual for the frozen cubic–quintic torus flow

A bandlimited trial state need not have a bandlimited exact trajectory.
Nevertheless its instantaneous nonlinear vector field has support in an
explicit finite sumset. This eliminates the infinite nonlinear-tail oracle
from residual evaluation on finite trial states, not from initial-data
approximation or global error control.
-/

namespace PVNP.TorusGalerkin
open PVNP.Torus

def Supported (S : Finset Z2) (v : ℓ2) : Prop :=
  ∀ k, k ∉ S → v k = 0

def sumSupport (S T : Finset Z2) : Finset Z2 :=
  (S.product T).image (fun p => p.1 + p.2)

def negSupport (S : Finset Z2) : Finset Z2 :=
  S.image Neg.neg

def cubicSupport (S : Finset Z2) : Finset Z2 :=
  sumSupport (sumSupport S S) (negSupport S)

def quinticSupport (S : Finset Z2) : Finset Z2 :=
  sumSupport (sumSupport (sumSupport (sumSupport S S) S) (negSupport S)) (negSupport S)

def nonlinearSupport (S : Finset Z2) : Finset Z2 :=
  cubicSupport S ∪ quinticSupport S

theorem trunc_supported (S : Finset Z2) (v : ℓ2) :
    Supported S (trunc S v) := by
  intro k hk
  simp [trunc_apply, hk]

theorem supported_trunc_eq {S : Finset Z2} {v : ℓ2} (h : Supported S v) :
    trunc S v = v := by
  ext k
  rw [trunc_apply]
  by_cases hk : k ∈ S
  · simp [hk]
  · rw [if_neg hk, h k hk]

theorem support_mono {S T : Finset Z2} {v : ℓ2}
    (hST : S ⊆ T) (hv : Supported S v) : Supported T v := by
  intro k hk
  exact hv k (fun h => hk (hST h))

theorem support_U (L κ t : ℝ) {S : Finset Z2} {v : ℓ2}
    (hv : Supported S v) : Supported S (U L κ t v) := by
  intro k hk
  rw [U_apply, hv k hk, mul_zero]

theorem support_smul (c : ℂ) {S : Finset Z2} {v : ℓ2}
    (hv : Supported S v) : Supported S (c • v) := by
  intro k hk
  simp [lp.coeFn_smul, hv k hk]

theorem support_add {S T : Finset Z2} {v w : ℓ2}
    (hv : Supported S v) (hw : Supported T w) : Supported (S ∪ T) (v + w) := by
  intro k hk
  have hs : k ∉ S := fun h => hk (Finset.mem_union_left T h)
  have ht : k ∉ T := fun h => hk (Finset.mem_union_right S h)
  simp [lp.coeFn_add, hv k hs, hw k ht]

theorem support_conj {S : Finset Z2} {v : ℓ2}
    (hv : Supported S v) : Supported (negSupport S) (conjH v) := by
  intro k hk
  have hn : -k ∉ S := by
    intro h
    apply hk
    exact Finset.mem_image.mpr ⟨-k, h, neg_neg k⟩
  rw [conjH_apply, hv _ hn, map_zero]

theorem support_mulH {L : ℝ} (hL : 0 < L) {S T : Finset Z2} {v w : ℓ2}
    (hv : Supported S v) (hw : Supported T w) :
    Supported (sumSupport S T) (mulH L v w) := by
  intro k hk
  rw [mulH_apply hL, pr]
  have hz : (fun j : Z2 => co L v (k-j) * co L w j) = 0 := by
    funext j
    change co L v (k-j) * co L w j = 0
    by_cases hj : j ∈ T
    · have hsub : k-j ∉ S := by
        intro h
        apply hk
        exact Finset.mem_image.mpr ⟨(k-j,j), Finset.mem_product.mpr ⟨h,hj⟩,
          sub_add_cancel k j⟩
      simp [co, hv _ hsub]
    · simp [co, hw _ hj]
  rw [hz, tsum_zero, mul_zero, mul_zero]

/-- Both polynomial convolution branches have explicitly finite support. -/
theorem support_Fnl {L : ℝ} (hL : 0 < L) (β γ : ℝ)
    {S : Finset Z2} {v : ℓ2} (hv : Supported S v) :
    Supported (nonlinearSupport S) (Fnl L β γ v) := by
  unfold Fnl nonlinearSupport cubicSupport quinticSupport
  exact support_add
    (support_smul _ (support_mulH hL (support_mulH hL hv hv) (support_conj hv)))
    (support_smul _ (support_mulH hL
      (support_mulH hL (support_mulH hL (support_mulH hL hv hv) hv) (support_conj hv))
      (support_conj hv)))

theorem support_Gf {L : ℝ} (hL : 0 < L) (κ β γ t : ℝ)
    {S : Finset Z2} {v : ℓ2} (hv : Supported S v) :
    Supported (nonlinearSupport S) (Gf L κ β γ t v) := by
  unfold Gf
  exact support_smul _ (support_U L κ (-t)
    (support_Fnl hL β γ (support_U L κ t hv)))

/-- The full nonlinear field is exactly its projection onto a known finite
sumset, even though the original trial cutoff need not contain that sumset. -/
theorem finite_nonlinear_field {L : ℝ} (hL : 0 < L) (κ β γ t : ℝ)
    {S : Finset Z2} {v : ℓ2} (hv : Supported S v) :
    trunc (nonlinearSupport S) (Gf L κ β γ t v) = Gf L κ β γ t v :=
  supported_trunc_eq (support_Gf hL κ β γ t hv)

/-- Exact square of the full residual norm from finitely many coefficients.
The derivative and the nonlinear field may have different supports. -/
theorem finite_residual_sq {L : ℝ} (hL : 0 < L) (κ β γ t : ℝ)
    {S D : Finset Z2} {v dv : ℓ2} (hv : Supported S v) (hd : Supported D dv) :
    ‖dv - Gf L κ β γ t v‖ ^ 2 =
      ∑ k ∈ D ∪ nonlinearSupport S, ‖(dv - Gf L κ β γ t v) k‖ ^ 2 := by
  rw [norm_sq_eq]
  apply tsum_eq_sum
  intro k hk
  have hD : k ∉ D := fun h => hk (Finset.mem_union_left _ h)
  have hN : k ∉ nonlinearSupport S := fun h => hk (Finset.mem_union_right _ h)
  simp [lp.coeFn_sub, hd k hD, support_Gf hL κ β γ t hv k hN]

/-- Every coefficient convolution can be evaluated over its known finite
right-hand support, without summing over infinitely many lattice modes. -/
theorem finite_pr (L : ℝ) (a b : Z2 → ℂ) (T : Finset Z2)
    (hb : ∀ j, j ∉ T → b j = 0) (k : Z2) :
    pr L a b k = (L : ℂ)⁻¹ * ∑ j ∈ T, a (k-j) * b j := by
  unfold pr
  congr 1
  apply tsum_eq_sum
  intro j hj
  rw [hb j hj, mul_zero]

end PVNP.TorusGalerkin
