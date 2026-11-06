import PVNP.CurvatureBarrier

/-! Part I, separator price on a finite-volume mesh and its precise range
on a bounded-degree two-level graph rail. -/
namespace PVNP.SeparatorPrice

variable {E : Type*}

/-- One term for each counted mesh face. A face of area a has dual volume h*a.
Other nonnegative terms, including the curvature term, can be added to the budget. -/
theorem mesh_price (faces cut : Finset E) (jump : E → ℝ) (h a δ remainder : ℝ)
    (hh : 0 < h) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hr : 0 ≤ remainder) (hc : cut ⊆ faces)
    (hcut : ∀ e ∈ cut, δ ≤ jump e) :
    (δ^2/h) * ((cut.card : ℝ)*a) ≤
      (∑ e ∈ faces, (jump e/h)^2 * (h*a)) + remainder := by
  have point (e : E) (he : e ∈ cut) : δ^2 / h * a ≤ (jump e / h)^2*(h*a) := by
    have sq := pow_le_pow_left₀ hδ (hcut e he) 2
    calc δ^2/h*a ≤ (jump e)^2/h*a := by gcongr
         _ = _ := by field_simp
  calc _ = ∑ _e ∈ cut, δ^2/h*a := by simp; ring
       _ ≤ ∑ e ∈ cut, (jump e/h)^2*(h*a) := Finset.sum_le_sum point
       _ ≤ ∑ e ∈ faces, (jump e/h)^2*(h*a) :=
         Finset.sum_le_sum_of_subset_of_nonneg hc (by intros; positivity)
       _ ≤ _ := by linarith

/-- A K-Lipschitz scalar readout gives the contrast from the gap between its
two decision regions on opposite sides of a face. -/
theorem contrast_of_readout {u v threshold margin K jump : ℝ} (hK : 0 < K)
    (hu : u ≤ threshold - margin) (hv : threshold + margin ≤ v)
    (hlip : |v-u| ≤ K*jump) : 2*margin/K ≤ jump := by
  apply (div_le_iff₀ hK).mpr
  have := le_abs_self (v-u); linarith

open CurvatureBarrier

/-- The count is oriented; for an undirected symmetric neighborhood each cut
edge contributes twice. -/
def crossDegree {n : ℕ} (nb : Fin n → Finset (Fin n)) (bits : Fin n → Bool) (i : Fin n) :=
  ((nb i).filter (fun j => bits j ≠ bits i)).card

private theorem lap_sq_eq {n : ℕ} (nb : Fin n → Finset (Fin n)) (bits : Fin n → Bool) (i : Fin n) :
    (graphLaplacian nb bits i)^2 = ((crossDegree nb bits i : ℕ) : ℚ)^2 := by
  have sum_ind : (∑ j ∈ nb i, (if bits j ≠ bits i then (1:ℚ) else 0)) = crossDegree nb bits i := by
    exact Finset.sum_boole _ _
  have h (j : Fin n) : amplitude (bits j) - amplitude (bits i) =
      (if bits i then (-1:ℚ) else 1) * (if bits j ≠ bits i then 1 else 0) := by
    cases bits i <;> cases bits j <;> norm_num [amplitude]
  unfold graphLaplacian
  simp_rw [h]
  rw [← Finset.mul_sum, sum_ind, mul_pow]
  cases bits i <;> norm_num

/-- On the unit-contrast rail, curvature is between the number of oriented
cut incidences and that number times the maximum degree. -/
theorem binary_cut_price {n d : ℕ} (nb : Fin n → Finset (Fin n)) (bits : Fin n → Bool)
    (hd : ∀ i, (nb i).card ≤ d) :
    (∑ i, (crossDegree nb bits i : ℚ)) ≤ graphStorageCost nb bits ∧
    graphStorageCost nb bits ≤ (d:ℚ) * (∑ i, (crossDegree nb bits i : ℚ)) := by
  unfold graphStorageCost
  simp_rw [lap_sq_eq]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) (crossDegree nb bits i)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hc : crossDegree nb bits i ≤ d := (Finset.card_filter_le ..).trans (hd i)
    exact_mod_cast (show (crossDegree nb bits i)^2 ≤ d*crossDegree nb bits i by
      rw [pow_two]; exact Nat.mul_le_mul_right _ hc)

end PVNP.SeparatorPrice
