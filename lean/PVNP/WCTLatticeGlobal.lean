import PVNP.WCTLatticeGlobalBounds

/-!
# Global classical evolution of the finite WCT lattice

We construct globally Lipschitz bounded truncations and glue their
Picard--Lindelof solutions on expanding time intervals. A radial retraction
preserves tangency to mass spheres, so mass conservation proves that a
truncation chosen from the initial mass never acts on the resulting solution.

The interval-gluing and radial-retraction architecture is adapted from
`rickyjreyes/math`, `MathProofs/CubicQuinticFlow.lean` at commit
`30a5ddc9271a107c355024a7241f13d86ec496a9`. This file proves the finite lattice
statement directly; it imports no whole-space PDE existence theorem.
-/

open Filter Topology Set
open scoped NNReal

namespace PVNP.BoundedODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Construction on an arbitrary compact time interval. -/
theorem exists_interval (v : E → E) (K B : ℝ≥0) (hLip : LipschitzWith K v)
    (hB : ∀ x, ‖v x‖ ≤ B) (u₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → E, α 0 = u₀ ∧ ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt α (v (α t)) (Icc (-T) T) t := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hPL : IsPicardLindelof (fun (_ : ℝ) x => v x)
      (tmin := -T) (tmax := T) ⟨0, h0⟩ u₀
      ⟨B * T, mul_nonneg B.coe_nonneg hT⟩ 0 B K := by
    refine ⟨fun _ _ => hLip.lipschitzOnWith, fun _ _ => continuousOn_const,
      fun _ _ x _ => hB x, ?_⟩
    simp only [NNReal.coe_mk, NNReal.coe_zero, sub_zero, zero_sub, neg_neg, max_self]
    exact le_refl _
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- A bounded globally Lipschitz vector field has an actual global solution. -/
theorem exists_global (v : E → E) (K B : ℝ≥0) (hLip : LipschitzWith K v)
    (hB : ∀ x, ‖v x‖ ≤ B) (u₀ : E) :
    ∃ z : ℝ → E, z 0 = u₀ ∧ ∀ t, HasDerivAt z (v (z t)) t := by
  have hloc : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = u₀ ∧
      ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        HasDerivWithinAt α (v (α t)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t :=
    fun n => exists_interval v K B hLip hB u₀ (by positivity)
  choose α hα0 hα using hloc
  have hder : ∀ (n : ℕ) (t : ℝ), |t| < (n : ℝ) + 1 →
      HasDerivAt (α n) (v (α n t)) t := by
    intro n t ht
    have h1 := neg_abs_le t
    have h2 := le_abs_self t
    exact (hα n t ⟨by linarith, by linarith⟩).hasDerivAt
      (Icc_mem_nhds (by linarith) (by linarith))
  have hcons : ∀ (m n : ℕ) (t : ℝ), |t| < (m : ℝ) + 1 →
      |t| < (n : ℝ) + 1 → α m t = α n t := by
    intro m n t hm hn
    let T := min ((m : ℝ) + 1) ((n : ℝ) + 1)
    have hTm : T ≤ (m : ℝ) + 1 := min_le_left _ _
    have hTn : T ≤ (n : ℝ) + 1 := min_le_right _ _
    have htT : |t| < T := lt_min hm hn
    have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg t) htT
    have key := ODE_solution_unique_of_mem_Ioo (v := fun (_ : ℝ) x => v x)
      (s := fun _ => univ) (fun _ _ => hLip.lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, hT0⟩)
      (fun s hs => ⟨hder m s (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩), trivial⟩)
      (fun s hs => ⟨hder n s (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩), trivial⟩)
      ((hα0 m).trans (hα0 n).symm)
    exact key ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨fun t => α ⌈|t|⌉₊ t, hα0 _, fun t => ?_⟩
  have hn : |t| < (⌈|t|⌉₊ : ℝ) + 1 :=
    lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  refine (hder _ t hn).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_abs.tendsto t).eventually (gt_mem_nhds hn)] with s hs
  exact hcons _ _ s (lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)) hs

/-- Radial retraction, used in the original finite-dimensional norm. -/
noncomputable def retract (R : ℝ) (x : E) : E :=
  if ‖x‖ ≤ R then x else (R / ‖x‖) • x

theorem retract_eq {R : ℝ} {x : E} (h : ‖x‖ ≤ R) : retract R x = x := if_pos h

theorem norm_retract_le {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖retract R x‖ ≤ R := by
  by_cases h : ‖x‖ ≤ R
  · rwa [retract_eq h]
  · have hx : 0 < ‖x‖ := lt_of_le_of_lt hR (lt_of_not_ge h)
    rw [retract, if_neg h, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hR hx.le), div_mul_cancel₀ _ hx.ne']

theorem norm_sub_retract_le {R : ℝ} (hR : 0 ≤ R) {x y : E}
    (hx : ‖x‖ ≤ R) (hy : R < ‖y‖) :
    ‖x - (R / ‖y‖) • y‖ ≤ 2 * ‖x - y‖ := by
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt hR hy
  have hc : R / ‖y‖ ≤ 1 := (div_le_one hy0).2 hy.le
  have e : y - (R / ‖y‖) • y = (1 - R / ‖y‖) • y := by
    rw [sub_smul, one_smul]
  have h1 : ‖y - (R / ‖y‖) • y‖ = ‖y‖ - R := by
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      sub_mul, one_mul, div_mul_cancel₀ _ hy0.ne']
  have h2 : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le y x
  calc
    _ ≤ ‖x - y‖ + ‖y - (R / ‖y‖) • y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖x - y‖ := by rw [h1]; linarith

theorem retract_arith {R a b d : ℝ} (hR : 0 ≤ R) (ha : R < a) (hb : R < b)
    (hd : |a - b| ≤ d) : R / a * d + |R / a - R / b| * b ≤ 2 * d := by
  have ha0 : 0 < a := lt_of_le_of_lt hR ha
  have hb0 : 0 < b := lt_of_le_of_lt hR hb
  have hc : 0 ≤ R / a := div_nonneg hR ha0.le
  have hc1 : R / a ≤ 1 := (div_le_one ha0).2 ha.le
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  have e1 : |R / a - R / b| * b = |(R / a - R / b) * b| := by
    rw [abs_mul, abs_of_pos hb0]
  have e2 : (R / a - R / b) * b = R / a * (b - a) := by field_simp
  have h1 : |R / a - R / b| * b = R / a * |a - b| := by
    rw [e1, e2, abs_mul, abs_of_nonneg hc, abs_sub_comm]
  rw [h1]
  calc
    _ ≤ R / a * d + R / a * d := by gcongr
    _ = R / a * (2 * d) := by ring
    _ ≤ 1 * (2 * d) := by gcongr
    _ = 2 * d := one_mul _

theorem lipschitz_retract {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 2 (retract (E := E) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖retract R x - retract R y‖ ≤ 2 * ‖x - y‖
  rcases le_or_gt ‖x‖ R with hx | hx <;> rcases le_or_gt ‖y‖ R with hy | hy
  · rw [retract_eq hx, retract_eq hy]
    linarith [norm_nonneg (x - y)]
  · rw [retract_eq hx, retract, if_neg (not_le.2 hy)]
    exact norm_sub_retract_le hR hx hy
  · rw [retract, if_neg (not_le.2 hx), retract_eq hy, norm_sub_rev, norm_sub_rev x y]
    exact norm_sub_retract_le hR hy hx
  · rw [retract, if_neg (not_le.2 hx), retract, if_neg (not_le.2 hy)]
    have hx0 : 0 < ‖x‖ := lt_of_le_of_lt hR hx
    have e : (R / ‖x‖) • x - (R / ‖y‖) • y =
        (R / ‖x‖) • (x - y) + (R / ‖x‖ - R / ‖y‖) • y := by
      rw [smul_sub, sub_smul]
      abel
    rw [e]
    calc
      _ ≤ ‖(R / ‖x‖) • (x - y)‖ + ‖(R / ‖x‖ - R / ‖y‖) • y‖ := norm_add_le _ _
      _ = R / ‖x‖ * ‖x - y‖ + |R / ‖x‖ - R / ‖y‖| * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hR hx0.le)]
      _ ≤ 2 * ‖x - y‖ := retract_arith hR hx hy (abs_norm_sub_norm_le x y)

end PVNP.BoundedODE

namespace PVNP.WCTLattice

open PVNP.BoundedODE
open scoped InnerProductSpace

variable {N : ℕ} [NeZero N]

theorem vf_locallyLipschitz (a b β γ : ℝ) :
    LocallyLipschitz (vf (N := N) a b β γ) :=
  (contDiff_vf a b β γ).locallyLipschitz

/-- One Lipschitz constant on each fixed finite-dimensional closed ball. -/
theorem vf_lipschitz_ball (a b β γ R : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (vf (N := N) a b β γ) (Metric.closedBall 0 R) := by
  have hc := (contDiff_vf (N := N) a b β γ).continuous_fderiv (by rfl)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fld N) R).bddAbove_image hc.norm.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (contDiff_vf a b β γ).differentiable (by rfl) x) _ (convex_closedBall 0 R)
  intro x hx
  change ‖fderiv ℝ (vf a b β γ) x‖ ≤ max C 0
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)

noncomputable def truncated (a b β γ R : ℝ) (u : Fld N) : Fld N :=
  vf a b β γ (retract R u)

theorem truncated_bounded_lipschitz (a b β γ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K B : ℝ≥0, LipschitzWith K (truncated (N := N) a b β γ R) ∧
      ∀ u : Fld N, ‖truncated a b β γ R u‖ ≤ B := by
  obtain ⟨K, hK⟩ := vf_lipschitz_ball (N := N) a b β γ R
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fld N) R).bddAbove_image
    (contDiff_vf a b β γ).continuous.norm.continuousOn
  have hr : ∀ u : Fld N, retract R u ∈ Metric.closedBall 0 R := fun u => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using norm_retract_le hR u
  refine ⟨K * 2, ⟨max B 0, le_max_right _ _⟩, ?_, fun u => ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    calc
      _ ≤ K * dist (retract R u) (retract R v) := hK.dist_le_mul _ (hr u) _ (hr v)
      _ ≤ K * (2 * dist u v) :=
        mul_le_mul_of_nonneg_left ((lipschitz_retract hR).dist_le_mul u v) K.coe_nonneg
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
  · exact (hB ⟨retract R u, hr u, rfl⟩).trans (le_max_left _ _)

/-- The radial truncation remains tangent to every mass sphere. -/
theorem sum_inner_truncated (a b β γ : ℝ) {R : ℝ} (hR : 0 < R) (u : Fld N) :
    ∑ j, ⟪u j, truncated a b β γ R u j⟫_ℝ = 0 := by
  by_cases hu : ‖u‖ ≤ R
  · simpa only [truncated, retract_eq hu] using sum_inner_vf a b β γ u
  · have hu0 : 0 < ‖u‖ := lt_trans hR (lt_of_not_ge hu)
    have hc : R / ‖u‖ ≠ 0 := ne_of_gt (div_pos hR hu0)
    have ht := sum_inner_vf a b β γ (retract R u)
    change ∑ j, ⟪retract R u j, truncated a b β γ R u j⟫_ℝ = 0 at ht
    simp only [retract, if_neg hu, Pi.smul_apply, real_inner_smul_left] at ht
    rw [← Finset.mul_sum] at ht
    exact (mul_eq_zero.mp ht).resolve_left hc

theorem norm_le_sqrt_mass (u : Fld N) : ‖u‖ ≤ Real.sqrt (mass u) := by
  exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    (coordinate_norm_le_sqrt_mass u)

/-- Construct a global solution of the original equation, with no positivity
restriction on a, b, beta or gamma. The conserved mass prevents blowup. -/
theorem exists_global_solution (a b β γ : ℝ) (u₀ : Fld N) :
    ∃ z : ℝ → Fld N, z 0 = u₀ ∧ IsSol a b β γ z := by
  let R := Real.sqrt (mass u₀) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨K, B, hK, hB⟩ := truncated_bounded_lipschitz (N := N) a b β γ hR.le
  obtain ⟨z, hz0, hz⟩ := BoundedODE.exists_global (truncated a b β γ R) K B hK hB u₀
  have hmassDer : ∀ t, HasDerivAt (fun s => mass (z s)) 0 t := by
    intro t
    have ht := hasDerivAt_nsq (hasDerivAt_pi.1 (hz t))
    rwa [← Finset.mul_sum, sum_inner_truncated a b β γ hR, mul_zero] at ht
  have hmass : ∀ t, mass (z t) = mass u₀ := by
    intro t
    have h := is_const_of_deriv_eq_zero (fun s => (hmassDer s).differentiableAt)
      (fun s => (hmassDer s).deriv) t 0
    rwa [hz0] at h
  have hnorm : ∀ t, ‖z t‖ ≤ R := by
    intro t
    calc
      _ ≤ Real.sqrt (mass (z t)) := norm_le_sqrt_mass _
      _ ≤ R := by rw [hmass]; dsimp [R]; linarith
  refine ⟨z, hz0, fun t j => ?_⟩
  simpa only [truncated, retract_eq (hnorm t)] using (hasDerivAt_pi.1 (hz t)) j

/-- Global uniqueness in the original solution convention. -/
theorem global_solution_unique {a b β γ : ℝ} {z w : ℝ → Fld N}
    (hz : IsSol a b β γ z) (hw : IsSol a b β γ w) (h0 : z 0 = w 0) : z = w := by
  let R := Real.sqrt (mass (z 0))
  obtain ⟨K, hK⟩ := vf_lipschitz_ball (N := N) a b β γ R
  have hzb : ∀ t, z t ∈ Metric.closedBall 0 R := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ Real.sqrt (mass (z t)) := norm_le_sqrt_mass _
      _ = R := by rw [mass_conserved hz t]
  have hwb : ∀ t, w t ∈ Metric.closedBall 0 R := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ Real.sqrt (mass (w t)) := norm_le_sqrt_mass _
      _ = R := by rw [mass_conserved hw t, ← h0]
  funext t
  let T := |t| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hinit : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  have ht : t ∈ Ioo (-T) T := by
    dsimp [T]
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  exact ODE_solution_unique_of_mem_Ioo (v := fun (_ : ℝ) u => vf a b β γ u)
    (s := fun _ => Metric.closedBall 0 R) (fun _ _ => hK) hinit
    (fun s _ => ⟨hasDerivAt_pi.2 (hz s), hzb s⟩)
    (fun s _ => ⟨hasDerivAt_pi.2 (hw s), hwb s⟩) h0 ht

/-- M3-G: every initial condition has exactly one global classical solution. -/
theorem global_wellposed (a b β γ : ℝ) (u₀ : Fld N) :
    ∃! z : ℝ → Fld N, z 0 = u₀ ∧ IsSol a b β γ z := by
  obtain ⟨z, hz0, hz⟩ := exists_global_solution a b β γ u₀
  exact ⟨z, ⟨hz0, hz⟩, fun w hw => global_solution_unique hw.2 hz (hw.1.trans hz0.symm)⟩

/-- Conservation and bounds now hold for a constructed global solution. -/
theorem exists_global_conserved_bounded (a b β γ : ℝ) (u₀ : Fld N) :
    ∃ z : ℝ → Fld N, z 0 = u₀ ∧ IsSol a b β γ z ∧
      ∀ t, mass (z t) = mass u₀ ∧ ham a b β γ (z t) = ham a b β γ u₀ ∧
        ∀ j, ‖z t j‖ ≤ Real.sqrt (mass u₀) := by
  obtain ⟨z, hz0, hz⟩ := exists_global_solution a b β γ u₀
  refine ⟨z, hz0, hz, fun t => ?_⟩
  refine ⟨?_, ?_, fun j => ?_⟩
  · simpa only [hz0] using mass_conserved hz t
  · simpa only [hz0] using ham_conserved hz t
  · simpa only [hz0] using solution_uniform_coordinate_bound hz t j

/-- Every previously constructed local solution is the restriction of the
unique global solution with the same initial data. -/
theorem local_global_agree {a b β γ ε : ℝ} {z w : ℝ → Fld N}
    (hz : IsSol a b β γ z)
    (hw : ∀ t ∈ Ioo (-ε) ε, ∀ j,
      HasDerivAt (fun s => w s j) (vf a b β γ (w t) j) t)
    (h0 : z 0 = w 0) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : z t = w t := by
  let R := Real.sqrt (mass (z 0))
  obtain ⟨K, hK⟩ := vf_lipschitz_ball (N := N) a b β γ R
  have hinit : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith [ht.1, ht.2]
  have hzb : ∀ s, z s ∈ Metric.closedBall 0 R := by
    intro s
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ Real.sqrt (mass (z s)) := norm_le_sqrt_mass _
      _ = R := by rw [mass_conserved hz s]
  have hwb : ∀ s ∈ Ioo (-ε) ε, w s ∈ Metric.closedBall 0 R := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ Real.sqrt (mass (w s)) := norm_le_sqrt_mass _
      _ = R := by rw [(local_conservation hw hs).1, ← h0]
  exact ODE_solution_unique_of_mem_Ioo (v := fun (_ : ℝ) u => vf a b β γ u)
    (s := fun _ => Metric.closedBall 0 R) (fun _ _ => hK) hinit
    (fun s _ => ⟨hasDerivAt_pi.2 (hz s), hzb s⟩)
    (fun s hs => ⟨hasDerivAt_pi.2 (hw s hs), hwb s hs⟩) h0 ht

theorem vf_zero (a b β γ : ℝ) : vf (N := N) a b β γ 0 = 0 := by
  funext j
  simp [vf, grad, Aop, nlin]

/-- Zero initial data gives the zero solution, even with degenerate or
negative coefficients. -/
theorem zero_initial_stationary {a b β γ : ℝ} {z : ℝ → Fld N}
    (hz : IsSol a b β γ z) (h0 : z 0 = 0) : z = fun _ => 0 := by
  apply global_solution_unique hz _ h0
  intro t j
  simpa only [vf_zero, Pi.zero_apply] using hasDerivAt_const t (0 : ℂ)

/-- With all coefficients zero the unique global flow fixes every datum. -/
theorem zero_coefficients_stationary {z : ℝ → Fld N} (hz : IsSol 0 0 0 0 z) :
    z = fun _ => z 0 := by
  apply global_solution_unique (w := fun _ => z 0) hz _ rfl
  intro t j
  simpa [vf, grad, Aop, nlin] using hasDerivAt_const t (z 0 j)

end PVNP.WCTLattice
