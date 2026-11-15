import PVNP.TorusGalerkinCertificate

/-!
# Compact-trajectory Fourier approximation

The radius cutoff gives a bounded globally Lipschitz finite Fourier vector field.
Compactness supplies qualitative uniform tails, not a computable tail modulus.
-/
open Filter Topology Set
namespace PVNP.TorusGalerkin
open PVNP.Torus PVNP.ContinuumPrecision

theorem trunc_lipschitz (S : Finset Z2) : LipschitzWith 1 (trunc S) := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, ← trunc_sub] using
    trunc_norm_le S (v - w)

/-- Pointwise Fourier convergence is uniform on each compact set of H² states. -/
theorem compact_uniform_tail {K : Set ℓ2} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : Finset Z2 in atTop, ∀ v ∈ K, ‖trunc S v - v‖ < ε := by
  obtain ⟨a, haK, ha, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 4 by positivity)
  have hev : ∀ v ∈ a, ∀ᶠ S : Finset Z2 in atTop, ‖trunc S v - v‖ < ε / 2 := by
    intro v _
    have h : Tendsto (fun S : Finset Z2 => ‖trunc S v - v‖) atTop (𝓝 0) := by
      simpa using ((tendsto_trunc v).sub
        (show Tendsto (fun _ : Finset Z2 => v) atTop (𝓝 v) from tendsto_const_nhds)).norm
    exact h.eventually (gt_mem_nhds (by positivity))
  filter_upwards [ha.eventually_all.2 hev] with S hS
  intro v hv
  obtain ⟨w, hwa, hw⟩ := mem_iUnion₂.1 (hcover hv)
  have hd : ‖v - w‖ < ε / 4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hproj : ‖trunc S v - trunc S w‖ ≤ ‖v - w‖ := by
    rw [← trunc_sub]; exact trunc_norm_le S _
  have htri := norm_sub_le_norm_sub_add_norm_sub (trunc S v) (trunc S w) v
  have htri' := norm_sub_le_norm_sub_add_norm_sub (trunc S w) w v
  rw [norm_sub_rev w v] at htri'
  have := hS w hwa
  linarith

noncomputable def clipped (S : Finset Z2) (L κ β γ R t : ℝ) (v : ℓ2) : ℓ2 :=
  trunc S (Gtr L κ β γ R t (trunc S v))

theorem clipped_support (S : Finset Z2) (L κ β γ R t : ℝ) (v : ℓ2)
    {k : Z2} (hk : k ∉ S) : clipped S L κ β γ R t v k = 0 := by
  simp [clipped, trunc_apply, hk]

theorem clipped_lipschitz {L κ β γ R : ℝ} (hL : 0 < L) (hR : 0 ≤ R)
    (S : Finset Z2) (t : ℝ) :
    LipschitzWith ⟨2 * LF L β γ R, mul_nonneg zero_le_two (LF_nonneg L β γ R)⟩
      (clipped S L κ β γ R t) := by
  simpa only [mul_one, one_mul] using
    (trunc_lipschitz S).comp ((lipschitzWith_Gtr hL hR t).comp (trunc_lipschitz S))

theorem clipped_bound {L κ β γ R : ℝ} (hL : 0 < L) (hR : 0 ≤ R)
    (S : Finset Z2) (t : ℝ) (v : ℓ2) :
    ‖clipped S L κ β γ R t v‖ ≤ LF L β γ R * R :=
  (trunc_norm_le S _).trans (norm_Gtr_le hL hR t _)

theorem clipped_continuous_time {L κ β γ R : ℝ} (hL : 0 < L)
    (S : Finset Z2) (v : ℓ2) : Continuous fun t => clipped S L κ β γ R t v :=
  (trunc_lipschitz S).continuous.comp (continuous_Gtr_time hL R (trunc S v))

theorem clipped_eq_galerkin (S : Finset Z2) (L κ β γ R t : ℝ) {v : ℓ2}
    (hv : ‖v‖ ≤ R) : clipped S L κ β γ R t v = galerkin S L κ β γ t v := by
  unfold clipped galerkin
  rw [Gtr_of_le t ((trunc_norm_le S v).trans hv)]

/-- Uniform consistency along a continuous bounded trajectory on a compact time set. -/
theorem clipped_uniform_consistency {L κ β γ R : ℝ} (hL : 0 < L)
    {J : Set ℝ} (hJ : IsCompact J) {w : ℝ → ℓ2} (hw : Continuous w)
    (hR : ∀ t ∈ J, ‖w t‖ ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : Finset Z2 in atTop, ∀ t ∈ J,
      ‖clipped S L κ β γ R t (w t) - Gf L κ β γ t (w t)‖ < ε := by
  have hLF := LF_nonneg L β γ R
  let d := ε / (2 * (LF L β γ R + 1))
  have hd : 0 < d := div_pos hε (by positivity)
  have hg : Continuous fun t => Gf L κ β γ t (w t) :=
    (continuous_Gf hL).comp (continuous_id.prodMk hw)
  filter_upwards [compact_uniform_tail (hJ.image hw) hd,
    compact_uniform_tail (hJ.image hg) hd] with S hs hgS
  intro t ht
  rw [clipped_eq_galerkin S L κ β γ R t (hR t ht)]
  have h := consistency_bound hL S t (hR t ht)
  have h1 := hs (w t) (mem_image_of_mem w ht)
  have h2 := hgS (Gf L κ β γ t (w t)) (mem_image_of_mem _ ht)
  have hdval : (LF L β γ R + 1) * d = ε / 2 := by
    dsimp [d]
    field_simp
    <;> ring
  have hmul := mul_le_mul_of_nonneg_left h1.le hLF
  nlinarith

variable {L κ β γ : ℝ}

/-- Local existence on `[−T, T]` for the truncated equation (Picard–Lindelöf). -/
theorem exists_local_clipped (hL : 0 < L) (S : Finset Z2) {R : ℝ} (hR : 0 ≤ R) (u₀ : ℓ2) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → ℓ2, α 0 = u₀ ∧ ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt α (clipped S L κ β γ R t (α t)) (Icc (-T) T) t := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  obtain ⟨B, hB⟩ : ∃ B, B = LF L β γ R * R := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact mul_nonneg (LF_nonneg L β γ R) hR
  have hPL : IsPicardLindelof (clipped S L κ β γ R) (tmin := -T) (tmax := T) ⟨0, h0⟩ u₀
      ⟨B * T, mul_nonneg hB0 hT⟩ 0 ⟨B, hB0⟩
      ⟨2 * LF L β γ R, mul_nonneg zero_le_two (LF_nonneg L β γ R)⟩ := by
    refine ⟨fun t _ => (clipped_lipschitz hL hR S t).lipschitzOnWith, fun x _ => ?_,
      fun t _ x _ => ?_, ?_⟩
    · exact (clipped_continuous_time hL S x).continuousOn
    · rw [NNReal.coe_mk, hB]; exact clipped_bound hL hR S t x
    · simp only [NNReal.coe_mk, NNReal.coe_zero, sub_zero, zero_sub, neg_neg, max_self]
      exact le_refl _
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hα⟩

/-- Global existence for the truncated equation. -/
theorem exists_global_clipped (hL : 0 < L) (S : Finset Z2) {R : ℝ} (hR : 0 ≤ R) (u₀ : ℓ2) :
    ∃ W : ℝ → ℓ2, W 0 = u₀ ∧ ∀ t, HasDerivAt W (clipped S L κ β γ R t (W t)) t := by
  have hloc : ∀ n : ℕ, ∃ α : ℝ → ℓ2, α 0 = u₀ ∧ ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivWithinAt α (clipped S L κ β γ R t (α t)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t :=
    fun n => exists_local_clipped hL S hR u₀ (by positivity)
  choose α hα0 hα using hloc
  have hder : ∀ (n : ℕ) (t : ℝ), |t| < (n : ℝ) + 1 →
      HasDerivAt (α n) (clipped S L κ β γ R t (α n t)) t := by
    intro n t ht
    have h1 := neg_abs_le t
    have h2 := le_abs_self t
    exact (hα n t ⟨by linarith, by linarith⟩).hasDerivAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcons : ∀ (m n : ℕ) (t : ℝ), |t| < (m : ℝ) + 1 → |t| < (n : ℝ) + 1 → α m t = α n t := by
    intro m n t hm hn
    obtain ⟨T, hT⟩ : ∃ T, T = min ((m : ℝ) + 1) ((n : ℝ) + 1) := ⟨_, rfl⟩
    have hTm : T ≤ (m : ℝ) + 1 := hT ▸ min_le_left _ _
    have hTn : T ≤ (n : ℝ) + 1 := hT ▸ min_le_right _ _
    have htT : |t| < T := hT ▸ lt_min hm hn
    have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg t) htT
    have key := ODE_solution_unique_of_mem_Ioo (v := clipped S L κ β γ R) (s := fun _ => univ)
      (fun s _ => (clipped_lipschitz hL hR S s).lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, hT0⟩)
      (fun s hs => ⟨hder m s (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩), trivial⟩)
      (fun s hs => ⟨hder n s (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩), trivial⟩)
      ((hα0 m).trans (hα0 n).symm)
    exact key ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨fun t => α ⌈|t|⌉₊ t, hα0 _, fun t => ?_⟩
  have hn : |t| < (⌈|t|⌉₊ : ℝ) + 1 := lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  refine (hder _ t hn).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_abs.tendsto t).eventually (gt_mem_nhds hn)] with s hs
  exact hcons _ _ s (lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)) hs


/-- No unrepresented Fourier coordinate is created by the clipped evolution. -/
theorem clipped_trajectory_support {R : ℝ} {S : Finset Z2} {W : ℝ → ℓ2}
    (hW : ∀ t, HasDerivAt W (clipped S L κ β γ R t (W t)) t)
    {k : Z2} (hk : k ∉ S) (h0 : W 0 k = 0) (t : ℝ) : W t k = 0 := by
  have hd : ∀ t, HasDerivAt (fun s => W s k) 0 t := by
    intro s
    have h := ((evalL k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hW s)
    simpa only [ContinuousLinearMap.restrictScalars_apply, evalL_apply,
      clipped_support S L κ β γ R s (W s) hk] using h
  exact (is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0).trans h0

theorem gronwall_diagonal_scale (d K t : ℝ) :
    gronwallBound d K d t = d * gronwallBound 1 K 1 t := by
  unfold gronwallBound
  split_ifs <;> ring

theorem gronwall_diagonal_mono {d K t T : ℝ} (hd : 0 ≤ d) (hK : 0 ≤ K)
    (ht : t ≤ T) : gronwallBound d K d t ≤ gronwallBound d K d T := by
  unfold gronwallBound
  split_ifs with h
  · gcongr
  · have hK' : 0 < K := lt_of_le_of_ne hK (Ne.symm h)
    have he : Real.exp (K * t) ≤ Real.exp (K * T) := Real.exp_le_exp.mpr (by gcongr)
    have hdiv : 0 ≤ d / K := div_nonneg hd hK
    nlinarith [mul_le_mul_of_nonneg_left he hd, mul_le_mul_of_nonneg_left he hdiv]

/-- Comparison uses the finite field for both curves. No radius bound on W is assumed. -/
theorem clipped_trajectory_error (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R)
    (S : Finset Z2) {W w : ℝ → ℓ2} {T δ η : ℝ}
    (hW : ∀ t, HasDerivAt W (clipped S L κ β γ R t (W t)) t)
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t)
    (hres : ∀ t ∈ Ico 0 T,
      ‖clipped S L κ β γ R t (w t) - Gf L κ β γ t (w t)‖ ≤ η)
    (h0 : ‖W 0 - w 0‖ ≤ δ) :
    ∀ t ∈ Icc 0 T, ‖W t - w t‖ ≤ gronwallBound δ (2 * LF L β γ R) η t := by
  have hcW : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hcw : Continuous w := continuous_iff_continuousAt.2 fun t => (hw t).continuousAt
  have h := dist_le_of_approx_trajectories_ODE
    (v := clipped S L κ β γ R) (a := 0) (b := T)
    (f := W) (g := w) (f' := fun t => clipped S L κ β γ R t (W t))
    (g' := fun t => Gf L κ β γ t (w t)) (εf := 0) (εg := η) (δ := δ)
    (clipped_lipschitz hL hR S) hcW.continuousOn (fun t _ => (hW t).hasDerivWithinAt)
    (fun t _ => by simp) hcw.continuousOn (fun t _ => (hw t).hasDerivWithinAt)
    (fun t ht => by rw [dist_eq_norm, norm_sub_rev]; exact hres t ht)
    (by simpa only [dist_eq_norm] using h0)
  simpa only [dist_eq_norm, NNReal.coe_mk, zero_add, sub_zero] using h

/-- A family of actual finite-system trajectories converges uniformly on every fixed
compact forward interval to a bounded exact interaction-picture solution. -/
theorem exists_convergent_clipped (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R)
    {w : ℝ → ℓ2} (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t)
    (hball : ∀ t, ‖w t‖ ≤ R) :
    ∃ W : Finset Z2 → ℝ → ℓ2,
      (∀ S, W S 0 = trunc S (w 0)) ∧
      (∀ S t, HasDerivAt (W S) (clipped S L κ β γ R t (W S t)) t) ∧
      (∀ S k, k ∉ S → ∀ t, W S t k = 0) ∧
      ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ S : Finset Z2 in atTop, ∀ t ∈ Icc 0 T, ‖W S t - w t‖ < ε := by
  choose W hW0 hW using fun S : Finset Z2 =>
    exists_global_clipped hL S hR (trunc S (w 0))
  refine ⟨W, hW0, hW, ?_, ?_⟩
  · intro S k hk t
    apply clipped_trajectory_support (hW S) hk _ t
    rw [hW0 S, trunc_apply, if_neg hk]
  · intro T hT ε hε
    let K := 2 * LF L β γ R
    let C := |gronwallBound 1 K 1 T| + 1
    let d := ε / (2 * C)
    have hK : 0 ≤ K := mul_nonneg zero_le_two (LF_nonneg L β γ R)
    have hC : 0 < C := by dsimp [C]; positivity
    have hd : 0 < d := div_pos hε (by positivity)
    have hdC : d * C = ε / 2 := by dsimp [d]; field_simp; ring
    have hc : Continuous w := continuous_iff_continuousAt.2 fun t => (hw t).continuousAt
    have hi : ∀ᶠ S : Finset Z2 in atTop, ‖trunc S (w 0) - w 0‖ < d := by
      have h : Tendsto (fun S : Finset Z2 => ‖trunc S (w 0) - w 0‖) atTop (𝓝 0) := by
        simpa using ((tendsto_trunc (w 0)).sub
          (show Tendsto (fun _ : Finset Z2 => w 0) atTop (𝓝 (w 0)) from tendsto_const_nhds)).norm
      exact h.eventually (gt_mem_nhds hd)
    filter_upwards [hi, clipped_uniform_consistency hL isCompact_Icc hc
      (fun t _ => hball t) hd] with S hi hs
    intro t ht
    have he := clipped_trajectory_error hL hR S (hW S) hw
      (fun s hst => (hs s ⟨hst.1, hst.2.le⟩).le)
      (show ‖W S 0 - w 0‖ ≤ d by rw [hW0]; exact hi.le) t ht
    have hm := gronwall_diagonal_mono hd.le hK ht.2
    rw [gronwall_diagonal_scale] at hm
    have ha := le_abs_self (gronwallBound 1 K 1 T)
    have hb : gronwallBound 1 K 1 T < C := by dsimp [C]; linarith
    have hm' := mul_lt_mul_of_pos_left hb hd
    change ‖W S t - w t‖ ≤ gronwallBound d K d t at he
    linarith

/-- With one unit of radius slack, the cutoff is eventually inactive on each
compact interval. The resulting trajectories solve the original Galerkin system. -/
theorem exists_convergent_galerkin (hL : 0 < L) {R : ℝ} (hR : 0 ≤ R)
    {w : ℝ → ℓ2} (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t)
    (hball : ∀ t, ‖w t‖ ≤ R) :
    ∃ W : Finset Z2 → ℝ → ℓ2,
      (∀ S, W S 0 = trunc S (w 0)) ∧
      (∀ S k, k ∉ S → ∀ t, W S t k = 0) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ᶠ S : Finset Z2 in atTop,
        ∀ t ∈ Icc 0 T, HasDerivAt (W S) (galerkin S L κ β γ t (W S t)) t) ∧
      ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ S : Finset Z2 in atTop, ∀ t ∈ Icc 0 T, ‖W S t - w t‖ < ε := by
  obtain ⟨W, h0, hW, hs, he⟩ := exists_convergent_clipped hL
    (show 0 ≤ R + 1 by linarith) hw (fun t => (hball t).trans (by linarith))
  refine ⟨W, h0, hs, ?_, he⟩
  intro T hT
  filter_upwards [he T hT 1 zero_lt_one] with S hS
  intro t ht
  have hn := norm_le_norm_sub_add (W S t) (w t)
  have hb : ‖W S t‖ ≤ R + 1 := by linarith [hS t ht, hball t]
  simpa only [clipped_eq_galerkin S L κ β γ (R + 1) t hb] using hW S t

/-- Actual frozen-PDE solutions admit finite Fourier ODE trajectories with arbitrarily
small uniform H² error on a finite forward interval. This existence theorem has
no computable cutoff modulus and no arithmetic cost assertion. -/
theorem frozen_galerkin_approximation (hL : 0 < L) (hγ : 0 < γ)
    {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ S : Finset Z2, ∃ W : ℝ → ℓ2,
      W 0 = trunc S (u 0) ∧
      (∀ k, k ∉ S → ∀ t, W t k = 0) ∧
      (∀ t ∈ Icc 0 T, HasDerivAt W (galerkin S L κ β γ t (W t)) t) ∧
      ∀ t ∈ Icc 0 T, ‖U L κ t (W t) - u t‖ < ε := by
  let w := fun t => U L κ (-t) (u t)
  let R := Rap κ β γ (mass L (u 0)) (ham L κ β γ (u 0))
  have hR : 0 ≤ R := (norm_nonneg (u 0)).trans (apriori hL hγ hu 0)
  have hw := ode_of_isSolution hL hu
  have hb : ∀ t, ‖w t‖ ≤ R := by
    intro t
    dsimp [w]
    rw [norm_U]
    exact apriori hL hγ hu t
  obtain ⟨W, h0, hs, hd, he⟩ := exists_convergent_galerkin hL hR hw hb
  obtain ⟨S, hS, hE⟩ := ((hd T hT).and (he T hT ε hε)).exists
  refine ⟨S, W S, ?_, hs S, hS, ?_⟩
  · simpa only [w, neg_zero, U_zero] using h0 S
  · intro t ht
    have hnorm : ‖U L κ t (W S t) - u t‖ = ‖W S t - w t‖ := by
      calc
        _ = ‖U L κ t (W S t - U L κ (-t) (u t))‖ := by rw [map_sub, U_U_neg]
        _ = _ := norm_U _ _ _ _
    rw [hnorm]
    exact hE t ht

end PVNP.TorusGalerkin
