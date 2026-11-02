import Mathlib

/-!
# Noise-robust bandlimited receiver packing bound (issue #15)

Formalization of `pvnp/proofs/bandlimited-noisy-wave-packing.md`.

* `packing_card_le`: in **any** finite-dimensional real normed space `E`, a
  finite family of vectors of norm `≤ R` that are pairwise at distance
  `≥ 2η` (`η > 0`) has at most `(1 + R/η)^(finrank ℝ E)` elements.  The proof
  is the genuine volume argument with an additive Haar measure (disjoint
  `η`-balls inside the `(R+η)`-ball, homogeneity `μ(B(x,r)) = r^d μ(B(0,1))`).
* `finrank_real_euclideanSpace_complex`: a complex `D`-mode receiver space
  `ℂ^D` has real dimension exactly `2D`.
* `complex_receiver_packing`: `N ≤ (1 + √M/η)^(2D)` for `N` codewords in
  `ℂ^D` with `‖v‖ ≤ √M` and pairwise distance `≥ 2η`.  (The supplement
  assumes the strictly stronger separation `> 2η`; see
  `complex_receiver_packing_strict`.)
* `subspace_receiver_packing`: the same bound for any complex
  `D`-dimensional receiver *subspace* of an arbitrary complex inner-product
  space, applied to orthogonal projections of states of mass `≤ M`.
* `capacity_bits_le`, `mass_lower_bound`: the bit-capacity and mass corollaries.

Scope: this is a static coding bound for a declared finite-dimensional noisy
receiver.  It does **not** assert that a nonlinear PDE preserves finite
Fourier support (see `PVNP.FourierReceiverProjection`) and it is **not** a
decision-time lower bound (see `PVNP.DecisionVsEncodingCounterexample`).
-/

namespace PVNP.Packing

open MeasureTheory Metric Module

/-- Disjointness of the noise balls from the separation hypothesis. -/
theorem noise_balls_disjoint {E : Type*} [MetricSpace E] {v w : E} {η : ℝ}
    (h : 2 * η ≤ dist v w) : Disjoint (ball v η) (ball w η) :=
  ball_disjoint_ball (by linarith)

/-- **General packing theorem.** -/
theorem packing_card_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) {R η : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hnorm : ∀ v ∈ s, ‖v‖ ≤ R)
    (hsep : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → 2 * η ≤ dist v w) :
    (s.card : ℝ) ≤ (1 + R / η) ^ finrank ℝ E := by
  borelize E
  set μ : Measure E := Measure.addHaar
  set d := finrank ℝ E
  have hRη : 0 < R + η := by linarith
  -- disjoint balls
  have hdisj : (s : Set E).PairwiseDisjoint fun v => ball v η := by
    intro v hv w hw hvw
    exact noise_balls_disjoint (hsep v hv w hw hvw)
  -- containment
  have hsub : (⋃ v ∈ s, ball v η) ⊆ ball (0 : E) (R + η) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨v, hv, hz⟩ := hz
    rw [mem_ball, dist_zero_right]
    rw [mem_ball] at hz
    calc ‖z‖ = ‖v + (z - v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v‖ + ‖z - v‖ := norm_add_le _ _
      _ < R + η := by
        have := hnorm v hv
        rw [← dist_eq_norm]; linarith
  have hvol : μ (⋃ v ∈ s, ball v η) = ∑ v ∈ s, μ (ball v η) :=
    measure_biUnion_finset hdisj (fun v _ => measurableSet_ball)
  have hball : ∀ v : E, μ (ball v η) = ENNReal.ofReal (η ^ d) * μ (ball 0 1) :=
    fun v => Measure.addHaar_ball_of_pos μ v hη
  have hbig : μ (ball (0 : E) (R + η)) = ENNReal.ofReal ((R + η) ^ d) * μ (ball 0 1) :=
    Measure.addHaar_ball_of_pos μ 0 hRη
  have hle := measure_mono (μ := μ) hsub
  rw [hvol, hbig] at hle
  simp only [hball, Finset.sum_const, nsmul_eq_mul] at hle
  have hpos : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hfin : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have hle2 := (ENNReal.mul_le_mul_right hpos hfin).1 hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle2
  have hηd : 0 < η ^ d := pow_pos hη d
  rw [show 1 + R / η = (R + η) / η by field_simp; ring, div_pow, le_div_iff₀ hηd]
  exact hle2

/-- The real dimension of a complex `D`-mode receiver is `2D`. -/
theorem finrank_real_euclideanSpace_complex (D : ℕ) :
    finrank ℝ (EuclideanSpace ℂ (Fin D)) = 2 * D := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

/-- **Complex receiver packing bound** `N ≤ (1 + √M/η)^(2D)`. -/
theorem complex_receiver_packing (D : ℕ) (s : Finset (EuclideanSpace ℂ (Fin D)))
    {M η : ℝ} (hη : 0 < η)
    (hnorm : ∀ v ∈ s, ‖v‖ ≤ Real.sqrt M)
    (hsep : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → 2 * η ≤ dist v w) :
    (s.card : ℝ) ≤ (1 + Real.sqrt M / η) ^ (2 * D) := by
  have := packing_card_le s hη (Real.sqrt_nonneg M) hnorm hsep
  rwa [finrank_real_euclideanSpace_complex] at this

/-- The supplement's strict separation hypothesis is a special case. -/
theorem complex_receiver_packing_strict (D : ℕ) (s : Finset (EuclideanSpace ℂ (Fin D)))
    {M η : ℝ} (hη : 0 < η)
    (hnorm : ∀ v ∈ s, ‖v‖ ≤ Real.sqrt M)
    (hsep : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → 2 * η < dist v w) :
    (s.card : ℝ) ≤ (1 + Real.sqrt M / η) ^ (2 * D) :=
  complex_receiver_packing D s hη hnorm fun v hv w hw h => (hsep v hv w hw h).le

/-- Orthogonal receiver projection is norm-nonincreasing. -/
theorem receiver_projection_norm_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (K : Submodule ℂ H) [K.HasOrthogonalProjection] (ψ : H) :
    ‖K.orthogonalProjection ψ‖ ≤ ‖ψ‖ :=
  K.norm_orthogonalProjection_apply_le ψ

/-- **Receiver-subspace packing.** `N` labels encoded as states `ψ j` of mass
`‖ψ j‖² ≤ M` in an arbitrary complex inner-product space, observed through
orthogonal projection onto a complex `D`-dimensional receiver subspace `K`,
whose projections are pairwise `≥ 2η` apart, satisfy
`N ≤ (1 + √M/η)^(2D)`. -/
theorem subspace_receiver_packing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    {N : ℕ} (ψ : Fin N → H) {M η : ℝ} (hη : 0 < η)
    (hmass : ∀ j, ‖ψ j‖ ^ 2 ≤ M)
    (hsep : ∀ j k, j ≠ k →
      2 * η ≤ dist (K.orthogonalProjection (ψ j)) (K.orthogonalProjection (ψ k))) :
    (N : ℝ) ≤ (1 + Real.sqrt M / η) ^ (2 * finrank ℂ K) := by
  haveI : FiniteDimensional ℝ K := FiniteDimensional.complexToReal K
  classical
  set v : Fin N → K := fun j => K.orthogonalProjection (ψ j)
  have hinj : Function.Injective v := by
    intro j k h
    by_contra hjk
    have := hsep j k hjk
    simp only [v] at h
    rw [h, dist_self] at this
    linarith
  have hcard : (Finset.univ.image v).card = N := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hp := packing_card_le (E := K) (Finset.univ.image v) hη (Real.sqrt_nonneg M)
    (by
      intro w hw
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
      calc ‖v j‖ ≤ ‖ψ j‖ := receiver_projection_norm_le K (ψ j)
        _ = Real.sqrt (‖ψ j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt M := Real.sqrt_le_sqrt (hmass j))
    (by
      intro w hw w' hw' hne
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hw'
      exact hsep j k (fun h => hne (by rw [h])))
  rw [hcard, finrank_real_of_complex] at hp
  exact hp

/-- **Bit capacity.** If `2^n` labels are robustly distinguishable, then
`n ≤ 2D · log₂(1 + √M/η)`. -/
theorem capacity_bits_le {n D : ℕ} {M η : ℝ} (hη : 0 < η)
    (h : (2 : ℝ) ^ n ≤ (1 + Real.sqrt M / η) ^ (2 * D)) :
    (n : ℝ) ≤ 2 * D * Real.logb 2 (1 + Real.sqrt M / η) := by
  have hb : 0 < 1 + Real.sqrt M / η := by
    have := div_nonneg (Real.sqrt_nonneg M) hη.le; linarith
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
  push_cast at this
  linarith

/-- **Mass lower bound.** With `D ≥ 1`, robust storage of `2^n` labels needs
`M ≥ η² (2^{n/(2D)} - 1)²`. -/
theorem mass_lower_bound {n D : ℕ} (hD : 0 < D) {M η : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (h : (2 : ℝ) ^ n ≤ (1 + Real.sqrt M / η) ^ (2 * D)) :
    η ^ 2 * ((2 : ℝ) ^ ((n : ℝ) / (2 * D)) - 1) ^ 2 ≤ M := by
  have hb : 0 ≤ 1 + Real.sqrt M / η := by
    have := div_nonneg (Real.sqrt_nonneg M) hη.le; linarith
  have h2D : (0 : ℝ) < 2 * D := by positivity
  -- take the (2D)-th root
  have hroot : (2 : ℝ) ^ ((n : ℝ) / (2 * D)) ≤ 1 + Real.sqrt M / η := by
    have h1 : (2 : ℝ) ^ ((n : ℝ) / (2 * D)) = ((2 : ℝ) ^ n) ^ ((1 : ℝ) / (2 * D)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; field_simp
    have h2 : 1 + Real.sqrt M / η = ((1 + Real.sqrt M / η) ^ (2 * D)) ^ ((1 : ℝ) / (2 * D)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
      push_cast
      rw [mul_one_div_cancel h2D.ne', Real.rpow_one]
    rw [h1, h2]
    exact Real.rpow_le_rpow (by positivity) h (by positivity)
  have hge1 : 1 ≤ (2 : ℝ) ^ ((n : ℝ) / (2 * D)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hsq : (2 : ℝ) ^ ((n : ℝ) / (2 * D)) - 1 ≤ Real.sqrt M / η := by linarith
  have hmul : η * ((2 : ℝ) ^ ((n : ℝ) / (2 * D)) - 1) ≤ Real.sqrt M := by
    rw [le_div_iff₀ hη] at hsq; linarith
  have hnn : 0 ≤ η * ((2 : ℝ) ^ ((n : ℝ) / (2 * D)) - 1) := by
    have := sub_nonneg.2 hge1; positivity
  calc η ^ 2 * ((2 : ℝ) ^ ((n : ℝ) / (2 * D)) - 1) ^ 2
      = (η * ((2 : ℝ) ^ ((n : ℝ) / (2 * D)) - 1)) ^ 2 := by ring
    _ ≤ (Real.sqrt M) ^ 2 := pow_le_pow_left₀ hnn hmul 2
    _ = M := Real.sq_sqrt hM

end PVNP.Packing
