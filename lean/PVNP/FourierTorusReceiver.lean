import PVNP.BandlimitedNoisyPacking
import PVNP.FourierReceiverProjection

/-!
# Fourier receivers on the genuine `L²` torus: Bessel bound and packing (issue #15)

This module removes the last abstraction in the receiver chain of
`pvnp/proofs/bandlimited-noisy-wave-packing.md`: the receiver is **literally
the list of Fourier coefficients** `f̂(k)`, `k ∈ S`, of a field
`f ∈ L²(𝕋^d)` on the `d`-dimensional unit torus (Mathlib's `UnitAddTorus d`
with its normalized Haar probability measure).

* `receiverVec`: the observed coefficient vector in `ℂ^S`.
* `receiver_bessel`: `‖receiverVec S f‖² ≤ ∫ ‖f‖²` (Bessel's inequality, from
  Mathlib's Parseval identity `hasSum_sq_mFourierCoeff`).
* `torus_receiver_packing`: `N` fields of mean-square mass `≤ M` whose
  observed coefficient vectors are pairwise `≥ 2η` apart satisfy
  `N ≤ (1 + √M/η)^(2|S|)`.
* `torus2_bandlimited_packing`: on the 2-torus, for the receiver that
  observes all modes with `|2πk/L| ≤ K` (a side-`L` domain rescaled to the
  unit torus), `N ≤ (1 + √M/η)^(2 (2⌊LK/2π⌋+1)²)`.

Normalization: on a physical side-`L` square, Fourier coefficients in the
orthonormal basis `e^{2πik·x/L}/L` are `L · f̂(k)` and the physical mass is
`L² ∫ ‖f‖²`; both sides of the packing statement rescale by the same factor
`L`, so the statement is unchanged in physical units.  Receiver bandwidth is
an assumption about the *measurement*; by
`PVNP.FourierReceiver.cubic_quintic_generates_new_modes` it is not a property
of the nonlinear evolution.
-/

open MeasureTheory UnitAddTorus

attribute [local instance] Real.fact_zero_lt_one

/-- Same normalized measure on `ℝ/ℤ` as Mathlib's `Analysis/Fourier/AddCircleMulti`. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

namespace PVNP.FourierTorus

variable {d : Type} [Fintype d]

/-- Observed Fourier-coefficient vector of a field on the finite mode set `S`. -/
noncomputable def receiverVec (S : Finset (d → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : EuclideanSpace ℂ S :=
  WithLp.toLp 2 fun k : S => mFourierCoeff f k

theorem receiverVec_norm_sq (S : Finset (d → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖receiverVec S f‖ ^ 2 = ∑ k ∈ S, ‖mFourierCoeff f k‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [receiverVec, PiLp.toLp_apply]
  exact Finset.sum_coe_sort S (fun k => ‖mFourierCoeff f k‖ ^ 2)

/-- **Bessel bound for a finite Fourier receiver.** -/
theorem receiver_bessel (S : Finset (d → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖receiverVec S f‖ ^ 2 ≤ ∫ t, ‖f t‖ ^ 2 := by
  rw [receiverVec_norm_sq]
  exact sum_le_hasSum S (fun _ _ => sq_nonneg _) (hasSum_sq_mFourierCoeff f)

theorem receiverVec_norm_le (S : Finset (d → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) {M : ℝ}
    (hM : ∫ t, ‖f t‖ ^ 2 ≤ M) : ‖receiverVec S f‖ ≤ Real.sqrt M := by
  rw [← Real.sqrt_sq (norm_nonneg (receiverVec S f))]
  exact Real.sqrt_le_sqrt ((receiver_bessel S f).trans hM)

omit [Fintype d] in
theorem finrank_receiver (S : Finset (d → ℤ)) :
    Module.finrank ℝ (EuclideanSpace ℂ S) = 2 * S.card := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_coe]

/-- **Fourier-receiver packing on the `d`-torus.** -/
theorem torus_receiver_packing (S : Finset (d → ℤ)) {N : ℕ}
    (ψ : Fin N → Lp ℂ 2 (volume : Measure (UnitAddTorus d))) {M η : ℝ} (hη : 0 < η)
    (hmass : ∀ j, ∫ t, ‖ψ j t‖ ^ 2 ≤ M)
    (hsep : ∀ j k, j ≠ k → 2 * η ≤ dist (receiverVec S (ψ j)) (receiverVec S (ψ k))) :
    (N : ℝ) ≤ (1 + Real.sqrt M / η) ^ (2 * S.card) := by
  classical
  set v : Fin N → EuclideanSpace ℂ S := fun j => receiverVec S (ψ j)
  have hinj : Function.Injective v := by
    intro j k h
    by_contra hjk
    have := hsep j k hjk
    simp only [v] at h
    rw [h, dist_self] at this
    linarith
  have hcard : (Finset.univ.image v).card = N := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hp := PVNP.Packing.packing_card_le (Finset.univ.image v) hη (Real.sqrt_nonneg M)
    (by
      intro w hw
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
      exact receiverVec_norm_le S (ψ j) (hmass j))
    (by
      intro w hw w' hw' hne
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hw'
      exact hsep j k (fun h => hne (by rw [h])))
  rwa [hcard, finrank_receiver] at hp

/-- Coordinates of a 2-D mode as a pair. -/
def toPair (k : Fin 2 → ℤ) : ℤ × ℤ := (k 0, k 1)

theorem toPair_injective : Function.Injective toPair := by
  intro k l h
  simp only [toPair, Prod.mk.injEq] at h
  funext i; fin_cases i
  · exact h.1
  · exact h.2

/-- **Bandlimited 2-torus receiver packing.** A receiver observing the lattice
modes with `|2πk/L| ≤ K` can robustly distinguish at most
`(1 + √M/η)^(2 (2⌊LK/2π⌋+1)²)` fields of mean-square mass `≤ M`. -/
theorem torus2_bandlimited_packing (S : Finset (Fin 2 → ℤ)) {L K : ℝ} (hL : 0 < L) (hK : 0 ≤ K)
    (hS : ∀ k ∈ S, (2 * Real.pi / L) ^ 2 * (((k 0 : ℤ) : ℝ) ^ 2 + ((k 1 : ℤ) : ℝ) ^ 2) ≤ K ^ 2)
    {N : ℕ} (ψ : Fin N → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) {M η : ℝ}
    (hη : 0 < η) (hmass : ∀ j, ∫ t, ‖ψ j t‖ ^ 2 ≤ M)
    (hsep : ∀ j k, j ≠ k → 2 * η ≤ dist (receiverVec S (ψ j)) (receiverVec S (ψ k))) :
    (N : ℝ) ≤ (1 + Real.sqrt M / η) ^ (2 * (2 * ⌊L * K / (2 * Real.pi)⌋₊ + 1) ^ 2) := by
  have hcount : S.card ≤ (2 * ⌊L * K / (2 * Real.pi)⌋₊ + 1) ^ 2 := by
    have := PVNP.FourierReceiver.receiver_mode_count (S.map ⟨toPair, toPair_injective⟩) hL hK
      (by
        intro j hj
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hj
        exact hS k hk)
    rwa [Finset.card_map] at this
  have hbase : 1 ≤ 1 + Real.sqrt M / η := by
    have := div_nonneg (Real.sqrt_nonneg M) hη.le; linarith
  calc (N : ℝ) ≤ (1 + Real.sqrt M / η) ^ (2 * S.card) := torus_receiver_packing S ψ hη hmass hsep
    _ ≤ (1 + Real.sqrt M / η) ^ (2 * (2 * ⌊L * K / (2 * Real.pi)⌋₊ + 1) ^ 2) :=
      pow_le_pow_right₀ hbase (by omega)

end PVNP.FourierTorus
