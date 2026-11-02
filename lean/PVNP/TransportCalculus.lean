import PVNP.HamiltonianTransport

/-!
# Genuine calculus for the WCT transport tradeoff and Hamiltonian control (issue #10)

`PVNP.HamiltonianTransport` composes *assumed* inequalities
(`δ ≤ Γτ`, `τ⁴ ≤ T³D`, `B² − c·mass² ≤ H`).  This module proves the analytic
steps behind them as theorems about real functions and Lebesgue integrals:

* `sq_integral_le`: `(∫₀ᵀ f)² ≤ T ∫₀ᵀ f²` for continuous `f` (Cauchy–Schwarz,
  via `∫(f − c)² ≥ 0`).
* `power_mean_four`: `(∫₀ᵀ f)⁴ ≤ T³ ∫₀ᵀ f⁴` for continuous `f ≥ 0` (the
  time-Hölder step with exponents `4` and `4/3`).
* `transport_tradeoff`: if a detector reading `J` is `C¹` on `[0,T]` and obeys
  the **instantaneous flux inequality** `|J'(t)| ≤ Γ √D(t)` with `D ≥ 0`
  continuous, then `|J(T) − J(0)|⁴ ≤ Γ⁴ T³ ∫₀ᵀ D(t)² dt`.
* `curvature_time_lower_bound`: hence a readout change `δ > 0` forces
  `∫₀ᵀ D(t)² dt ≥ δ⁴ / (Γ⁴ T³)` — the boxed bound of
  `pvnp/proofs/wct-pde-transport-bound.md` with `D(t) = ‖Δψ(t)‖₂`.
* `hamiltonian_controls_bandpass`: on any measure space, with integrable
  densities, `∫‖B‖² ≤ H + (3β²/(16γ)) ∫‖ψ‖²` where
  `H = ∫(‖B‖² − (β/2)‖ψ‖⁴ + (γ/3)‖ψ‖⁶)` (with `B` standing for `(Δ+κ)ψ`).

The flux inequality itself is derived in the supplement from the PDE by
integration by parts and remains an explicit premise here.
-/

open MeasureTheory intervalIntegral Set

namespace PVNP.TransportCalculus

theorem sq_integral_le (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T)) :
    (∫ t in (0 : ℝ)..T, f t) ^ 2 ≤ T * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  rcases eq_or_lt_of_le hT with rfl | hT'
  · simp
  have hfi : IntervalIntegrable f volume 0 T := (hf.mono (by simp [uIcc_of_le hT])).intervalIntegrable_of_Icc hT
  have hf2 : IntervalIntegrable (fun t => f t ^ 2) volume 0 T :=
    ((hf.pow 2).mono (by simp [uIcc_of_le hT])).intervalIntegrable_of_Icc hT
  set I := ∫ t in (0 : ℝ)..T, f t
  set I2 := ∫ t in (0 : ℝ)..T, f t ^ 2
  set c := I / T
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..T, (f t - c) ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
  have hexp : ∫ t in (0 : ℝ)..T, (f t - c) ^ 2 = I2 - 2 * c * I + c ^ 2 * T := by
    have h1 : (fun t => (f t - c) ^ 2) = fun t => (f t ^ 2 - 2 * c * f t) + c ^ 2 := by
      funext t; ring
    rw [h1, intervalIntegral.integral_add (hf2.sub (hfi.const_mul _)) _root_.intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hfi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp [smul_eq_mul]; ring
  rw [hexp] at hnn
  have hc : c * T = I := by simp only [c]; field_simp
  have : I ^ 2 ≤ T * I2 := by
    have h2 : 0 ≤ T * (I2 - 2 * c * I + c ^ 2 * T) := mul_nonneg hT hnn
    have h3 : T * (I2 - 2 * c * I + c ^ 2 * T) = T * I2 - I ^ 2 := by
      rw [← hc]; ring
    linarith
  exact this

theorem power_mean_four (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T)) :
    (∫ t in (0 : ℝ)..T, f t) ^ 4 ≤ T ^ 3 * ∫ t in (0 : ℝ)..T, f t ^ 4 := by
  have h1 := sq_integral_le f hT hf
  have h2 := sq_integral_le (fun t => f t ^ 2) hT (hf.pow 2)
  simp only [← pow_mul] at h2
  have hI2 : 0 ≤ ∫ t in (0 : ℝ)..T, f t ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
  calc (∫ t in (0 : ℝ)..T, f t) ^ 4 = ((∫ t in (0 : ℝ)..T, f t) ^ 2) ^ 2 := by ring
    _ ≤ (T * ∫ t in (0 : ℝ)..T, f t ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = T ^ 2 * (∫ t in (0 : ℝ)..T, f t ^ 2) ^ 2 := by ring
    _ ≤ T ^ 2 * (T * ∫ t in (0 : ℝ)..T, f t ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); simpa using h2
    _ = T ^ 3 * ∫ t in (0 : ℝ)..T, f t ^ 4 := by ring

/-- **Finite-time transport tradeoff** from the instantaneous flux inequality. -/
theorem transport_tradeoff (J J' D : ℝ → ℝ) {T Γ : ℝ} (hT : 0 ≤ T) (hΓ : 0 ≤ Γ)
    (hJ : ∀ t ∈ uIcc 0 T, HasDerivAt J (J' t) t) (hJ' : ContinuousOn J' (Icc 0 T))
    (hD : ContinuousOn D (Icc 0 T)) (hD0 : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hflux : ∀ t ∈ Icc 0 T, |J' t| ≤ Γ * Real.sqrt (D t)) :
    |J T - J 0| ^ 4 ≤ Γ ^ 4 * T ^ 3 * ∫ t in (0 : ℝ)..T, D t ^ 2 := by
  have hJ'i : IntervalIntegrable J' volume 0 T :=
    (hJ'.mono (by simp [uIcc_of_le hT])).intervalIntegrable_of_Icc hT
  have hsq : ContinuousOn (fun t => Real.sqrt (D t)) (Icc 0 T) := hD.sqrt
  have hsqi : IntervalIntegrable (fun t => Real.sqrt (D t)) volume 0 T :=
    (hsq.mono (by simp [uIcc_of_le hT])).intervalIntegrable_of_Icc hT
  have hftc : J T - J 0 = ∫ t in (0 : ℝ)..T, J' t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hJ hJ'i).symm
  have habs : |J T - J 0| ≤ Γ * ∫ t in (0 : ℝ)..T, Real.sqrt (D t) := by
    rw [hftc, ← intervalIntegral.integral_const_mul]
    calc |∫ t in (0 : ℝ)..T, J' t| ≤ ∫ t in (0 : ℝ)..T, |J' t| :=
          intervalIntegral.abs_integral_le_integral_abs hT
      _ ≤ ∫ t in (0 : ℝ)..T, Γ * Real.sqrt (D t) :=
          intervalIntegral.integral_mono_on hT hJ'i.abs (hsqi.const_mul Γ)
            (fun t ht => hflux t ht)
  have hpm := power_mean_four (fun t => Real.sqrt (D t)) hT hsq
  have hfour : (∫ t in (0 : ℝ)..T, Real.sqrt (D t) ^ 4) = ∫ t in (0 : ℝ)..T, D t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    simp only
    rw [show Real.sqrt (D t) ^ 4 = (Real.sqrt (D t) ^ 2) ^ 2 by ring, Real.sq_sqrt (hD0 t ht)]
  rw [hfour] at hpm
  have hsq0 : 0 ≤ ∫ t in (0 : ℝ)..T, Real.sqrt (D t) :=
    intervalIntegral.integral_nonneg hT (fun t _ => Real.sqrt_nonneg _)
  calc |J T - J 0| ^ 4 ≤ (Γ * ∫ t in (0 : ℝ)..T, Real.sqrt (D t)) ^ 4 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 4
    _ = Γ ^ 4 * (∫ t in (0 : ℝ)..T, Real.sqrt (D t)) ^ 4 := by ring
    _ ≤ Γ ^ 4 * (T ^ 3 * ∫ t in (0 : ℝ)..T, D t ^ 2) :=
        mul_le_mul_of_nonneg_left hpm (by positivity)
    _ = Γ ^ 4 * T ^ 3 * ∫ t in (0 : ℝ)..T, D t ^ 2 := by ring

/-- **Curvature-time lower bound** (boxed bound of the transport supplement). -/
theorem curvature_time_lower_bound (J J' D : ℝ → ℝ) {T Γ δ : ℝ} (hT : 0 < T) (hΓ : 0 < Γ)
    (hJ : ∀ t ∈ uIcc 0 T, HasDerivAt J (J' t) t) (hJ' : ContinuousOn J' (Icc 0 T))
    (hD : ContinuousOn D (Icc 0 T)) (hD0 : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hflux : ∀ t ∈ Icc 0 T, |J' t| ≤ Γ * Real.sqrt (D t)) (hδ : 0 ≤ δ)
    (hchange : δ ≤ |J T - J 0|) :
    δ ^ 4 / (Γ ^ 4 * T ^ 3) ≤ ∫ t in (0 : ℝ)..T, D t ^ 2 := by
  have h := transport_tradeoff J J' D hT.le hΓ.le hJ hJ' hD hD0 hflux
  have hδ4 : δ ^ 4 ≤ |J T - J 0| ^ 4 := pow_le_pow_left₀ hδ hchange 4
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Hamiltonian control of the bandpass norm** (integrated, any measure). -/
theorem hamiltonian_controls_bandpass {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (B ψ : X → ℂ) (β γ : ℝ) (hγ : 0 < γ)
    (hB : Integrable (fun x => ‖B x‖ ^ 2) μ) (h2 : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
    (h4 : Integrable (fun x => ‖ψ x‖ ^ 4) μ) (h6 : Integrable (fun x => ‖ψ x‖ ^ 6) μ) :
    ∫ x, ‖B x‖ ^ 2 ∂μ ≤
      (∫ x, (‖B x‖ ^ 2 - β / 2 * ‖ψ x‖ ^ 4 + γ / 3 * ‖ψ x‖ ^ 6) ∂μ) +
        3 * β ^ 2 / (16 * γ) * ∫ x, ‖ψ x‖ ^ 2 ∂μ := by
  have hH : Integrable (fun x => ‖B x‖ ^ 2 - β / 2 * ‖ψ x‖ ^ 4 + γ / 3 * ‖ψ x‖ ^ 6) μ :=
    (hB.sub (h4.const_mul _)).add (h6.const_mul _)
  rw [← MeasureTheory.integral_const_mul, ← integral_add hH (h2.const_mul _)]
  apply integral_mono hB (hH.add (h2.const_mul _))
  intro x
  have hp := PVNP.HamiltonianTransport.cubic_quintic_potential_lower β γ (‖ψ x‖ ^ 2) hγ
    (sq_nonneg _)
  simp only [Pi.add_apply]
  have e4 : ‖ψ x‖ ^ 4 = (‖ψ x‖ ^ 2) ^ 2 := by ring
  have e6 : ‖ψ x‖ ^ 6 = (‖ψ x‖ ^ 2) ^ 3 := by ring
  rw [e4, e6]
  linarith

end PVNP.TransportCalculus
