import PVNP.AnalyticPropagation
import PVNP.SpatialModeCount
import PVNP.TaylorIntegrator

/-!
# End-to-end simulation of the frozen flow from analytic data

This module combines three earlier results: the propagated analyticity of `AnalyticPropagation`,
the tail comparison of `SpatialModeCount`, and the certified Taylor integrator of
`TaylorIntegrator`.

* `pde_apriori`: actual PDE trajectories (`w' = Gf(t, w)`) satisfy the conserved `H²` bound
  `‖w(t)‖ ≤ Rap(mass, ham)`.
* `galerkin_analytic`: every actual Galerkin trajectory with `A_{σ₀}(W(0)) ≤ M` and
  `2R ≤ M` (`R` its `H²` bound) satisfies `A_{σ(t)}(W(t))² ≤ 4M²` with
  `σ(t) = σ₀ 4^{−⌊t/τ(M)⌋}`. No constant depends on `S`.
* `analytic_galerkin_pde_error`: suppose `S` contains every mode of size below `N` and
  `σ_T N ≥ LF(R)·T + log(M_tot(1+T)/ε)`, with `σ_T = σ₀ 4^{−⌊T/τ⌋}` and
  `M_tot = M + |β|C_A²(2M)³ + |γ|C_A⁴(2M)⁵`. Then the weak (`L²`) distance between the Galerkin
  trajectory and the PDE solution at time `T` is at most `ε`.
* `analytic_end_to_end`: the restarted Taylor integrator on that Galerkin system, with the
  Phase XXVIII parameter conditions for accuracy `ε₁` and per-step errors `≤ ρ`, ends within
  `ε₁ + ε₂` of the true PDE state `U(T)w(T)` in the weak norm.

The cutoff size grows like `4^{T/τ}`. The simulation is polynomial only for horizons
`T = O(τ(M) log n)`, where `τ(M)^{-1} = 2(8|β|C_A²M² + 32|γ|C_A⁴M⁴ + 1)` is polynomial in `M`.
-/

namespace PVNP.Analytic

open Finset Set PVNP.Torus PVNP.TorusGalerkin PVNP.GalerkinTaylor Complex

variable {L : ℝ}

/-- **A priori bound for actual PDE trajectories.** -/
theorem pde_apriori (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) {w : ℝ → ℓ2}
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t) (t : ℝ) :
    ‖w t‖ ≤ Rap κ β γ (mass L (w 0)) (ham L κ β γ (w 0)) := by
  obtain ⟨hm, he⟩ := conserved (κ := κ) (β := β) (γ := γ) hL hw t
  have h := norm_le_apriori (κ := κ) (β := β) hL hγ (U L κ t (w t))
  rw [norm_U, mass_U, hm, he] at h
  exact h

theorem supported_U {S : Finset Z2} {v : ℓ2} (hv : Supported S v) (κ t : ℝ) :
    Supported S (U L κ t v) := fun k hk => by rw [U_apply, hv k hk, mul_zero]

/-- **Analytic regularity of every actual Galerkin trajectory**, uniformly in `S`. -/
theorem galerkin_analytic (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {W : ℝ → ℓ2}
    (hs : ∀ t, Supported S (W t)) (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    {R M σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hM : 0 < M) (hR : ∀ t, ‖W t‖ ≤ R) (hRM : 2 * R ≤ M)
    (h0 : asq σ₀ (W 0) ≤ M ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    asq (σ₀ / 4 ^ (⌊t / tstep L β γ M⌋₊)) (W t) ≤ 4 * M ^ 2 := by
  have hu := hasDerivAt_phys hL hs hW
  have hsU : ∀ t, Supported S (U L κ t (W t)) := fun t => supported_U (hs t) κ t
  have hRU : ∀ t, ‖U L κ t (W t)‖ ≤ R := fun t => by rw [norm_U]; exact hR t
  have h0U : asq σ₀ (U L κ 0 (W 0)) ≤ M ^ 2 := by rw [asq_U]; exact h0
  have h := radius_at (u := fun s => U L κ s (W s)) hL hsU hu hσ₀ hM hRU hRM h0U ht
  simp only at h
  rwa [asq_U] at h

/-- The radius at the horizon is the smallest radius used up to it. -/
theorem radius_mono {σ₀ τ t T : ℝ} (hσ₀ : 0 < σ₀) (hτ : 0 < τ) (htT : t ≤ T) :
    σ₀ / 4 ^ (⌊T / τ⌋₊) ≤ σ₀ / 4 ^ (⌊t / τ⌋₊) := by
  have hfl : ⌊t / τ⌋₊ ≤ ⌊T / τ⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right htT hτ.le)
  have hp : (4:ℝ) ^ (⌊t / τ⌋₊) ≤ 4 ^ (⌊T / τ⌋₊) := pow_le_pow_right₀ (by norm_num) hfl
  exact div_le_div_of_nonneg_left hσ₀.le (by positivity) hp

/-- The total tail constant. -/
noncomputable def Mtot (L β γ M : ℝ) : ℝ :=
  M + |β| * CA L ^ 2 * (2 * M) ^ 3 + |γ| * CA L ^ 4 * (2 * M) ^ 5

/-- **Galerkin versus PDE from analytic data.** -/
theorem analytic_galerkin_pde_error (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2}
    {W w : ℝ → ℓ2} (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t) (hW0 : W 0 = trunc S (w 0))
    {R M σ₀ T ε N : ℝ} (hσ₀ : 0 < σ₀) (hM : 0 < M) (hRW : ∀ t, ‖W t‖ ≤ R)
    (hRw : ∀ t, ‖w t‖ ≤ R) (hRM : 2 * R ≤ M) (ha : ASum σ₀ (w 0))
    (h0 : asq σ₀ (w 0) ≤ M ^ 2) (hT : 0 ≤ T) (hε : 0 < ε) (hN0 : 0 ≤ N)
    (hcut : ∀ k ∉ S, N ≤ size k)
    (hN : LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε) ≤
      σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊) * N) :
    ‖Lc L (W T - w T)‖ ≤ ε := by
  set τ := tstep L β γ M
  have hτ := tstep_pos L β γ M
  set σT := σ₀ / 4 ^ (⌊T / τ⌋₊)
  have hσT : 0 < σT := by positivity
  have hC := CA_nonneg hL
  have hMt : 0 < Mtot L β γ M := by unfold Mtot; positivity
  have hW0a : asq σ₀ (W 0) ≤ M ^ 2 := by
    rw [hW0]; exact (asq_trunc_le S ha).trans h0
  -- the omitted output tail along the Galerkin trajectory
  have hres : ∀ t ∈ Ico 0 T,
      ‖Lc L (galerkin S L κ β γ t (W t) - Gf L κ β γ t (W t))‖ ≤
        Mtot L β γ M * Real.exp (-σT * N) := by
    intro t ht
    have hga := galerkin_analytic hL hs hW hσ₀ hM hRW hRM hW0a ht.1
    have hmono := radius_mono hσ₀ hτ ht.2.le
    have hasW := asum_of_supported (hs t) σT
    have hW2 : asq σT (W t) ≤ 4 * M ^ 2 := by
      have hasW' := asum_of_supported (hs t) (σ₀ / 4 ^ (⌊t / τ⌋₊))
      exact (asq_mono hmono hasW').2.trans hga
    have haU := asum_U (L := L) κ t hasW
    obtain ⟨hFs, hFle⟩ := anorm_Fnl_le hL hσT.le β γ haU
    set X := Gf L κ β γ t (W t)
    have hX : X = (-I) • U L κ (-t) (Fnl L β γ (U L κ t (W t))) := rfl
    have hXs : ASum σT X := by rw [hX]; exact asum_smul _ (asum_U κ _ hFs)
    have hXn : anorm σT X = anorm σT (Fnl L β γ (U L κ t (W t))) := by
      rw [hX, anorm_smul, norm_neg, Complex.norm_I, one_mul, anorm, anorm, asq_U]
    have haW : anorm σT (U L κ t (W t)) ≤ 2 * M := by
      rw [anorm, asq_U]
      calc Real.sqrt (asq σT (W t)) ≤ Real.sqrt (4 * M ^ 2) := Real.sqrt_le_sqrt hW2
        _ = 2 * M := by
          rw [show (4:ℝ) * M ^ 2 = (2 * M) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hXb : anorm σT X ≤ |β| * CA L ^ 2 * (2 * M) ^ 3 + |γ| * CA L ^ 4 * (2 * M) ^ 5 := by
      rw [hXn]
      refine hFle.trans ?_
      have h0' := anorm_nonneg σT (U L κ t (W t))
      gcongr
    have hgal : galerkin S L κ β γ t (W t) = trunc S X := by
      unfold galerkin; rw [supported_trunc_eq (hs t)]
    have htl := tail_le hσT.le hXs S hcut
    have hsq : ‖trunc S X - X‖ ≤ Real.exp (-σT * N) * anorm σT X := by
      have e : Real.exp (-(2 * σT * N)) * asq σT X = (Real.exp (-σT * N) * anorm σT X) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul, anorm_sq]; push_cast; ring_nf
      rw [e] at htl
      have hc0 : 0 ≤ Real.exp (-σT * N) * anorm σT X :=
        mul_nonneg (Real.exp_pos _).le (anorm_nonneg _ _)
      have h' := Real.sqrt_le_sqrt htl
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hc0] at h'
    rw [hgal]
    calc ‖Lc L (trunc S X - X)‖ ≤ ‖trunc S X - X‖ := norm_Lc_le _ _
      _ ≤ Real.exp (-σT * N) * anorm σT X := hsq
      _ ≤ Real.exp (-σT * N) * Mtot L β γ M := by
          gcongr; unfold Mtot; linarith
      _ = Mtot L β γ M * Real.exp (-σT * N) := by ring
  -- the initial tail
  have h0t : ‖Lc L (W 0 - w 0)‖ ≤ Mtot L β γ M * Real.exp (-σT * N) := by
    rw [hW0]
    have htl := tail_le hσ₀.le ha S hcut
    have hsq : ‖trunc S (w 0) - w 0‖ ≤ Real.exp (-σ₀ * N) * M := by
      have hM0 : anorm σ₀ (w 0) ≤ M := by
        rw [anorm]
        calc Real.sqrt (asq σ₀ (w 0)) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt h0
          _ = M := Real.sqrt_sq hM.le
      have e : Real.exp (-(2 * σ₀ * N)) * asq σ₀ (w 0) =
          (Real.exp (-σ₀ * N) * anorm σ₀ (w 0)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul, anorm_sq]; push_cast; ring_nf
      rw [e] at htl
      have hc0 : 0 ≤ Real.exp (-σ₀ * N) * anorm σ₀ (w 0) :=
        mul_nonneg (Real.exp_pos _).le (anorm_nonneg _ _)
      have h' := Real.sqrt_le_sqrt htl
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hc0] at h'
      exact h'.trans (mul_le_mul_of_nonneg_left hM0 (Real.exp_pos _).le)
    have hσle : σT ≤ σ₀ := by
      have : (1:ℝ) ≤ 4 ^ (⌊T / τ⌋₊) := one_le_pow₀ (by norm_num)
      exact div_le_self hσ₀.le this
    have hE : Real.exp (-σ₀ * N) ≤ Real.exp (-σT * N) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc ‖Lc L (trunc S (w 0) - w 0)‖ ≤ ‖trunc S (w 0) - w 0‖ := norm_Lc_le _ _
      _ ≤ Real.exp (-σ₀ * N) * M := hsq
      _ ≤ Real.exp (-σT * N) * Mtot L β γ M := by
          have hMle : M ≤ Mtot L β γ M := by
            unfold Mtot
            have h1 : 0 ≤ |β| * CA L ^ 2 * (2 * M) ^ 3 := by positivity
            have h2 : 0 ≤ |γ| * CA L ^ 4 * (2 * M) ^ 5 := by positivity
            linarith
          exact mul_le_mul hE hMle hM.le (Real.exp_pos _).le
      _ = Mtot L β γ M * Real.exp (-σT * N) := by ring
  exact galerkin_error_of_tail hL hT hMt hε hW hw hRW hRw hres h0t hN

/-- **End-to-end simulation from analytic data.** The restarted Taylor integrator on the Galerkin
system, started from the Galerkin data, ends within `ε₁ + ε₂` of the true PDE state in the weak
norm. -/
theorem analytic_end_to_end (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2}
    {W w : ℝ → ℓ2} (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t) (hW0 : W 0 = trunc S (w 0))
    {R M σ₀ T ε₁ ε₂ N Ω ρ : ℝ} (hσ₀ : 0 < σ₀) (hM : 0 < M) (hR0 : 0 ≤ R)
    (hRW : ∀ t, ‖W t‖ ≤ R) (hRw : ∀ t, ‖w t‖ ≤ R) (hRM : 2 * R ≤ M) (ha : ASum σ₀ (w 0))
    (h0 : asq σ₀ (w 0) ≤ M ^ 2) (hT : 0 ≤ T) (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂ : 0 < ε₂)
    (hN0 : 0 ≤ N) (hcut : ∀ k ∉ S, N ≤ size k)
    (hN : LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε₂) ≤
      σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊) * N)
    (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω) (hρ : 0 ≤ ρ) (Nst q : ℕ) (hNst : 1 ≤ Nst)
    (hstepsize : T / Nst *
      (2 * TaylorMajorant.rate (R + 1) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) + 2) ≤ 1)
    (horder : 4 * (R + 1) * Nst * Real.exp ((Ω + LF L β γ (2 * (R + 1))) * T) ≤
      2 ^ (q+1) * ε₁)
    (hprec : 2 * Nst * Real.exp ((Ω + LF L β γ (2 * (R + 1))) * T) * ρ ≤ ε₁)
    {ũ : ℕ → ℓ2} (hũ0 : ũ 0 = W 0)
    (hstep : ∀ j, ‖ũ (j+1) - taylorStep L κ β γ S q (T / Nst) (ũ j)‖ ≤ ρ) :
    ‖Lc L (ũ Nst - U L κ T (w T))‖ ≤ ε₁ + ε₂ := by
  have hu := hasDerivAt_phys hL hs hW
  have hRU : ∀ t, ‖U L κ t (W t)‖ ≤ R := fun t => by rw [norm_U]; exact hRW t
  have hint := certified_integrator (u := fun s => U L κ s (W s)) hL hu hR0 hΩ hS hRU hT hε₁
    hε₁1 hρ Nst q hNst hstepsize horder hprec (by simp only [U_zero]; exact hũ0) hstep
  have hsp := analytic_galerkin_pde_error hL hs hW hw hW0 hσ₀ hM hRW hRw hRM ha h0 hT hε₂ hN0
    hcut hN
  have e : ũ Nst - U L κ T (w T) = (ũ Nst - U L κ T (W T)) + U L κ T (W T - w T) := by
    rw [map_sub]; abel
  rw [e, map_add]
  calc ‖Lc L (ũ Nst - U L κ T (W T)) + Lc L (U L κ T (W T - w T))‖
      ≤ ‖Lc L (ũ Nst - U L κ T (W T))‖ + ‖Lc L (U L κ T (W T - w T))‖ := norm_add_le _ _
    _ ≤ ‖ũ Nst - U L κ T (W T)‖ + ‖Lc L (W T - w T)‖ := by
        gcongr
        · exact norm_Lc_le _ _
        · rw [Lc_U, norm_U]
    _ ≤ ε₁ + ε₂ := add_le_add hint hsp

end PVNP.Analytic
