import PVNP.DetectorDynamic
import PVNP.AnalyticSimulation
import PVNP.UniformGalerkinRadius

/-!
# The dynamic detector theorem for the continuum PDE

`DetectorDynamic.galerkin_detector_dynamic_data` bounds the detector error between a coarse and
a fine Galerkin trajectory, uniformly in the fine mode set. Here the fine set exhausts `ℤ²`, and
the bound passes to the actual frozen PDE solution.

* `cutoffBox`, `exists_finer_set`: every finite mode set has finer sets whose complement has
  arbitrarily large mode size.
* `pde_detector_dynamic`, the **dynamic detector theorem for the PDE**. Hypotheses:
  - `w` is the interaction-picture PDE solution with analytic data;
  - `W` is the coarse Galerkin trajectory with `W(0) = P_S w(0)`;
  - every mode outside `S` has size `≥ N`;
  - `γ > 0`, so that Galerkin trajectories are global and uniformly bounded in `H²`.

  With `σ_T = σ₀4^{−⌊T/τ⌋}`, the physical readouts satisfy
  `|J(u(T)) − J(u_S(T))| ≤ 4 C_A A_{σ_T}(χ) M e^{−2σ_T N} ((A_{σ_T}(w(0))² + G(2M)²T)
  e^{(2K_F(2M)+1)T})^{1/2}`.

**Proof.** For every `ε > 0`:
1. Choose a fine set `S' ⊇ S` whose cutoff meets the hypothesis of
   `Analytic.analytic_galerkin_pde_error`.
2. Take the global fine trajectory of `TorusGalerkin.exists_uniform_galerkin`.
3. Bound both trajectories analytically on `[0, T]` with `Analytic.galerkin_analytic`.
4. Apply the Galerkin–Galerkin theorem between the coarse and fine trajectories.
5. Control the fine-to-PDE gap with the `L²` Lipschitz bound of the detector, giving `O(ε)`.

Then let `ε → 0`. The doubled exponent `e^{−2σ_T N}` survives the limit.
-/

namespace PVNP.DetectorPDE

open Complex PVNP.Torus PVNP.TorusGalerkin PVNP.GalerkinTaylor PVNP.Analytic PVNP.DualResidual
  PVNP.DetectorDynamic PVNP.ContinuumPrecision

variable {L : ℝ}

/-- The square box of modes `|k₁|, |k₂| ≤ n`. -/
def cutoffBox (n : ℕ) : Finset Z2 := Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

theorem abs_ge_of_not_mem_Icc {n : ℕ} {a : ℤ} (h : a ∉ Finset.Icc (-(n : ℤ)) n) :
    (n : ℝ) + 1 ≤ |(a : ℝ)| := by
  rw [Finset.mem_Icc] at h
  have h3 : (n : ℤ) + 1 ≤ |a| := by
    rcases le_or_gt 0 a with ha | ha
    · rw [abs_of_nonneg ha]; omega
    · rw [abs_of_neg ha]; omega
  calc (n : ℝ) + 1 = (((n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
    _ ≤ ((|a| : ℤ) : ℝ) := by exact_mod_cast h3
    _ = |(a : ℝ)| := Int.cast_abs

theorem size_ge_of_not_mem_box {n : ℕ} {k : Z2} (hk : k ∉ cutoffBox n) :
    (n : ℝ) + 1 ≤ size k := by
  unfold cutoffBox at hk
  rw [Finset.mem_product, not_and_or] at hk
  unfold size
  rcases hk with h | h
  · have h1 := abs_ge_of_not_mem_Icc h
    have h2 := abs_nonneg ((k.2 : ℤ) : ℝ)
    linarith
  · have h1 := abs_ge_of_not_mem_Icc h
    have h2 := abs_nonneg ((k.1 : ℤ) : ℝ)
    linarith

/-- Every finite mode set has finer sets with arbitrarily large cutoff. -/
theorem exists_finer_set (S : Finset Z2) (N : ℝ) :
    ∃ S' : Finset Z2, S ⊆ S' ∧ ∀ k ∉ S', N ≤ size k := by
  refine ⟨S ∪ cutoffBox ⌈N⌉₊, Finset.subset_union_left, fun k hk => ?_⟩
  have hk' : k ∉ cutoffBox ⌈N⌉₊ := fun h => hk (Finset.mem_union_right _ h)
  have h1 := size_ge_of_not_mem_box hk'
  have h2 : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
  linarith

/-- **The dynamic detector theorem for the continuum PDE.** -/
theorem pde_detector_dynamic (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {σ₀ M R B T N : ℝ} (hσ₀ : 0 < σ₀) (hM : 0 < M)
    (hT : 0 ≤ T) (hχ : ASum σ₀ χv) {w : ℝ → ℓ2}
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t) (hB : ‖w 0‖ ≤ B)
    (hRw : ∀ t, ‖w t‖ ≤ R) (hRB : uniformRadius L κ β γ B ≤ R) (hRM : 2 * R ≤ M)
    (ha : ASum σ₀ (w 0)) (h0 : asq σ₀ (w 0) ≤ M ^ 2)
    {S : Finset Z2} (hS : ∀ k ∉ S, N ≤ size k) {W : ℝ → ℓ2} (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t) (hW0 : W 0 = trunc S (w 0))
    (hRW : ∀ t, ‖W t‖ ≤ R) :
    |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W T))| ≤
      CA L * anorm (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) χv * (2 * (2 * M)) *
        Real.exp (-(2 * (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) * N)) *
        Real.sqrt ((asq (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) (w 0) + G L β γ (2 * M) ^ 2 * T) *
          Real.exp ((2 * KF L β γ (2 * M) + 1) * T)) := by
  have hτ := tstep_pos L β γ M
  have hσT : 0 < σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊) := by positivity
  have hσTle : σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊) ≤ σ₀ :=
    div_le_self hσ₀.le (one_le_pow₀ (by norm_num))
  have hR : 0 ≤ R := (norm_nonneg _).trans (hRw 0)
  -- analytic bounds along Galerkin trajectories started from truncations of `w 0`
  have hbound : ∀ (S₁ : Finset Z2) (V : ℝ → ℓ2), (∀ t, Supported S₁ (V t)) →
      (∀ t, HasDerivAt V (galerkin S₁ L κ β γ t (V t)) t) → V 0 = trunc S₁ (w 0) →
      (∀ t, ‖V t‖ ≤ R) → ∀ t ∈ Set.Icc 0 T,
        anorm (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) (U L κ t (V t)) ≤ 2 * M := by
    intro S₁ V hsV hV hV0 hRV t ht
    have h0V : asq σ₀ (V 0) ≤ M ^ 2 := by rw [hV0]; exact (asq_trunc_le S₁ ha).trans h0
    have hg := galerkin_analytic hL hsV hV hσ₀ hM hRV hRM h0V ht.1
    have hmono := radius_mono hσ₀ hτ ht.2
    have h1 := (asq_mono hmono (asum_of_supported (hsV t) _)).2
    rw [anorm, asq_U]
    calc Real.sqrt (asq (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) (V t)) ≤ Real.sqrt (4 * M ^ 2) :=
          Real.sqrt_le_sqrt (h1.trans hg)
      _ = 2 * M := by
          rw [show (4 : ℝ) * M ^ 2 = (2 * M) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have hu_d := hasDerivAt_phys hL hs hW
  have hu_s : ∀ t, Supported S (U L κ t (W t)) := fun t => supported_U (hs t) κ t
  have hMu := hbound S W hs hW hW0 hRW
  have hχT : ASum (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) χv := (asq_mono hσTle hχ).1
  have haT : ASum (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) (w 0) := (asq_mono hσTle ha).1
  have hC := Cdet_nonneg hL χv
  -- for every `ε > 0`, compare through a fine Galerkin trajectory
  have key : ∀ ε, 0 < ε →
      |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W T))| ≤
        CA L * anorm (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) χv * (2 * (2 * M)) *
          Real.exp (-(2 * (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) * N)) *
          Real.sqrt ((asq (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)) (w 0) +
            G L β γ (2 * M) ^ 2 * T) * Real.exp ((2 * KF L β γ (2 * M) + 1) * T)) +
        Cdet L χv * (R + R) * ε := by
    intro ε hε
    obtain ⟨S', hSS', hS'⟩ := exists_finer_set S (max 0
      ((LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε)) /
        (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊))))
    obtain ⟨W', hW'0, hs', hW', hRW'⟩ := exists_uniform_galerkin (κ := κ) (β := β) hL hγ S' hB
    have hRW'' : ∀ t, ‖W' t‖ ≤ R := fun t => (hRW' t).trans hRB
    have hN : LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε) ≤
        σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊) * max 0
          ((LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε)) /
            (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊))) := by
      have h := le_max_right (0 : ℝ) ((LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε)) /
        (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)))
      rw [div_le_iff₀ hσT] at h
      linarith
    have herr := analytic_galerkin_pde_error hL hs' hW' hw hW'0 hσ₀ hM hRW'' hRw hRM ha h0 hT hε
      (le_max_left _ _) hS' hN
    have hMw := hbound S' W' hs' hW' hW'0 hRW''
    have hdyn := galerkin_detector_dynamic_data (u := fun t => U L κ t (W t))
      (w := fun t => U L κ t (W' t)) hL hreal hσT.le hT hSS' hS hu_s
      (fun t => supported_U (hs' t) κ t) hu_d (hasDerivAt_phys hL hs' hW') hMu hMw hχT haT
      (by show U L κ 0 (W 0) = trunc S (w 0); rw [U_zero, hW0])
      (by show U L κ 0 (W' 0) = trunc S' (w 0); rw [U_zero, hW'0])
    simp only at hdyn
    have hlip := weak_detector_lipschitz hL hreal (U L κ T (w T)) (U L κ T (W' T))
    have hLc : ∀ x, ‖Lc L (U L κ T x)‖ ≤ ‖x‖ := fun x => by
      rw [Lc_U, norm_U]; exact norm_Lc_le L x
    have hdiff : ‖Lc L (U L κ T (w T) - U L κ T (W' T))‖ ≤ ε := by
      rw [← map_sub, Lc_U, norm_U, map_sub, norm_sub_rev, ← map_sub]; exact herr
    have hl2 : |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W' T))| ≤
        Cdet L χv * (R + R) * ε :=
      hlip.trans (mul_le_mul (mul_le_mul_of_nonneg_left
        (add_le_add ((hLc _).trans (hRw T)) ((hLc _).trans (hRW'' T))) hC) hdiff
        (norm_nonneg _) (mul_nonneg hC (by linarith)))
    calc |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W T))|
        ≤ |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W' T))| +
          |Jdet L χv (U L κ T (W' T)) - Jdet L χv (U L κ T (W T))| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc1 : 0 < Cdet L χv * (R + R) + 1 := by
    have := mul_nonneg hC (by linarith : (0 : ℝ) ≤ R + R); linarith
  have h := key (ε / (Cdet L χv * (R + R) + 1)) (div_pos hε hc1)
  have h2 : Cdet L χv * (R + R) * (ε / (Cdet L χv * (R + R) + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hc1]
    nlinarith [mul_nonneg hC (by linarith : (0 : ℝ) ≤ R + R)]
  linarith

end PVNP.DetectorPDE
