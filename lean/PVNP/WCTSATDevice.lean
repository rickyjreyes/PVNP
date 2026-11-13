import PVNP.PhysicalSATReadout
import PVNP.PhaseLockScope

/-!
# The frozen WCT SAT readout bound: device form, and what it needs

`PhysicalSATReadout` proved, for two exact solutions of the frozen torus equation
`i ∂ₜψ = (Δ+κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ` read by one real detector `J(ψ) = ∫ χ|ψ|²`, that a
SAT-correct pair with margin `m`, readout error `ρ` and initial detector skew `ε` must spend
curvature budget: `((2(m−ρ) − ε)/2)⁴ ≤ Γ⁴T³B` for one of the two trajectories.

This module does three things.

**1. The device form** (`device_pair_budget`). For a uniform device (one parameter set, one
detector, one threshold, one evolution time `T`, one readout error `ρ`) and a SAT/UNSAT pair
with initial skew at most `ε` and flux constants at most `G`, with `d = m − ρ − ε/2 ≥ 0`,

  `d⁴ ≤ G⁴ T³ (B_SAT + B_UNSAT)`,  `B_F = ∫₀ᵀ ‖Δψ_F(t)‖² dt`.

Compared with `PhysicalSATReadout`, the hypothesis `Γ > 0` is removed: a zero flux constant
freezes the reading (`Jdet_const_of_Gam_eq_zero`). The flux constant is controlled by the
prepared mass and energy (`Gam_le_of_bounds`), so `G` is a charged preparation bound, not a
free parameter (`device_pair_budget_of_preparation`).

**2. The preloaded-answer countermodel** (`preloaded_device`). On every torus with `κ ≠ 0` and
`γ > 0` there are exact solutions — the zero-mode states `ψ(t,x) = L⁻¹ c e^{−iΩt}`,
`Ω = κ² − β|c|²/L² + γ|c|⁴/L⁴` (`zeroMode_isSolution`) — with zero curvature
(`Dc_zeroMode`) and constant detector reading `|c|²/L` for the detector
`χ = L⁻¹(1 + cos(2πx₁/L))` (`Jdet_zeroMode_detector`). Encoding the SAT bit in the amplitude
(`|c| = 2` for satisfiable formulas, `1` otherwise) gives a device that is SAT-correct with
margin `3/(2L)` at every time, uses one detector and one threshold, has positive flux
constants, and spends no curvature budget at all. The encoder prepares the answer at time
zero: the initial skew equals the final contrast.

**3. Necessity of the blindness rail** (`blindness_necessary`). Consequently the conclusion of
`PhysicalSATReadout.sat_pair_readout_resource_disjunction` fails if its initial-skew hypothesis
is dropped, while every other hypothesis holds. For the preloaded device the bound is sharp in
the following sense (`preloaded_skew_eq_contrast`): its skew is exactly `2m`, so the
hypothesis `ε ≤ 2m` can be met only with `ε = 2m`, where the bound reads `0 ≤ …`.

The encoder `F ↦ c_F` is a SAT decider. So this countermodel does not show that SAT is easy;
it shows that a physical transport lower bound must charge the encoder (or impose blindness),
and that SAT correctness alone does not force the two trajectories to start with nearly equal
readings. Charging the encoder is the subject of `WCTSATScaling`.
-/

open Complex MeasureTheory Filter
open scoped Real

namespace PVNP.WCTSATDevice

open PVNP.Torus PVNP.PartIPsiSat PVNP.PhysicalSATReadout PVNP.PhysicalReadoutCapacity

variable {L κ β γ : ℝ}

/-! ### The device form of the readout bound -/

/-- The flux constant is nonnegative. -/
theorem Gam_nonneg (L κ β γ : ℝ) (χv u₀ : ℓ2) :
    0 ≤ Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) u₀ := by
  unfold Gam PVNP.ContinuumFlux.budget
  have ha := aW_nonneg L (co L χv)
  have hb := bW_nonneg L (co L χv)
  have s1 := Real.sqrt_nonneg (Real.sqrt (mass L u₀))
  have s2 := Real.sqrt_nonneg (mass L u₀)
  have hD : 0 ≤ Real.sqrt (ham L κ β γ u₀ + 3 * β ^ 2 / (16 * γ) * mass L u₀) +
      |κ| * Real.sqrt (mass L u₀) :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg κ) s2)
  have t1 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ha) s1) hD
  have t2 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb) s2)
    (Real.sqrt_nonneg (Real.sqrt (ham L κ β γ u₀ + 3 * β ^ 2 / (16 * γ) * mass L u₀) +
      |κ| * Real.sqrt (mass L u₀)))
  have t3 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (abs_nonneg κ)) ha) s2) s1
  linarith

/-- **A zero flux constant freezes the reading**: `J'(t) = 0` for all `t`. -/
theorem Jdet_const_of_Gam_eq_zero (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2}
    (hq : L1q L (co L χv)) (hreal : rev (co L χv) = co L χv) {u : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u)
    (h0 : Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) = 0) (T : ℝ) :
    Jdet L χv (u T) = Jdet L χv (u 0) := by
  have hd : ∀ t, HasDerivAt (fun s => Jdet L χv (u s)) 0 t := by
    intro t
    have h1 := flux_identity hL hreal hu t
    have h2 := flux_inequality hL hγ hq hreal (aW_nonneg L _) (bW_nonneg L _)
      (detector_bounds hq).1 (detector_bounds hq).2 hu t
    rw [h0, zero_mul] at h2
    have h3 : Jdot L κ χv (u t) = 0 := abs_nonpos_iff.mp h2
    rwa [h3] at h1
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) T 0

/-- The curvature budget `∫₀ᵀ ‖Δψ‖²` is nonnegative. -/
theorem budget_nonneg {T : ℝ} (hT : 0 ≤ T) (u : ℝ → ℓ2) :
    0 ≤ ∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2 :=
  intervalIntegral.integral_nonneg hT (fun _ _ => sq_nonneg _)

/-- **One trajectory, any flux bound.** A detected change `δ` costs `δ⁴ ≤ G⁴T³B` whenever the
flux constant is at most `G`; no positivity of the flux constant is needed. -/
theorem change_budget (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv) {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u)
    {T δ G : ℝ} (hT : 0 < T) (hδ : 0 ≤ δ)
    (hG : Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ≤ G)
    (hchange : δ ≤ |Jdet L χv (u T) - Jdet L χv (u 0)|) :
    δ ^ 4 ≤ G ^ 4 * T ^ 3 * ∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2 := by
  have hB := budget_nonneg (L := L) hT.le u
  have hΓ0 := Gam_nonneg L κ β γ χv (u 0)
  have hG0 : 0 ≤ G := hΓ0.trans hG
  rcases hΓ0.lt_or_eq with hpos | hzero
  · have h := detector_contrast_budget hL hγ hq hreal hu hT hδ hpos hchange le_rfl
    have hpow := pow_le_pow_left₀ hΓ0 hG 4
    calc δ ^ 4 ≤ Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ^ 4 * T ^ 3 *
          ∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2 := h
      _ ≤ G ^ 4 * T ^ 3 * ∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (by positivity)) hB
  · rw [Jdet_const_of_Gam_eq_zero hL hγ hq hreal hu hzero.symm T, sub_self, abs_zero] at hchange
    have hδ0 : δ = 0 := le_antisymm hchange hδ
    rw [hδ0]
    have : 0 ≤ G ^ 4 * T ^ 3 * ∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2 := by positivity
    simpa using this

/-- **The device form of the SAT readout bound.** One frozen torus, one real detector, one
threshold, one time `T`, one readout error `ρ`. If the device reads every satisfiable formula
at least `m` above the threshold and every unsatisfiable one at least `m` below (after an
observation error at most `ρ`), the two prepared states differ in reading by at most `ε`, and
both flux constants are at most `G`, then with `d = m − ρ − ε/2 ≥ 0`

  `d⁴ ≤ G⁴ T³ (∫₀ᵀ ‖Δψ_SAT‖² + ∫₀ᵀ ‖Δψ_UNSAT‖²)`. -/
theorem device_pair_budget (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv) (run : CNF3 → ℝ → ℓ2)
    (hsol : ∀ F, IsSolution L κ β γ (run F)) (observe : CNF3 → ℝ)
    (Fyes Fno : CNF3) (hsat : Sat Fyes) (hunsat : ¬ Sat Fno)
    {T margin rho eps threshold G : ℝ} (hT : 0 < T) (hd : 0 ≤ margin - rho - eps / 2)
    (hGyes : Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (run Fyes 0) ≤ G)
    (hGno : Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (run Fno 0) ≤ G)
    (hcorrect_yes : ∀ F, Sat F → threshold + margin ≤ observe F)
    (hcorrect_no : ∀ F, ¬ Sat F → observe F ≤ threshold - margin)
    (hnoise : ∀ F, |observe F - Jdet L χv (run F T)| ≤ rho)
    (hinit : |Jdet L χv (run Fyes 0) - Jdet L χv (run Fno 0)| ≤ eps) :
    (margin - rho - eps / 2) ^ 4 ≤ G ^ 4 * T ^ 3 *
      ((∫ t in (0 : ℝ)..T, ‖Dc L (run Fyes t)‖ ^ 2) +
        ∫ t in (0 : ℝ)..T, ‖Dc L (run Fno t)‖ ^ 2) := by
  have hsep := noisy_margin_implies_contrast (observe Fyes) (observe Fno)
    (Jdet L χv (run Fyes T)) (Jdet L χv (run Fno T)) threshold margin rho
    (hcorrect_yes Fyes hsat) (hcorrect_no Fno hunsat) (hnoise Fyes) (hnoise Fno)
  have hByes := budget_nonneg (L := L) hT.le (run Fyes)
  have hBno := budget_nonneg (L := L) hT.le (run Fno)
  have hG0 : 0 ≤ G := (Gam_nonneg L κ β γ χv _).trans hGyes
  have hpos : 0 ≤ G ^ 4 * T ^ 3 := by positivity
  have e : (2 * (margin - rho) - eps) / 2 = margin - rho - eps / 2 := by ring
  rcases two_outcomes_with_initial_skew _ _ _ _ _ _ hinit hsep with hc | hc
  · rw [e] at hc
    have h := change_budget hL hγ hq hreal (hsol Fyes) hT hd hGyes hc
    nlinarith [mul_nonneg hpos hBno]
  · rw [e] at hc
    have h := change_budget hL hγ hq hreal (hsol Fno) hT hd hGno hc
    nlinarith [mul_nonneg hpos hByes]

/-- The flux-budget function is monotone in the mass and curvature-energy arguments. -/
theorem budget_mono {a b κ P P' D D' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 0 ≤ P)
    (hPP : P ≤ P') (hD : 0 ≤ D) (hDD : D ≤ D') :
    PVNP.ContinuumFlux.budget a b κ P D ≤ PVNP.ContinuumFlux.budget a b κ P' D' := by
  unfold PVNP.ContinuumFlux.budget
  have h1 : Real.sqrt P ≤ Real.sqrt P' := Real.sqrt_le_sqrt hPP
  have h2 : Real.sqrt D ≤ Real.sqrt D' := Real.sqrt_le_sqrt hDD
  have hP' : 0 ≤ P' := hP.trans hPP
  have s1 := Real.sqrt_nonneg P
  have s2 := Real.sqrt_nonneg D
  have hka : 0 ≤ |κ| * a := mul_nonneg (abs_nonneg κ) ha
  have t1 : a * Real.sqrt P * D ≤ a * Real.sqrt P' * D' :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 ha) hDD hD (mul_nonneg ha (Real.sqrt_nonneg _))
  have t2 : b * P * Real.sqrt D ≤ b * P' * Real.sqrt D' :=
    mul_le_mul (mul_le_mul_of_nonneg_left hPP hb) h2 s2 (mul_nonneg hb hP')
  have t3 : |κ| * a * P * Real.sqrt P ≤ |κ| * a * P' * Real.sqrt P' :=
    mul_le_mul (mul_le_mul_of_nonneg_left hPP hka) h1 s1 (mul_nonneg hka hP')
  linarith

/-- **The flux constant is a charged preparation quantity.** If the prepared state has mass at
most `M` and Hamiltonian at most `H`, its flux constant is at most the explicit
`budget a b κ √M (√(H + 3β²M/16γ) + |κ|√M)`. -/
theorem Gam_le_of_bounds (hγ : 0 < γ) (χv u₀ : ℓ2) {M H : ℝ} (hM : mass L u₀ ≤ M)
    (hH : ham L κ β γ u₀ ≤ H) :
    Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) u₀ ≤
      PVNP.ContinuumFlux.budget (aW L (co L χv)) (bW L (co L χv)) κ (Real.sqrt M)
        (Real.sqrt (H + 3 * β ^ 2 / (16 * γ) * M) + |κ| * Real.sqrt M) := by
  unfold Gam
  have hc : 0 ≤ 3 * β ^ 2 / (16 * γ) := by positivity
  apply budget_mono (aW_nonneg L _) (bW_nonneg L _) (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt hM)
    (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg κ) (Real.sqrt_nonneg _)))
  have h1 : Real.sqrt (ham L κ β γ u₀ + 3 * β ^ 2 / (16 * γ) * mass L u₀) ≤
      Real.sqrt (H + 3 * β ^ 2 / (16 * γ) * M) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : |κ| * Real.sqrt (mass L u₀) ≤ |κ| * Real.sqrt M :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hM) (abs_nonneg κ)
  linarith

/-- **The device bound with charged preparation.** If both prepared states have mass at most
`M` and Hamiltonian at most `H`, the bound of `device_pair_budget` holds with the explicit
`G = budget a b κ √M (√(H + 3β²M/16γ) + |κ|√M)` determined by `M`, `H` and the detector. -/
theorem device_pair_budget_of_preparation (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2}
    (hq : L1q L (co L χv)) (hreal : rev (co L χv) = co L χv) (run : CNF3 → ℝ → ℓ2)
    (hsol : ∀ F, IsSolution L κ β γ (run F)) (observe : CNF3 → ℝ)
    (Fyes Fno : CNF3) (hsat : Sat Fyes) (hunsat : ¬ Sat Fno)
    {T margin rho eps threshold M H : ℝ} (hT : 0 < T) (hd : 0 ≤ margin - rho - eps / 2)
    (hM : ∀ F, mass L (run F 0) ≤ M) (hH : ∀ F, ham L κ β γ (run F 0) ≤ H)
    (hcorrect_yes : ∀ F, Sat F → threshold + margin ≤ observe F)
    (hcorrect_no : ∀ F, ¬ Sat F → observe F ≤ threshold - margin)
    (hnoise : ∀ F, |observe F - Jdet L χv (run F T)| ≤ rho)
    (hinit : |Jdet L χv (run Fyes 0) - Jdet L χv (run Fno 0)| ≤ eps) :
    (margin - rho - eps / 2) ^ 4 ≤
      PVNP.ContinuumFlux.budget (aW L (co L χv)) (bW L (co L χv)) κ (Real.sqrt M)
          (Real.sqrt (H + 3 * β ^ 2 / (16 * γ) * M) + |κ| * Real.sqrt M) ^ 4 * T ^ 3 *
        ((∫ t in (0 : ℝ)..T, ‖Dc L (run Fyes t)‖ ^ 2) +
          ∫ t in (0 : ℝ)..T, ‖Dc L (run Fno t)‖ ^ 2) :=
  device_pair_budget hL hγ hq hreal run hsol observe Fyes Fno hsat hunsat hT hd
    (Gam_le_of_bounds hγ χv _ (hM Fyes) (hH Fyes)) (Gam_le_of_bounds hγ χv _ (hM Fno) (hH Fno))
    hcorrect_yes hcorrect_no hnoise hinit

/-! ### One-mode states -/

theorem qf_zero (L : ℝ) : qf L 0 = 0 := by simp [qf, xi1, xi2]

theorem wt_zero (L : ℝ) : wt L 0 = 1 := by simp [wt, qf_zero]

/-- The state whose only Fourier coefficient is `c`, at the mode `j`. -/
noncomputable def mode (L : ℝ) (j : Z2) (c : ℂ) : ℓ2 := lp.single 2 j ((wt L j : ℂ) * c)

theorem co_mode (L : ℝ) (j : Z2) (c : ℂ) : co L (mode L j c) = Pi.single j c := by
  funext k
  rw [co, mode, lp.single_apply]
  by_cases h : k = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, mul_div_cancel_left₀ _ (wt_ne_zero L k)]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_div]

theorem L1q_single (L : ℝ) (j : Z2) (c : ℂ) : L1q L (Pi.single j c) := by
  unfold L1q
  apply summable_of_ne_finset_zero (s := {j})
  intro k hk
  rw [Finset.mem_singleton] at hk
  rw [Pi.single_eq_of_ne hk, norm_zero, mul_zero]

theorem field_single (L : ℝ) (j : Z2) (c : ℂ) (x : ℝ × ℝ) :
    Torus.field L (Pi.single j c) x = (L : ℂ)⁻¹ * (c * emode L j x) := by
  unfold Torus.field
  congr 1
  rw [tsum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro k hk
    rw [Pi.single_eq_of_ne hk, zero_mul]

theorem field_single_zero (L : ℝ) (c : ℂ) (x : ℝ × ℝ) :
    Torus.field L (Pi.single 0 c) x = (L : ℂ)⁻¹ * c := by
  rw [field_single, emode_zero, mul_one]

/-- The Fourier coefficients of a constant function. -/
theorem fc_const (hL : 0 < L) (K : ℂ) (k : Z2) :
    fc L (fun _ => K) k = (Pi.single (0 : Z2) ((L : ℂ) * K) : Z2 → ℂ) k := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : (fun _ : ℝ × ℝ => K) = Torus.field L (Pi.single 0 ((L : ℂ) * K)) := by
    funext x
    rw [field_single_zero, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul]
  rw [e, fc_field hL (L1q_single L 0 _).l1]

theorem continuous_mode (L : ℝ) (j : Z2) {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous fun t => mode L j (g t) := by
  have hiso : Isometry (fun z : ℂ => (lp.single 2 j z : ℓ2)) := by
    refine Isometry.of_dist_eq fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, ← lp.single_sub, lp.norm_single (by norm_num)]
  exact hiso.continuous.comp (continuous_const.mul hg)

theorem Dc_mode_zero (L : ℝ) (c : ℂ) : Dc L (mode L 0 c) = 0 := by
  ext k
  rw [Dc_apply, co_mode]
  by_cases hk : k = 0
  · subst hk
    simp [qf_zero]
  · simp [Pi.single_eq_of_ne hk]

theorem mass_mode (L : ℝ) (j : Z2) (c : ℂ) : mass L (mode L j c) = ‖c‖ ^ 2 := by
  unfold mass
  rw [co_mode, tsum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro k hk
    rw [Pi.single_eq_of_ne hk, norm_zero]
    norm_num

/-! ### Exact zero-mode solutions -/

/-- The frequency of the zero-mode solution of amplitude norm `r`. -/
noncomputable def Om (L κ β γ r : ℝ) : ℝ :=
  κ ^ 2 - β * (r ^ 2 / L ^ 2) + γ * (r ^ 2 / L ^ 2) ^ 2

/-- The zero-mode trajectory `ψ(t, x) = L⁻¹ c e^{−iΩt}`. -/
noncomputable def zeroMode (L κ β γ : ℝ) (c : ℂ) (t : ℝ) : ℓ2 :=
  mode L 0 (c * cexp (((-(Om L κ β γ ‖c‖ * t) : ℝ) : ℂ) * I))

theorem norm_amp (c : ℂ) (s : ℝ) : ‖c * cexp ((s : ℂ) * I)‖ = ‖c‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Zero-mode states are exact solutions** of the frozen equation, for all parameters. -/
theorem zeroMode_isSolution (hL : 0 < L) (c : ℂ) :
    IsSolution L κ β γ (zeroMode L κ β γ c) := by
  set Ω := Om L κ β γ ‖c‖ with hΩ
  set g : ℝ → ℂ := fun t => c * cexp (((-(Ω * t) : ℝ) : ℂ) * I) with hg
  have hgn : ∀ t, ‖g t‖ = ‖c‖ := fun t => norm_amp c _
  have hgc : Continuous g := by
    refine continuous_const.mul (Complex.continuous_exp.comp ?_)
    exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id).neg).mul
      continuous_const
  have hgd : ∀ t, HasDerivAt g (-I * ((Ω : ℂ) * g t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Ω * s)) (-(Ω * 1)) t :=
      ((hasDerivAt_id t).const_mul Ω).neg
    have h2 := (((h1.ofReal_comp).mul_const I).cexp).const_mul c
    convert h2 using 1
    simp only [g]
    push_cast
    ring
  have hz : ∀ s, zeroMode L κ β γ c s = mode L 0 (g s) := fun s => rfl
  refine ⟨continuous_mode L 0 hgc, fun t k => ?_⟩
  · simp_rw [hz, co_mode, field_single_zero]
    rw [fc_const hL]
    by_cases hk : k = 0
    · subst hk
      simp only [Pi.single_eq_same]
      convert hgd t using 1
      rw [fnl_eq]
      have hn : ‖(L : ℂ)⁻¹ * g t‖ = ‖c‖ / L := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, hgn]
        field_simp
      rw [hn, om, qf_zero, hΩ, Om]
      have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
      ring
    · simp only [Pi.single_eq_of_ne hk, mul_zero, zero_add]
      simpa using hasDerivAt_const t (0 : ℂ)

theorem Dc_zeroMode (L κ β γ : ℝ) (c : ℂ) (t : ℝ) : Dc L (zeroMode L κ β γ c t) = 0 :=
  Dc_mode_zero L _

/-- The curvature budget of a zero-mode trajectory is zero. -/
theorem budget_zeroMode (L κ β γ : ℝ) (c : ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖Dc L (zeroMode L κ β γ c t)‖ ^ 2) = 0 := by
  simp [Dc_zeroMode]

theorem mass_zeroMode (L κ β γ : ℝ) (c : ℂ) (t : ℝ) :
    mass L (zeroMode L κ β γ c t) = ‖c‖ ^ 2 := by
  rw [zeroMode, mass_mode, norm_amp]

/-! ### Detector readings of zero-mode states -/

theorem integrable_field {a : Z2 → ℂ} (ha : L1 a) :
    Integrable (Torus.field L a) (box L) :=
  Integrable.mono' (integrable_const (|L|⁻¹ * ∑' k, ‖a k‖))
    (continuous_field ha).aestronglyMeasurable (Eventually.of_forall fun x => norm_field_le ha x)

/-- A zero-mode state is read as `‖c‖²/L · Re ĉ_χ(0)`. -/
theorem Jdet_mode_zero (hL : 0 < L) (χv : ℓ2) (c : ℂ) :
    Jdet L χv (mode L 0 c) = ‖c‖ ^ 2 / L * (co L χv 0).re := by
  unfold Jdet
  rw [co_mode]
  simp_rw [field_single_zero]
  have hn : ‖(L : ℂ)⁻¹ * c‖ ^ 2 = ‖c‖ ^ 2 / L ^ 2 := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    field_simp
  have hre := integral_re (integrable_field (L := L) (L1_co' hL χv))
  simp only [RCLike.re_to_complex] at hre
  rw [hn, integral_mul_const, hre, integral_field hL (L1_co' hL χv)]
  have hre : ((L : ℂ) * co L χv 0).re = L * (co L χv 0).re := by
    simp [Complex.mul_re]
  rw [hre]
  field_simp

/-! ### A real detector with positive flux constant -/

/-- The first lattice direction. -/
def e1v : Z2 := (1, 0)

theorem e1v_ne_zero : e1v ≠ 0 := by decide

theorem neg_e1v_ne_zero : -e1v ≠ 0 := by decide

theorem e1v_ne_neg : e1v ≠ -e1v := by decide

/-- The detector coefficients: `1` at `0` and `1/2` at `±e₁`, i.e. `χ(x) = L⁻¹(1 + cos(2πx₁/L))`. -/
noncomputable def dco : Z2 → ℂ := Pi.single 0 1 + Pi.single e1v (1 / 2) + Pi.single (-e1v) (1 / 2)

/-- The detector state. -/
noncomputable def detector (L : ℝ) : ℓ2 := mode L 0 1 + mode L e1v (1 / 2) + mode L (-e1v) (1 / 2)

theorem co_detector (L : ℝ) : co L (detector L) = dco := by
  simp only [detector, co_add, co_mode, dco]

theorem dco_zero : dco 0 = 1 := by
  simp [dco, e1v_ne_zero.symm, neg_e1v_ne_zero.symm]

theorem dco_e1v : dco e1v = 1 / 2 := by
  simp [dco, e1v_ne_zero, e1v_ne_neg]

theorem dco_neg_e1v : dco (-e1v) = 1 / 2 := by
  simp [dco, e1v_ne_zero, e1v_ne_neg.symm]

theorem dco_eq_zero {k : Z2} (h0 : k ≠ 0) (h1 : k ≠ e1v) (h2 : k ≠ -e1v) : dco k = 0 := by
  simp [dco, h0, h1, h2]

theorem conj_half : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]

theorem L1q_dco (L : ℝ) : L1q L dco := by
  unfold L1q
  apply summable_of_ne_finset_zero (s := {0, e1v, -e1v})
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rw [dco_eq_zero hk.1 hk.2.1 hk.2.2, norm_zero, mul_zero]

theorem rev_dco : rev dco = dco := by
  funext k
  unfold rev
  by_cases h0 : k = 0
  · subst h0
    rw [neg_zero, dco_zero, map_one]
  by_cases h1 : k = e1v
  · subst h1
    rw [dco_neg_e1v, dco_e1v, conj_half]
  by_cases h2 : k = -e1v
  · subst h2
    rw [neg_neg, dco_e1v, dco_neg_e1v, conj_half]
  have h0' : -k ≠ 0 := neg_ne_zero.mpr h0
  have h1' : -k ≠ e1v := fun h => h2 (by rw [← h, neg_neg])
  have h2' : -k ≠ -e1v := fun h => h1 (neg_injective h)
  rw [dco_eq_zero h0' h1' h2', dco_eq_zero h0 h1 h2, map_zero]

theorem aW_dco_pos (hL : 0 < L) : 0 < aW L dco := by
  unfold aW
  refine mul_pos (inv_pos.mpr (abs_pos.mpr hL.ne')) ?_
  have hsum : Summable fun k => (|xi1 L k| + |xi2 L k|) * ‖dco k‖ := by
    apply summable_of_ne_finset_zero (s := {0, e1v, -e1v})
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [dco_eq_zero hk.1 hk.2.1 hk.2.2, norm_zero, mul_zero]
  refine hsum.tsum_pos (fun k => by positivity) e1v ?_
  rw [dco_e1v]
  have hx : xi1 L e1v = 2 * π / L := by simp [xi1, e1v]
  rw [hx]
  have : 0 < 2 * π / L := by positivity
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  have := abs_nonneg (xi2 L e1v)
  rw [abs_of_pos ‹0 < 2 * π / L›]
  positivity

/-- The detector reads a zero-mode state as `‖c‖²/L`. -/
theorem Jdet_detector_mode (hL : 0 < L) (c : ℂ) :
    Jdet L (detector L) (mode L 0 c) = ‖c‖ ^ 2 / L := by
  rw [Jdet_mode_zero hL, co_detector, dco_zero]
  simp

theorem Jdet_zeroMode_detector (hL : 0 < L) (c : ℂ) (t : ℝ) :
    Jdet L (detector L) (zeroMode L κ β γ c t) = ‖c‖ ^ 2 / L := by
  rw [zeroMode, Jdet_detector_mode hL, norm_amp]

/-- The flux constant of a zero-mode state is positive when `κ ≠ 0` and `c ≠ 0`. -/
theorem Gam_zeroMode_pos (hL : 0 < L) (hκ : κ ≠ 0) {c : ℂ} (hc : c ≠ 0) (t : ℝ) :
    0 < Gam L κ β γ (aW L (co L (detector L))) (bW L (co L (detector L)))
      (zeroMode L κ β γ c t) := by
  rw [co_detector]
  unfold Gam PVNP.ContinuumFlux.budget
  rw [mass_zeroMode]
  have ha := aW_dco_pos hL
  have hb := bW_nonneg L dco
  have hP : 0 < Real.sqrt (‖c‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hD : 0 < Real.sqrt (ham L κ β γ (zeroMode L κ β γ c t) +
      3 * β ^ 2 / (16 * γ) * ‖c‖ ^ 2) + |κ| * Real.sqrt (‖c‖ ^ 2) := by
    have : 0 < |κ| * Real.sqrt (‖c‖ ^ 2) := mul_pos (abs_pos.mpr hκ) hP
    have := Real.sqrt_nonneg (ham L κ β γ (zeroMode L κ β γ c t) +
      3 * β ^ 2 / (16 * γ) * ‖c‖ ^ 2)
    linarith
  have h1 : 0 < 4 * aW L dco * Real.sqrt (Real.sqrt (‖c‖ ^ 2)) *
      (Real.sqrt (ham L κ β γ (zeroMode L κ β γ c t) + 3 * β ^ 2 / (16 * γ) * ‖c‖ ^ 2) +
        |κ| * Real.sqrt (‖c‖ ^ 2)) := by
    have := Real.sqrt_pos.mpr hP
    positivity
  have h2 : 0 ≤ 2 * bW L dco * Real.sqrt (‖c‖ ^ 2) *
      Real.sqrt (Real.sqrt (ham L κ β γ (zeroMode L κ β γ c t) +
        3 * β ^ 2 / (16 * γ) * ‖c‖ ^ 2) + |κ| * Real.sqrt (‖c‖ ^ 2)) := by positivity
  have h3 : 0 ≤ 4 * |κ| * aW L dco * Real.sqrt (‖c‖ ^ 2) * Real.sqrt (Real.sqrt (‖c‖ ^ 2)) := by
    positivity
  linarith

/-! ### The preloaded SAT device -/

open Classical in
/-- The preloaded encoder: amplitude `2` for satisfiable formulas and `1` otherwise. It is a
SAT decider; nothing here makes it efficient. -/
noncomputable def preAmp (F : CNF3) : ℂ := if Sat F then 2 else 1

theorem preAmp_ne_zero (F : CNF3) : preAmp F ≠ 0 := by
  unfold preAmp; split_ifs <;> norm_num

/-- The preloaded device: one zero-mode trajectory per formula. -/
noncomputable def preRun (L κ β γ : ℝ) (F : CNF3) : ℝ → ℓ2 := zeroMode L κ β γ (preAmp F)

theorem Jdet_preRun_sat (hL : 0 < L) {F : CNF3} (hF : Sat F) (t : ℝ) :
    Jdet L (detector L) (preRun L κ β γ F t) = 4 / L := by
  rw [preRun, Jdet_zeroMode_detector hL, preAmp, if_pos hF]
  norm_num

theorem Jdet_preRun_unsat (hL : 0 < L) {F : CNF3} (hF : ¬ Sat F) (t : ℝ) :
    Jdet L (detector L) (preRun L κ β γ F t) = 1 / L := by
  rw [preRun, Jdet_zeroMode_detector hL, preAmp, if_neg hF]
  norm_num

/-- **The preloaded-answer device.** For every torus `L > 0` and parameters with `κ ≠ 0`, every
formula's trajectory is an exact solution; one real detector with `L1q` coefficients and one
threshold `5/(2L)` read every satisfiable formula as `≥ threshold + 3/(2L)` and every
unsatisfiable one as `≤ threshold − 3/(2L)`, **at every time**; all flux constants are
positive; the curvature budget is zero on every interval. -/
theorem preloaded_device (hL : 0 < L) (hκ : κ ≠ 0) :
    (∀ F, IsSolution L κ β γ (preRun L κ β γ F)) ∧
    L1q L (co L (detector L)) ∧ rev (co L (detector L)) = co L (detector L) ∧
    (∀ F t, 0 < Gam L κ β γ (aW L (co L (detector L))) (bW L (co L (detector L)))
      (preRun L κ β γ F t)) ∧
    (∀ F T, (∫ t in (0 : ℝ)..T, ‖Dc L (preRun L κ β γ F t)‖ ^ 2) = 0) ∧
    (∀ F t, Sat F → 5 / (2 * L) + 3 / (2 * L) ≤ Jdet L (detector L) (preRun L κ β γ F t)) ∧
    (∀ F t, ¬ Sat F → Jdet L (detector L) (preRun L κ β γ F t) ≤ 5 / (2 * L) - 3 / (2 * L)) := by
  refine ⟨fun F => zeroMode_isSolution hL _, ?_, ?_, fun F t => ?_, fun F T => ?_,
    fun F t hF => ?_, fun F t hF => ?_⟩
  · rw [co_detector]; exact L1q_dco L
  · rw [co_detector]; exact rev_dco
  · exact Gam_zeroMode_pos hL hκ (preAmp_ne_zero F) t
  · exact budget_zeroMode L κ β γ _ T
  · have e : 5 / (2 * L) + 3 / (2 * L) = 4 / L := by field_simp; ring
    rw [Jdet_preRun_sat hL hF, e]
  · have e : 5 / (2 * L) - 3 / (2 * L) = 1 / L := by field_simp; ring
    rw [Jdet_preRun_unsat hL hF, e]

/-- The preloaded device's initial skew equals its final contrast `2m = 3/L`. -/
theorem preloaded_skew_eq_contrast (hL : 0 < L) {Fy Fn : CNF3} (hy : Sat Fy) (hn : ¬ Sat Fn)
    (t : ℝ) :
    |Jdet L (detector L) (preRun L κ β γ Fy 0) - Jdet L (detector L) (preRun L κ β γ Fn 0)| =
      |Jdet L (detector L) (preRun L κ β γ Fy t) - Jdet L (detector L) (preRun L κ β γ Fn t)| ∧
    |Jdet L (detector L) (preRun L κ β γ Fy 0) - Jdet L (detector L) (preRun L κ β γ Fn 0)| =
      2 * (3 / (2 * L)) := by
  rw [Jdet_preRun_sat hL hy, Jdet_preRun_unsat hL hn, Jdet_preRun_sat hL hy,
    Jdet_preRun_unsat hL hn]
  refine ⟨rfl, ?_⟩
  rw [show 4 / L - 1 / L = 3 / L by ring, abs_of_pos (by positivity)]
  field_simp

/-- A satisfiable formula: one clause `x₀ ∨ x₀ ∨ x₀`. -/
def oneClause : CNF3 := [fun _ => ⟨0, true⟩]

theorem oneClause_sat : Sat oneClause :=
  ⟨fun _ => true, by
    intro c hc
    simp only [oneClause, List.mem_singleton] at hc
    subst hc
    simp [clauseVal, litVal]⟩

/-- **The initial-blindness rail is necessary.** Drop the initial-skew hypothesis
`|J(ψ_SAT(0)) − J(ψ_UNSAT(0))| ≤ ε` from `sat_pair_readout_resource_disjunction` (take
`ε = 0`, the strongest form of its conclusion) and keep every other hypothesis: exact solutions,
one real `L1q` detector, positive flux constants, SAT correctness with margin, and budgets.
The resulting statement is false. -/
theorem blindness_necessary :
    ¬ ∀ (L κ β γ : ℝ) (χv : ℓ2) (run : CNF3 → ℝ → ℓ2) (Fyes Fno : CNF3)
        (T margin threshold Byes Bno : ℝ),
        0 < L → 0 < γ → L1q L (co L χv) → rev (co L χv) = co L χv →
        (∀ F, IsSolution L κ β γ (run F)) → Sat Fyes → ¬ Sat Fno → 0 < T → 0 < margin →
        0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (run Fyes 0) →
        0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (run Fno 0) →
        (∀ F, Sat F → threshold + margin ≤ Jdet L χv (run F T)) →
        (∀ F, ¬ Sat F → Jdet L χv (run F T) ≤ threshold - margin) →
        (∫ t in (0 : ℝ)..T, ‖Dc L (run Fyes t)‖ ^ 2) ≤ Byes →
        (∫ t in (0 : ℝ)..T, ‖Dc L (run Fno t)‖ ^ 2) ≤ Bno →
        (margin ^ 4 ≤ Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (run Fyes 0) ^ 4 *
            T ^ 3 * Byes ∨
          margin ^ 4 ≤ Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (run Fno 0) ^ 4 *
            T ^ 3 * Bno) := by
  intro h
  obtain ⟨hsol, hq, hreal, hΓ, hB, hyes, hno⟩ :=
    preloaded_device (L := 1) (κ := 1) (β := 0) (γ := 1) one_pos one_ne_zero
  have hc := h 1 1 0 1 (detector 1) (preRun 1 1 0 1) oneClause PhaseLockScope.contradictory
    1 (3 / (2 * 1)) (5 / (2 * 1)) 0 0 one_pos one_pos hq hreal hsol oneClause_sat
    PhaseLockScope.contradictory_unsat one_pos (by norm_num) (hΓ _ 0) (hΓ _ 0)
    (fun F hF => hyes F 1 hF) (fun F hF => hno F 1 hF) (hB _ 1).le (hB _ 1).le
  norm_num at hc

end PVNP.WCTSATDevice
