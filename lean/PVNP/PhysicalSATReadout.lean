import PVNP.PhysicalReadoutCapacity
import PVNP.PhasePenaltyGap

/-!
# SAT readout under a charged, approximately blind frozen-WCT detector

This is a model-relative bridge from the previously proved torus detector
transport bound to two inputs with opposite SAT membership.

Crucial extra hypotheses:
* ONE fixed solution family and ONE detector/threshold classify the formulas;
* the two input encodings have initial detector contrast at most eps;
* terminal readings have a uniform margin m above/below the same threshold;
* both exact frozen torus trajectories have their own charged budgets and Gamma.

Then at least one trajectory must transport at least m - eps/2 of
detected mass. This implication neither constructs the input encoder
nor proves its preparation cost, robust realizability, or SAT hardness.

The bound is a disjunction, not an exponential lower bound. A nontrivial
family-level conclusion would additionally require a uniform upper bound
on the Gamma constants, a time/resource scaling theorem, and a proof
that every admissible SAT device must satisfy the initial-blindness rail.
-/

open MeasureTheory

namespace PVNP.PhysicalSATReadout

open PVNP.Torus
open PVNP.PartIPsiSat
open PVNP.PhysicalReadoutCapacity

variable {L κ β γ : ℝ}

/-- Two final readouts on opposite sides of a common threshold with margin
m are separated by at least 2m. -/
theorem margin_implies_contrast
    {yes no threshold margin : ℝ}
    (hyes : threshold + margin ≤ yes)
    (hno : no ≤ threshold - margin) :
    2 * margin ≤ |yes - no| := by
  have h : 2 * margin ≤ yes - no := by linarith
  exact h.trans (le_abs_self _)

/-- If each displayed outcome has absolute calibration error at most rho,
the true physical detector separation loses at most 2rho of margin. -/
theorem noisy_margin_implies_contrast
    (obsYes obsNo physYes physNo threshold margin rho : ℝ)
    (hyes : threshold + margin ≤ obsYes)
    (hno : obsNo ≤ threshold - margin)
    (hyerr : |obsYes - physYes| ≤ rho)
    (hnerr : |obsNo - physNo| ≤ rho) :
    2 * (margin - rho) ≤ |physYes - physNo| := by
  have hy := (abs_le.mp hyerr).2
  have hn := (abs_le.mp hnerr).1
  have h : 2 * (margin - rho) ≤ physYes - physNo := by linarith
  exact h.trans (le_abs_self _)

/-- If final detector contrast is delta but the two initial readings
differ by at most eps, at least one trajectory changes by (delta-eps)/2.
The lower bound is vacuous when eps >= delta: a preloaded answer is a
concrete obstruction to an unconditional transport lower bound. -/
theorem two_outcomes_with_initial_skew
    (a₀ b₀ aT bT delta eps : ℝ)
    (hinit : |a₀ - b₀| ≤ eps)
    (hsep : delta ≤ |aT - bT|) :
    (delta - eps) / 2 ≤ |aT - a₀| ∨
    (delta - eps) / 2 ≤ |bT - b₀| := by
  have hd : aT - bT = ((aT - a₀) + (a₀ - b₀)) + (b₀ - bT) := by ring
  have htri : |aT - bT| ≤
      |aT - a₀| + |a₀ - b₀| + |bT - b₀| := by
    rw [hd]
    have hfirst := abs_add_le ((aT - a₀) + (a₀ - b₀)) (b₀ - bT)
    have hsecond := abs_add_le (aT - a₀) (a₀ - b₀)
    rw [abs_sub_comm b₀ bT] at hfirst
    linarith
  by_contra h
  have ha : |aT - a₀| < (delta - eps) / 2 :=
    lt_of_not_ge (fun hge => h (Or.inl hge))
  have hb : |bT - b₀| < (delta - eps) / 2 :=
    lt_of_not_ge (fun hge => h (Or.inr hge))
  linarith

/-- The two-trajectory frozen-torus PDE bound allowing distinct initial
readings with certified maximum skew eps.

Compared with PhysicalReadoutCapacity.binary_readout_resource_disjunction,
the effective contrast is (delta-eps), not delta. The eps <= delta
assumption is necessary for a nonnegative change threshold. -/
theorem skewed_binary_readout_resource_disjunction
    (hL : 0 < L) (hγ : 0 < γ)
    {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv)
    (u v : ℝ → ℓ2)
    (hu : IsSolution L κ β γ u) (hv : IsSolution L κ β γ v)
    {T delta eps Bu Bv : ℝ}
    (hT : 0 < T) (heps : 0 ≤ eps) (hskew : eps ≤ delta)
    (hΓu : 0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0))
    (hΓv : 0 < Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (v 0))
    (hinit : |Jdet L χv (u 0) - Jdet L χv (v 0)| ≤ eps)
    (hsep : delta ≤ |Jdet L χv (u T) - Jdet L χv (v T)|)
    (hBu : (∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2) ≤ Bu)
    (hBv : (∫ t in (0 : ℝ)..T, ‖Dc L (v t)‖ ^ 2) ≤ Bv) :
    ((delta - eps) / 2) ^ 4 ≤
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) ^ 4 *
        T ^ 3 * Bu ∨
    ((delta - eps) / 2) ^ 4 ≤
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (v 0) ^ 4 *
        T ^ 3 * Bv := by
  have hnonneg : 0 ≤ (delta - eps) / 2 := by linarith
  rcases two_outcomes_with_initial_skew
      (Jdet L χv (u 0)) (Jdet L χv (v 0))
      (Jdet L χv (u T)) (Jdet L χv (v T))
      delta eps hinit hsep with hc | hc
  · exact Or.inl (detector_contrast_budget (L := L) (κ := κ)
      (β := β) (γ := γ) hL hγ hq hreal hu hT hnonneg hΓu hc hBu)
  · exact Or.inr (detector_contrast_budget (L := L) (κ := κ)
      (β := β) (γ := γ) hL hγ hq hreal hv hT hnonneg hΓv hc hBv)

/-- An explicitly SAT-correct *single* readout procedure on the frozen torus
must incur a two-instance transport cost if its initial detector is
approximately input-blind and the two terminal decisions have margin.

The arbitrary family `run` is ASSUMED to produce exact PDE solutions and
to have SAT-correct readings. Neither efficient input encoding nor the
SAT-correctness and robustness of such a physical machine is proved.
The SAT and UNSAT formulas are distinct inputs, and the uniform procedure
must handle both with the same detector and threshold. -/
theorem sat_pair_readout_resource_disjunction
    (hL : 0 < L) (hγ : 0 < γ)
    {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv)
    (run : CNF3 → ℝ → ℓ2)
    (hsol : ∀ F, IsSolution L κ β γ (run F))
    (Fyes Fno : CNF3) (hsat : Sat Fyes) (hunsat : ¬ Sat Fno)
    {T margin eps threshold Byes Bno : ℝ}
    (hT : 0 < T) (hmargin : 0 < margin)
    (heps : 0 ≤ eps) (hblind : eps ≤ 2 * margin)
    (hΓyes : 0 < Gam L κ β γ (aW L (co L χv))
      (bW L (co L χv)) (run Fyes 0))
    (hΓno : 0 < Gam L κ β γ (aW L (co L χv))
      (bW L (co L χv)) (run Fno 0))
    (hcorrect_yes : ∀ F, Sat F →
      threshold + margin ≤ Jdet L χv (run F T))
    (hcorrect_no : ∀ F, ¬ Sat F →
      Jdet L χv (run F T) ≤ threshold - margin)
    (hinit : |Jdet L χv (run Fyes 0) -
        Jdet L χv (run Fno 0)| ≤ eps)
    (hByes : (∫ t in (0 : ℝ)..T, ‖Dc L (run Fyes t)‖ ^ 2) ≤ Byes)
    (hBno : (∫ t in (0 : ℝ)..T, ‖Dc L (run Fno t)‖ ^ 2) ≤ Bno) :
    ((2 * margin - eps) / 2) ^ 4 ≤
      Gam L κ β γ (aW L (co L χv))
        (bW L (co L χv)) (run Fyes 0) ^ 4 * T ^ 3 * Byes ∨
    ((2 * margin - eps) / 2) ^ 4 ≤
      Gam L κ β γ (aW L (co L χv))
        (bW L (co L χv)) (run Fno 0) ^ 4 * T ^ 3 * Bno := by
  have hsep : 2 * margin ≤
      |Jdet L χv (run Fyes T) - Jdet L χv (run Fno T)| :=
    margin_implies_contrast (hcorrect_yes Fyes hsat) (hcorrect_no Fno hunsat)
  exact skewed_binary_readout_resource_disjunction
    (L := L) (κ := κ) (β := β) (γ := γ)
    hL hγ hq hreal (run Fyes) (run Fno)
    (hsol Fyes) (hsol Fno) hT heps hblind hΓyes hΓno hinit hsep hByes hBno

/-- Measured SAT correctness yields a physical contrast bound only after
subtracting explicit readout error. This theorem uses the same frozen WCT
PDE and one fixed detector for both SAT outcomes; no algorithm-independent
SAT complexity lower bound is asserted. -/
theorem noisy_sat_pair_readout_resource_disjunction
    (hL : 0 < L) (hγ : 0 < γ)
    {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv)
    (run : CNF3 → ℝ → ℓ2)
    (hsol : ∀ F, IsSolution L κ β γ (run F))
    (observe : CNF3 → ℝ)
    (Fyes Fno : CNF3) (hsat : Sat Fyes) (hunsat : ¬ Sat Fno)
    {T margin rho eps threshold Byes Bno : ℝ}
    (hT : 0 < T) (hmargin : 0 < margin)
    (hrho : 0 ≤ rho) (heps : 0 ≤ eps)
    (hblind : eps ≤ 2 * (margin - rho))
    (hΓyes : 0 < Gam L κ β γ (aW L (co L χv))
      (bW L (co L χv)) (run Fyes 0))
    (hΓno : 0 < Gam L κ β γ (aW L (co L χv))
      (bW L (co L χv)) (run Fno 0))
    (hcorrect_yes : ∀ F, Sat F → threshold + margin ≤ observe F)
    (hcorrect_no : ∀ F, ¬ Sat F → observe F ≤ threshold - margin)
    (hnoise : ∀ F,
      |observe F - Jdet L χv (run F T)| ≤ rho)
    (hinit : |Jdet L χv (run Fyes 0) -
        Jdet L χv (run Fno 0)| ≤ eps)
    (hByes : (∫ t in (0 : ℝ)..T, ‖Dc L (run Fyes t)‖ ^ 2) ≤ Byes)
    (hBno : (∫ t in (0 : ℝ)..T, ‖Dc L (run Fno t)‖ ^ 2) ≤ Bno) :
    ((2 * (margin - rho) - eps) / 2) ^ 4 ≤
      Gam L κ β γ (aW L (co L χv))
        (bW L (co L χv)) (run Fyes 0) ^ 4 * T ^ 3 * Byes ∨
    ((2 * (margin - rho) - eps) / 2) ^ 4 ≤
      Gam L κ β γ (aW L (co L χv))
        (bW L (co L χv)) (run Fno 0) ^ 4 * T ^ 3 * Bno := by
  have hsep : 2 * (margin - rho) ≤
      |Jdet L χv (run Fyes T) - Jdet L χv (run Fno T)| :=
    noisy_margin_implies_contrast
      (observe Fyes) (observe Fno)
      (Jdet L χv (run Fyes T)) (Jdet L χv (run Fno T))
      threshold margin rho
      (hcorrect_yes Fyes hsat) (hcorrect_no Fno hunsat)
      (hnoise Fyes) (hnoise Fno)
  exact skewed_binary_readout_resource_disjunction
    (L := L) (κ := κ) (β := β) (γ := γ)
    hL hγ hq hreal (run Fyes) (run Fno)
    (hsol Fyes) (hsol Fno) hT heps hblind hΓyes hΓno hinit hsep hByes hBno

/-- If each trajectory's flux coefficient is bounded by the same G and both
budgets are nonnegative, the disjunction implies a lower bound on their
*combined* squared-Laplacian expenditure.

The coefficient G remains an explicit physical assumption, and the bound
is only inverse-polynomial when margin, time and G are polynomially bounded
in the usual direction. -/
theorem combined_budget_of_disjunction
    {d G T Γu Γv Bu Bv : ℝ}
    (hT : 0 < T) (hG : 0 ≤ G)
    (hΓu : 0 ≤ Γu) (hΓv : 0 ≤ Γv)
    (hu : Γu ≤ G) (hv : Γv ≤ G)
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv)
    (h : d ^ 4 ≤ Γu ^ 4 * T ^ 3 * Bu ∨
         d ^ 4 ≤ Γv ^ 4 * T ^ 3 * Bv) :
    d ^ 4 ≤ G ^ 4 * T ^ 3 * (Bu + Bv) := by
  have hpowu : Γu ^ 4 ≤ G ^ 4 := pow_le_pow_left₀ hΓu hu 4
  have hpowv : Γv ^ 4 ≤ G ^ 4 := pow_le_pow_left₀ hΓv hv 4
  rcases h with h | h
  · calc
      d ^ 4 ≤ Γu ^ 4 * T ^ 3 * Bu := h
      _ ≤ G ^ 4 * T ^ 3 * Bu := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpowu (by positivity)) hBu
      _ ≤ G ^ 4 * T ^ 3 * (Bu + Bv) := by
        have hp : 0 ≤ G ^ 4 * T ^ 3 := by positivity
        nlinarith [mul_nonneg hp hBv]
  · calc
      d ^ 4 ≤ Γv ^ 4 * T ^ 3 * Bv := h
      _ ≤ G ^ 4 * T ^ 3 * Bv := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpowv (by positivity)) hBv
      _ ≤ G ^ 4 * T ^ 3 * (Bu + Bv) := by
        have hp : 0 ≤ G ^ 4 * T ^ 3 := by positivity
        nlinarith [mul_nonneg hp hBu]

end PVNP.PhysicalSATReadout
