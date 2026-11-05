import PVNP.TransportCalculus

/-!
# F-1: from the static fourth-order flux budget to a square-root bound

For smooth periodic solutions of the frozen Hamiltonian PDE, the
integration-by-parts calculation gives a static estimate of the form

  |J'| ≤ (4 a G + 2 b P) D + 4 |κ| a P G,

where P = ‖ψ‖₂, G = ‖∇ψ‖₂, D = ‖Δψ‖₂, and
a = ‖∇χ‖∞, b = ‖Δχ‖∞.

This file proves the *consequences* of that calculation:
  G² ≤ P D and D ≤ Dmax produce a uniform Γ sqrt(D) bound;
  the already verified time-Hölder theorem then yields a curvature-time
  inequality without an independent instantaneous flux assumption.

The analytic static PDE identity, periodic integration by parts,
differentiation of J, and conservation-derived Dmax are still separate
F-1 obligations.  This module does not claim that they are proved.
-/

open Set MeasureTheory

namespace PVNP.ContinuumFlux

/-- The constant in the instantaneous flux estimate. -/
noncomputable def budget (a b κ P Dmax : ℝ) : ℝ :=
  4 * a * Real.sqrt P * Dmax +
    2 * b * P * Real.sqrt Dmax +
    4 * |κ| * a * P * Real.sqrt P

theorem grad_le_sqrt (P G D : ℝ) (hP : 0 ≤ P)
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hgrad : G ^ 2 ≤ P * D) :
    G ≤ Real.sqrt P * Real.sqrt D := by
  have heq : (Real.sqrt P * Real.sqrt D) ^ 2 = P * D := by
    calc
      (Real.sqrt P * Real.sqrt D) ^ 2 =
          (Real.sqrt P) ^ 2 * (Real.sqrt D) ^ 2 := by ring
      _ = P * D := by rw [Real.sq_sqrt hP, Real.sq_sqrt hD]
  have hnon : 0 ≤ Real.sqrt P * Real.sqrt D :=
    mul_nonneg (Real.sqrt_nonneg P) (Real.sqrt_nonneg D)
  nlinarith

/-- Algebraic completion of the static PDE bound, with all rails explicit. -/
theorem static_to_sqrt (a b κ P G D Dmax Jdot : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hcap : D ≤ Dmax) (hgrad : G ^ 2 ≤ P * D)
    (hstatic : |Jdot| ≤ (4 * a * G + 2 * b * P) * D + 4 * |κ| * a * P * G) :
    |Jdot| ≤ budget a b κ P Dmax * Real.sqrt D := by
  have hg := grad_le_sqrt P G D hP hD hG hgrad
  have hs : Real.sqrt D ≤ Real.sqrt Dmax := Real.sqrt_le_sqrt hcap
  have hdroot : D ≤ Real.sqrt Dmax * Real.sqrt D := by
    calc
      D = Real.sqrt D * Real.sqrt D := by nlinarith [Real.sq_sqrt hD]
      _ ≤ Real.sqrt Dmax * Real.sqrt D :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg D)
  have hgd : G * D ≤ (Real.sqrt P * Dmax) * Real.sqrt D := by
    calc
      G * D ≤ (Real.sqrt P * Real.sqrt D) * D :=
        mul_le_mul_of_nonneg_right hg hD
      _ ≤ (Real.sqrt P * Real.sqrt D) * Dmax :=
        mul_le_mul_of_nonneg_left hcap
          (mul_nonneg (Real.sqrt_nonneg P) (Real.sqrt_nonneg D))
      _ = (Real.sqrt P * Dmax) * Real.sqrt D := by ring
  have hpd : P * D ≤ P * (Real.sqrt Dmax * Real.sqrt D) :=
    mul_le_mul_of_nonneg_left hdroot hP
  have hpg : P * G ≤ P * (Real.sqrt P * Real.sqrt D) :=
    mul_le_mul_of_nonneg_left hg hP
  have h1 := mul_le_mul_of_nonneg_left hgd (show 0 ≤ 4 * a by positivity)
  have h2 := mul_le_mul_of_nonneg_left hpd (show 0 ≤ 2 * b by positivity)
  have h3 := mul_le_mul_of_nonneg_left hpg
    (show 0 ≤ 4 * |κ| * a by positivity)
  calc
    |Jdot| ≤ (4 * a) * (G * D) + (2 * b) * (P * D) +
        (4 * |κ| * a) * (P * G) := by nlinarith [hstatic]
    _ ≤ (4 * a) * ((Real.sqrt P * Dmax) * Real.sqrt D) +
        (2 * b) * (P * (Real.sqrt Dmax * Real.sqrt D)) +
        (4 * |κ| * a) * (P * (Real.sqrt P * Real.sqrt D)) := by
          exact add_le_add (add_le_add h1 h2) h3
    _ = budget a b κ P Dmax * Real.sqrt D := by
          unfold budget
          ring

/-- Compose the static estimate with the established continuum transport
theorem.  The pointwise static PDE bound and the gradient interpolation
bound are explicit premises, not silently assumed facts about the PDE. -/
theorem transport_from_static (J J' G D : ℝ → ℝ)
    (a b κ P Dmax T : ℝ) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 0 ≤ P) (hmax : 0 ≤ Dmax)
    (hJ : ∀ t ∈ uIcc 0 T, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc 0 T))
    (hD : ContinuousOn D (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hG : ∀ t ∈ Icc 0 T, 0 ≤ G t)
    (hcap : ∀ t ∈ Icc 0 T, D t ≤ Dmax)
    (hinterp : ∀ t ∈ Icc 0 T, (G t) ^ 2 ≤ P * D t)
    (hstatic : ∀ t ∈ Icc 0 T,
      |J' t| ≤ (4 * a * G t + 2 * b * P) * D t + 4 * |κ| * a * P * G t) :
    |J T - J 0| ^ 4 ≤
      budget a b κ P Dmax ^ 4 * T ^ 3 *
        ∫ t in (0 : ℝ)..T, D t ^ 2 := by
  have hbudget : 0 ≤ budget a b κ P Dmax := by
    unfold budget
    positivity
  apply PVNP.TransportCalculus.transport_tradeoff
    J J' D hT hbudget hJ hJ' hD hpos
  intro t ht
  exact static_to_sqrt a b κ P (G t) (D t) Dmax (J' t)
    ha hb hP (hpos t ht) (hG t ht) (hcap t ht)
    (hinterp t ht) (hstatic t ht)

end PVNP.ContinuumFlux
