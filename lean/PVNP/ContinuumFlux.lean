import Mathlib

/-!
# Periodic integration by parts for the spatial part of F-1

For smooth periodic fields on the square torus, `flux_static` moves one copy of
`A = Δ + κ` from the field to the detector-weighted conjugate field.  The real
detector cancels the bulk term.  `flux_split` separates the remaining commutator
into a Laplacian term and a first-order term.

These identities are evaluated at a fixed time. The time derivative of the detector
mass and existence of a global solution require separate theorems.
-/

open MeasureTheory intervalIntegral Set Complex
open scoped ContDiff

namespace PVNP.ContinuumFlux

/-! ### Partial derivatives and periodicity -/

/-- Partial derivative in the first coordinate. -/
noncomputable def d1 (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ f p (1, 0)

/-- Partial derivative in the second coordinate. -/
noncomputable def d2 (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ f p (0, 1)

/-- The Laplacian. -/
noncomputable def lap (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := d1 (d1 f) p + d2 (d2 f) p

/-- `L`-periodicity in both coordinates. -/
def Per (L : ℝ) (f : ℝ × ℝ → ℂ) : Prop :=
  ∀ p : ℝ × ℝ, f (p + (L, 0)) = f p ∧ f (p + (0, L)) = f p

/-- Smooth functions. -/
abbrev Sm (f : ℝ × ℝ → ℂ) : Prop := ContDiff ℝ ∞ f

theorem Sm.fderiv {f : ℝ × ℝ → ℂ} (hf : Sm f) : ContDiff ℝ ∞ (fun p => fderiv ℝ f p) :=
  (contDiff_infty_iff_fderiv.1 hf).2

theorem Sm.d1 {f : ℝ × ℝ → ℂ} (hf : Sm f) : Sm (d1 f) :=
  hf.fderiv.clm_apply contDiff_const

theorem Sm.d2 {f : ℝ × ℝ → ℂ} (hf : Sm f) : Sm (d2 f) :=
  hf.fderiv.clm_apply contDiff_const

theorem Sm.lap {f : ℝ × ℝ → ℂ} (hf : Sm f) : Sm (lap f) :=
  hf.d1.d1.add hf.d2.d2

theorem Sm.diff {f : ℝ × ℝ → ℂ} (hf : Sm f) : Differentiable ℝ f :=
  ContDiff.differentiable hf (by simp)

theorem hasDerivAt_d1 {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun s => f (s, y)) (d1 f (x, y)) x := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  exact (hf (x, y)).hasFDerivAt.comp_hasDerivAt x h1

theorem hasDerivAt_d2 {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun s => f (x, s)) (d2 f (x, y)) y := by
  have h1 : HasDerivAt (fun s : ℝ => ((x, s) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  exact (hf (x, y)).hasFDerivAt.comp_hasDerivAt y h1

theorem fderiv_per {f : ℝ × ℝ → ℂ} (v : ℝ × ℝ) (hv : ∀ p, f (p + v) = f p) (p : ℝ × ℝ) :
    fderiv ℝ f (p + v) = fderiv ℝ f p := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext q
  exact hv q

theorem Per.d1 {L : ℝ} {f : ℝ × ℝ → ℂ} (hf : Per L f) : Per L (d1 f) := by
  intro p
  simp only [PVNP.ContinuumFlux.d1]
  rw [fderiv_per (L, 0) (fun q => (hf q).1) p, fderiv_per (0, L) (fun q => (hf q).2) p]
  exact ⟨rfl, rfl⟩

theorem Per.d2 {L : ℝ} {f : ℝ × ℝ → ℂ} (hf : Per L f) : Per L (d2 f) := by
  intro p
  simp only [PVNP.ContinuumFlux.d2]
  rw [fderiv_per (L, 0) (fun q => (hf q).1) p, fderiv_per (0, L) (fun q => (hf q).2) p]
  exact ⟨rfl, rfl⟩

theorem Per.lap {L : ℝ} {f : ℝ × ℝ → ℂ} (hf : Per L f) : Per L (lap f) := by
  intro p
  simp only [PVNP.ContinuumFlux.lap]
  rw [(hf.d1.d1 p).1, (hf.d2.d2 p).1, (hf.d1.d1 p).2, (hf.d2.d2 p).2]
  exact ⟨rfl, rfl⟩

theorem Per.mul {L : ℝ} {f g : ℝ × ℝ → ℂ} (hf : Per L f) (hg : Per L g) : Per L (f * g) := by
  intro p
  exact ⟨by simp only [Pi.mul_apply, (hf p).1, (hg p).1], by simp only [Pi.mul_apply, (hf p).2, (hg p).2]⟩

/-! ### The cell integral and Fubini -/

/-- The fundamental cell `[0,L]²`. -/
def cell (L : ℝ) : Set (ℝ × ℝ) := Icc 0 L ×ˢ Icc 0 L

theorem isCompact_cell (L : ℝ) : IsCompact (cell L) := isCompact_Icc.prod isCompact_Icc

/-- Integral over the fundamental cell. -/
noncomputable def I2 (L : ℝ) (f : ℝ × ℝ → ℂ) : ℂ := ∫ q in cell L, f q

theorem integrableOn_cell {L : ℝ} {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    IntegrableOn f (cell L) := hf.continuousOn.integrableOn_compact (isCompact_cell L)

theorem interval_eq_Icc {L : ℝ} (hL : 0 ≤ L) (g : ℝ → ℂ) :
    ∫ x in (0 : ℝ)..L, g x = ∫ x in Icc 0 L, g x := by
  rw [intervalIntegral.integral_of_le hL, integral_Icc_eq_integral_Ioc]

/-- **Fubini**, `x` outer. -/
theorem I2_iter {L : ℝ} (hL : 0 ≤ L) {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    I2 L f = ∫ x in (0 : ℝ)..L, ∫ y in (0 : ℝ)..L, f (x, y) := by
  have hi := integrableOn_cell (L := L) hf
  unfold I2 cell at *
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod f hi, interval_eq_Icc hL]
  congr 1
  funext x
  rw [interval_eq_Icc hL]

/-- **Fubini**, `y` outer. -/
theorem I2_iter' {L : ℝ} (hL : 0 ≤ L) {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    I2 L f = ∫ y in (0 : ℝ)..L, ∫ x in (0 : ℝ)..L, f (x, y) := by
  have h1 : I2 L f = I2 L (fun z => f z.swap) := by
    unfold I2 cell
    rw [Measure.volume_eq_prod]
    exact (setIntegral_prod_swap (Icc 0 L) (Icc 0 L) f).symm
  rw [h1, I2_iter hL (f := fun z => f z.swap) (hf.comp continuous_swap)]
  rfl

theorem I2_add {L : ℝ} {f g : ℝ × ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    I2 L (fun q => f q + g q) = I2 L f + I2 L g :=
  integral_add (integrableOn_cell hf) (integrableOn_cell hg)

theorem I2_sub {L : ℝ} {f g : ℝ × ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    I2 L (fun q => f q - g q) = I2 L f - I2 L g :=
  integral_sub (integrableOn_cell hf) (integrableOn_cell hg)

theorem I2_neg {L : ℝ} (f : ℝ × ℝ → ℂ) : I2 L (fun q => -f q) = -I2 L f := integral_neg _

theorem I2_const_mul {L : ℝ} (c : ℂ) (f : ℝ × ℝ → ℂ) : I2 L (fun q => c * f q) = c * I2 L f :=
  integral_const_mul c _

theorem I2_congr {L : ℝ} {f g : ℝ × ℝ → ℂ} (h : ∀ q, f q = g q) : I2 L f = I2 L g := by
  unfold I2; congr 1; funext q; exact h q

/-! ### Periodic integration by parts -/

/-- One-dimensional periodic integration by parts. -/
theorem ibp1 {u v u' v' : ℝ → ℂ} (L : ℝ) (hu : ∀ x, HasDerivAt u (u' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hu' : Continuous u') (hv' : Continuous v')
    (hper : u L * v L = u 0 * v 0) :
    ∫ x in (0 : ℝ)..L, u x * v' x = -∫ x in (0 : ℝ)..L, u' x * v x := by
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu x) (fun x _ => hv x)
    (hu'.intervalIntegrable _ _) (hv'.intervalIntegrable _ _), hper]
  ring

theorem cont_y {f : ℝ × ℝ → ℂ} (hf : Continuous f) (x : ℝ) : Continuous fun y => f (x, y) :=
  hf.comp (Continuous.prodMk continuous_const continuous_id)

theorem cont_x {f : ℝ × ℝ → ℂ} (hf : Continuous f) (y : ℝ) : Continuous fun x => f (x, y) :=
  hf.comp (Continuous.prodMk continuous_id continuous_const)

/-- **Periodic integration by parts** in `y`. -/
theorem ibp_d2 {L : ℝ} (hL : 0 ≤ L) {u v : ℝ × ℝ → ℂ} (hu : Sm u) (hv : Sm v) (hpu : Per L u)
    (hpv : Per L v) : I2 L (fun q => u q * d2 v q) = -I2 L (fun q => d2 u q * v q) := by
  rw [I2_iter hL (hu.continuous.mul hv.d2.continuous), I2_iter hL (hu.d2.continuous.mul hv.continuous),
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _
  refine ibp1 L (fun y => hasDerivAt_d2 hu.diff x y) (fun y => hasDerivAt_d2 hv.diff x y)
    (cont_y hu.d2.continuous x) (cont_y hv.d2.continuous x) ?_
  have h1 := (hpu (x, 0)).2
  have h2 := (hpv (x, 0)).2
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h1 h2
  rw [h1, h2]

/-- **Periodic integration by parts** in `x`. -/
theorem ibp_d1 {L : ℝ} (hL : 0 ≤ L) {u v : ℝ × ℝ → ℂ} (hu : Sm u) (hv : Sm v) (hpu : Per L u)
    (hpv : Per L v) : I2 L (fun q => u q * d1 v q) = -I2 L (fun q => d1 u q * v q) := by
  rw [I2_iter' hL (hu.continuous.mul hv.d1.continuous), I2_iter' hL (hu.d1.continuous.mul hv.continuous),
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro y _
  refine ibp1 L (fun x => hasDerivAt_d1 hu.diff x y) (fun x => hasDerivAt_d1 hv.diff x y)
    (cont_x hu.d1.continuous y) (cont_x hv.d1.continuous y) ?_
  have h1 := (hpu (0, y)).1
  have h2 := (hpv (0, y)).1
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h1 h2
  rw [h1, h2]

/-! ### Algebra of the partial derivatives -/

theorem d1_add {f g : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    d1 (fun q => f q + g q) = fun q => d1 f q + d1 g q := by
  funext q; show fderiv ℝ (f + g) q (1, 0) = _; rw [fderiv_add (hf q) (hg q)]; rfl

theorem d2_add {f g : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    d2 (fun q => f q + g q) = fun q => d2 f q + d2 g q := by
  funext q; show fderiv ℝ (f + g) q (0, 1) = _; rw [fderiv_add (hf q) (hg q)]; rfl

theorem d1_mul {f g : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    d1 (fun q => f q * g q) = fun q => d1 f q * g q + f q * d1 g q := by
  funext q; show fderiv ℝ (f * g) q (1, 0) = _; rw [fderiv_mul (hf q) (hg q)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, d1]; ring

theorem d2_mul {f g : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    d2 (fun q => f q * g q) = fun q => d2 f q * g q + f q * d2 g q := by
  funext q; show fderiv ℝ (f * g) q (0, 1) = _; rw [fderiv_mul (hf q) (hg q)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, d2]; ring

theorem d1_const_mul (c : ℂ) {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) :
    d1 (fun q => c * f q) = fun q => c * d1 f q := by
  funext q; simp only [d1]; rw [fderiv_const_mul (hf q) c]; rfl

theorem d2_const_mul (c : ℂ) {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) :
    d2 (fun q => c * f q) = fun q => c * d2 f q := by
  funext q; simp only [d2]; rw [fderiv_const_mul (hf q) c]; rfl

/-- Complex conjugate of a field. -/
noncomputable def cj (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun q => star (f q)

theorem d1_cj (f : ℝ × ℝ → ℂ) : d1 (cj f) = cj (d1 f) := by
  funext q
  show fderiv ℝ (fun y => star (f y)) q (1, 0) = star (fderiv ℝ f q (1, 0))
  rw [fderiv_star]; rfl

theorem d2_cj (f : ℝ × ℝ → ℂ) : d2 (cj f) = cj (d2 f) := by
  funext q
  show fderiv ℝ (fun y => star (f y)) q (0, 1) = star (fderiv ℝ f q (0, 1))
  rw [fderiv_star]; rfl

theorem lap_cj (f : ℝ × ℝ → ℂ) : lap (cj f) = cj (lap f) := by
  funext q; simp [lap, d1_cj, d2_cj, cj]

theorem Sm.cj {f : ℝ × ℝ → ℂ} (hf : Sm f) : Sm (cj f) := by
  have : PVNP.ContinuumFlux.cj f = fun q => (starL' ℝ : ℂ ≃L[ℝ] ℂ) (f q) := rfl
  rw [this]
  exact (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hf

theorem Per.cj {L : ℝ} {f : ℝ × ℝ → ℂ} (hf : Per L f) : Per L (cj f) := by
  intro p
  exact ⟨by simp only [PVNP.ContinuumFlux.cj, (hf p).1], by simp only [PVNP.ContinuumFlux.cj, (hf p).2]⟩

/-- **Product rule for the Laplacian.** -/
theorem lap_mul {f g : ℝ × ℝ → ℂ} (hf : Sm f) (hg : Sm g) :
    lap (fun q => f q * g q) =
      fun q => lap f q * g q + 2 * (d1 f q * d1 g q + d2 f q * d2 g q) + f q * lap g q := by
  funext q
  simp only [lap]
  rw [d1_mul hf.diff hg.diff, d2_mul hf.diff hg.diff,
    d1_add (f := fun q => d1 f q * g q) (g := fun q => f q * d1 g q) (hf.d1.diff.mul hg.diff)
      (hf.diff.mul hg.d1.diff),
    d2_add (f := fun q => d2 f q * g q) (g := fun q => f q * d2 g q) (hf.d2.diff.mul hg.diff)
      (hf.diff.mul hg.d2.diff),
    d1_mul hf.d1.diff hg.diff, d1_mul hf.diff hg.d1.diff, d2_mul hf.d2.diff hg.diff,
    d2_mul hf.diff hg.d2.diff]
  ring

/-! ### Symmetry of the Laplacian on the torus -/

theorem I2_d1d1 {L : ℝ} (hL : 0 ≤ L) {u v : ℝ × ℝ → ℂ} (hu : Sm u) (hv : Sm v) (hpu : Per L u)
    (hpv : Per L v) : I2 L (fun q => u q * d1 (d1 v) q) = I2 L (fun q => d1 (d1 u) q * v q) := by
  rw [ibp_d1 hL hu hv.d1 hpu hpv.d1]
  have h := ibp_d1 hL hv hu.d1 hpv hpu.d1
  have e1 : I2 L (fun q => d1 u q * d1 v q) = I2 L (fun q => d1 v q * d1 u q) :=
    I2_congr fun q => mul_comm _ _
  have e2 : I2 L (fun q => d1 (d1 u) q * v q) = I2 L (fun q => v q * d1 (d1 u) q) :=
    I2_congr fun q => mul_comm _ _
  rw [e1, e2, h]

theorem I2_d2d2 {L : ℝ} (hL : 0 ≤ L) {u v : ℝ × ℝ → ℂ} (hu : Sm u) (hv : Sm v) (hpu : Per L u)
    (hpv : Per L v) : I2 L (fun q => u q * d2 (d2 v) q) = I2 L (fun q => d2 (d2 u) q * v q) := by
  rw [ibp_d2 hL hu hv.d2 hpu hpv.d2]
  have h := ibp_d2 hL hv hu.d2 hpv hpu.d2
  have e1 : I2 L (fun q => d2 u q * d2 v q) = I2 L (fun q => d2 v q * d2 u q) :=
    I2_congr fun q => mul_comm _ _
  have e2 : I2 L (fun q => d2 (d2 u) q * v q) = I2 L (fun q => v q * d2 (d2 u) q) :=
    I2_congr fun q => mul_comm _ _
  rw [e1, e2, h]

/-- **`Δ` is symmetric** (bilinear form) on smooth periodic fields. -/
theorem I2_lap_symm {L : ℝ} (hL : 0 ≤ L) {u v : ℝ × ℝ → ℂ} (hu : Sm u) (hv : Sm v) (hpu : Per L u)
    (hpv : Per L v) : I2 L (fun q => u q * lap v q) = I2 L (fun q => lap u q * v q) := by
  have e1 : I2 L (fun q => u q * lap v q) =
      I2 L (fun q => u q * d1 (d1 v) q) + I2 L (fun q => u q * d2 (d2 v) q) := by
    rw [← I2_add (hu.continuous.mul hv.d1.d1.continuous) (hu.continuous.mul hv.d2.d2.continuous)]
    exact I2_congr fun q => by simp only [lap]; ring
  have e2 : I2 L (fun q => lap u q * v q) =
      I2 L (fun q => d1 (d1 u) q * v q) + I2 L (fun q => d2 (d2 u) q * v q) := by
    rw [← I2_add (hu.d1.d1.continuous.mul hv.continuous) (hu.d2.d2.continuous.mul hv.continuous)]
    exact I2_congr fun q => by simp only [lap]; ring
  rw [e1, e2, I2_d1d1 hL hu hv hpu hpv, I2_d2d2 hL hu hv hpu hpv]

/-- **Gradient identity**: `∫ ψ̄ Δψ = −∫ (|∂₁ψ|² + |∂₂ψ|²)`. -/
theorem I2_cj_lap {L : ℝ} (hL : 0 ≤ L) {f : ℝ × ℝ → ℂ} (hf : Sm f) (hp : Per L f) :
    I2 L (fun q => cj f q * lap f q) =
      -I2 L (fun q => cj (d1 f) q * d1 f q + cj (d2 f) q * d2 f q) := by
  have e1 : I2 L (fun q => cj f q * lap f q) =
      I2 L (fun q => cj f q * d1 (d1 f) q) + I2 L (fun q => cj f q * d2 (d2 f) q) := by
    rw [← I2_add (hf.cj.continuous.mul hf.d1.d1.continuous) (hf.cj.continuous.mul hf.d2.d2.continuous)]
    exact I2_congr fun q => by simp only [lap]; ring
  rw [e1, ibp_d1 hL hf.cj hf.d1 hp.cj hp.d1, ibp_d2 hL hf.cj hf.d2 hp.cj hp.d2, d1_cj, d2_cj,
    I2_add (hf.d1.cj.continuous.mul hf.d1.continuous) (hf.d2.cj.continuous.mul hf.d2.continuous)]
  ring

/-! ### The operator `A = Δ + κ` and real-valued fields -/

/-- `A f = (Δ + κ) f`. -/
noncomputable def A (κ : ℝ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p => lap f p + (κ : ℂ) * f p

theorem Sm.A {κ : ℝ} {f : ℝ × ℝ → ℂ} (hf : Sm f) : Sm (A κ f) := hf.lap.add (contDiff_const.mul hf)

theorem Per.A {L κ : ℝ} {f : ℝ × ℝ → ℂ} (hf : Per L f) : Per L (A κ f) := by
  intro p
  exact ⟨by simp only [PVNP.ContinuumFlux.A, (hf.lap p).1, (hf p).1],
    by simp only [PVNP.ContinuumFlux.A, (hf.lap p).2, (hf p).2]⟩

theorem A_cj (κ : ℝ) (f : ℝ × ℝ → ℂ) : A κ (cj f) = cj (A κ f) := by
  funext q; simp [A, lap_cj, cj, Complex.conj_ofReal]

theorem Sm.mul {f g : ℝ × ℝ → ℂ} (hf : Sm f) (hg : Sm g) : Sm (fun q => f q * g q) :=
  ContDiff.mul hf hg

/-- **`A` is symmetric** (bilinear form) on smooth periodic fields. -/
theorem I2_A_symm {L : ℝ} (hL : 0 ≤ L) (κ : ℝ) {u v : ℝ × ℝ → ℂ} (hu : Sm u) (hv : Sm v)
    (hpu : Per L u) (hpv : Per L v) :
    I2 L (fun q => u q * A κ v q) = I2 L (fun q => A κ u q * v q) := by
  have e1 : I2 L (fun q => u q * A κ v q) =
      I2 L (fun q => u q * lap v q) + I2 L (fun q => (κ : ℂ) * (u q * v q)) := by
    rw [← I2_add (hu.continuous.mul hv.lap.continuous)
      (continuous_const.mul (hu.continuous.mul hv.continuous))]
    exact I2_congr fun q => by simp only [A]; ring
  have e2 : I2 L (fun q => A κ u q * v q) =
      I2 L (fun q => lap u q * v q) + I2 L (fun q => (κ : ℂ) * (u q * v q)) := by
    rw [← I2_add (hu.lap.continuous.mul hv.continuous)
      (continuous_const.mul (hu.continuous.mul hv.continuous))]
    exact I2_congr fun q => by simp only [A]; ring
  rw [e1, e2, I2_lap_symm hL hu hv hpu hpv]

/-- Real-valued fields. -/
def IsR (f : ℝ × ℝ → ℂ) : Prop := ∀ q, (f q).im = 0

theorem IsR.d1 {f : ℝ × ℝ → ℂ} (hR : IsR f) (hf : Sm f) : IsR (d1 f) := by
  intro q
  obtain ⟨x, y⟩ := q
  have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_d1 hf.diff x y)
  have h2 : (fun s => Complex.imCLM (f (s, y))) = fun _ => (0 : ℝ) := funext fun s => hR (s, y)
  have h3 : HasDerivAt (fun s => Complex.imCLM (f (s, y))) (Complex.imCLM (PVNP.ContinuumFlux.d1 f (x, y))) x := h1
  rw [h2] at h3
  have := h3.unique (hasDerivAt_const x (0 : ℝ))
  simpa using this

theorem IsR.d2 {f : ℝ × ℝ → ℂ} (hR : IsR f) (hf : Sm f) : IsR (d2 f) := by
  intro q
  obtain ⟨x, y⟩ := q
  have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_d2 hf.diff x y)
  have h2 : (fun s => Complex.imCLM (f (x, s))) = fun _ => (0 : ℝ) := funext fun s => hR (x, s)
  have h3 : HasDerivAt (fun s => Complex.imCLM (f (x, s))) (Complex.imCLM (PVNP.ContinuumFlux.d2 f (x, y))) y := h1
  rw [h2] at h3
  have := h3.unique (hasDerivAt_const y (0 : ℝ))
  simpa using this

theorem IsR.lap {f : ℝ × ℝ → ℂ} (hR : IsR f) (hf : Sm f) : IsR (lap f) := by
  intro q
  simp only [PVNP.ContinuumFlux.lap, Complex.add_im, (hR.d1 hf).d1 hf.d1 q, (hR.d2 hf).d2 hf.d2 q,
    add_zero]

/-- The integral of a real-valued field is real. -/
theorem I2_im {L : ℝ} {f : ℝ × ℝ → ℂ} (hf : Continuous f) (hR : ∀ q, (f q).im = 0) :
    (I2 L f).im = 0 := by
  have h := integral_im (μ := volume.restrict (cell L)) (integrableOn_cell (L := L) hf)
  simp only [RCLike.im_to_complex] at h
  unfold I2
  rw [← h]
  simp [hR]

/-! ### The static flux identity -/

/-- `∇χ · ∇ψ̄`. -/
noncomputable def Gd (χ ψ : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  d1 χ q * d1 (cj ψ) q + d2 χ q * d2 (cj ψ) q

/-- The commutator density `Δχ ψ̄ + 2 ∇χ·∇ψ̄`. -/
noncomputable def Qf (χ ψ : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ := lap χ q * cj ψ q + 2 * Gd χ ψ q

theorem Sm.Gd {χ ψ : ℝ × ℝ → ℂ} (hχ : Sm χ) (hψ : Sm ψ) : Sm (Gd χ ψ) :=
  (hχ.d1.mul hψ.cj.d1).add (hχ.d2.mul hψ.cj.d2)

theorem Sm.Qf {χ ψ : ℝ × ℝ → ℂ} (hχ : Sm χ) (hψ : Sm ψ) : Sm (Qf χ ψ) :=
  (hχ.lap.mul hψ.cj).add (contDiff_const.mul (hχ.Gd hψ))

theorem A_mul_cj {κ : ℝ} {χ ψ : ℝ × ℝ → ℂ} (hχ : Sm χ) (hψ : Sm ψ) (q : ℝ × ℝ) :
    A κ (fun q => χ q * cj ψ q) q = χ q * cj (A κ ψ) q + Qf χ ψ q := by
  have h1 : cj (A κ ψ) q = lap (cj ψ) q + (κ : ℂ) * cj ψ q := by
    rw [← A_cj]; rfl
  have h2 : A κ (fun q => χ q * cj ψ q) q =
      lap (fun q => χ q * cj ψ q) q + (κ : ℂ) * (χ q * cj ψ q) := rfl
  rw [h2, h1, lap_mul hχ hψ.cj]
  beta_reduce
  simp only [Qf, Gd]
  ring

/-- **Static flux identity**: `Im ∫ χ ψ̄ A²ψ = Im ∫ Qf · Aψ` (the `χ|Aψ|²` term is real). -/
theorem flux_static {L : ℝ} (hL : 0 ≤ L) (κ : ℝ) {χ ψ : ℝ × ℝ → ℂ} (hχ : Sm χ) (hψ : Sm ψ)
    (hpχ : Per L χ) (hpψ : Per L ψ) (hR : IsR χ) :
    (I2 L (fun q => χ q * cj ψ q * A κ (A κ ψ) q)).im = (I2 L (fun q => Qf χ ψ q * A κ ψ q)).im := by
  have hu : Sm (fun q => χ q * cj ψ q) := hχ.mul hψ.cj
  have hpu : Per L (fun q => χ q * cj ψ q) := hpχ.mul hpψ.cj
  rw [I2_A_symm hL κ hu hψ.A hpu hpψ.A]
  have e : I2 L (fun q => A κ (fun q => χ q * cj ψ q) q * A κ ψ q) =
      I2 L (fun q => χ q * (cj (A κ ψ) q * A κ ψ q)) + I2 L (fun q => Qf χ ψ q * A κ ψ q) := by
    rw [← I2_add (hχ.continuous.mul (hψ.A.cj.continuous.mul hψ.A.continuous))
      ((hχ.Qf hψ).continuous.mul hψ.A.continuous)]
    exact I2_congr fun q => by rw [A_mul_cj hχ hψ q]; ring
  rw [e, Complex.add_im, I2_im (hχ.continuous.mul (hψ.A.cj.continuous.mul hψ.A.continuous)), zero_add]
  intro q
  have h1 : cj (A κ ψ) q * A κ ψ q = ((Complex.normSq (A κ ψ q) : ℝ) : ℂ) := by
    simp only [cj]; rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [h1, Complex.mul_im, hR q]
  simp

/-- **Splitting `Aψ = Δψ + κψ`**: the `κ Δχ |ψ|²` term is real. -/
theorem flux_split {L : ℝ} (κ : ℝ) {χ ψ : ℝ × ℝ → ℂ} (hχ : Sm χ) (hψ : Sm ψ) (hR : IsR χ) :
    (I2 L (fun q => Qf χ ψ q * A κ ψ q)).im =
      (I2 L (fun q => Qf χ ψ q * lap ψ q)).im + 2 * κ * (I2 L (fun q => Gd χ ψ q * ψ q)).im := by
  have hRl : IsR (lap χ) := hR.lap hχ
  have e : I2 L (fun q => Qf χ ψ q * A κ ψ q) =
      I2 L (fun q => Qf χ ψ q * lap ψ q) +
        (I2 L (fun q => (κ : ℂ) * (lap χ q * (cj ψ q * ψ q))) +
          I2 L (fun q => (2 * κ : ℂ) * (Gd χ ψ q * ψ q))) := by
    rw [← I2_add (continuous_const.mul (hχ.lap.continuous.mul (hψ.cj.continuous.mul hψ.continuous)))
      (continuous_const.mul ((hχ.Gd hψ).continuous.mul hψ.continuous)),
      ← I2_add ((hχ.Qf hψ).continuous.mul hψ.lap.continuous)
        ((continuous_const.mul (hχ.lap.continuous.mul (hψ.cj.continuous.mul hψ.continuous))).add
          (continuous_const.mul ((hχ.Gd hψ).continuous.mul hψ.continuous)))]
    exact I2_congr fun q => by simp only [A, Qf]; ring
  rw [e, Complex.add_im, Complex.add_im, I2_im (continuous_const.mul
    (hχ.lap.continuous.mul (hψ.cj.continuous.mul hψ.continuous))), zero_add, I2_const_mul,
    Complex.mul_im]
  · simp
  · intro q
    have h1 : cj ψ q * ψ q = ((Complex.normSq (ψ q) : ℝ) : ℂ) := by
      simp only [cj]; rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [h1, Complex.mul_im, Complex.mul_im, hRl q]
    simp

/-! ### Norms and Cauchy–Schwarz on the cell -/

theorem integrableOn_cell' {L : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f (cell L) :=
  hf.continuousOn.integrableOn_compact (isCompact_cell L)

theorem measurableSet_cell (L : ℝ) : MeasurableSet (cell L) := measurableSet_Icc.prod measurableSet_Icc

/-- `∫_{cell} ‖f‖²`. -/
noncomputable def N2 (L : ℝ) (f : ℝ × ℝ → ℂ) : ℝ := ∫ q in cell L, ‖f q‖ ^ 2

/-- The `L²` norm over the cell. -/
noncomputable def nrm (L : ℝ) (f : ℝ × ℝ → ℂ) : ℝ := Real.sqrt (N2 L f)

/-- The `L²` norm of the gradient over the cell. -/
noncomputable def Gr (L : ℝ) (f : ℝ × ℝ → ℂ) : ℝ :=
  Real.sqrt (∫ q in cell L, (‖d1 f q‖ ^ 2 + ‖d2 f q‖ ^ 2))

theorem nrm_nonneg (L : ℝ) (f : ℝ × ℝ → ℂ) : 0 ≤ nrm L f := Real.sqrt_nonneg _
theorem Gr_nonneg (L : ℝ) (f : ℝ × ℝ → ℂ) : 0 ≤ Gr L f := Real.sqrt_nonneg _

/-- Cauchy–Schwarz for continuous real functions on the cell. -/
theorem cs_real {L : ℝ} {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ q in cell L, f q * g q) ^ 2 ≤ (∫ q in cell L, f q ^ 2) * (∫ q in cell L, g q ^ 2) := by
  set A := ∫ q in cell L, f q ^ 2 with hAdef
  set B := ∫ q in cell L, g q ^ 2 with hBdef
  set C := ∫ q in cell L, f q * g q with hCdef
  have key : ∀ s : ℝ, 0 ≤ s ^ 2 * A - 2 * s * C + B := by
    intro s
    have h : ∫ q in cell L, (s * f q - g q) ^ 2 = s ^ 2 * A - 2 * s * C + B := by
      have e : (fun q => (s * f q - g q) ^ 2) =
          fun q => s ^ 2 * f q ^ 2 - 2 * s * (f q * g q) + g q ^ 2 := by
        funext q; ring
      have i1 : IntegrableOn (fun q => s ^ 2 * f q ^ 2) (cell L) :=
        integrableOn_cell' (continuous_const.mul (hf.pow 2))
      have i2 : IntegrableOn (fun q => 2 * s * (f q * g q)) (cell L) :=
        integrableOn_cell' (continuous_const.mul (hf.mul hg))
      have i3 : IntegrableOn (fun q => g q ^ 2) (cell L) := integrableOn_cell' (hg.pow 2)
      have hadd := MeasureTheory.integral_add (i1.sub i2) i3
      simp only [Pi.sub_apply] at hadd
      rw [e, hadd, MeasureTheory.integral_sub i1 i2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [← h]
    exact setIntegral_nonneg (measurableSet_cell L) (fun q _ => sq_nonneg _)
  have hA : 0 ≤ A := setIntegral_nonneg (measurableSet_cell L) (fun q _ => sq_nonneg _)
  by_cases hA0 : A = 0
  · have hC : C = 0 := by
      by_contra hC
      have h := key ((B + 1) / (2 * C))
      rw [hA0] at h
      have e : (B + 1) / (2 * C) * C = (B + 1) / 2 := by field_simp
      have e2 : ((B + 1) / (2 * C)) ^ 2 * 0 - 2 * ((B + 1) / (2 * C)) * C + B = -1 := by
        rw [mul_zero, zero_sub, mul_assoc, e]; ring
      linarith
    rw [hC, hA0]; simp
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have h := key (C / A)
    have e : (C / A) ^ 2 * A - 2 * (C / A) * C + B = B - C ^ 2 / A := by
      field_simp; ring
    rw [e] at h
    have h2 : C ^ 2 / A ≤ B := by linarith
    rw [div_le_iff₀ hApos] at h2
    nlinarith

/-- **Weighted Cauchy–Schwarz**: if `‖u‖ ≤ c g` then `‖∫ u v‖ ≤ c ‖g‖₂ ‖v‖₂`. -/
theorem I2_bound {L : ℝ} {u v : ℝ × ℝ → ℂ} {g : ℝ × ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hg : Continuous g) {c : ℝ} (hc : 0 ≤ c) (h : ∀ q, ‖u q‖ ≤ c * g q) :
    ‖I2 L (fun q => u q * v q)‖ ≤ c * Real.sqrt (∫ q in cell L, g q ^ 2) * nrm L v := by
  have h1 : ‖I2 L (fun q => u q * v q)‖ ≤ ∫ q in cell L, ‖u q‖ * ‖v q‖ := by
    unfold I2
    calc ‖∫ q in cell L, u q * v q‖ ≤ ∫ q in cell L, ‖u q * v q‖ := norm_integral_le_integral_norm _
      _ = ∫ q in cell L, ‖u q‖ * ‖v q‖ := by simp_rw [norm_mul]
  have h2 : ∫ q in cell L, ‖u q‖ * ‖v q‖ ≤ ∫ q in cell L, c * (g q * ‖v q‖) :=
    setIntegral_mono_on (integrableOn_cell' (hu.norm.mul hv.norm))
      (integrableOn_cell' (continuous_const.mul (hg.mul hv.norm))) (measurableSet_cell L)
      (fun q _ => by
        have := h q
        have hv0 := norm_nonneg (v q)
        nlinarith)
  rw [MeasureTheory.integral_const_mul] at h2
  have h3 := cs_real (L := L) hg hv.norm
  have h4 : ∫ q in cell L, g q * ‖v q‖ ≤
      Real.sqrt (∫ q in cell L, g q ^ 2) * nrm L v := by
    unfold nrm N2
    rw [← Real.sqrt_mul (setIntegral_nonneg (measurableSet_cell L) (fun q _ => sq_nonneg _))]
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h3)
  calc ‖I2 L (fun q => u q * v q)‖ ≤ c * ∫ q in cell L, g q * ‖v q‖ := le_trans h1 h2
    _ ≤ c * (Real.sqrt (∫ q in cell L, g q ^ 2) * nrm L v) := mul_le_mul_of_nonneg_left h4 hc
    _ = _ := by ring

theorem sqrt_int_norm_sq {L : ℝ} (f : ℝ × ℝ → ℂ) :
    Real.sqrt (∫ q in cell L, ‖f q‖ ^ 2) = nrm L f := rfl

/-- The gradient magnitude. -/
noncomputable def gm (f : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℝ := Real.sqrt (‖d1 f q‖ ^ 2 + ‖d2 f q‖ ^ 2)

theorem gm_sq (f : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : gm f q ^ 2 = ‖d1 f q‖ ^ 2 + ‖d2 f q‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem Gr_eq (L : ℝ) (f : ℝ × ℝ → ℂ) : Gr L f = Real.sqrt (∫ q in cell L, gm f q ^ 2) := by
  unfold Gr; simp_rw [gm_sq]

theorem continuous_gm {f : ℝ × ℝ → ℂ} (hf : Sm f) : Continuous (gm f) :=
  ((hf.d1.continuous.norm.pow 2).add (hf.d2.continuous.norm.pow 2)).sqrt

/-- Two-dimensional Cauchy–Schwarz for the gradient pairing. -/
theorem norm_Gd_le {χ ψ : ℝ × ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hga : ∀ q, ‖d1 χ q‖ ^ 2 + ‖d2 χ q‖ ^ 2 ≤ a ^ 2) (q : ℝ × ℝ) : ‖Gd χ ψ q‖ ≤ a * gm ψ q := by
  have hc1 : ‖d1 (cj ψ) q‖ = ‖d1 ψ q‖ := by rw [d1_cj]; simp [cj]
  have hc2 : ‖d2 (cj ψ) q‖ = ‖d2 ψ q‖ := by rw [d2_cj]; simp [cj]
  have hx1 := norm_nonneg (d1 χ q)
  have hx2 := norm_nonneg (d2 χ q)
  have hy1 := norm_nonneg (d1 ψ q)
  have hy2 := norm_nonneg (d2 ψ q)
  have hgm : 0 ≤ gm ψ q := Real.sqrt_nonneg _
  have hgm2 := gm_sq ψ q
  have h1 : ‖Gd χ ψ q‖ ≤ ‖d1 χ q‖ * ‖d1 ψ q‖ + ‖d2 χ q‖ * ‖d2 ψ q‖ := by
    unfold Gd
    calc ‖d1 χ q * d1 (cj ψ) q + d2 χ q * d2 (cj ψ) q‖
        ≤ ‖d1 χ q * d1 (cj ψ) q‖ + ‖d2 χ q * d2 (cj ψ) q‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul, hc1, hc2]
  have h2 : (‖d1 χ q‖ * ‖d1 ψ q‖ + ‖d2 χ q‖ * ‖d2 ψ q‖) ^ 2 ≤ (a * gm ψ q) ^ 2 := by
    rw [mul_pow, hgm2]
    nlinarith [sq_nonneg (‖d1 χ q‖ * ‖d2 ψ q‖ - ‖d2 χ q‖ * ‖d1 ψ q‖), hga q,
      mul_nonneg (sq_nonneg (‖d1 ψ q‖)) (sq_nonneg (‖d2 ψ q‖))]
  have h3 : ‖d1 χ q‖ * ‖d1 ψ q‖ + ‖d2 χ q‖ * ‖d2 ψ q‖ ≤ a * gm ψ q := by
    have hX : 0 ≤ ‖d1 χ q‖ * ‖d1 ψ q‖ + ‖d2 χ q‖ * ‖d2 ψ q‖ := by positivity
    have hY : 0 ≤ a * gm ψ q := mul_nonneg ha hgm
    nlinarith
  exact h1.trans h3

end PVNP.ContinuumFlux
