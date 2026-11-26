import PVNP.WCTSATDevice

/-!
# A genuine exponential mode of the constant-background linearization

The constant plane wave of the frozen PDE gives, on a real cosine
sideband, x' = H*y, y' = -(H+2*c)*x with
H=q²-2κq, c=a²(-β+2γa²).
This module proves the linearized mode algebra and the explicit
growing solution of that two-dimensional system. The connection to
the Fréchet derivative of the full PDE flow is not formalized here.
-/
namespace PVNP.SidebandAmplification

def H (κ q : ℝ) : ℝ := q^2-2*κ*q
def c (a β γ : ℝ) : ℝ := a^2*(-β+2*γ*a^2)
def discriminant (κ q a β γ : ℝ) : ℝ :=
  -H κ q * (H κ q + 2*c a β γ)

theorem growing_rate {h g : ℝ} (hu : 0 < -h*(h+2*g)) :
    ∃ r : ℝ, 0 < r ∧ r^2 = -h*(h+2*g) := by
  exact ⟨Real.sqrt (-h*(h+2*g)), Real.sqrt_pos.2 hu,
    Real.sq_sqrt hu.le⟩

theorem eigenvector {h g r : ℝ} (hr : r^2 = -h*(h+2*g)) :
    h*r = r*h ∧ -(h+2*g)*h = r*r := by
  constructor
  · ring
  · nlinarith only [hr]

theorem explicit_growing_sideband :
    H 0 1 = 1 ∧ c 1 2 (1/2) = -1 ∧
    discriminant 0 1 1 2 (1/2) = 1 := by
  norm_num [H,c,discriminant]

theorem exponential_solution (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp s) (H 0 1 * Real.exp t) t ∧
    HasDerivAt (fun s : ℝ => Real.exp s)
      (-(H 0 1 + 2*c 1 2 (1/2))*Real.exp t) t := by
  have h1 : H 0 1 = 1 := by norm_num [H]
  have h2 : -(H 0 1 + 2*c 1 2 (1/2)) = 1 := by norm_num [H, c]
  rw [h2, h1, one_mul]
  exact ⟨Real.hasDerivAt_exp t, Real.hasDerivAt_exp t⟩


open Complex PVNP.Torus PVNP.WCTSATDevice

/-- Remove the background's nonlinear phase frequency. The derivative
is real-linear, not complex-linear, because of the conjugation term. -/
theorem rotated_fnl_deriv (a β γ : ℝ) (z : ℂ) :
    HasDerivAt (fun e : ℝ =>
      fnl β γ ((a : ℂ)+(e : ℂ)*z) -
        ((-β*a^2+γ*a^4 : ℝ) : ℂ)*((a : ℂ)+(e : ℂ)*z))
      ((c a β γ : ℂ)*(z+(starRingEnd ℂ) z)) 0 := by
  have he : HasDerivAt (fun e : ℝ => (e : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hz := (he.mul_const z).const_add (a : ℂ)
  have hc := (he.mul_const ((starRingEnd ℂ) z)).const_add (a : ℂ)
  have h3 := ((hz.mul hz).mul hc).const_mul (-(β : ℂ))
  have h5 := ((((hz.mul hz).mul hz).mul hc).mul hc).const_mul (γ : ℂ)
  have hphase := hz.const_mul ((-β*a^2+γ*a^4 : ℝ) : ℂ)
  have h := (h3.add h5).sub hphase
  convert h using 1
  · funext e
    simp only [fnl, map_add, map_mul, Complex.conj_ofReal, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply]
    try ring
  · simp only [Pi.mul_apply, Complex.ofReal_zero, zero_mul, add_zero, one_mul]
    unfold c
    push_cast
    ring

/-- The above derivative is taken on the actual reconstructed physical
field of Fnl, along a perturbation of its existing constant mode. -/
theorem actual_field_first_variation {L : ℝ} (hL : 0 < L)
    (a β γ : ℝ) (v : ℓ2) (x : ℝ × ℝ) :
    let base := mode L 0 ((L*a : ℝ) : ℂ)
    let p := fun e : ℝ => base + (e : ℂ) • v
    HasDerivAt (fun e : ℝ =>
      field L (co L (Fnl L β γ (p e))) x -
        ((-β*a^2+γ*a^4 : ℝ) : ℂ)*field L (co L (p e)) x)
      ((c a β γ : ℂ)*(field L (co L v) x+
        (starRingEnd ℂ) (field L (co L v) x))) 0 := by
  dsimp only
  have hbase : field L (co L (mode L 0 ((L*a : ℝ) : ℂ))) x = (a : ℂ) := by
    rw [co_mode, field_single_zero]
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
  have hpath (e : ℝ) :
      field L (co L (mode L 0 ((L*a : ℝ) : ℂ) + (e : ℂ) • v)) x =
        (a : ℂ)+(e : ℂ)*field L (co L v) x := by
    rw [co_add, co_smul, field_add (L1_co' hL _) (L1_smul _ (L1_co' hL _)),
      field_smul, hbase]
  simp_rw [field_Fnl hL, hpath]
  exact rotated_fnl_deriv a β γ (field L (co L v) x)

/-- The signed quadratic invariant of each real sideband system. -/
theorem sideband_energy_deriv {h g : ℝ} {x y : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (h*y t) t)
    (hy : HasDerivAt y (-(h+2*g)*x t) t) :
    HasDerivAt (fun s => (h+2*g)*(x s)^2+h*(y s)^2) 0 t := by
  have h := ((hx.pow 2).const_mul (h+2*g)).add ((hy.pow 2).const_mul h)
  convert h using 1 <;> ring

theorem sideband_energy_conserved {h g : ℝ} {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (h*y t) t)
    (hy : ∀ t, HasDerivAt y (-(h+2*g)*x t) t) (t : ℝ) :
    (h+2*g)*(x t)^2+h*(y t)^2 =
      (h+2*g)*(x 0)^2+h*(y 0)^2 := by
  exact is_const_of_deriv_eq_zero
    (fun s => (sideband_energy_deriv (hx s) (hy s)).differentiableAt)
    (fun s => (sideband_energy_deriv (hx s) (hy s)).deriv) t 0

/-- Positive definite sideband energy bounds all times without
exponential growth. Negative definite energy works after negation. -/
theorem stable_sideband_bound {h g : ℝ} {x y : ℝ → ℝ}
    (hh : 0 < h) (hg : 0 < h+2*g)
    (hx : ∀ t, HasDerivAt x (h*y t) t)
    (hy : ∀ t, HasDerivAt y (-(h+2*g)*x t) t) (t : ℝ) :
    min h (h+2*g)*((x t)^2+(y t)^2) ≤
      max h (h+2*g)*((x 0)^2+(y 0)^2) := by
  calc
    _ ≤ (h+2*g)*(x t)^2+h*(y t)^2 := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
    _ = (h+2*g)*(x 0)^2+h*(y 0)^2 := sideband_energy_conserved hx hy t
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))


/-- **Uniform-in-time sideband bound.** With both quadratic coefficients positive, the
sideband amplitude stays bounded for all time by the ratio of the extreme coefficients:
no exponential growth occurs in the linear stable regime. -/
theorem stable_sideband_ratio_bound {h g : ℝ} {x y : ℝ → ℝ}
    (hh : 0 < h) (hg : 0 < h+2*g)
    (hx : ∀ t, HasDerivAt x (h*y t) t)
    (hy : ∀ t, HasDerivAt y (-(h+2*g)*x t) t) (t : ℝ) :
    (x t)^2+(y t)^2 ≤
      (max h (h+2*g) / min h (h+2*g))*((x 0)^2+(y 0)^2) := by
  have hmin : 0 < min h (h+2*g) := lt_min hh hg
  have hb := stable_sideband_bound hh hg hx hy t
  rw [div_mul_eq_mul_div, le_div_iff₀ hmin]
  linarith [mul_comm (min h (h+2*g)) ((x t)^2+(y t)^2)]

/-- All nonzero q have positive-definite sideband energy under
these sufficient background conditions. This is linear stability,
not global nonlinear stability. -/
theorem stable_background_coefficients {κ q a β γ : ℝ}
    (hκ : κ ≤ 0) (hq : 0 < q) (hc : β ≤ 2*γ*a^2) :
    0 < H κ q ∧ 0 < H κ q + 2*c a β γ := by
  have hh : 0 < H κ q := by
    unfold H
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hκ hq.le, sq_pos_of_pos hq]
  have hg : 0 ≤ c a β γ := by
    unfold c
    exact mul_nonneg (sq_nonneg _) (by linarith)
  exact ⟨hh,by linarith⟩

theorem unstable_sideband_iff {h g : ℝ} (hh : 0 < h) :
    0 < -h*(h+2*g) ↔ h+2*g < 0 := by
  rw [neg_mul, neg_pos]
  constructor
  · intro hlt
    by_contra hge
    push_neg at hge
    exact absurd hlt (not_lt.2 (mul_nonneg hh.le hge))
  · intro hlt
    exact mul_neg_of_pos_of_neg hh hlt

/-- Exact quadratic detector expansion for a real directional
perturbation. It uses the original physical Jdet. -/
theorem detector_directional_expansion {L : ℝ} (hL : 0 < L)
    {χ : ℓ2} (hreal : rev (co L χ) = co L χ) (u v : ℓ2) (e : ℝ) :
    Jdet L χ (u+(e : ℂ) • v) =
      Jdet L χ u +
        e * (2*(inner ℂ (Lc L u) (Lc L (mulH L χ v))).re) +
        e^2 * Jdet L χ v := by
  have hc : (inner ℂ (Lc L v) (Lc L (mulH L χ u))).re =
      (inner ℂ (Lc L u) (Lc L (mulH L χ v))).re := by
    rw [inner_mulH_symm hL hreal v u]
    rw [← inner_conj_symm (𝕜 := ℂ) (Lc L (mulH L χ v)) (Lc L u),
      Complex.conj_re]
  simp only [Jdet_eq_re hL hreal, mulH_add_right hL, mulH_smul_right hL,
    map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hc]
  ring

theorem detector_directional_deriv {L : ℝ} (hL : 0 < L)
    {χ : ℓ2} (hreal : rev (co L χ) = co L χ) (u v : ℓ2) :
    HasDerivAt (fun e : ℝ => Jdet L χ (u+(e : ℂ) • v))
      (2*(inner ℂ (Lc L u) (Lc L (mulH L χ v))).re) 0 := by
  let d := 2*(inner ℂ (Lc L u) (Lc L (mulH L χ v))).re
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const d).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (Jdet L χ v))).const_add (Jdet L χ u)
  convert h using 1
  · funext e
    rw [detector_directional_expansion hL hreal]
    dsimp [d]
    ring
  · simp [d]

end PVNP.SidebandAmplification
