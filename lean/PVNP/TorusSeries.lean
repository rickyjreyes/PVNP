import PVNP.WCTPlaneWave

/-!
# Fourier series on the flat torus `T_L² = (ℝ/Lℤ)²` (Phase VI groundwork for M3-T and F-1)

The frozen physical model `WCT-Phys` lives on the periodic square `Ω = [0, L)²`.  This module sets
up the Fourier-series layer that the continuum well-posedness theory (`PVNP.TorusH2`,
`PVNP.TorusFlow`, `PVNP.TorusWellPosed`) and the continuum flux theorem (`PVNP.TorusFlux`) are
built on.  Everything is stated for the *physical* domain, with Lebesgue measure on the
fundamental box `[0, L]²` (`box L`), and for an arbitrary period `L > 0`.

* Modes `e_k(x) = exp(2πi(k₁x₁ + k₂x₂)/L)` (`emode`), `k ∈ ℤ²`, of modulus one, multiplicative
  in `k`, `L`-periodic, with `∫_{[0,L]²} e_k = L²·[k = 0]` (`integral_emode`).
* Absolutely convergent series `field L a = L⁻¹ Σ_k a_k e_k` (the orthonormal-basis
  normalisation: `‖field L a‖_{L²} = ‖a‖_{ℓ²}`).  For `a ∈ ℓ¹` the field is a continuous,
  `L`-periodic function (`continuous_field`, `field_periodic₁`, `field_periodic₂`).
* Products and conjugates are again series: `field_mul` (Cauchy product on `ℤ²`, the
  coefficients of `fg` are `pr L a b = L⁻¹ (a ⋆ b)`), `field_rev` (`conj f` has coefficients
  `rev a k = conj (a (-k))`).
* Parseval for absolutely convergent series: `integral_conj_mul`,
  `∫_{[0,L]²} conj(field a) · field b = Σ_k conj(a_k) b_k`, and `integral_norm_sq`.
* Fourier coefficients `fc L f k = L⁻¹ ∫_{[0,L]²} f · conj(e_k)` recover the series:
  `fc_field`.
* Classical derivatives: the coordinate derivatives of `WCTPlaneWave` (`d1`, `d2`, `lap`) act on
  series as the Fourier multipliers `iξ₁`, `iξ₂`, `−|ξ|²` (`d1_field`, `d2_field`, `lap_field`),
  where `ξ_k = 2πk/L`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ENNReal NNReal

namespace PVNP.Torus

/-- The lattice of wave numbers `ℤ²`. -/
abbrev Z2 := ℤ × ℤ

/-! ### One-dimensional modes -/

/-- The one-dimensional mode `exp(2πi m s / L)`. -/
noncomputable def e1 (L : ℝ) (m : ℤ) (s : ℝ) : ℂ :=
  Complex.exp (((2 * π / L * m * s : ℝ) : ℂ) * I)

theorem norm_e1 (L : ℝ) (m : ℤ) (s : ℝ) : ‖e1 L m s‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem e1_add (L : ℝ) (m n : ℤ) (s : ℝ) : e1 L (m + n) s = e1 L m s * e1 L n s := by
  rw [e1, e1, e1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e1_neg (L : ℝ) (m : ℤ) (s : ℝ) : e1 L (-m) s = (starRingEnd ℂ) (e1 L m s) := by
  rw [e1, e1, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem e1_zero (L : ℝ) (s : ℝ) : e1 L 0 s = 1 := by
  simp [e1]

theorem continuous_e1 (L : ℝ) (m : ℤ) : Continuous (e1 L m) := by
  unfold e1
  fun_prop

theorem e1_eq_exp (L : ℝ) (m : ℤ) (s : ℝ) :
    e1 L m s = Complex.exp (((2 * π / L * m : ℝ) : ℂ) * I * (s : ℂ)) := by
  rw [e1]
  congr 1
  push_cast
  ring

theorem hasDerivAt_e1 (L : ℝ) (m : ℤ) (s : ℝ) :
    HasDerivAt (e1 L m) ((((2 * π / L * m : ℝ) : ℂ) * I) * e1 L m s) s := by
  set c : ℂ := ((2 * π / L * m : ℝ) : ℂ) * I with hc
  have h : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c s := by
    simpa using ((hasDerivAt_id (s : ℂ)).const_mul c).comp_ofReal
  have e : ∀ x, e1 L m x = Complex.exp (c * (x : ℂ)) := fun x => e1_eq_exp L m x
  refine (h.cexp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => e x)).congr_deriv ?_
  rw [e]
  ring

theorem e1_periodic (L : ℝ) (hL : L ≠ 0) (m : ℤ) (s : ℝ) : e1 L m (s + L) = e1 L m s := by
  have h : (((2 * π / L * m * (s + L) : ℝ) : ℂ) * I) =
      (((2 * π / L * m * s : ℝ) : ℂ) * I) + (m : ℂ) * (2 * π * I) := by
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    push_cast
    field_simp
  rw [e1, e1, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `∫₀ᴸ exp(2πims/L) ds = L·[m = 0]`. -/
theorem integral_e1 {L : ℝ} (hL : 0 < L) (m : ℤ) :
    ∫ s in Icc (0 : ℝ) L, e1 L m s = if m = 0 then (L : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le]
  split_ifs with hm
  · subst hm
    simp [e1_zero, intervalIntegral.integral_const]
  · have hc : (((2 * π / L * m : ℝ) : ℂ) * I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      have : (2 * π / L * m : ℝ) ≠ 0 := by
        have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
        have : 2 * π / L ≠ 0 := by positivity
        exact mul_ne_zero this hm'
      exact_mod_cast this
    simp_rw [e1_eq_exp]
    rw [integral_exp_mul_complex hc]
    have h1 : (((2 * π / L * m : ℝ) : ℂ) * I) * ((L : ℝ) : ℂ) = (m : ℂ) * (2 * π * I) := by
      have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
    rw [h1, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-! ### Two-dimensional modes and the fundamental box -/

/-- The Fourier mode `e_k(x) = exp(2πi(k₁x₁ + k₂x₂)/L)` on `ℝ²`, `L`-periodic in each variable. -/
noncomputable def emode (L : ℝ) (k : Z2) (x : ℝ × ℝ) : ℂ := e1 L k.1 x.1 * e1 L k.2 x.2

theorem norm_emode (L : ℝ) (k : Z2) (x : ℝ × ℝ) : ‖emode L k x‖ = 1 := by
  rw [emode, norm_mul, norm_e1, norm_e1, mul_one]

theorem emode_add (L : ℝ) (k j : Z2) (x : ℝ × ℝ) :
    emode L (k + j) x = emode L k x * emode L j x := by
  simp only [emode, Prod.fst_add, Prod.snd_add, e1_add]
  ring

theorem emode_neg (L : ℝ) (k : Z2) (x : ℝ × ℝ) :
    emode L (-k) x = (starRingEnd ℂ) (emode L k x) := by
  simp only [emode, Prod.fst_neg, Prod.snd_neg, e1_neg, map_mul]

theorem emode_zero (L : ℝ) (x : ℝ × ℝ) : emode L 0 x = 1 := by
  simp [emode, e1_zero]

theorem emode_sub (L : ℝ) (k j : Z2) (x : ℝ × ℝ) :
    emode L (k - j) x = emode L k x * (starRingEnd ℂ) (emode L j x) := by
  rw [sub_eq_add_neg, emode_add, emode_neg]

theorem continuous_emode (L : ℝ) (k : Z2) : Continuous (emode L k) := by
  unfold emode
  exact ((continuous_e1 L k.1).comp continuous_fst).mul ((continuous_e1 L k.2).comp continuous_snd)

theorem emode_mul_conj (L : ℝ) (k : Z2) (x : ℝ × ℝ) :
    emode L k x * (starRingEnd ℂ) (emode L k x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_emode]
  simp

/-- Lebesgue measure on the fundamental box `[0, L]²`. -/
noncomputable def box (L : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) L)).prod (volume.restrict (Icc (0 : ℝ) L))

instance (L : ℝ) : IsFiniteMeasure (box L) := by
  unfold box
  infer_instance

/-- `∫_{[0,L]²} e_k = L²·[k = 0]`. -/
theorem integral_emode {L : ℝ} (hL : 0 < L) (k : Z2) :
    ∫ x, emode L k x ∂box L = if k = 0 then (L : ℂ) ^ 2 else 0 := by
  unfold emode box
  rw [integral_prod_mul (fun s => e1 L k.1 s) (fun s => e1 L k.2 s), integral_e1 hL,
    integral_e1 hL]
  by_cases h : k = 0
  · subst h
    simp [sq]
  · rw [if_neg h]
    have : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (Prod.ext hc.1 hc.2)
    rcases this with h1 | h2
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h2, mul_zero]

/-! ### Absolutely convergent series -/

/-- Absolutely summable coefficient sequences. -/
def L1 (a : Z2 → ℂ) : Prop := Summable fun k => ‖a k‖

/-- The field `L⁻¹ Σ_k a_k e_k` (orthonormal-basis normalisation). -/
noncomputable def field (L : ℝ) (a : Z2 → ℂ) (x : ℝ × ℝ) : ℂ :=
  (L : ℂ)⁻¹ * ∑' k, a k * emode L k x

variable {L : ℝ}

theorem norm_term (a : Z2 → ℂ) (k : Z2) (x : ℝ × ℝ) : ‖a k * emode L k x‖ = ‖a k‖ := by
  rw [norm_mul, norm_emode, mul_one]

theorem summable_term {a : Z2 → ℂ} (ha : L1 a) (x : ℝ × ℝ) :
    Summable fun k => a k * emode L k x :=
  Summable.of_norm (by simpa only [norm_term] using ha)

theorem continuous_field {a : Z2 → ℂ} (ha : L1 a) : Continuous (field L a) := by
  unfold field
  exact continuous_const.mul (continuous_tsum (fun k => continuous_const.mul (continuous_emode L k))
    ha (fun k x => (norm_term a k x).le))

theorem norm_field_le {a : Z2 → ℂ} (ha : L1 a) (x : ℝ × ℝ) :
    ‖field L a x‖ ≤ |L|⁻¹ * ∑' k, ‖a k‖ := by
  unfold field
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  calc ‖∑' k, a k * emode L k x‖ ≤ ∑' k, ‖a k * emode L k x‖ :=
        norm_tsum_le_tsum_norm (by simpa only [norm_term] using ha)
    _ = ∑' k, ‖a k‖ := by simp only [norm_term]

theorem field_periodic₁ (hL : L ≠ 0) (a : Z2 → ℂ) (x : ℝ × ℝ) :
    field L a (x.1 + L, x.2) = field L a x := by
  simp only [field, emode, e1_periodic L hL]

theorem field_periodic₂ (hL : L ≠ 0) (a : Z2 → ℂ) (x : ℝ × ℝ) :
    field L a (x.1, x.2 + L) = field L a x := by
  simp only [field, emode, e1_periodic L hL]

theorem field_add {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) (x : ℝ × ℝ) :
    field L (a + b) x = field L a x + field L b x := by
  simp only [field, Pi.add_apply, add_mul]
  rw [(summable_term ha x).tsum_add (summable_term hb x), mul_add]

theorem field_sub {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) (x : ℝ × ℝ) :
    field L (a - b) x = field L a x - field L b x := by
  simp only [field, Pi.sub_apply, sub_mul]
  rw [(summable_term ha x).tsum_sub (summable_term hb x), mul_sub]

theorem field_smul (c : ℂ) (a : Z2 → ℂ) (x : ℝ × ℝ) :
    field L (c • a) x = c * field L a x := by
  simp only [field, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [tsum_mul_left]
  ring

theorem L1_add {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) : L1 (a + b) :=
  (ha.add hb).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)

theorem L1_smul (c : ℂ) {a : Z2 → ℂ} (ha : L1 a) : L1 (c • a) := by
  unfold L1
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact ha.mul_left _

/-! ### Reindexing double series along `(k, j) ↦ (k − j, j)` -/

/-- The shear `(k, j) ↦ (k − j, j)` of `ℤ² × ℤ²`. -/
def shear : Z2 × Z2 ≃ Z2 × Z2 where
  toFun p := (p.1 - p.2, p.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem summable_shear {E : Type*} [NormedAddCommGroup E] {F : Z2 × Z2 → E} (hF : Summable F) :
    Summable fun p : Z2 × Z2 => F (p.1 - p.2, p.2) :=
  (shear.summable_iff (f := F)).2 hF

theorem tsum_shear {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {F : Z2 × Z2 → E}
    (hF : Summable F) : ∑' k, ∑' j, F (k - j, j) = ∑' p, F p := by
  rw [← (summable_shear hF).tsum_prod]
  exact shear.tsum_eq F

theorem summable_mul_norm {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) :
    Summable fun p : Z2 × Z2 => ‖a p.1‖ * ‖b p.2‖ := by
  have h := summable_mul_of_summable_norm (f := fun k => ‖a k‖) (g := fun k => ‖b k‖)
    (by simpa using ha) (by simpa using hb)
  simpa using h

/-! ### Products and conjugates -/

/-- The coefficients `L⁻¹ Σ_j a_{k−j} b_j` of the product of two series. -/
noncomputable def pr (L : ℝ) (a b : Z2 → ℂ) (k : Z2) : ℂ := (L : ℂ)⁻¹ * ∑' j, a (k - j) * b j

/-- The coefficients `conj (a (−k))` of the complex conjugate. -/
noncomputable def rev (a : Z2 → ℂ) (k : Z2) : ℂ := (starRingEnd ℂ) (a (-k))

theorem summable_conv_norm {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) :
    Summable fun p : Z2 × Z2 => ‖a (p.1 - p.2)‖ * ‖b p.2‖ :=
  summable_shear (F := fun p : Z2 × Z2 => ‖a p.1‖ * ‖b p.2‖) (summable_mul_norm ha hb)

theorem summable_conv_fiber {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) (k : Z2) :
    Summable fun j => a (k - j) * b j :=
  Summable.of_norm (by
    simpa only [norm_mul] using (summable_conv_norm ha hb).prod_factor k)

theorem norm_pr_le {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) (k : Z2) :
    ‖pr L a b k‖ ≤ |L|⁻¹ * ∑' j, ‖a (k - j)‖ * ‖b j‖ := by
  unfold pr
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  calc ‖∑' j, a (k - j) * b j‖ ≤ ∑' j, ‖a (k - j) * b j‖ :=
        norm_tsum_le_tsum_norm (by
          simpa only [norm_mul] using (summable_conv_norm ha hb).prod_factor k)
    _ = ∑' j, ‖a (k - j)‖ * ‖b j‖ := by simp only [norm_mul]

theorem L1_pr {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) : L1 (pr L a b) := by
  have hs : Summable fun k => |L|⁻¹ * ∑' j, ‖a (k - j)‖ * ‖b j‖ :=
    ((summable_conv_norm ha hb).prod).mul_left _
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_pr_le ha hb k)

theorem tsum_norm_pr_le {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) :
    ∑' k, ‖pr L a b k‖ ≤ |L|⁻¹ * ((∑' k, ‖a k‖) * ∑' k, ‖b k‖) := by
  have hs : Summable fun k => |L|⁻¹ * ∑' j, ‖a (k - j)‖ * ‖b j‖ :=
    ((summable_conv_norm ha hb).prod).mul_left _
  calc ∑' k, ‖pr L a b k‖ ≤ ∑' k, |L|⁻¹ * ∑' j, ‖a (k - j)‖ * ‖b j‖ :=
        (L1_pr ha hb).tsum_le_tsum (fun k => norm_pr_le ha hb k) hs
    _ = |L|⁻¹ * ∑' k, ∑' j, ‖a (k - j)‖ * ‖b j‖ := tsum_mul_left
    _ = |L|⁻¹ * ((∑' k, ‖a k‖) * ∑' k, ‖b k‖) := by
        rw [tsum_shear (F := fun p : Z2 × Z2 => ‖a p.1‖ * ‖b p.2‖) (summable_mul_norm ha hb),
          tsum_mul_tsum_of_summable_norm (by simpa using ha) (by simpa using hb)]

theorem tsum_mul_series {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) (x : ℝ × ℝ) :
    (∑' k, a k * emode L k x) * (∑' k, b k * emode L k x) =
      ∑' k, (∑' j, a (k - j) * b j) * emode L k x := by
  have hA : Summable fun k => ‖a k * emode L k x‖ := by simpa only [norm_term] using ha
  have hB : Summable fun k => ‖b k * emode L k x‖ := by simpa only [norm_term] using hb
  have hprod : Summable fun p : Z2 × Z2 => a p.1 * emode L p.1 x * (b p.2 * emode L p.2 x) :=
    summable_mul_of_summable_norm (f := fun k => a k * emode L k x)
      (g := fun k => b k * emode L k x) hA hB
  rw [tsum_mul_tsum_of_summable_norm (f := fun k => a k * emode L k x)
      (g := fun k => b k * emode L k x) hA hB]
  rw [← tsum_shear (F := fun p : Z2 × Z2 => a p.1 * emode L p.1 x * (b p.2 * emode L p.2 x)) hprod]
  refine tsum_congr fun k => ?_
  rw [← tsum_mul_right]
  refine tsum_congr fun j => ?_
  have : emode L k x = emode L (k - j) x * emode L j x := by
    rw [← emode_add, sub_add_cancel]
  rw [this]
  ring

/-- **Product of two absolutely convergent series** (Cauchy product on `ℤ²`). -/
theorem field_mul {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) (x : ℝ × ℝ) :
    field L a x * field L b x = field L (pr L a b) x := by
  unfold field pr
  have e : (L : ℂ)⁻¹ * (∑' k, a k * emode L k x) * ((L : ℂ)⁻¹ * ∑' k, b k * emode L k x) =
      (L : ℂ)⁻¹ * ((L : ℂ)⁻¹ * ((∑' k, a k * emode L k x) * (∑' k, b k * emode L k x))) := by
    ring
  rw [e, tsum_mul_series ha hb, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  ring

theorem L1_rev {a : Z2 → ℂ} (ha : L1 a) : L1 (rev a) := by
  unfold L1 rev
  simp only [Complex.norm_conj]
  exact (Equiv.neg Z2).summable_iff.2 ha

theorem rev_rev (a : Z2 → ℂ) : rev (rev a) = a := by
  funext k
  simp [rev]

/-- **Complex conjugate of a series.** -/
theorem field_rev (a : Z2 → ℂ) (x : ℝ × ℝ) :
    field L (rev a) x = (starRingEnd ℂ) (field L a x) := by
  unfold field rev
  rw [map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_tsum]
  congr 1
  rw [← (Equiv.neg Z2).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply, neg_neg, emode_neg]
  rw [map_mul]

/-! ### Integrals, Parseval and Fourier coefficients -/

theorem integral_term {L : ℝ} (hL : 0 < L) (a : Z2 → ℂ) (k : Z2) :
    ∫ x, a k * emode L k x ∂box L = a k * (if k = 0 then (L : ℂ) ^ 2 else 0) := by
  rw [integral_const_mul, integral_emode hL]

/-- `∫_{[0,L]²} field L a = L · a₀`. -/
theorem integral_field {L : ℝ} (hL : 0 < L) {a : Z2 → ℂ} (ha : L1 a) :
    ∫ x, field L a x ∂box L = (L : ℂ) * a 0 := by
  unfold field
  rw [integral_const_mul]
  have hmeas : ∀ k, AEStronglyMeasurable (fun x => a k * emode L k x) (box L) :=
    fun k => (continuous_const.mul (continuous_emode L k)).aestronglyMeasurable
  have hfin : ∑' k, ∫⁻ x, ‖a k * emode L k x‖ₑ ∂box L ≠ ∞ := by
    have e : ∀ k, ∫⁻ x, ‖a k * emode L k x‖ₑ ∂box L = ‖a k‖ₑ * box L univ := by
      intro k
      have : (fun x => ‖a k * emode L k x‖ₑ) = fun _ => ‖a k‖ₑ := by
        funext x
        rw [enorm_mul, ← ofReal_norm_eq_enorm (emode L k x), norm_emode, ENNReal.ofReal_one,
          mul_one]
      rw [this, lintegral_const]
    simp_rw [e]
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ (measure_ne_top _ _)
    have hs : Summable fun k => ‖a k‖₊ := by
      rw [← NNReal.summable_coe]
      simpa using ha
    simpa [enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.2 hs
  rw [integral_tsum hmeas hfin]
  simp_rw [integral_term hL]
  rw [tsum_eq_single 0 (fun k hk => by rw [if_neg hk, mul_zero])]
  simp only [if_true]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

/-- **Parseval** for absolutely convergent series:
`∫_{[0,L]²} conj(field a) · field b = Σ_k conj(a_k) b_k`. -/
theorem integral_conj_mul {L : ℝ} (hL : 0 < L) {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b) :
    ∫ x, (starRingEnd ℂ) (field L a x) * field L b x ∂box L =
      ∑' k, (starRingEnd ℂ) (a k) * b k := by
  have e : (fun x => (starRingEnd ℂ) (field L a x) * field L b x) =
      field L (pr L (rev a) b) := by
    funext x
    rw [← field_rev, field_mul (L1_rev ha) hb]
  rw [e, integral_field hL (L1_pr (L1_rev ha) hb)]
  unfold pr rev
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [← mul_assoc, mul_inv_cancel₀ hL0, one_mul]
  refine tsum_congr fun k => ?_
  simp

/-- `∫_{[0,L]²} |field a|² = Σ_k |a_k|²`. -/
theorem integral_norm_sq {L : ℝ} (hL : 0 < L) {a : Z2 → ℂ} (ha : L1 a) :
    ∫ x, ‖field L a x‖ ^ 2 ∂box L = ∑' k, ‖a k‖ ^ 2 := by
  have h := integral_conj_mul hL ha ha
  have e1 : ∀ x, (starRingEnd ℂ) (field L a x) * field L a x = ((‖field L a x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : ∀ k, (starRingEnd ℂ) (a k) * a k = ((‖a k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e1, e2] at h
  rw [integral_complex_ofReal, ← Complex.ofReal_tsum] at h
  exact_mod_cast h

/-- The Fourier coefficient `L⁻¹ ∫_{[0,L]²} f · conj(e_k)` (orthonormal-basis normalisation). -/
noncomputable def fc (L : ℝ) (f : ℝ × ℝ → ℂ) (k : Z2) : ℂ :=
  (L : ℂ)⁻¹ * ∫ x, f x * (starRingEnd ℂ) (emode L k x) ∂box L

theorem field_mul_conj_emode (a : Z2 → ℂ) (k : Z2) (x : ℝ × ℝ) :
    field L a x * (starRingEnd ℂ) (emode L k x) = field L (fun j => a (j + k)) x := by
  unfold field
  rw [mul_assoc, ← tsum_mul_right]
  congr 1
  rw [← (Equiv.addRight k).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.coe_addRight]
  rw [emode_add, mul_assoc, mul_assoc, emode_mul_conj, mul_one]

/-- **Fourier coefficients of a series** are its coefficients. -/
theorem fc_field {L : ℝ} (hL : 0 < L) {a : Z2 → ℂ} (ha : L1 a) (k : Z2) :
    fc L (field L a) k = a k := by
  have hs : L1 fun j => a (j + k) := (Equiv.addRight k).summable_iff.2 ha
  unfold fc
  simp_rw [field_mul_conj_emode a k]
  rw [integral_field hL hs]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [zero_add, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul]

/-- Uniqueness of coefficients. -/
theorem coeff_unique {L : ℝ} (hL : 0 < L) {a b : Z2 → ℂ} (ha : L1 a) (hb : L1 b)
    (h : field L a = field L b) : a = b := by
  funext k
  rw [← fc_field hL ha k, ← fc_field hL hb k, h]

/-! ### Classical derivatives of series -/

/-- First wave-vector component `ξ_{k,1} = 2πk₁/L`. -/
noncomputable def xi1 (L : ℝ) (k : Z2) : ℝ := 2 * π / L * k.1

/-- Second wave-vector component `ξ_{k,2} = 2πk₂/L`. -/
noncomputable def xi2 (L : ℝ) (k : Z2) : ℝ := 2 * π / L * k.2

/-- `|ξ_k|²`, the symbol of `−Δ`. -/
noncomputable def qf (L : ℝ) (k : Z2) : ℝ := xi1 L k ^ 2 + xi2 L k ^ 2

theorem qf_nonneg (L : ℝ) (k : Z2) : 0 ≤ qf L k := by unfold qf; positivity

theorem abs_xi1_le (L : ℝ) (k : Z2) : |xi1 L k| ≤ 1 + qf L k := by
  unfold qf
  nlinarith [sq_nonneg (xi2 L k), sq_abs (xi1 L k),
    abs_nonneg (xi1 L k), sq_nonneg (|xi1 L k| - 1)]

theorem abs_xi2_le (L : ℝ) (k : Z2) : |xi2 L k| ≤ 1 + qf L k := by
  unfold qf
  nlinarith [sq_nonneg (xi1 L k), sq_abs (xi2 L k), abs_nonneg (xi2 L k),
    sq_nonneg (|xi2 L k| - 1)]

theorem hasDerivAt_emode₁ (L : ℝ) (k : Z2) (x2 s : ℝ) :
    HasDerivAt (fun s => emode L k (s, x2)) ((I * xi1 L k) * emode L k (s, x2)) s := by
  have h := (hasDerivAt_e1 L k.1 s).mul_const (e1 L k.2 x2)
  convert h using 1
  simp only [emode, xi1]
  push_cast
  ring

theorem hasDerivAt_emode₂ (L : ℝ) (k : Z2) (x1 s : ℝ) :
    HasDerivAt (fun s => emode L k (x1, s)) ((I * xi2 L k) * emode L k (x1, s)) s := by
  have h := (hasDerivAt_e1 L k.2 s).const_mul (e1 L k.1 x1)
  convert h using 1
  simp only [emode, xi2]
  push_cast
  ring

/-- Termwise differentiation in `x₁`. -/
theorem hasDerivAt_field₁ {a : Z2 → ℂ} (ha : L1 a) (ha1 : L1 fun k => (I * xi1 L k) * a k)
    (x : ℝ × ℝ) :
    HasDerivAt (fun s => field L a (s, x.2)) (field L (fun k => (I * xi1 L k) * a k) x) x.1 := by
  have h := hasDerivAt_tsum (u := fun k => ‖(I * xi1 L k) * a k‖)
    (g := fun k s => a k * emode L k (s, x.2))
    (g' := fun k s => a k * ((I * xi1 L k) * emode L k (s, x.2))) ha1
    (fun k s => (hasDerivAt_emode₁ L k x.2 s).const_mul (a k))
    (fun k s => by
      show ‖a k * ((I * xi1 L k) * emode L k (s, x.2))‖ ≤ ‖(I * xi1 L k) * a k‖
      exact le_of_eq (by simp only [norm_mul, norm_emode, mul_one]; ring_nf))
    (summable_term ha (x.1, x.2)) x.1
  unfold field
  convert h.const_mul ((L : ℂ)⁻¹) using 2
  refine tsum_congr fun k => ?_
  ring

/-- Termwise differentiation in `x₂`. -/
theorem hasDerivAt_field₂ {a : Z2 → ℂ} (ha : L1 a) (ha2 : L1 fun k => (I * xi2 L k) * a k)
    (x : ℝ × ℝ) :
    HasDerivAt (fun s => field L a (x.1, s)) (field L (fun k => (I * xi2 L k) * a k) x) x.2 := by
  have h := hasDerivAt_tsum (u := fun k => ‖(I * xi2 L k) * a k‖)
    (g := fun k s => a k * emode L k (x.1, s))
    (g' := fun k s => a k * ((I * xi2 L k) * emode L k (x.1, s))) ha2
    (fun k s => (hasDerivAt_emode₂ L k x.1 s).const_mul (a k))
    (fun k s => by
      show ‖a k * ((I * xi2 L k) * emode L k (x.1, s))‖ ≤ ‖(I * xi2 L k) * a k‖
      exact le_of_eq (by simp only [norm_mul, norm_emode, mul_one]; ring_nf))
    (summable_term ha (x.1, x.2)) x.2
  unfold field
  convert h.const_mul ((L : ℂ)⁻¹) using 2
  refine tsum_congr fun k => ?_
  ring

theorem d1_field {a : Z2 → ℂ} (ha : L1 a) (ha1 : L1 fun k => (I * xi1 L k) * a k) :
    PVNP.WCTPlaneWave.d1 (field L a) = field L (fun k => (I * xi1 L k) * a k) := by
  funext x
  exact (hasDerivAt_field₁ ha ha1 x).deriv

theorem d2_field {a : Z2 → ℂ} (ha : L1 a) (ha2 : L1 fun k => (I * xi2 L k) * a k) :
    PVNP.WCTPlaneWave.d2 (field L a) = field L (fun k => (I * xi2 L k) * a k) := by
  funext x
  exact (hasDerivAt_field₂ ha ha2 x).deriv

/-- Summability with the weight `1 + |ξ|²`, enough for two classical derivatives. -/
def L1q (L : ℝ) (a : Z2 → ℂ) : Prop := Summable fun k => (1 + qf L k) * ‖a k‖

theorem L1q.l1 {a : Z2 → ℂ} (h : L1q L a) : L1 a :=
  h.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => le_mul_of_one_le_left (norm_nonneg _) (by linarith [qf_nonneg L k]))

theorem L1q.mul_bound {a : Z2 → ℂ} (h : L1q L a) (m : Z2 → ℂ) (hm : ∀ k, ‖m k‖ ≤ 1 + qf L k) :
    L1 fun k => m k * a k :=
  h.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _))

theorem norm_I_xi1 (L : ℝ) (k : Z2) : ‖I * (xi1 L k : ℂ)‖ = |xi1 L k| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_I_xi2 (L : ℝ) (k : Z2) : ‖I * (xi2 L k : ℂ)‖ = |xi2 L k| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **The classical Laplacian of a series is the Fourier multiplier `−|ξ|²`.** -/
theorem lap_field {a : Z2 → ℂ} (h : L1q L a) :
    PVNP.WCTPlaneWave.lap (field L a) = field L (fun k => -(qf L k : ℂ) * a k) := by
  have h1 : L1 fun k => (I * xi1 L k) * a k :=
    h.mul_bound _ (fun k => by rw [norm_I_xi1]; exact abs_xi1_le L k)
  have h2 : L1 fun k => (I * xi2 L k) * a k :=
    h.mul_bound _ (fun k => by rw [norm_I_xi2]; exact abs_xi2_le L k)
  have h11 : L1 fun k => (I * xi1 L k) * ((I * xi1 L k) * a k) :=
    h.mul_bound (fun k => (I * xi1 L k) * (I * xi1 L k)) (fun k => by
      rw [norm_mul, norm_I_xi1, ← sq, sq_abs]; unfold qf; nlinarith [sq_nonneg (xi2 L k)])
      |>.congr fun k => by ring_nf
  have h22 : L1 fun k => (I * xi2 L k) * ((I * xi2 L k) * a k) :=
    h.mul_bound (fun k => (I * xi2 L k) * (I * xi2 L k)) (fun k => by
      rw [norm_mul, norm_I_xi2, ← sq, sq_abs]; unfold qf; nlinarith [sq_nonneg (xi1 L k)])
      |>.congr fun k => by ring_nf
  funext x
  simp only [PVNP.WCTPlaneWave.lap]
  rw [d1_field h.l1 h1, d1_field h1 h11, d2_field h.l1 h2, d2_field h2 h22,
    ← field_add h11 h22]
  congr 1
  funext k
  simp only [Pi.add_apply, qf]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end PVNP.Torus
