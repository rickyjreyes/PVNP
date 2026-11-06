import PVNP.TorusMult
import PVNP.ContinuumFluxBudget

/-!
# F-1: the continuum flux inequality `|J'(t)| ≤ Γ √D(t)` on `T_L²`, derived from the PDE

**Detector.**  A real weight `χ ∈ H²(T_L²)` given by an `ℓ2` state `χv` whose coefficients
`c = co L χv` satisfy `Σ_k (1 + |ξ_k|²)|c_k| < ∞` (`L1q`, so `χ` has two classical derivatives
given by absolutely convergent series) and `rev c = c` (`χ` is real-valued).  The constants are
`a ≥ sup_x |∇χ(x)|` and `b ≥ sup_x |Δχ(x)|`, stated for the **classical** derivatives
`WCTPlaneWave.d1`, `d2`, `lap` of `χ = field L c`.

**Readout.** `Jdet L χv v = ∫_{[0,L]²} χ(x) |ψ(x)|² dx` (`ψ = field L (co L v)`), literally the
localized mass of `pvnp/proofs/wct-pde-transport-bound.md` §3.

**Results** (along every `H²` solution, every `L > 0`):

* `flux_identity`: `J'(t) = Jdot(ψ(t)) = 2 Im ⟨(Δ+κ)(χψ), (Δ+κ)ψ⟩_{L²}` — derived from the
  equation; the cubic–quintic term drops out because it is a real multiple of `ψ`;
* `flux_static`: `|J'| ≤ (4aG + 2bP)D + 4|κ|aPG` with `P = ‖ψ‖₂`, `G = ‖∇ψ‖₂`, `D = ‖Δψ‖₂`
  (the commutator `[Δ, χ]ψ = (Δχ)ψ + 2∇χ·∇ψ` and the sup-norm bounds of `PVNP.TorusMult`);
* `flux_inequality`: `|J'(t)| ≤ Γ √D(t)` with
  `Γ = ContinuumFlux.budget a b κ P₀ D₀ = 4a√P₀ D₀ + 2bP₀√D₀ + 4|κ|aP₀√P₀`,
  `P₀ = ‖ψ(0)‖₂`, `D₀ = √(H₀ + 3β²M₀/16γ) + |κ|P₀` — exactly the constant of the analytic
  supplement, with `D = ‖Δψ‖₂` the norm (not its square);
* `curvature_time_bound`: `∫₀ᵀ ‖Δψ(t)‖²₂ dt ≥ δ⁴/(Γ⁴T³)` whenever the detected mass changes by
  `δ`, **with no flux premise** (`TransportCalculus.curvature_time_lower_bound` applied to the
  derived inequality).

`Γ` depends on `L` only through the detector constants `a, b` and the conserved `M₀, H₀`; the
estimate `|J'| ≤ Γ D` (without the square root) is not claimed.
-/

open Complex Set Filter Topology InnerProductSpace MeasureTheory
open scoped Real ENNReal NNReal

namespace PVNP.Torus

variable {L κ β γ : ℝ}

attribute [local irreducible] U Fnl

/-! ### The readout -/

/-- The localized mass `J = ∫_{[0,L]²} χ |ψ|²` of the field represented by `v`. -/
noncomputable def Jdet (L : ℝ) (χv v : ℓ2) : ℝ :=
  ∫ x, (field L (co L χv) x).re * ‖field L (co L v) x‖ ^ 2 ∂box L

/-- The flux `J' = 2 Im ⟨(Δ+κ)(χψ), (Δ+κ)ψ⟩`. -/
noncomputable def Jdot (L κ : ℝ) (χv v : ℓ2) : ℝ :=
  2 * (inner ℂ (Ac L κ (mulH L χv v)) (Ac L κ v)).im

theorem field_re_of_rev {c : Z2 → ℂ} (hreal : rev c = c) (x : ℝ × ℝ) :
    field L c x = ((field L c x).re : ℂ) := by
  apply Complex.ext
  · simp
  · have h := field_real_of_rev (L := L) hreal x
    have : (field L c x).im = -(field L c x).im := by
      conv_lhs => rw [← h]
      simp
    simp; linarith

/-- `⟨x, χy⟩ = ⟨χx, y⟩` for a real weight. -/
theorem inner_mulH_symm (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv) (x y : ℓ2) :
    inner ℂ (Lc L x) (Lc L (mulH L χv y)) = inner ℂ (Lc L (mulH L χv x)) (Lc L y) := by
  rw [inner_Lc, inner_Lc, ← integral_conj_mul hL (L1_co' hL x) (L1_co' hL _),
    ← integral_conj_mul hL (L1_co' hL _) (L1_co' hL y)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [field_mulH hL, map_mul, field_real_of_rev hreal]
  ring

/-- `J` as an `L²` inner product. -/
theorem Jdet_eq (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv) (v : ℓ2) :
    ((Jdet L χv v : ℝ) : ℂ) = inner ℂ (Lc L v) (Lc L (mulH L χv v)) := by
  rw [inner_Lc, ← integral_conj_mul hL (L1_co' hL v) (L1_co' hL _), Jdet,
    ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [field_mulH hL]
  rw [field_re_of_rev hreal z, mul_comm (((field L (co L χv) z).re : ℂ)), ← mul_assoc,
    mul_comm _ (field L (co L v) z), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_re]
  push_cast
  ring

theorem Jdet_eq_re (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv) (v : ℓ2) :
    Jdet L χv v = (inner ℂ (Lc L v) (Lc L (mulH L χv v))).re := by
  rw [← Jdet_eq hL hreal, Complex.ofReal_re]

/-! ### The flux identity -/

/-- `Re ⟨χψ, −i F(ψ)⟩ = 0`: the nonlinearity does not contribute to the flux. -/
theorem re_inner_mulH_Fnl (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv) (u : ℓ2) :
    (inner ℂ (Lc L (mulH L χv u)) (Lc L ((-I) • Fnl L β γ u))).re = 0 := by
  rw [map_smul, inner_smul_right, re_neg_I_mul, inner_Lc,
    ← integral_conj_mul hL (L1_co' hL _) (L1_co' hL _)]
  have e : (fun x => (starRingEnd ℂ) (field L (co L (mulH L χv u)) x) *
      field L (co L (Fnl L β γ u)) x) = fun x =>
      ((((field L (co L χv) x).re * (-β * ‖field L (co L u) x‖ ^ 4 +
        γ * ‖field L (co L u) x‖ ^ 6)) : ℝ) : ℂ) := by
    funext x
    rw [field_mulH hL, field_Fnl hL, map_mul, field_real_of_rev hreal, mul_assoc,
      conj_mul_fnl, field_re_of_rev hreal x]
    simp only [Complex.ofReal_re]
    push_cast
    ring
  rw [e, integral_complex_ofReal, Complex.ofReal_im]

/-- `‖χ δ‖_{L²} ≤ L⁻¹ ‖ĉ‖₁ ‖δ‖_{L²}`. -/
theorem norm_Lc_mulH_le (hL : 0 < L) (χv δ : ℓ2) :
    ‖Lc L (mulH L χv δ)‖ ≤ L⁻¹ * (∑' j, ‖co L χv j‖) * ‖Lc L δ‖ := by
  have hc := L1_co' hL χv
  have e : Lc L (mulH L χv δ) = Mc L (co L χv) (Lc L δ) := by
    ext k
    rw [Lc_apply, co_mulH hL, Mc_apply_pr hc]
    unfold pr
    congr 2
    funext j
    rw [Lc_apply]
  rw [e]
  have h := norm_Mc_le (L := L) hc (Lc L δ)
  rwa [abs_of_pos hL] at h

/-- **The flux identity, derived from the PDE**: `J'(t) = 2 Im ⟨(Δ+κ)(χψ), (Δ+κ)ψ⟩`. -/
theorem flux_identity (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv) {u : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u) (t : ℝ) :
    HasDerivAt (fun s => Jdet L χv (u s)) (Jdot L κ χv (u t)) t := by
  set w : ℝ → ℓ2 := fun s => U L κ (-s) (u s) with hw_def
  have hw : ∀ s, HasDerivAt w (Gf L κ β γ s (w s)) s := ode_of_isSolution hL hu
  have huw : ∀ s, u s = U L κ s (w s) := fun s => by rw [hw_def]; simp only [U_U_neg]
  set f := mulH L χv (u t) with hf
  -- the linear part
  have hφ := hasDerivAt_inner_U (L := L) (κ := κ) f (hw t)
  set φ : ℝ → ℂ := fun s => inner ℂ (Lc L f) (Lc L (U L κ s (w s)))
  have hφ' : HasDerivAt (fun s => 2 * (φ s - φ t).re)
      (2 * (inner ℂ (Lc L f) (Lc L (U L κ t (Gf L κ β γ t (w t)))) +
        Lw L κ f (U L κ t (w t))).re) t := by
    have h1 := hφ.sub_const (φ t)
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1).const_mul 2
  -- the remainder
  set C := L⁻¹ * (∑' j, ‖co L χv j‖)
  have hrem : HasDerivAt (fun s => (inner ℂ (Lc L (u s - u t)) (Lc L (mulH L χv (u s - u t)))).re)
      0 t := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hlim := (tendsto_norm_sq_div (L := L) (κ := κ) (hw t)).const_mul C
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with h hh0
    have hh' : 0 < |h| := abs_pos.2 hh0
    simp only [sub_self, map_zero, inner_zero_left, Complex.zero_re, sub_zero]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, inv_mul_eq_div,
      huw (t + h), huw t]
    rw [div_le_iff₀ hh', mul_div_assoc', div_mul_cancel₀ _ hh'.ne']
    set δ := U L κ (t + h) (w (t + h)) - U L κ t (w t)
    have h1 : |(inner ℂ (Lc L δ) (Lc L (mulH L χv δ))).re| ≤ ‖Lc L δ‖ * (C * ‖Lc L δ‖) :=
      (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (norm_Lc_mulH_le hL χv δ) (norm_nonneg _)))
    have e : Lc L δ = Lc L (U L κ (t + h) (w (t + h))) - Lc L (U L κ t (w t)) := map_sub _ _ _
    rw [← e]
    linarith [h1]
  -- the algebraic identity
  have hid : ∀ s, Jdet L χv (u s) = Jdet L χv (u t) + 2 * (φ s - φ t).re +
      (inner ℂ (Lc L (u s - u t)) (Lc L (mulH L χv (u s - u t)))).re := by
    intro s
    have e1 : u s = u t + (u s - u t) := by abel
    rw [Jdet_eq_re hL hreal, Jdet_eq_re hL hreal]
    have hφs : φ s - φ t = inner ℂ (Lc L f) (Lc L (u s - u t)) := by
      simp only [φ, ← huw, map_sub, inner_sub_right]
    rw [hφs]
    conv_lhs => rw [e1]
    rw [map_add, mulH_add_right hL, map_add, inner_add_left, inner_add_right, inner_add_right,
      inner_mulH_symm hL hreal (u t) (u s - u t), ← hf]
    have hc := inner_conj_symm (𝕜 := ℂ) (Lc L f) (Lc L (u s - u t))
    simp only [Complex.add_re]
    rw [← hc, Complex.conj_re]
    ring
  have hsum := ((hasDerivAt_const t (Jdet L χv (u t))).add hφ').add hrem
  simp only [zero_add, add_zero] at hsum
  have hfun : (fun s => Jdet L χv (u s)) = fun s => Jdet L χv (u t) + 2 * (φ s - φ t).re +
      (inner ℂ (Lc L (u s - u t)) (Lc L (mulH L χv (u s - u t)))).re := funext hid
  rw [hfun]
  convert hsum using 1
  -- evaluate the derivative
  rw [U_Gf, ← huw t, Complex.add_re, re_inner_mulH_Fnl hL hreal, zero_add, Lw, re_neg_I_mul]
  rfl

/-! ### The commutator `[Δ, χ]ψ = (Δχ)ψ + 2∇χ·∇ψ` -/

/-- Coefficients of `Δχ`. -/
noncomputable def cq (L : ℝ) (c : Z2 → ℂ) (k : Z2) : ℂ := -(qf L k : ℂ) * c k

/-- Coefficients of `∂₁χ`. -/
noncomputable def c1 (L : ℝ) (c : Z2 → ℂ) (k : Z2) : ℂ := (I * xi1 L k) * c k

/-- Coefficients of `∂₂χ`. -/
noncomputable def c2 (L : ℝ) (c : Z2 → ℂ) (k : Z2) : ℂ := (I * xi2 L k) * c k

theorem L1_cq {c : Z2 → ℂ} (hq : L1q L c) : L1 (cq L c) :=
  hq.mul_bound _ (fun k => by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (qf_nonneg L k)]; linarith)

theorem L1_c1 {c : Z2 → ℂ} (hq : L1q L c) : L1 (c1 L c) :=
  hq.mul_bound _ (fun k => by rw [norm_I_xi1]; exact abs_xi1_le L k)

theorem L1_c2 {c : Z2 → ℂ} (hq : L1q L c) : L1 (c2 L c) :=
  hq.mul_bound _ (fun k => by rw [norm_I_xi2]; exact abs_xi2_le L k)

theorem rev_cq {c : Z2 → ℂ} (hreal : rev c = c) : rev (cq L c) = cq L c := by
  funext k
  have h := congrFun hreal k
  simp only [rev] at h ⊢
  simp only [cq, map_mul, map_neg, Complex.conj_ofReal, qf_neg, h]

theorem field_cq {c : Z2 → ℂ} (hq : L1q L c) :
    field L (cq L c) = PVNP.WCTPlaneWave.lap (field L c) := (lap_field hq).symm

theorem field_c1 {c : Z2 → ℂ} (hq : L1q L c) :
    field L (c1 L c) = PVNP.WCTPlaneWave.d1 (field L c) := (d1_field hq.l1 (L1_c1 hq)).symm

theorem field_c2 {c : Z2 → ℂ} (hq : L1q L c) :
    field L (c2 L c) = PVNP.WCTPlaneWave.d2 (field L c) := (d2_field hq.l1 (L1_c2 hq)).symm

theorem summable_pr_l2 {d : Z2 → ℂ} (hd : L1 d) (y : ℓ2) (k : Z2) :
    Summable fun j => d (k - j) * y j := by
  have h := summable_conv_l2 hd y k
  rw [← (Equiv.subLeft k).summable_iff] at h
  refine h.congr fun j => ?_
  simp only [Function.comp, Equiv.subLeft_apply, sub_sub_cancel]

theorem xi1_sub_add (L : ℝ) (k j : Z2) : xi1 L k = xi1 L (k - j) + xi1 L j := by
  rw [← xi1_add, sub_add_cancel]

theorem xi2_sub_add (L : ℝ) (k j : Z2) : xi2 L k = xi2 L (k - j) + xi2 L j := by
  rw [← xi2_add, sub_add_cancel]

/-- **Commutator decomposition**, coefficientwise:
`(Δ+κ)(χψ) = χ (Δ+κ)ψ + (Δχ)ψ + 2(∂₁χ ∂₁ψ + ∂₂χ ∂₂ψ)`. -/
theorem Ac_mulH_eq (hL : 0 < L) (κ : ℝ) {χv : ℓ2} (hq : L1q L (co L χv)) (v : ℓ2) :
    Ac L κ (mulH L χv v) = Mc L (co L χv) (Ac L κ v) +
      (Mc L (cq L (co L χv)) (Lc L v) +
        (2 : ℂ) • (Mc L (c1 L (co L χv)) (G1c L v) + Mc L (c2 L (co L χv)) (G2c L v))) := by
  have hc := hq.l1
  ext k
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Ac_apply, co_mulH hL, Mc_apply_pr hc, Mc_apply_pr (L1_cq hq), Mc_apply_pr (L1_c1 hq),
    Mc_apply_pr (L1_c2 hq)]
  unfold pr
  have s0 := summable_pr_l2 hc (Ac L κ v) k
  have s1 := summable_pr_l2 (L1_cq hq) (Lc L v) k
  have s2 := summable_pr_l2 (L1_c1 hq) (G1c L v) k
  have s3 := summable_pr_l2 (L1_c2 hq) (G2c L v) k
  rw [mul_left_comm, ← tsum_mul_left]
  rw [show (L : ℂ)⁻¹ * ∑' j, co L χv (k - j) * (Ac L κ v) j +
      ((L : ℂ)⁻¹ * ∑' j, cq L (co L χv) (k - j) * (Lc L v) j +
        2 * ((L : ℂ)⁻¹ * ∑' j, c1 L (co L χv) (k - j) * (G1c L v) j +
          (L : ℂ)⁻¹ * ∑' j, c2 L (co L χv) (k - j) * (G2c L v) j)) =
      (L : ℂ)⁻¹ * ∑' j, (co L χv (k - j) * (Ac L κ v) j +
        (cq L (co L χv) (k - j) * (Lc L v) j +
          2 * (c1 L (co L χv) (k - j) * (G1c L v) j + c2 L (co L χv) (k - j) * (G2c L v) j))) by
    rw [s0.tsum_add (s1.add ((s2.add s3).mul_left 2)), s1.tsum_add ((s2.add s3).mul_left 2),
      tsum_mul_left, s2.tsum_add s3]
    ring]
  congr 1
  refine tsum_congr fun j => ?_
  rw [Ac_apply, Lc_apply, G1c_apply, G2c_apply]
  simp only [cq, c1, c2, qf]
  have h1 := xi1_sub_add L k j
  have h2 := xi2_sub_add L k j
  rw [h1, h2]
  push_cast
  linear_combination (-2 * (xi1 L (k - j) : ℂ) * (xi1 L j : ℂ) * co L χv (k - j) * co L v j -
    2 * (xi2 L (k - j) : ℂ) * (xi2 L j : ℂ) * co L χv (k - j) * co L v j) * Complex.I_sq

/-! ### The static flux bound -/

/-- The `L²` norm of `∇ψ`. -/
noncomputable def gradN (L : ℝ) (v : ℓ2) : ℝ := Real.sqrt (‖G1c L v‖ ^ 2 + ‖G2c L v‖ ^ 2)

/-- **Static flux bound**: `|J'| ≤ (4aG + 2bP)D + 4|κ|aPG` with `P = ‖ψ‖₂`, `G = ‖∇ψ‖₂`,
`D = ‖Δψ‖₂`, `a ≥ sup|∇χ|`, `b ≥ sup|Δχ|` (classical derivatives of `χ`). -/
theorem flux_static (hL : 0 < L) (κ : ℝ) {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv) {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ x, ‖PVNP.WCTPlaneWave.d1 (field L (co L χv)) x‖ ^ 2 +
      ‖PVNP.WCTPlaneWave.d2 (field L (co L χv)) x‖ ^ 2 ≤ a ^ 2)
    (hb : ∀ x, ‖PVNP.WCTPlaneWave.lap (field L (co L χv)) x‖ ≤ b) (v : ℓ2) :
    |Jdot L κ χv v| ≤ (4 * a * gradN L v + 2 * b * ‖Lc L v‖) * ‖Dc L v‖ +
      4 * |κ| * a * ‖Lc L v‖ * gradN L v := by
  set c := co L χv
  set Kq := Mc L (cq L c) (Lc L v)
  set V := Mc L (c1 L c) (G1c L v) + Mc L (c2 L c) (G2c L v)
  have hV : ‖V‖ ≤ a * gradN L v := by
    have h := norm_Mc2_le_sup hL (L1_c1 hq) (L1_c2 hq) ha0
      (fun x => by rw [field_c1 hq, field_c2 hq]; exact ha x) (G1c L v) (G2c L v)
    exact h
  have hK : ‖Kq‖ ≤ b * ‖Lc L v‖ :=
    norm_Mc_le_sup hL (L1_cq hq) hb0 (fun x => by rw [field_cq hq]; exact hb x) _
  have him1 : (inner ℂ (Mc L c (Ac L κ v)) (Ac L κ v)).im = 0 :=
    im_inner_Mc_self hL hq.l1 hreal _
  have him2 : (inner ℂ Kq (Lc L v)).im = 0 := im_inner_Mc_self hL (L1_cq hq) (rev_cq hreal) _
  have hA : Ac L κ v = Dc L v + (κ : ℂ) • Lc L v := by rw [Dc_eq L κ]; abel
  have e1 : inner ℂ (Ac L κ (mulH L χv v)) (Ac L κ v) =
      inner ℂ (Mc L c (Ac L κ v)) (Ac L κ v) + inner ℂ (Kq + (2 : ℂ) • V) (Ac L κ v) := by
    rw [Ac_mulH_eq hL κ hq v, inner_add_left]
  have e2 : inner ℂ (Kq + (2 : ℂ) • V) (Ac L κ v) =
      inner ℂ (Kq + (2 : ℂ) • V) (Dc L v) + (κ : ℂ) * inner ℂ (Kq + (2 : ℂ) • V) (Lc L v) := by
    rw [hA, inner_add_right, inner_smul_right]
  have e3 : inner ℂ (Kq + (2 : ℂ) • V) (Lc L v) =
      inner ℂ Kq (Lc L v) + 2 * inner ℂ V (Lc L v) := by
    have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    rw [inner_add_left, inner_smul_left, h2]
  have key : (inner ℂ (Ac L κ (mulH L χv v)) (Ac L κ v)).im =
      (inner ℂ (Kq + (2 : ℂ) • V) (Dc L v)).im + 2 * κ * (inner ℂ V (Lc L v)).im := by
    rw [e1, e2, e3, Complex.add_im, him1, zero_add, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.add_im, him2, zero_add,
      Complex.mul_im]
    simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
    ring
  have hDd := norm_nonneg (Dc L v)
  have hPn := norm_nonneg (Lc L v)
  have hG0 : 0 ≤ gradN L v := Real.sqrt_nonneg _
  have b1 : |(inner ℂ (Kq + (2 : ℂ) • V) (Dc L v)).im| ≤ (b * ‖Lc L v‖ + 2 * (a * gradN L v)) *
      ‖Dc L v‖ := by
    refine (Complex.abs_im_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ hDd
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have b2 : |(inner ℂ V (Lc L v)).im| ≤ a * gradN L v * ‖Lc L v‖ :=
    (Complex.abs_im_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hV hPn))
  unfold Jdot
  rw [key, abs_mul, abs_two]
  have b3 : |(inner ℂ (Kq + (2 : ℂ) • V) (Dc L v)).im + 2 * κ * (inner ℂ V (Lc L v)).im| ≤
      (b * ‖Lc L v‖ + 2 * (a * gradN L v)) * ‖Dc L v‖ + 2 * |κ| * (a * gradN L v * ‖Lc L v‖) := by
    refine (abs_add_le _ _).trans (add_le_add b1 ?_)
    calc |2 * κ * (inner ℂ V (Lc L v)).im| = 2 * |κ| * |(inner ℂ V (Lc L v)).im| := by
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ 2 * |κ| * (a * gradN L v * ‖Lc L v‖) :=
          mul_le_mul_of_nonneg_left b2 (by positivity)
  nlinarith [abs_nonneg κ]

/-! ### The flux inequality along solutions and the curvature–time bound -/

/-- The flux constant `Γ` fixed by the data: `P₀ = ‖ψ(0)‖₂`,
`D₀ = √(H₀ + 3β²M₀/16γ) + |κ|P₀`. -/
noncomputable def Gam (L κ β γ a b : ℝ) (u₀ : ℓ2) : ℝ :=
  PVNP.ContinuumFlux.budget a b κ (Real.sqrt (mass L u₀))
    (Real.sqrt (ham L κ β γ u₀ + 3 * β ^ 2 / (16 * γ) * mass L u₀) +
      |κ| * Real.sqrt (mass L u₀))

/-- **F-1, the continuum flux inequality** `|J'(t)| ≤ Γ √D(t)`, `D(t) = ‖Δψ(t)‖₂`, along every
`H²(T_L²)` solution of the frozen PDE, with the explicit constant `Γ = Gam … (u 0)`. -/
theorem flux_inequality (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv) {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ x, ‖PVNP.WCTPlaneWave.d1 (field L (co L χv)) x‖ ^ 2 +
      ‖PVNP.WCTPlaneWave.d2 (field L (co L χv)) x‖ ^ 2 ≤ a ^ 2)
    (hb : ∀ x, ‖PVNP.WCTPlaneWave.lap (field L (co L χv)) x‖ ≤ b) {u : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u) (t : ℝ) :
    |Jdot L κ χv (u t)| ≤ Gam L κ β γ a b (u 0) * Real.sqrt (‖Dc L (u t)‖) := by
  have hcons := conservation hL hu t
  have hP : ‖Lc L (u t)‖ = Real.sqrt (mass L (u 0)) := by
    rw [← hcons.1, mass_eq_norm_Lc, Real.sqrt_sq (norm_nonneg _)]
  have hcap : ‖Dc L (u t)‖ ≤ Real.sqrt (ham L κ β γ (u 0) + 3 * β ^ 2 / (16 * γ) * mass L (u 0)) +
      |κ| * Real.sqrt (mass L (u 0)) := by
    have h1 := norm_Dc_le L κ (u t)
    have h2 : ‖Ac L κ (u t)‖ ≤ Real.sqrt (ham L κ β γ (u 0) +
        3 * β ^ 2 / (16 * γ) * mass L (u 0)) := by
      rw [← hcons.1, ← hcons.2]
      exact Real.le_sqrt_of_sq_le (kin_le_ham hL hγ (u t))
    rw [hP] at h1
    linarith
  have hgrad : gradN L (u t) ^ 2 ≤ Real.sqrt (mass L (u 0)) * ‖Dc L (u t)‖ := by
    rw [gradN, Real.sq_sqrt (by positivity), ← hP]
    exact normG_sq_le L (u t)
  have hstatic := flux_static hL κ hq hreal ha0 hb0 ha hb (u t)
  rw [hP] at hstatic
  exact PVNP.ContinuumFlux.static_to_sqrt a b κ _ (gradN L (u t)) ‖Dc L (u t)‖ _ _ ha0 hb0
    (Real.sqrt_nonneg _) (norm_nonneg _) (Real.sqrt_nonneg _) hcap hgrad hstatic

theorem continuous_mulH_right (hL : 0 < L) (χv : ℓ2) : Continuous (mulH L χv) := by
  have hlip : LipschitzWith ⟨CA L * ‖χv‖, mul_nonneg (CA_nonneg hL) (norm_nonneg _)⟩
      (mulH L χv) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk, ← mulH_sub_right hL]
    exact norm_mulH_le hL _ _
  exact hlip.continuous

theorem continuous_Jdot (hL : 0 < L) (κ : ℝ) (χv : ℓ2) : Continuous (Jdot L κ χv) := by
  unfold Jdot
  have h1 := (Ac L κ).continuous.comp (continuous_mulH_right hL χv)
  have h2 := (Ac L κ).continuous
  exact continuous_const.mul (Complex.continuous_im.comp (h1.inner h2))

/-- **Curvature–time lower bound on `T_L²`, with the flux inequality derived**: if the localized
mass changes by `δ` in time `T`, then `∫₀ᵀ ‖Δψ(t)‖²₂ dt ≥ δ⁴ / (Γ⁴ T³)`. -/
theorem curvature_time_bound (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv) {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ x, ‖PVNP.WCTPlaneWave.d1 (field L (co L χv)) x‖ ^ 2 +
      ‖PVNP.WCTPlaneWave.d2 (field L (co L χv)) x‖ ^ 2 ≤ a ^ 2)
    (hb : ∀ x, ‖PVNP.WCTPlaneWave.lap (field L (co L χv)) x‖ ≤ b) {u : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u) {T δ : ℝ} (hT : 0 < T) (hΓ : 0 < Gam L κ β γ a b (u 0))
    (hδ : 0 ≤ δ) (hchange : δ ≤ |Jdet L χv (u T) - Jdet L χv (u 0)|) :
    δ ^ 4 / (Gam L κ β γ a b (u 0) ^ 4 * T ^ 3) ≤ ∫ t in (0 : ℝ)..T, ‖Dc L (u t)‖ ^ 2 := by
  have hJ'c : Continuous fun t => Jdot L κ χv (u t) := (continuous_Jdot hL κ χv).comp hu.1
  have hDc : Continuous fun t => ‖Dc L (u t)‖ := continuous_norm.comp ((Dc L).continuous.comp hu.1)
  exact PVNP.TransportCalculus.curvature_time_lower_bound
    (fun t => Jdet L χv (u t)) (fun t => Jdot L κ χv (u t)) (fun t => ‖Dc L (u t)‖) hT hΓ
    (fun t _ => flux_identity hL hreal hu t) hJ'c.continuousOn hDc.continuousOn
    (fun t _ => norm_nonneg _)
    (fun t _ => flux_inequality hL hγ hq hreal ha0 hb0 ha hb hu t) hδ hchange

/-- For fields with two classical derivatives, `‖Δψ‖²` in Fourier variables is the classical
`∫_{[0,L]²} |Δψ|²` with `WCTPlaneWave.lap`. -/
theorem normD_eq_integral (hL : 0 < L) (v : ℓ2) (hq : L1q L (co L v)) :
    ‖Dc L v‖ ^ 2 = ∫ x, ‖PVNP.WCTPlaneWave.lap (field L (co L v)) x‖ ^ 2 ∂box L := by
  have hq1 : L1 fun k => -(qf L k : ℂ) * co L v k :=
    hq.mul_bound _ (fun k => by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (qf_nonneg L k)]
      linarith)
  rw [lap_field hq, integral_norm_sq hL hq1, norm_sq_eq]
  refine tsum_congr fun k => ?_
  rw [Dc_apply]
  push_cast
  ring_nf

/-! ### Explicit detector constants: the hypotheses are always satisfiable -/

/-- Wiener bound for `|∇χ|`: `L⁻¹ Σ_k (|ξ_{k,1}| + |ξ_{k,2}|) |ĉ_k|`. -/
noncomputable def aW (L : ℝ) (c : Z2 → ℂ) : ℝ := |L|⁻¹ * ∑' k, (|xi1 L k| + |xi2 L k|) * ‖c k‖

/-- Wiener bound for `|Δχ|`: `L⁻¹ Σ_k |ξ_k|² |ĉ_k|`. -/
noncomputable def bW (L : ℝ) (c : Z2 → ℂ) : ℝ := |L|⁻¹ * ∑' k, qf L k * ‖c k‖

theorem aW_nonneg (L : ℝ) (c : Z2 → ℂ) : 0 ≤ aW L c := by
  unfold aW; exact mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity)

theorem bW_nonneg (L : ℝ) (c : Z2 → ℂ) : 0 ≤ bW L c := by
  unfold bW; exact mul_nonneg (by positivity)
    (tsum_nonneg fun k => mul_nonneg (qf_nonneg L k) (norm_nonneg _))

/-- Every detector in the class satisfies the hypotheses of `flux_inequality` with the explicit
constants `a = aW L c`, `b = bW L c`. -/
theorem detector_bounds {c : Z2 → ℂ} (hq : L1q L c) :
    (∀ x, ‖PVNP.WCTPlaneWave.d1 (field L c) x‖ ^ 2 +
      ‖PVNP.WCTPlaneWave.d2 (field L c) x‖ ^ 2 ≤ aW L c ^ 2) ∧
    (∀ x, ‖PVNP.WCTPlaneWave.lap (field L c) x‖ ≤ bW L c) := by
  have h1 := L1_c1 hq
  have h2 := L1_c2 hq
  have e1 : ∀ k, ‖c1 L c k‖ = |xi1 L k| * ‖c k‖ := fun k => by rw [c1, norm_mul, norm_I_xi1]
  have e2 : ∀ k, ‖c2 L c k‖ = |xi2 L k| * ‖c k‖ := fun k => by rw [c2, norm_mul, norm_I_xi2]
  have s1 : Summable fun k => |xi1 L k| * ‖c k‖ := by
    have := h1; unfold L1 at this; simpa only [e1] using this
  have s2 : Summable fun k => |xi2 L k| * ‖c k‖ := by
    have := h2; unfold L1 at this; simpa only [e2] using this
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [← field_c1 hq, ← field_c2 hq]
    have b1 := norm_field_le (L := L) h1 x
    have b2 := norm_field_le (L := L) h2 x
    simp only [e1] at b1
    simp only [e2] at b2
    set A1 := |L|⁻¹ * ∑' k, |xi1 L k| * ‖c k‖
    set A2 := |L|⁻¹ * ∑' k, |xi2 L k| * ‖c k‖
    have hA : aW L c = A1 + A2 := by
      unfold aW
      rw [← mul_add, ← s1.tsum_add s2]
      congr 1; refine tsum_congr fun k => ?_; ring
    have hA1 : 0 ≤ A1 := (norm_nonneg _).trans b1
    have hA2 : 0 ≤ A2 := (norm_nonneg _).trans b2
    rw [hA]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) b1 2, pow_le_pow_left₀ (norm_nonneg _) b2 2,
      mul_nonneg hA1 hA2]
  · rw [← field_cq hq]
    have b := norm_field_le (L := L) (L1_cq hq) x
    have e : ∀ k, ‖cq L c k‖ = qf L k * ‖c k‖ := fun k => by
      rw [cq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (qf_nonneg L k)]
    simp only [e] at b
    exact b

/-- **F-1 with explicit detector constants** (no hypothesis on the detector beyond
`χ ∈ C²` via `L1q` and `χ` real). -/
theorem flux_inequality_explicit (hL : 0 < L) (hγ : 0 < γ) {χv : ℓ2} (hq : L1q L (co L χv))
    (hreal : rev (co L χv) = co L χv) {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) (t : ℝ) :
    |Jdot L κ χv (u t)| ≤
      Gam L κ β γ (aW L (co L χv)) (bW L (co L χv)) (u 0) * Real.sqrt (‖Dc L (u t)‖) :=
  flux_inequality hL hγ hq hreal (aW_nonneg L _) (bW_nonneg L _) (detector_bounds hq).1
    (detector_bounds hq).2 hu t

end PVNP.Torus
