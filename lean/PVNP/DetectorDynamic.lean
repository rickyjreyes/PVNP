import PVNP.DualResidual
import PVNP.AnalyticPropagation
import PVNP.SpatialModeCount

/-!
# The dynamic detector theorem: quadratic detector convergence along the Galerkin flow

Let `u` and `w` be physical-picture Galerkin trajectories on mode sets `S ⊆ S'`. The coarse
cutoff discards every mode of size `< N` outside `S`. Assume both trajectories stay in the
analytic ball `A_σ ≤ M` on `[0, T]`; Phase XXIX's cutoff-independent propagation supplies this
uniformly in `S` and `S'`.

The error `e = w − u` is measured in the dual norm `|e|_{−σ}² = Σ e^{−2σ|k|} |e_k|²`.
* `hasDerivAt_dsq`, `deriv_dsq_le`, the **energy identity and inequality**:
  - the dispersion cancels exactly;
  - the nonlinear difference is bounded by the dual Lipschitz constant
    `K_F(M) = 3|β|C_A²M² + 5|γ|C_A⁴M⁴` (`dnorm_Fnl_sub_le`);
  - the forcing is the tail of the coarse nonlinearity outside `S`. It is `≤ e^{−2σN} G(M)` in the
    dual norm, with `G(M) = |β|C_A²M³ + |γ|C_A⁴M⁵` (`DualResidual.dsq_tail_le`, `anorm_Fnl_le`).
* `galerkin_dual_gronwall`:
  `|e(t)|²_{−σ} ≤ gronwallBound(|e(0)|²_{−σ}, 2K_F + 1, (e^{−2σN}G)², t)`.
* `detector_dual_bound`: `|J(v) − J(w)| ≤ C_A A_σ(χ)(A_σ(v) + A_σ(w)) |v − w|_{−σ}`. The detector
  pairs the error only with analytic functions.
* `galerkin_detector_dynamic`, `galerkin_detector_dynamic_data`, the **dynamic detector theorem**:
  from common analytic data `u(0) = P_S u₀`, `w(0) = P_{S'} u₀`,
  `|J(w(T)) − J(u(T))| ≤ 2 C_A A_σ(χ) M e^{−2σN} ((A_σ(u₀)² + G(M)² T) e^{(2K_F+1)T})^{1/2}`,
  uniformly in the fine set `S'`.

The quadratic rate `e^{−2σN}` is not assumed to persist from the static bound. It is proved for
the nonlinear evolution, at the price of the stability factor `e^{(K_F + 1/2)T}`.
-/

namespace PVNP.DetectorDynamic

open Complex PVNP.Torus PVNP.TorusGalerkin PVNP.GalerkinTaylor PVNP.Analytic PVNP.DualResidual

variable {L : ℝ}

/-! ### The dual norm as an operator norm -/

/-- The dual weighting `v ↦ (e^{−σ|k|} v_k)`. -/
noncomputable def Dw {σ : ℝ} (hσ : 0 ≤ σ) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (fun k => ((dw σ k : ℝ) : ℂ)) 1 zero_le_one (fun k => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (dw_pos σ k)]
    exact dw_le_one hσ k)

theorem Dw_apply {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) (k : Z2) :
    Dw hσ v k = ((dw σ k : ℝ) : ℂ) * v k := by
  simp only [Dw, dmul_apply]

/-- The dual norm `|v|_{−σ}`. -/
noncomputable def dnorm {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : ℝ := ‖Dw hσ v‖

theorem dnorm_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : 0 ≤ dnorm hσ v := norm_nonneg _

theorem dnorm_sq {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : dnorm hσ v ^ 2 = dsq σ v := by
  rw [dnorm, norm_sq_eq]
  unfold dsq
  refine tsum_congr fun k => ?_
  rw [Dw_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (dw_pos σ k), mul_pow]

theorem dnorm_eq_sqrt {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : dnorm hσ v = Real.sqrt (dsq σ v) := by
  rw [← dnorm_sq hσ, Real.sqrt_sq (dnorm_nonneg hσ v)]

theorem dnorm_add_le {σ : ℝ} (hσ : 0 ≤ σ) (v w : ℓ2) :
    dnorm hσ (v + w) ≤ dnorm hσ v + dnorm hσ w := by
  unfold dnorm; rw [map_add]; exact norm_add_le _ _

theorem dnorm_smul {σ : ℝ} (hσ : 0 ≤ σ) (c : ℂ) (v : ℓ2) :
    dnorm hσ (c • v) = ‖c‖ * dnorm hσ v := by
  unfold dnorm; rw [map_smul, norm_smul]

theorem dnorm_le_of_le {σ : ℝ} (hσ : 0 ≤ σ) {v w : ℓ2} (h : ∀ k, ‖v k‖ ≤ ‖w k‖) :
    dnorm hσ v ≤ dnorm hσ w := by
  have hs : dsq σ v ≤ dsq σ w :=
    (dsum hσ v).tsum_le_tsum (fun k => pow_le_pow_left₀
      (mul_nonneg (dw_pos σ k).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (h k) (dw_pos σ k).le) 2) (dsum hσ w)
  rw [dnorm_eq_sqrt, dnorm_eq_sqrt]
  exact Real.sqrt_le_sqrt hs

theorem dw_neg (σ : ℝ) (k : Z2) : dw σ (-k) = dw σ k := by
  unfold dw; rw [size_neg]

theorem dsq_conjH (σ : ℝ) (v : ℓ2) : dsq σ (conjH v) = dsq σ v := by
  unfold dsq
  rw [← (Equiv.neg Z2).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply, conjH_apply, Complex.norm_conj, dw_neg, neg_neg]

theorem dnorm_conjH {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : dnorm hσ (conjH v) = dnorm hσ v := by
  rw [dnorm_eq_sqrt, dnorm_eq_sqrt, dsq_conjH]

/-- **Dual module estimate, norm form**: `|v·w|_{−σ} ≤ C_A A_σ(v) |w|_{−σ}`. -/
theorem dnorm_mulH_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {v : ℓ2} (hv : ASum σ v) (w : ℓ2) :
    dnorm hσ (mulH L v w) ≤ CA L * anorm σ v * dnorm hσ w := by
  have h := dsq_mulH_le hL hσ hv w
  rw [← dnorm_sq hσ, ← dnorm_sq hσ, ← anorm_sq] at h
  have hnn : 0 ≤ CA L * anorm σ v * dnorm hσ w :=
    mul_nonneg (mul_nonneg (CA_nonneg hL) (anorm_nonneg σ v)) (dnorm_nonneg hσ w)
  rw [← sq_le_sq₀ (dnorm_nonneg hσ _) hnn]
  calc dnorm hσ (mulH L v w) ^ 2 ≤ CA L ^ 2 * anorm σ v ^ 2 * dnorm hσ w ^ 2 := h
    _ = (CA L * anorm σ v * dnorm hσ w) ^ 2 := by ring

/-- Product difference in the dual norm. -/
theorem dnorm_mulH_sub_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {x y x' y' : ℓ2}
    (hy : ASum σ y) (hx' : ASum σ x') :
    dnorm hσ (mulH L x y - mulH L x' y') ≤
      CA L * (anorm σ y * dnorm hσ (x - x') + anorm σ x' * dnorm hσ (y - y')) := by
  have e : mulH L x y - mulH L x' y' = mulH L y (x - x') + mulH L x' (y - y') := by
    rw [weak_mulH_comm hL y (x - x'), mulH_sub_left hL, mulH_sub_right hL]; abel
  rw [e]
  calc dnorm hσ (mulH L y (x - x') + mulH L x' (y - y'))
      ≤ dnorm hσ (mulH L y (x - x')) + dnorm hσ (mulH L x' (y - y')) := dnorm_add_le hσ _ _
    _ ≤ CA L * anorm σ y * dnorm hσ (x - x') + CA L * anorm σ x' * dnorm hσ (y - y') :=
        add_le_add (dnorm_mulH_le hL hσ hy _) (dnorm_mulH_le hL hσ hx' _)
    _ = _ := by ring

/-! ### The dual Lipschitz bound of the nonlinearity -/

/-- The dual Lipschitz constant of `F` on the analytic ball of radius `M`. -/
noncomputable def KF (L β γ M : ℝ) : ℝ := 3 * |β| * CA L ^ 2 * M ^ 2 + 5 * |γ| * CA L ^ 4 * M ^ 4

/-- The analytic size of `F` on the analytic ball of radius `M`. -/
noncomputable def G (L β γ M : ℝ) : ℝ := |β| * CA L ^ 2 * M ^ 3 + |γ| * CA L ^ 4 * M ^ 5

theorem KF_nonneg (L β γ M : ℝ) : 0 ≤ KF L β γ M := by unfold KF; positivity

theorem G_nonneg (L β γ : ℝ) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ G L β γ M := by unfold G; positivity

theorem step {c A1 X1 A2 X2 m1 b1 m2 b2 : ℝ} (hc : 0 ≤ c) (hA1 : 0 ≤ A1) (h1 : A1 ≤ m1)
    (hX1 : 0 ≤ X1) (g1 : X1 ≤ b1) (hA2 : 0 ≤ A2) (h2 : A2 ≤ m2) (hX2 : 0 ≤ X2) (g2 : X2 ≤ b2) :
    c * (A1 * X1 + A2 * X2) ≤ c * (m1 * b1 + m2 * b2) :=
  mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul h1 g1 hX1 (hA1.trans h1))
    (mul_le_mul h2 g2 hX2 (hA2.trans h2))) hc

theorem anorm_mul_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {v w : ℓ2} (hv : ASum σ v)
    (hw : ASum σ w) {a b : ℝ} (ha : anorm σ v ≤ a) (hb : anorm σ w ≤ b) :
    anorm σ (mulH L v w) ≤ CA L * a * b :=
  (anorm_mulH_le hL hσ hv hw).trans (mul_le_mul (mul_le_mul_of_nonneg_left ha (CA_nonneg hL))
    hb (anorm_nonneg _ _) (mul_nonneg (CA_nonneg hL) ((anorm_nonneg _ _).trans ha)))

/-- **Dual Lipschitz bound**: on the analytic ball of radius `M`,
`|F(a) − F(b)|_{−σ} ≤ K_F(M) |a − b|_{−σ}`. -/
theorem dnorm_Fnl_sub_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) (β γ : ℝ) {a b : ℓ2} {M : ℝ}
    (ha : ASum σ a) (hb : ASum σ b) (hMa : anorm σ a ≤ M) (hMb : anorm σ b ≤ M) :
    dnorm hσ (Fnl L β γ a - Fnl L β γ b) ≤ KF L β γ M * dnorm hσ (a - b) := by
  have hC := CA_nonneg hL
  have hM : 0 ≤ M := (anorm_nonneg σ a).trans hMa
  set d := dnorm hσ (a - b) with hd_def
  have hd : 0 ≤ d := dnorm_nonneg hσ _
  have hca := asum_conjH ha
  have hcb := asum_conjH hb
  have nca : anorm σ (conjH a) ≤ M := by rw [anorm_conjH]; exact hMa
  have ncb : anorm σ (conjH b) ≤ M := by rw [anorm_conjH]; exact hMb
  have dconj : dnorm hσ (conjH a - conjH b) = d := by rw [← conjH_sub, dnorm_conjH]
  have h2b := (asum_mulH hL hσ hb hb).1
  have h3b := (asum_mulH hL hσ h2b hb).1
  have h4b := (asum_mulH hL hσ h3b hcb).1
  have n2b : anorm σ (mulH L b b) ≤ CA L * M * M := anorm_mul_le hL hσ hb hb hMb hMb
  have n3b : anorm σ (mulH L (mulH L b b) b) ≤ CA L * (CA L * M * M) * M :=
    anorm_mul_le hL hσ h2b hb n2b hMb
  have n4b : anorm σ (mulH L (mulH L (mulH L b b) b) (conjH b)) ≤
      CA L * (CA L * (CA L * M * M) * M) * M := anorm_mul_le hL hσ h3b hcb n3b ncb
  have p2 : 0 ≤ CA L * M * M := by positivity
  have p3 : 0 ≤ CA L * (CA L * M * M) * M := by positivity
  -- the quadratic factor
  have d2 : dnorm hσ (mulH L a a - mulH L b b) ≤ CA L * (M * d + M * d) :=
    (dnorm_mulH_sub_le hL hσ ha hb).trans
      (step hC (anorm_nonneg _ _) hMa hd le_rfl (anorm_nonneg _ _) hMb hd le_rfl)
  have q2 : 0 ≤ CA L * (M * d + M * d) := by positivity
  -- the cubic term `(a a) ā`
  have d3 : dnorm hσ (mulH L (mulH L a a) (conjH a) - mulH L (mulH L b b) (conjH b)) ≤
      CA L * (M * (CA L * (M * d + M * d)) + CA L * M * M * d) := by
    refine (dnorm_mulH_sub_le hL hσ hca h2b).trans ?_
    rw [dconj]
    exact step hC (anorm_nonneg _ _) nca (dnorm_nonneg _ _) d2 (anorm_nonneg _ _) n2b hd le_rfl
  -- the quintic chain
  have e3 : dnorm hσ (mulH L (mulH L a a) a - mulH L (mulH L b b) b) ≤
      CA L * (M * (CA L * (M * d + M * d)) + CA L * M * M * d) :=
    (dnorm_mulH_sub_le hL hσ ha h2b).trans
      (step hC (anorm_nonneg _ _) hMa (dnorm_nonneg _ _) d2 (anorm_nonneg _ _) n2b hd le_rfl)
  have r3 : 0 ≤ CA L * (M * (CA L * (M * d + M * d)) + CA L * M * M * d) := by positivity
  have e4 : dnorm hσ (mulH L (mulH L (mulH L a a) a) (conjH a) -
        mulH L (mulH L (mulH L b b) b) (conjH b)) ≤
      CA L * (M * (CA L * (M * (CA L * (M * d + M * d)) + CA L * M * M * d)) +
        CA L * (CA L * M * M) * M * d) := by
    refine (dnorm_mulH_sub_le hL hσ hca h3b).trans ?_
    rw [dconj]
    exact step hC (anorm_nonneg _ _) nca (dnorm_nonneg _ _) e3 (anorm_nonneg _ _) n3b hd le_rfl
  have e5 : dnorm hσ (mulH L (mulH L (mulH L (mulH L a a) a) (conjH a)) (conjH a) -
        mulH L (mulH L (mulH L (mulH L b b) b) (conjH b)) (conjH b)) ≤
      CA L * (M * (CA L * (M * (CA L * (M * (CA L * (M * d + M * d)) + CA L * M * M * d)) +
        CA L * (CA L * M * M) * M * d)) + CA L * (CA L * (CA L * M * M) * M) * M * d) := by
    refine (dnorm_mulH_sub_le hL hσ hca h4b).trans ?_
    rw [dconj]
    exact step hC (anorm_nonneg _ _) nca (dnorm_nonneg _ _) e4 (anorm_nonneg _ _) n4b hd le_rfl
  -- assemble
  have hF : Fnl L β γ a - Fnl L β γ b =
      (-(β : ℂ)) • (mulH L (mulH L a a) (conjH a) - mulH L (mulH L b b) (conjH b)) +
        (γ : ℂ) • (mulH L (mulH L (mulH L (mulH L a a) a) (conjH a)) (conjH a) -
          mulH L (mulH L (mulH L (mulH L b b) b) (conjH b)) (conjH b)) := by
    simp only [Fnl, smul_sub]; abel
  rw [hF]
  refine (dnorm_add_le hσ _ _).trans ?_
  rw [dnorm_smul, dnorm_smul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have hb' := abs_nonneg β
  have hg' := abs_nonneg γ
  calc |β| * dnorm hσ (mulH L (mulH L a a) (conjH a) - mulH L (mulH L b b) (conjH b)) +
        |γ| * dnorm hσ (mulH L (mulH L (mulH L (mulH L a a) a) (conjH a)) (conjH a) -
          mulH L (mulH L (mulH L (mulH L b b) b) (conjH b)) (conjH b))
      ≤ |β| * (CA L * (M * (CA L * (M * d + M * d)) + CA L * M * M * d)) +
        |γ| * (CA L * (M * (CA L * (M * (CA L * (M * (CA L * (M * d + M * d)) +
          CA L * M * M * d)) + CA L * (CA L * M * M) * M * d)) +
          CA L * (CA L * (CA L * M * M) * M) * M * d)) :=
        add_le_add (mul_le_mul_of_nonneg_left d3 hb') (mul_le_mul_of_nonneg_left e5 hg')
    _ = KF L β γ M * d := by unfold KF; ring

/-! ### Dual pairing and the detector -/

/-- The analytic weighting `(e^{σ|k|} v_k)` of an analytic vector. -/
noncomputable def Aw {σ : ℝ} {v : ℓ2} (hv : ASum σ v) : ℓ2 :=
  mk (fun k => ((aw σ k : ℝ) : ℂ) * v k) (hv.congr fun k => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (aw_pos σ k)])

theorem Aw_apply {σ : ℝ} {v : ℓ2} (hv : ASum σ v) (k : Z2) :
    Aw hv k = ((aw σ k : ℝ) : ℂ) * v k := rfl

theorem norm_Aw {σ : ℝ} {v : ℓ2} (hv : ASum σ v) : ‖Aw hv‖ = anorm σ v := by
  rw [anorm, ← Real.sqrt_sq (norm_nonneg (Aw hv)), norm_sq_eq]
  congr 1
  unfold asq
  refine tsum_congr fun k => ?_
  rw [Aw_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (aw_pos σ k)]

/-- **Dual pairing**: `⟨x, v⟩ = ⟨D_σ x, A_σ v⟩`, so `|⟨x, v⟩| ≤ |x|_{−σ} A_σ(v)`. -/
theorem inner_dual {σ : ℝ} (hσ : 0 ≤ σ) (x : ℓ2) {v : ℓ2} (hv : ASum σ v) :
    inner ℂ x v = inner ℂ (Dw hσ x) (Aw hv) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  rw [Dw_apply, Aw_apply]
  have h : ((dw σ k : ℝ) : ℂ) * ((aw σ k : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, dw_mul_aw, Complex.ofReal_one]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  linear_combination (-((starRingEnd ℂ) (x k) * v k)) * h

theorem norm_Lc_apply_le (L : ℝ) (v : ℓ2) (k : Z2) : ‖Lc L v k‖ ≤ ‖v k‖ := by
  rw [Lc_apply, norm_co]
  exact div_le_self (norm_nonneg _) (one_le_wt L k)

theorem asum_Lc {σ : ℝ} {v : ℓ2} (hv : ASum σ v) : ASum σ (Lc L v) :=
  hv.of_nonneg_of_le (fun _ => sq_nonneg _) fun k =>
    pow_le_pow_left₀ (mul_nonneg (aw_pos σ k).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_Lc_apply_le L v k) (aw_pos σ k).le) 2

theorem anorm_Lc_le {σ : ℝ} {v : ℓ2} (hv : ASum σ v) : anorm σ (Lc L v) ≤ anorm σ v := by
  unfold anorm
  apply Real.sqrt_le_sqrt
  exact (asum_Lc hv).tsum_le_tsum (fun k => pow_le_pow_left₀
    (mul_nonneg (aw_pos σ k).le (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (norm_Lc_apply_le L v k) (aw_pos σ k).le) 2) hv

theorem dnorm_Lc_le {σ : ℝ} (hσ : 0 ≤ σ) (v : ℓ2) : dnorm hσ (Lc L v) ≤ dnorm hσ v :=
  dnorm_le_of_le hσ (norm_Lc_apply_le L v)

/-- **The detector in the dual norm**: `|J(v) − J(w)| ≤ C_A A_σ(χ)(A_σ(v) + A_σ(w)) |v − w|_{−σ}`. -/
theorem detector_dual_bound (hL : 0 < L) {χv : ℓ2} (hreal : rev (co L χv) = co L χv) {σ : ℝ}
    (hσ : 0 ≤ σ) (hχ : ASum σ χv) {v w : ℓ2} (hv : ASum σ v) (hw : ASum σ w) :
    |Jdet L χv v - Jdet L χv w| ≤
      CA L * anorm σ χv * (anorm σ v + anorm σ w) * dnorm hσ (v - w) := by
  rw [Jdet_eq_re hL hreal, Jdet_eq_re hL hreal, ← Complex.sub_re]
  have e : inner ℂ (Lc L v) (Lc L (mulH L χv v)) - inner ℂ (Lc L w) (Lc L (mulH L χv w)) =
      inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v)) +
        inner ℂ (Lc L w) (Lc L (mulH L χv (v - w))) := by
    rw [mulH_sub_right hL, map_sub, map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [e]
  have hC := CA_nonneg hL
  have hχv := (asum_mulH hL hσ hχ hv).1
  have h1 : ‖inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v))‖ ≤
      dnorm hσ (v - w) * (CA L * anorm σ χv * anorm σ v) := by
    rw [inner_dual hσ _ (asum_Lc hχv)]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_Aw]
    exact mul_le_mul (dnorm_Lc_le hσ _) ((anorm_Lc_le hχv).trans (anorm_mulH_le hL hσ hχ hv))
      (anorm_nonneg _ _) (dnorm_nonneg _ _)
  have h2 : ‖inner ℂ (Lc L w) (Lc L (mulH L χv (v - w)))‖ ≤
      (CA L * anorm σ χv * dnorm hσ (v - w)) * anorm σ w := by
    rw [norm_inner_symm, inner_dual hσ _ (asum_Lc hw)]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_Aw]
    exact mul_le_mul ((dnorm_Lc_le hσ _).trans (dnorm_mulH_le hL hσ hχ _)) (anorm_Lc_le hw)
      (anorm_nonneg _ _) (mul_nonneg (mul_nonneg hC (anorm_nonneg _ _)) (dnorm_nonneg _ _))
  calc |(inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v)) +
        inner ℂ (Lc L w) (Lc L (mulH L χv (v - w)))).re|
      ≤ ‖inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v)) +
        inner ℂ (Lc L w) (Lc L (mulH L χv (v - w)))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (Lc L (v - w)) (Lc L (mulH L χv v))‖ +
        ‖inner ℂ (Lc L w) (Lc L (mulH L χv (v - w)))‖ := norm_add_le _ _
    _ ≤ dnorm hσ (v - w) * (CA L * anorm σ χv * anorm σ v) +
        (CA L * anorm σ χv * dnorm hσ (v - w)) * anorm σ w := add_le_add h1 h2
    _ = _ := by ring

/-! ### The energy inequality along two Galerkin trajectories -/

theorem dsq_eq_sum {S : Finset Z2} {v : ℓ2} (hv : Supported S v) (σ : ℝ) :
    dsq σ v = ∑ k ∈ S, (dw σ k * ‖v k‖) ^ 2 := by
  unfold dsq
  exact tsum_eq_sum fun k hk => by rw [hv k hk, norm_zero, mul_zero]; norm_num

theorem supported_sub {S S' : Finset Z2} (hSS : S ⊆ S') {u w : ℓ2} (hu : Supported S u)
    (hw : Supported S' w) : Supported S' (w - u) := fun k hk => by
  rw [lp.coeFn_sub, Pi.sub_apply, hw k hk, hu k (fun h => hk (hSS h)), sub_zero]

/-- The difference of the two Galerkin fields, mode by mode on `S'`. -/
theorem field_diff {κ β γ : ℝ} {S S' : Finset Z2} {u w : ℓ2} (hu : Supported S u) {k : Z2}
    (hk : k ∈ S') :
    (physField L κ β γ S' w - physField L κ β γ S u) k =
      -I * (((om L κ k : ℝ) : ℂ) * (w - u) k) +
        -I * (Fnl L β γ w - trunc S (Fnl L β γ u)) k := by
  simp only [physField, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.coeFn_add, Pi.add_apply, Aop_apply, omMul, trunc_apply, if_pos hk]
  by_cases hkS : k ∈ S
  · simp only [if_pos hkS]; ring
  · simp only [if_neg hkS, hu k hkS]; ring

theorem hasDerivAt_dsq {κ β γ : ℝ} {S S' : Finset Z2} (hSS : S ⊆ S') {u w : ℝ → ℓ2}
    (hsu : ∀ t, Supported S (u t)) (hsw : ∀ t, Supported S' (w t))
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    (hw : ∀ t, HasDerivAt w (physField L κ β γ S' (w t)) t) (σ t : ℝ) :
    HasDerivAt (fun s => dsq σ (w s - u s))
      (∑ k ∈ S', (dw σ k) ^ 2 * (2 * inner ℝ ((w t - u t) k)
        ((physField L κ β γ S' (w t) - physField L κ β γ S (u t)) k))) t := by
  have e : (fun s => dsq σ (w s - u s)) =
      fun s => ∑ k ∈ S', (dw σ k) ^ 2 * ‖(w s - u s) k‖ ^ 2 := by
    funext s
    rw [dsq_eq_sum (supported_sub hSS (hsu s) (hsw s))]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have hd : HasDerivAt (fun s => w s - u s)
      (physField L κ β γ S' (w t) - physField L κ β γ S (u t)) t := (hw t).sub (hu t)
  exact HasDerivAt.fun_sum fun k _ => ((hasDerivAt_apply hd k).norm_sq).const_mul _

theorem inner_diff_le {κ β γ : ℝ} {S S' : Finset Z2} {u w : ℓ2} (hu : Supported S u) {k : Z2}
    (hk : k ∈ S') :
    inner ℝ ((w - u) k) ((physField L κ β γ S' w - physField L κ β γ S u) k) ≤
      ‖(w - u) k‖ * (‖(Fnl L β γ w - Fnl L β γ u) k‖ +
        ‖(Fnl L β γ u - trunc S (Fnl L β γ u)) k‖) := by
  rw [field_diff hu hk, inner_add_right, inner_disp_zero, zero_add]
  have e : (Fnl L β γ w - trunc S (Fnl L β γ u)) k =
      (Fnl L β γ w - Fnl L β γ u) k + (Fnl L β γ u - trunc S (Fnl L β γ u)) k := by
    simp only [lp.coeFn_sub, Pi.sub_apply]; ring
  calc inner ℝ ((w - u) k) (-I * (Fnl L β γ w - trunc S (Fnl L β γ u)) k)
      ≤ ‖(w - u) k‖ * ‖-I * (Fnl L β γ w - trunc S (Fnl L β γ u)) k‖ := real_inner_le_norm _ _
    _ = ‖(w - u) k‖ * ‖(Fnl L β γ w - trunc S (Fnl L β γ u)) k‖ := by
        rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    _ ≤ _ := by
        rw [e]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)

theorem sum_dual_le {σ : ℝ} (hσ : 0 ≤ σ) {S' : Finset Z2} {a : ℓ2} (ha : Supported S' a)
    (b : ℓ2) :
    ∑ k ∈ S', (dw σ k * ‖a k‖) * (dw σ k * ‖b k‖) ≤ dnorm hσ a * dnorm hσ b := by
  refine (Real.sum_mul_le_sqrt_mul_sqrt S' (fun k => dw σ k * ‖a k‖)
    (fun k => dw σ k * ‖b k‖)).trans ?_
  rw [← dsq_eq_sum ha σ, ← dnorm_eq_sqrt hσ]
  refine mul_le_mul_of_nonneg_left ?_ (dnorm_nonneg hσ a)
  rw [dnorm_eq_sqrt hσ]
  exact Real.sqrt_le_sqrt ((dsum hσ b).sum_le_tsum S' (fun k _ => sq_nonneg _))

theorem dnorm_tail_le {σ N : ℝ} (hσ : 0 ≤ σ) {v : ℓ2} (hv : ASum σ v) (S : Finset Z2)
    (hS : ∀ k ∉ S, N ≤ size k) :
    dnorm hσ (v - trunc S v) ≤ Real.exp (-(2 * σ * N)) * anorm σ v := by
  have h := dsq_tail_le hσ hv S hS
  rw [← dnorm_sq hσ, ← anorm_sq] at h
  have hnn : 0 ≤ Real.exp (-(2 * σ * N)) * anorm σ v :=
    mul_nonneg (Real.exp_pos _).le (anorm_nonneg _ _)
  rw [← sq_le_sq₀ (dnorm_nonneg hσ _) hnn, mul_pow, ← Real.exp_nat_mul]
  convert h using 3
  push_cast; ring

theorem anorm_Fnl_le_G (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) (β γ : ℝ) {u : ℓ2} (hu : ASum σ u)
    {M : ℝ} (hMu : anorm σ u ≤ M) : anorm σ (Fnl L β γ u) ≤ G L β γ M := by
  have h0 := anorm_nonneg σ u
  have h3 : anorm σ u ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ h0 hMu 3
  have h5 : anorm σ u ^ 5 ≤ M ^ 5 := pow_le_pow_left₀ h0 hMu 5
  have c1 : 0 ≤ |β| * CA L ^ 2 := by positivity
  have c2 : 0 ≤ |γ| * CA L ^ 4 := by positivity
  exact (anorm_Fnl_le hL hσ β γ hu).2.trans
    (add_le_add (mul_le_mul_of_nonneg_left h3 c1) (mul_le_mul_of_nonneg_left h5 c2))

/-- **Energy inequality.** Along two Galerkin trajectories on `S ⊆ S'`, the derivative of
`|w − u|²_{−σ}` is at most `2K_F|w − u|²_{−σ} + 2|w − u|_{−σ} e^{−2σN} G(M)`. The dispersion
cancels exactly. -/
theorem deriv_dsq_le (hL : 0 < L) {κ β γ : ℝ} {σ N M : ℝ} (hσ : 0 ≤ σ) {S S' : Finset Z2}
    (hSS : S ⊆ S') (hS : ∀ k ∉ S, N ≤ size k) {u w : ℓ2} (hu : Supported S u)
    (hw : Supported S' w) (hMu : anorm σ u ≤ M) (hMw : anorm σ w ≤ M) :
    ∑ k ∈ S', (dw σ k) ^ 2 * (2 * inner ℝ ((w - u) k)
        ((physField L κ β γ S' w - physField L κ β γ S u) k)) ≤
      2 * KF L β γ M * dsq σ (w - u) +
        2 * dnorm hσ (w - u) * (Real.exp (-(2 * σ * N)) * G L β γ M) := by
  have hau := asum_of_supported hu σ
  have haw := asum_of_supported hw σ
  have hsupp := supported_sub hSS hu hw
  have h1 : ∑ k ∈ S', (dw σ k) ^ 2 * (2 * inner ℝ ((w - u) k)
        ((physField L κ β γ S' w - physField L κ β γ S u) k)) ≤
      2 * (∑ k ∈ S', (dw σ k * ‖(w - u) k‖) * (dw σ k * ‖(Fnl L β γ w - Fnl L β γ u) k‖) +
        ∑ k ∈ S', (dw σ k * ‖(w - u) k‖) *
          (dw σ k * ‖(Fnl L β γ u - trunc S (Fnl L β γ u)) k‖)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have h := inner_diff_le (L := L) (κ := κ) (β := β) (γ := γ) (w := w) hu hk
    have hd := sq_nonneg (dw σ k)
    nlinarith [mul_le_mul_of_nonneg_left h hd]
  have h2 := sum_dual_le hσ hsupp (Fnl L β γ w - Fnl L β γ u)
  have h3 := sum_dual_le hσ hsupp (Fnl L β γ u - trunc S (Fnl L β γ u))
  have h4 : dnorm hσ (Fnl L β γ w - Fnl L β γ u) ≤ KF L β γ M * dnorm hσ (w - u) :=
    dnorm_Fnl_sub_le hL hσ β γ haw hau hMw hMu
  have h5 : dnorm hσ (Fnl L β γ u - trunc S (Fnl L β γ u)) ≤
      Real.exp (-(2 * σ * N)) * G L β γ M :=
    (dnorm_tail_le hσ (anorm_Fnl_le hL hσ β γ hau).1 S hS).trans
      (mul_le_mul_of_nonneg_left (anorm_Fnl_le_G hL hσ β γ hau hMu) (Real.exp_pos _).le)
  have hn := dnorm_nonneg hσ (w - u)
  rw [← dnorm_sq hσ (w - u)]
  nlinarith [mul_le_mul_of_nonneg_left h4 hn, mul_le_mul_of_nonneg_left h5 hn]

/-- **Gronwall in the dual norm.** -/
theorem galerkin_dual_gronwall (hL : 0 < L) {κ β γ : ℝ} {σ N M T : ℝ} (hσ : 0 ≤ σ)
    {S S' : Finset Z2} (hSS : S ⊆ S') (hS : ∀ k ∉ S, N ≤ size k) {u w : ℝ → ℓ2}
    (hsu : ∀ t, Supported S (u t)) (hsw : ∀ t, Supported S' (w t))
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    (hw : ∀ t, HasDerivAt w (physField L κ β γ S' (w t)) t)
    (hMu : ∀ t ∈ Set.Ico 0 T, anorm σ (u t) ≤ M) (hMw : ∀ t ∈ Set.Ico 0 T, anorm σ (w t) ≤ M) :
    ∀ t ∈ Set.Icc 0 T, dsq σ (w t - u t) ≤
      gronwallBound (dsq σ (w 0 - u 0)) (2 * KF L β γ M + 1)
        ((Real.exp (-(2 * σ * N)) * G L β γ M) ^ 2) t := by
  have hD := hasDerivAt_dsq hSS hsu hsw hu hw σ
  have key := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun s => dsq σ (w s - u s)) (a := 0) (b := T)
    (δ := dsq σ (w 0 - u 0)) (K := 2 * KF L β γ M + 1)
    (ε := (Real.exp (-(2 * σ * N)) * G L β γ M) ^ 2)
    (fun s _ => (hD s).continuousAt.continuousWithinAt)
    (fun x _ r hr => (hD x).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl
    (fun x hx => by
      have h := deriv_dsq_le (κ := κ) (β := β) (γ := γ) hL hσ hSS hS (hsu x) (hsw x) (hMu x hx) (hMw x hx)
      have hsq := dnorm_sq hσ (w x - u x)
      nlinarith [sq_nonneg (dnorm hσ (w x - u x) - Real.exp (-(2 * σ * N)) * G L β γ M)])
  intro t ht
  have h := key t ht
  rwa [sub_zero] at h

/-- **The dynamic detector theorem.** -/
theorem galerkin_detector_dynamic (hL : 0 < L) {κ β γ : ℝ} {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {σ N M T : ℝ} (hσ : 0 ≤ σ) (hT : 0 ≤ T)
    {S S' : Finset Z2} (hSS : S ⊆ S') (hS : ∀ k ∉ S, N ≤ size k) {u w : ℝ → ℓ2}
    (hsu : ∀ t, Supported S (u t)) (hsw : ∀ t, Supported S' (w t))
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    (hw : ∀ t, HasDerivAt w (physField L κ β γ S' (w t)) t)
    (hMu : ∀ t ∈ Set.Icc 0 T, anorm σ (u t) ≤ M) (hMw : ∀ t ∈ Set.Icc 0 T, anorm σ (w t) ≤ M)
    (hχ : ASum σ χv) :
    |Jdet L χv (w T) - Jdet L χv (u T)| ≤
      CA L * anorm σ χv * (2 * M) *
        Real.sqrt ((dsq σ (w 0 - u 0) + (Real.exp (-(2 * σ * N)) * G L β γ M) ^ 2 * T) *
          Real.exp ((2 * KF L β γ M + 1) * T)) := by
  have hTmem : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
  have hM : 0 ≤ M := (anorm_nonneg σ (u T)).trans (hMu T hTmem)
  have hC := CA_nonneg hL
  have hg := galerkin_dual_gronwall hL hσ hSS hS hsu hsw hu hw
    (fun t ht => hMu t (Set.Ico_subset_Icc_self ht))
    (fun t ht => hMw t (Set.Ico_subset_Icc_self ht)) T hTmem
  have hgb := gronwallBound_le (δ := dsq σ (w 0 - u 0)) (A := 2 * KF L β γ M + 1)
    (η := (Real.exp (-(2 * σ * N)) * G L β γ M) ^ 2) (t := T)
    (by linarith [KF_nonneg L β γ M]) (sq_nonneg _) hT
  have hdet := detector_dual_bound hL hreal hσ hχ (asum_of_supported (hsw T) σ)
    (asum_of_supported (hsu T) σ)
  have hdn : dnorm hσ (w T - u T) ≤
      Real.sqrt ((dsq σ (w 0 - u 0) + (Real.exp (-(2 * σ * N)) * G L β γ M) ^ 2 * T) *
        Real.exp ((2 * KF L β γ M + 1) * T)) := by
    rw [dnorm_eq_sqrt]
    exact Real.sqrt_le_sqrt (hg.trans hgb)
  have hA : CA L * anorm σ χv * (anorm σ (w T) + anorm σ (u T)) ≤ CA L * anorm σ χv * (2 * M) :=
    mul_le_mul_of_nonneg_left (by linarith [hMw T hTmem, hMu T hTmem])
      (mul_nonneg hC (anorm_nonneg _ _))
  exact hdet.trans (mul_le_mul hA hdn (dnorm_nonneg _ _)
    (mul_nonneg (mul_nonneg hC (anorm_nonneg _ _)) (by linarith)))

theorem dsq_annulus_le {σ N : ℝ} (hσ : 0 ≤ σ) {v : ℓ2} (hv : ASum σ v) {S S' : Finset Z2}
    (hSS : S ⊆ S') (hS : ∀ k ∉ S, N ≤ size k) :
    dsq σ (trunc S' v - trunc S v) ≤ Real.exp (-(4 * σ * N)) * asq σ v := by
  have hle : ∀ k, ‖(trunc S' v - trunc S v) k‖ ≤ ‖(v - trunc S v) k‖ := fun k => by
    by_cases hk : k ∈ S
    · simp [trunc_apply, hk, hSS hk]
    · by_cases hk' : k ∈ S'
      · simp [trunc_apply, hk, hk']
      · simp [trunc_apply, hk, hk']
  have h3 : dsq σ (trunc S' v - trunc S v) ≤ dsq σ (v - trunc S v) :=
    (dsum hσ _).tsum_le_tsum (fun k => pow_le_pow_left₀
      (mul_nonneg (dw_pos σ k).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hle k) (dw_pos σ k).le) 2) (dsum hσ _)
  exact h3.trans (dsq_tail_le hσ hv S hS)

/-- **The dynamic detector theorem from common analytic data.** If `u(0) = P_S u₀` and
`w(0) = P_{S'} u₀`, then
`|J(w(T)) − J(u(T))| ≤ 2 C_A A_σ(χ) M e^{−2σN} ((A_σ(u₀)² + G(M)²T) e^{(2K_F+1)T})^{1/2}`. -/
theorem galerkin_detector_dynamic_data (hL : 0 < L) {κ β γ : ℝ} {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {σ N M T : ℝ} (hσ : 0 ≤ σ) (hT : 0 ≤ T)
    {S S' : Finset Z2} (hSS : S ⊆ S') (hS : ∀ k ∉ S, N ≤ size k) {u w : ℝ → ℓ2}
    (hsu : ∀ t, Supported S (u t)) (hsw : ∀ t, Supported S' (w t))
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    (hw : ∀ t, HasDerivAt w (physField L κ β γ S' (w t)) t)
    (hMu : ∀ t ∈ Set.Icc 0 T, anorm σ (u t) ≤ M) (hMw : ∀ t ∈ Set.Icc 0 T, anorm σ (w t) ≤ M)
    (hχ : ASum σ χv) {u₀ : ℓ2} (hu₀ : ASum σ u₀) (h0u : u 0 = trunc S u₀)
    (h0w : w 0 = trunc S' u₀) :
    |Jdet L χv (w T) - Jdet L χv (u T)| ≤
      CA L * anorm σ χv * (2 * M) * Real.exp (-(2 * σ * N)) *
        Real.sqrt ((asq σ u₀ + G L β γ M ^ 2 * T) * Real.exp ((2 * KF L β γ M + 1) * T)) := by
  have h := galerkin_detector_dynamic hL hreal hσ hT hSS hS hsu hsw hu hw hMu hMw hχ
  rw [h0u, h0w] at h
  have hTmem : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
  have hM : 0 ≤ M := (anorm_nonneg σ (u T)).trans (hMu T hTmem)
  have hann := dsq_annulus_le hσ hu₀ hSS hS
  have hE : Real.exp (-(2 * σ * N)) ^ 2 = Real.exp (-(4 * σ * N)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hEp := (Real.exp_pos ((2 * KF L β γ M + 1) * T)).le
  have hX : (dsq σ (trunc S' u₀ - trunc S u₀) + (Real.exp (-(2 * σ * N)) * G L β γ M) ^ 2 * T) *
        Real.exp ((2 * KF L β γ M + 1) * T) ≤
      Real.exp (-(2 * σ * N)) ^ 2 *
        ((asq σ u₀ + G L β γ M ^ 2 * T) * Real.exp ((2 * KF L β γ M + 1) * T)) := by
    rw [mul_pow, hE]
    nlinarith [mul_le_mul_of_nonneg_right hann hEp]
  have hs : Real.sqrt ((dsq σ (trunc S' u₀ - trunc S u₀) +
        (Real.exp (-(2 * σ * N)) * G L β γ M) ^ 2 * T) * Real.exp ((2 * KF L β γ M + 1) * T)) ≤
      Real.exp (-(2 * σ * N)) *
        Real.sqrt ((asq σ u₀ + G L β γ M ^ 2 * T) * Real.exp ((2 * KF L β γ M + 1) * T)) := by
    calc _ ≤ Real.sqrt (Real.exp (-(2 * σ * N)) ^ 2 *
          ((asq σ u₀ + G L β γ M ^ 2 * T) * Real.exp ((2 * KF L β γ M + 1) * T))) :=
          Real.sqrt_le_sqrt hX
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
  have hc : 0 ≤ CA L * anorm σ χv * (2 * M) :=
    mul_nonneg (mul_nonneg (CA_nonneg hL) (anorm_nonneg _ _)) (by linarith)
  calc |Jdet L χv (w T) - Jdet L χv (u T)|
      ≤ CA L * anorm σ χv * (2 * M) * Real.sqrt ((dsq σ (trunc S' u₀ - trunc S u₀) +
        (Real.exp (-(2 * σ * N)) * G L β γ M) ^ 2 * T) *
          Real.exp ((2 * KF L β γ M + 1) * T)) := h
    _ ≤ CA L * anorm σ χv * (2 * M) * (Real.exp (-(2 * σ * N)) *
        Real.sqrt ((asq σ u₀ + G L β γ M ^ 2 * T) * Real.exp ((2 * KF L β γ M + 1) * T))) :=
        mul_le_mul_of_nonneg_left hs hc
    _ = _ := by ring

/-- **Cutoff for a margin-`m` readout.** If `2σN ≥ log(B/m)`, then `B e^{−2σN} ≤ m`. -/
theorem cutoff_for_margin {σ N B m : ℝ} (hB : 0 < B) (hm : 0 < m)
    (hN : Real.log (B / m) ≤ 2 * σ * N) : B * Real.exp (-(2 * σ * N)) ≤ m := by
  have h1 : Real.exp (Real.log (B / m)) ≤ Real.exp (2 * σ * N) := Real.exp_le_exp.2 hN
  rw [Real.exp_log (div_pos hB hm)] at h1
  have h2 : Real.exp (2 * σ * N) * Real.exp (-(2 * σ * N)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h3 := (div_le_iff₀ hm).1 h1
  have hp := (Real.exp_pos (-(2 * σ * N))).le
  nlinarith [mul_le_mul_of_nonneg_right h3 hp]

end PVNP.DetectorDynamic
