import PVNP.GalerkinTaylorNorm
import PVNP.UniformGalerkinRadius

/-!
# The actual Galerkin trajectory is the sum of its Taylor series

This module identifies the frozen cubic–quintic Galerkin trajectory with its Taylor series. It
uses the coefficient majorant of `GalerkinTaylorNorm` and gives an explicit analyticity
radius.

* The physical-picture trajectory `u(t) = U(t) W(t)` of an actual interaction-picture Galerkin
  trajectory `W` solves the autonomous system `u' = −i (A_S u + P_S Fnl(u))`
  (`hasDerivAt_phys`). Here `A_S` is the diagonal dispersion on the mode set `S`.
* `coeff` is the coefficient sequence of that system, defined by the exact recursion
  `(n+1) c_{n+1} = −i (A_S c_n + P_S [Fnl]_n)`, `c_0 = u(t₀)`.
* `hasSum_mulH_pow`: the product `mulH` of two absolutely convergent power series is the power
  series of the coefficientwise Cauchy product `cauchyH`. `hasSum_Fnl` applies this to the
  actual nonlinearity.
* `galerkin_taylor_series`: suppose `‖u(t)‖ ≤ K` for all `t`, `om k ≤ Ω` on `S`, and `λ r ≤ 1/2`
  with `λ = 4(Ω + 64|β|C_A²K² + 4096|γ|C_A⁴K⁴)`. Then for every `t₀` and every `|h| < r`,
  `u(t₀ + h) = Σ_n h^n c_n(u(t₀))`. The proof is termwise differentiation followed by ODE
  uniqueness (`ODE_solution_unique_of_mem_Ioo`) on the ball of radius `2K`.
* `taylor_poly_error`: the degree-`q` Taylor polynomial has error at most `2K (λ|h|)^{q+1}`.
* `actual_galerkin_taylor`: these apply with `K = uniformRadius L κ β γ B` to the actual global
  Galerkin trajectory of `exists_uniform_galerkin`, so `K` does not depend on `S`.
-/

namespace PVNP.GalerkinTaylor

open Finset Filter Topology PVNP.Torus PVNP.TaylorMajorant PVNP.TorusGalerkin Complex

variable {L : ℝ}

/-! ### Products of convergent power series through `mulH` -/

/-- `mulH L x` as a continuous linear map in its second argument. -/
noncomputable def mulHR (hL : 0 < L) (x : ℓ2) : ℓ2 →L[ℂ] ℓ2 :=
  LinearMap.mkContinuous
    { toFun := mulH L x
      map_add' := mulH_add_right hL x
      map_smul' := fun c w => by rw [mulH_smul_right hL, RingHom.id_apply] }
    (CA L * ‖x‖) (fun w => norm_mulH_le hL x w)

/-- `mulH L · y` as a continuous linear map in its first argument. -/
noncomputable def mulHL (hL : 0 < L) (y : ℓ2) : ℓ2 →L[ℂ] ℓ2 :=
  LinearMap.mkContinuous
    { toFun := fun x => mulH L x y
      map_add' := fun x x' => mulH_add_left hL x x' y
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        exact mulH_smul_left hL c x y }
    (CA L * ‖y‖) (fun x => by
      have h := norm_mulH_le hL x y
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      linarith [mul_comm (CA L * ‖y‖) ‖x‖, mul_assoc (CA L) ‖x‖ ‖y‖,
        mul_assoc (CA L) ‖y‖ ‖x‖, mul_comm ‖x‖ ‖y‖])

/-- **Bilinear Cauchy product.** Absolutely convergent series multiply through `mulH` along
antidiagonals. -/
theorem hasSum_mulH (hL : 0 < L) {f g : ℕ → ℓ2}
    (hf : Summable fun n => ‖f n‖) (hg : Summable fun n => ‖g n‖) :
    HasSum (fun n => ∑ ij ∈ antidiagonal n, mulH L (f ij.1) (g ij.2))
      (mulH L (∑' n, f n) (∑' n, g n)) := by
  set F : ℕ × ℕ → ℓ2 := fun p => mulH L (f p.1) (g p.2) with hFdef
  have hC := CA_nonneg hL
  have hFn : Summable fun p : ℕ × ℕ => ‖F p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (((hf.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))).mul_left (CA L))
    have := norm_mulH_le hL (f p.1) (g p.2)
    simp only [hFdef]
    linarith [mul_assoc (CA L) ‖f p.1‖ ‖g p.2‖]
  have hF : Summable F := hFn.of_norm
  have hfs : Summable f := hf.of_norm
  have hgs : Summable g := hg.of_norm
  have htot : ∑' p, F p = mulH L (∑' n, f n) (∑' n, g n) := by
    rw [hF.tsum_prod' (fun i => hF.prod_factor i)]
    have h1 : ∀ i, ∑' j, F (i, j) = mulH L (f i) (∑' n, g n) := by
      intro i
      have := (mulHR hL (f i)).map_tsum hgs
      simp only [mulHR, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [this]
    simp_rw [h1]
    have := (mulHL hL (∑' n, g n)).map_tsum hfs
    simp only [mulHL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this]
  rw [← htot]
  have hs := (Finset.sigmaAntidiagonalEquivProd.hasSum_iff (f := F)).mpr hF.hasSum
  have h2 := hs.sigma (fun n => hasSum_fintype _)
  convert h2 using 1
  funext n
  simp only [Function.comp_apply, Finset.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.sum_coe_sort (antidiagonal n) (fun ij => F ij)]

/-- Real scalars act on `ℓ²` through their complex image. -/
theorem real_smul_eq (r : ℝ) (v : ℓ2) : r • v = (r : ℂ) • v := by
  ext k
  simp only [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

theorem mulH_real_smul (hL : 0 < L) (a b : ℝ) (v w : ℓ2) :
    mulH L (a • v) (b • w) = (a * b) • mulH L v w := by
  rw [real_smul_eq a, real_smul_eq b, real_smul_eq (a * b), mulH_smul_left hL,
    mulH_smul_right hL, smul_smul, Complex.ofReal_mul]

/-- **Cauchy product of power series through `mulH`.** -/
theorem hasSum_mulH_pow (hL : 0 < L) {X Y : ℕ → ℓ2} {h : ℝ} {a b : ℓ2}
    (hX : Summable fun n => ‖h ^ n • X n‖) (hY : Summable fun n => ‖h ^ n • Y n‖)
    (ha : HasSum (fun n => h ^ n • X n) a) (hb : HasSum (fun n => h ^ n • Y n) b) :
    HasSum (fun n => h ^ n • cauchyH L X Y n) (mulH L a b) := by
  have H := hasSum_mulH hL hX hY
  rw [ha.tsum_eq, hb.tsum_eq] at H
  convert H using 1
  funext n
  rw [Finset.sum_congr rfl (fun ij hij => by
      rw [mulH_real_smul hL, ← pow_add, Finset.mem_antidiagonal.mp hij]),
    ← Finset.smul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => mulH L (X i) (Y j)) n]
  rfl

/-! ### Conjugation and the nonlinearity along a power series -/

theorem conjH_add (v w : ℓ2) : conjH (v + w) = conjH v + conjH w := by
  ext k
  simp only [conjH_apply, lp.coeFn_add, Pi.add_apply, map_add]

theorem conjH_real_smul (r : ℝ) (v : ℓ2) : conjH (r • v) = r • conjH v := by
  ext k
  simp only [conjH_apply, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, map_mul,
    Complex.conj_ofReal]

/-- Conjugation as a real continuous linear map. -/
noncomputable def conjL : ℓ2 →L[ℝ] ℓ2 :=
  LinearMap.mkContinuous
    { toFun := conjH
      map_add' := conjH_add
      map_smul' := fun r v => by rw [conjH_real_smul, RingHom.id_apply] }
    1 (fun v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_conjH, one_mul, le_refl])

theorem hasSum_conjSeq {c : ℕ → ℓ2} {h : ℝ} {a : ℓ2} (ha : HasSum (fun n => h ^ n • c n) a) :
    HasSum (fun n => h ^ n • conjSeq c n) (conjH a) := by
  have := conjL.hasSum ha
  simp only [conjL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    conjH_real_smul] at this
  exact this

/-- Coefficient sequences dominated by `A rⁿ/(n+1)²`. -/
def Dom (A r : ℝ) (X : ℕ → ℓ2) : Prop := ∀ n, ‖X n‖ ≤ A * r ^ n * TaylorMajorant.wt n

theorem sum_range_wt_le_two (n : ℕ) : ∑ i ∈ range n, TaylorMajorant.wt i ≤ 2 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
    (fun i _ _ => (TaylorMajorant.wt_pos i).le)).trans (sum_wt_le_two n)

theorem summable_wt : Summable TaylorMajorant.wt :=
  summable_of_sum_range_le (fun n => (TaylorMajorant.wt_pos n).le) sum_range_wt_le_two

theorem tsum_wt_le_two : ∑' n, TaylorMajorant.wt n ≤ 2 :=
  Real.tsum_le_of_sum_range_le (fun n => (TaylorMajorant.wt_pos n).le) sum_range_wt_le_two

theorem norm_pow_smul_le {A r h : ℝ} {X : ℕ → ℓ2} (hX : Dom A r X) (n : ℕ) : ‖h ^ n • X n‖ ≤ A * (r * |h|) ^ n * TaylorMajorant.wt n := by
  rw [norm_smul, norm_pow, Real.norm_eq_abs, mul_pow]
  calc |h| ^ n * ‖X n‖ ≤ |h| ^ n * (A * r ^ n * TaylorMajorant.wt n) :=
        mul_le_mul_of_nonneg_left (hX n) (by positivity)
    _ = A * (r ^ n * |h| ^ n) * TaylorMajorant.wt n := by ring

theorem Dom.summable {A r h : ℝ} {X : ℕ → ℓ2} (hX : Dom A r X) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hrh : r * |h| ≤ 1) : Summable fun n => ‖h ^ n • X n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_wt.mul_left A)
  have h1 := norm_pow_smul_le (h := h) hX n
  have h2 : (r * |h|) ^ n ≤ 1 := pow_le_one₀ (by positivity) hrh
  have h3 := TaylorMajorant.wt_pos n
  calc ‖h ^ n • X n‖ ≤ A * (r * |h|) ^ n * TaylorMajorant.wt n := h1
    _ ≤ A * 1 * TaylorMajorant.wt n := by gcongr
    _ = A * TaylorMajorant.wt n := by ring

theorem Dom.hasSum {A r h : ℝ} {X : ℕ → ℓ2} (hX : Dom A r X) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hrh : r * |h| ≤ 1) : HasSum (fun n => h ^ n • X n) (∑' n, h ^ n • X n) :=
  (hX.summable hA hr hrh).of_norm.hasSum

theorem Dom.cprod (hL : 0 < L) {A B r : ℝ} {X Y : ℕ → ℓ2} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hX : Dom A r X) (hY : Dom B r Y) :
    Dom (CA L * (8 * A * B)) r (cauchyH L X Y) := by
  intro n
  have h1 := norm_cauchyH_le hL X Y n
  have h2 := cauchy_bound (a := fun k => ‖X k‖) (b := fun k => ‖Y k‖) (n := n) hA hB hr
    (fun _ => norm_nonneg _) (fun k _ => hX k) (fun k _ => hY k)
  have hC := CA_nonneg hL
  calc ‖cauchyH L X Y n‖ ≤ CA L * cauchy (fun k => ‖X k‖) (fun k => ‖Y k‖) n := h1
    _ ≤ CA L * (8 * A * B * r ^ n * TaylorMajorant.wt n) := mul_le_mul_of_nonneg_left h2 hC
    _ = CA L * (8 * A * B) * r ^ n * TaylorMajorant.wt n := by ring

theorem Dom.conj {A r : ℝ} {X : ℕ → ℓ2} (hX : Dom A r X) : Dom A r (conjSeq X) :=
  fun n => by rw [norm_conjSeq]; exact hX n

/-- **The nonlinearity along a dominated power series.** -/
theorem hasSum_Fnl (hL : 0 < L) (β γ : ℝ) {c : ℕ → ℓ2} {K r h : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hc : Dom K r c) (hrh : r * |h| ≤ 1) :
    HasSum (fun n => h ^ n • fnlCoeff L β γ c n) (Fnl L β γ (∑' n, h ^ n • c n)) := by
  set s := ∑' n, h ^ n • c n
  have hC := CA_nonneg hL
  have hs : HasSum (fun n => h ^ n • c n) s := hc.hasSum hK hr hrh
  have hcs := hc.summable hK hr hrh
  have hj := hc.conj
  have hjs := hj.summable hK hr hrh
  have hjS : HasSum (fun n => h ^ n • conjSeq c n) (conjH s) := hasSum_conjSeq hs
  -- level 2
  have d2 := Dom.cprod hL hK hK hr hc hc
  have n2 : 0 ≤ CA L * (8 * K * K) := by positivity
  have s2 := hasSum_mulH_pow hL hcs hcs hs hs
  have m2 := d2.summable n2 hr hrh
  -- cubic branch
  have s3 := hasSum_mulH_pow hL m2 hjs s2 hjS
  -- quintic branch
  have d3' := Dom.cprod hL n2 hK hr d2 hc
  have n3 : 0 ≤ CA L * (8 * (CA L * (8 * K * K)) * K) := by positivity
  have s3' := hasSum_mulH_pow hL m2 hcs s2 hs
  have m3' := d3'.summable n3 hr hrh
  have d4 := Dom.cprod hL n3 hK hr d3' hj
  have n4 : 0 ≤ CA L * (8 * (CA L * (8 * (CA L * (8 * K * K)) * K)) * K) := by positivity
  have s4 := hasSum_mulH_pow hL m3' hjs s3' hjS
  have m4 := d4.summable n4 hr hrh
  have s5 := hasSum_mulH_pow hL m4 hjs s4 hjS
  have H := (s3.const_smul (-(β : ℂ))).add (s5.const_smul (γ : ℂ))
  rw [Fnl]
  convert H using 1
  funext n
  unfold fnlCoeff
  rw [smul_add]
  congr 1
  · rw [real_smul_eq, real_smul_eq, smul_smul, smul_smul, mul_comm]
  · rw [real_smul_eq, real_smul_eq, smul_smul, smul_smul, mul_comm]

/-! ### The physical-picture Galerkin system -/

theorem om_nonneg (L κ : ℝ) (k : Z2) : 0 ≤ om L κ k := sq_nonneg _

/-- A crude bound for the dispersion on `S`; any `Ω ≥ om` on `S` may be used instead. -/
noncomputable def omSum (L κ : ℝ) (S : Finset Z2) : ℝ := ∑ k ∈ S, om L κ k

theorem omSum_nonneg (L κ : ℝ) (S : Finset Z2) : 0 ≤ omSum L κ S :=
  Finset.sum_nonneg fun k _ => om_nonneg L κ k

theorem om_le_omSum (L κ : ℝ) (S : Finset Z2) {k : Z2} (hk : k ∈ S) :
    om L κ k ≤ omSum L κ S :=
  Finset.single_le_sum (fun j _ => om_nonneg L κ j) hk

/-- The multiplier of the restricted dispersion. -/
noncomputable def omMul (L κ : ℝ) (S : Finset Z2) (k : Z2) : ℂ :=
  if k ∈ S then ((om L κ k : ℝ) : ℂ) else 0

theorem norm_omMul_le (L κ : ℝ) (S : Finset Z2) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hS : ∀ k ∈ S, om L κ k ≤ Ω) (k : Z2) : ‖omMul L κ S k‖ ≤ Ω := by
  unfold omMul
  split_ifs with hk
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (om_nonneg L κ k)]
    exact hS k hk
  · rw [norm_zero]; exact hΩ

/-- The dispersion `(Δ+κ)²` restricted to the mode set `S`. -/
noncomputable def Aop (L κ : ℝ) (S : Finset Z2) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (omMul L κ S) (omSum L κ S) (omSum_nonneg L κ S)
    (norm_omMul_le L κ S (omSum_nonneg L κ S) (fun _ hk => om_le_omSum L κ S hk))

theorem Aop_apply (L κ : ℝ) (S : Finset Z2) (v : ℓ2) (k : Z2) :
    Aop L κ S v k = omMul L κ S k * v k := by
  simp only [Aop, dmul_apply]

theorem norm_Aop_le (L κ : ℝ) (S : Finset Z2) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hS : ∀ k ∈ S, om L κ k ≤ Ω) (v : ℓ2) : ‖Aop L κ S v‖ ≤ Ω * ‖v‖ := by
  have e : Aop L κ S v = dmul (omMul L κ S) Ω hΩ (norm_omMul_le L κ S hΩ hS) v := by
    ext k; rw [Aop_apply, dmul_apply]
  rw [e]
  unfold dmul
  exact ContinuousLinearMap.le_of_opNorm_le _ (LinearMap.mkContinuous_norm_le _ hΩ _) v

/-- The physical-picture Galerkin vector field `−i (A_S u + P_S Fnl u)`. -/
noncomputable def physField (L κ β γ : ℝ) (S : Finset Z2) (u : ℓ2) : ℓ2 :=
  (-I) • (Aop L κ S u + trunc S (Fnl L β γ u))

/-- **Physical picture.** If `W` is an actual interaction-picture Galerkin trajectory supported
in `S`, then `u(t) = U(t) W(t)` solves `u' = −i (A_S u + P_S Fnl u)`. -/
theorem hasDerivAt_phys (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {W : ℝ → ℓ2}
    (hs : ∀ t, Supported S (W t)) (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (t : ℝ) :
    HasDerivAt (fun s => U L κ s (W s)) (physField L κ β γ S (U L κ t (W t))) t := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hu : Continuous fun s => U L κ s (W s) := continuous_U_path hWc
  have hcont : Continuous fun s => physField L κ β γ S (U L κ s (W s)) := by
    unfold physField
    exact continuous_const.smul (((Aop L κ S).continuous.comp hu).add
      ((trunc_lipschitz S).continuous.comp ((continuous_Fnl hL β γ).comp hu)))
  refine hasDerivAt_of_coeff hcont (fun s k => ?_) t
  have hprod := (hasDerivAt_ph L κ s k).mul (hasDerivAt_apply (hW s) k)
  have hU := congrArg (fun v : ℓ2 => v k)
    (U_galerkin (L := L) (κ := κ) (β := β) (γ := γ) S s (hs s))
  simp only [U_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hU
  simp only [U_apply]
  convert hprod using 1
  rw [hU]
  simp only [physField, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, Pi.add_apply,
    Aop_apply, trunc_apply, omMul, U_apply]
  by_cases hk : k ∈ S
  · simp only [hk, if_true]; ring
  · simp only [hk, if_false, hs s k hk]; ring

/-! ### The Taylor coefficients -/

/-- The right side of `(n+1) c_{n+1} = −i (A_S c_n + P_S [Fnl]_n)`. -/
noncomputable def rhs (L κ β γ : ℝ) (S : Finset Z2) (c : ℕ → ℓ2) (n : ℕ) : ℓ2 :=
  (-I) • (Aop L κ S (c n) + trunc S (fnlCoeff L β γ c n))

/-- Prefixes of the coefficient sequence, built by structural recursion. -/
noncomputable def pre (L κ β γ : ℝ) (S : Finset Z2) (u₀ : ℓ2) : ℕ → ℕ → ℓ2
  | 0 => fun k => if k = 0 then u₀ else 0
  | n + 1 => fun k => if k ≤ n then pre L κ β γ S u₀ n k
      else if k = n + 1 then ((n : ℝ) + 1)⁻¹ • rhs L κ β γ S (pre L κ β γ S u₀ n) n else 0

/-- The Taylor coefficients of the physical-picture Galerkin system at `u₀`. -/
noncomputable def coeff (L κ β γ : ℝ) (S : Finset Z2) (u₀ : ℓ2) (n : ℕ) : ℓ2 :=
  pre L κ β γ S u₀ n n

theorem pre_eq_coeff (L κ β γ : ℝ) (S : Finset Z2) (u₀ : ℓ2) :
    ∀ n k, k ≤ n → pre L κ β γ S u₀ n k = coeff L κ β γ S u₀ k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    rfl
  | succ n ih =>
    intro k hk
    by_cases hkn : k ≤ n
    · show (if k ≤ n then pre L κ β γ S u₀ n k else _) = _
      rw [if_pos hkn]
      exact ih k hkn
    · obtain rfl : k = n + 1 := by omega
      rfl

theorem coeff_zero (L κ β γ : ℝ) (S : Finset Z2) (u₀ : ℓ2) : coeff L κ β γ S u₀ 0 = u₀ := by
  show (if (0:ℕ) = 0 then u₀ else 0) = u₀
  rw [if_pos rfl]

theorem cauchyH_congr {X X' Y Y' : ℕ → ℓ2} {n : ℕ} (hX : ∀ k ≤ n, X k = X' k)
    (hY : ∀ k ≤ n, Y k = Y' k) : cauchyH L X Y n = cauchyH L X' Y' n := by
  unfold cauchyH
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hX i hin, hY (n - i) (Nat.sub_le n i)]

theorem fnlCoeff_congr (β γ : ℝ) {c c' : ℕ → ℓ2} {n : ℕ} (h : ∀ k ≤ n, c k = c' k) :
    fnlCoeff L β γ c n = fnlCoeff L β γ c' n := by
  have h2 : ∀ k ≤ n, cauchyH L c c k = cauchyH L c' c' k := fun k hk =>
    cauchyH_congr (fun j hj => h j (hj.trans hk)) (fun j hj => h j (hj.trans hk))
  have hcj : ∀ k ≤ n, conjSeq c k = conjSeq c' k := fun k hk => by
    simp only [conjSeq, h k hk]
  have h3 : ∀ k ≤ n, cauchyH L (cauchyH L c c) c k = cauchyH L (cauchyH L c' c') c' k :=
    fun k hk => cauchyH_congr (fun j hj => h2 j (hj.trans hk)) (fun j hj => h j (hj.trans hk))
  have h4 : ∀ k ≤ n, cauchyH L (cauchyH L (cauchyH L c c) c) (conjSeq c) k =
      cauchyH L (cauchyH L (cauchyH L c' c') c') (conjSeq c') k := fun k hk =>
    cauchyH_congr (fun j hj => h3 j (hj.trans hk)) (fun j hj => hcj j (hj.trans hk))
  unfold fnlCoeff
  rw [cauchyH_congr (X' := cauchyH L c' c') (Y' := conjSeq c') h2 hcj,
    cauchyH_congr (X' := cauchyH L (cauchyH L (cauchyH L c' c') c') (conjSeq c'))
      (Y' := conjSeq c') h4 hcj]

theorem rhs_congr (κ β γ : ℝ) (S : Finset Z2) {c c' : ℕ → ℓ2} {n : ℕ}
    (h : ∀ k ≤ n, c k = c' k) : rhs L κ β γ S c n = rhs L κ β γ S c' n := by
  unfold rhs
  rw [h n le_rfl, fnlCoeff_congr β γ h]

theorem coeff_succ (L κ β γ : ℝ) (S : Finset Z2) (u₀ : ℓ2) (n : ℕ) :
    coeff L κ β γ S u₀ (n+1) = ((n : ℝ) + 1)⁻¹ • rhs L κ β γ S (coeff L κ β γ S u₀) n := by
  have e : coeff L κ β γ S u₀ (n+1) =
      ((n : ℝ) + 1)⁻¹ • rhs L κ β γ S (pre L κ β γ S u₀ n) n := by
    show (if n + 1 ≤ n then _ else if n + 1 = n + 1 then _ else _) = _
    rw [if_neg (by omega), if_pos rfl]
  rw [e, rhs_congr κ β γ S (fun k hk => pre_eq_coeff L κ β γ S u₀ n k hk)]

/-- The recursion in multiplied form. -/
theorem coeff_recursion (L κ β γ : ℝ) (S : Finset Z2) (u₀ : ℓ2) (n : ℕ) :
    ((n : ℝ) + 1) • coeff L κ β γ S u₀ (n+1) = rhs L κ β γ S (coeff L κ β γ S u₀) n := by
  rw [coeff_succ, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- **Coefficient majorant for the actual recursion.** -/
theorem coeff_dom (hL : 0 < L) (κ β γ : ℝ) (S : Finset Z2) {u₀ : ℓ2} {K Ω : ℝ}
    (hK : 0 ≤ K) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω) (h0 : ‖u₀‖ ≤ K) :
    Dom K (rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4)) (coeff L κ β γ S u₀) := by
  refine galerkin_taylor_majorant hL β γ hK hΩ (by rwa [coeff_zero]) (fun n => ?_)
  have e := congrArg norm (coeff_recursion L κ β γ S u₀ n)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ) + 1)] at e
  rw [e]
  unfold rhs
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_Aop_le L κ S hΩ hS _) (trunc_norm_le S _))

/-! ### Summation, differentiation and uniqueness -/

theorem rate_nonneg {K Ω B G : ℝ} (hΩ : 0 ≤ Ω) (hB : 0 ≤ B) (hG : 0 ≤ G) :
    0 ≤ rate K Ω B G := by
  unfold rate; positivity

theorem nat_mul_wt_le (n : ℕ) : (n : ℝ) * TaylorMajorant.wt n ≤ 1 := by
  unfold TaylorMajorant.wt
  rw [mul_one_div, div_le_one (by positivity)]
  nlinarith

theorem trunc_add (S : Finset Z2) (v w : ℓ2) : trunc S (v + w) = trunc S v + trunc S w := by
  ext k
  simp only [trunc_apply, lp.coeFn_add, Pi.add_apply]
  split_ifs <;> simp

/-- `trunc S` as a continuous linear map. -/
noncomputable def truncL (S : Finset Z2) : ℓ2 →L[ℂ] ℓ2 :=
  LinearMap.mkContinuous
    { toFun := trunc S
      map_add' := trunc_add S
      map_smul' := fun c v => by rw [trunc_smul, RingHom.id_apply] }
    1 (fun v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact trunc_norm_le S v)

theorem truncL_apply (S : Finset Z2) (v : ℓ2) : truncL S v = trunc S v := rfl

theorem real_smul_comm_I (r : ℝ) (v : ℓ2) : r • ((-I) • v) = (-I) • (r • v) := by
  rw [real_smul_eq, real_smul_eq, smul_smul, smul_smul, mul_comm]

/-- The physical field along a dominated Taylor series. -/
theorem hasSum_rhs (hL : 0 < L) (κ β γ : ℝ) (S : Finset Z2) {c : ℕ → ℓ2} {K r h : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hc : Dom K r c) (hrh : r * |h| ≤ 1) :
    HasSum (fun n => h ^ n • rhs L κ β γ S c n) (physField L κ β γ S (∑' n, h ^ n • c n)) := by
  have hs := hc.hasSum hK hr hrh
  have hA := (Aop L κ S).hasSum hs
  have hF := (truncL S).hasSum (hasSum_Fnl hL β γ hK hr hc hrh)
  have H := (hA.add hF).const_smul (-I)
  unfold physField
  rw [← truncL_apply]
  convert H using 1
  funext n
  unfold rhs
  rw [real_smul_comm_I]
  congr 1
  simp only [smul_add, real_smul_eq, map_smul, truncL_apply]

theorem norm_deriv_term_le {c : ℕ → ℓ2} {K lam r : ℝ} (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (hr : 0 ≤ r) (hc : Dom K lam c) (hlr : lam * r ≤ 1/2) (n : ℕ) {y : ℝ} (hy : |y| ≤ r) :
    ‖((n : ℝ) * y ^ (n - 1)) • c n‖ ≤ 2 * K * lam * (1/2 : ℝ) ^ n := by
  rcases n with _ | m
  · simp only [Nat.cast_zero, zero_mul, zero_smul, norm_zero]; positivity
  · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast, Nat.add_sub_cancel]
    have h1 := hc (m+1)
    have h2 : |y| ^ m ≤ r ^ m := pow_le_pow_left₀ (abs_nonneg y) hy m
    have h3 : (lam * r) ^ m ≤ (1/2) ^ m := pow_le_pow_left₀ (by positivity) hlr m
    have h4 := nat_mul_wt_le (m+1)
    have h5 := TaylorMajorant.wt_pos (m+1)
    calc ((m+1 : ℕ) : ℝ) * |y| ^ m * ‖c (m+1)‖
        ≤ ((m+1 : ℕ) : ℝ) * r ^ m * (K * lam ^ (m+1) * TaylorMajorant.wt (m+1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)) h1 (norm_nonneg _)
            (by positivity)
      _ = K * lam * (lam * r) ^ m * (((m+1 : ℕ) : ℝ) * TaylorMajorant.wt (m+1)) := by ring
      _ ≤ K * lam * (1/2) ^ m * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h3 (by positivity)) h4 (by positivity)
            (by positivity)
      _ = 2 * K * lam * (1/2) ^ (m+1) := by ring

/-- **Termwise differentiation** of a dominated Taylor series on `(−r, r)`. -/
theorem hasDerivAt_series {c : ℕ → ℓ2} {K lam r : ℝ} (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (hr : 0 < r) (hc : Dom K lam c) (hlr : lam * r ≤ 1/2) {h : ℝ} (hh : h ∈ Set.Ioo (-r) r) :
    HasDerivAt (fun y => ∑' n : ℕ, y ^ n • c n) (∑' n : ℕ, ((n : ℝ) * h ^ (n - 1)) • c n) h := by
  have hsum : Summable fun n : ℕ => 2 * K * lam * (1/2 : ℝ) ^ n :=
    summable_geometric_two.mul_left _
  have h0 : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hg0 : Summable fun n : ℕ => (0:ℝ) ^ n • c n :=
    (hc.summable hK hlam (by simp)).of_norm
  exact hasDerivAt_tsum_of_isPreconnected (g := fun n y => y ^ n • c n)
    (g' := fun n y => ((n : ℝ) * y ^ (n - 1)) • c n) hsum isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_pow n y).smul_const (c n))
    (fun n y hy => norm_deriv_term_le hK hlam hr.le hc hlr n (abs_lt.mpr ⟨hy.1, hy.2⟩).le)
    h0 hg0 hh

theorem series_zero (c : ℕ → ℓ2) : ∑' n, (0:ℝ) ^ n • c n = c 0 := by
  rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, zero_smul]), pow_zero, one_smul]

theorem norm_series_le {c : ℕ → ℓ2} {K lam h : ℝ} (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (hc : Dom K lam c) (hlh : lam * |h| ≤ 1) : ‖∑' n, h ^ n • c n‖ ≤ 2 * K := by
  have hs := hc.summable hK hlam hlh
  calc ‖∑' n, h ^ n • c n‖ ≤ ∑' n, ‖h ^ n • c n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, K * TaylorMajorant.wt n := by
        refine Summable.tsum_le_tsum (fun n => ?_) hs (summable_wt.mul_left K)
        have h1 := norm_pow_smul_le (h := h) hc n
        have h2 : (lam * |h|) ^ n ≤ 1 := pow_le_one₀ (by positivity) hlh
        have h3 := TaylorMajorant.wt_pos n
        calc ‖h ^ n • c n‖ ≤ K * (lam * |h|) ^ n * TaylorMajorant.wt n := h1
          _ ≤ K * 1 * TaylorMajorant.wt n := by gcongr
          _ = K * TaylorMajorant.wt n := by ring
    _ = K * ∑' n, TaylorMajorant.wt n := tsum_mul_left
    _ ≤ K * 2 := mul_le_mul_of_nonneg_left tsum_wt_le_two hK
    _ = 2 * K := by ring

/-- **The Taylor series solves the physical-picture Galerkin system** on `(−r, r)`. -/
theorem series_solves (hL : 0 < L) (κ β γ : ℝ) (S : Finset Z2) {u₀ : ℓ2} {K Ω r : ℝ}
    (hK : 0 ≤ K) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω) (h0 : ‖u₀‖ ≤ K) (hr : 0 < r)
    (hlr : rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * r ≤ 1/2) {h : ℝ}
    (hh : h ∈ Set.Ioo (-r) r) :
    HasDerivAt (fun y => ∑' n, y ^ n • coeff L κ β γ S u₀ n)
      (physField L κ β γ S (∑' n, h ^ n • coeff L κ β γ S u₀ n)) h := by
  have hC := CA_nonneg hL
  have hlam : 0 ≤ rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) :=
    rate_nonneg hΩ (by positivity) (by positivity)
  have hc := coeff_dom hL κ β γ S hK hΩ hS h0
  have hD := hasDerivAt_series hK hlam hr hc hlr hh
  have hh' : |h| ≤ r := (abs_lt.mpr ⟨hh.1, hh.2⟩).le
  have hlh : rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * |h| ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hh' hlam
    linarith
  have hsum : Summable fun n : ℕ => ((n:ℝ) * h ^ (n-1)) • coeff L κ β γ S u₀ n :=
    Summable.of_norm_bounded (summable_geometric_two.mul_left _)
      (fun n => norm_deriv_term_le hK hlam hr.le hc hlr n hh')
  have key : ∑' n : ℕ, ((n:ℝ) * h ^ (n-1)) • coeff L κ β γ S u₀ n =
      physField L κ β γ S (∑' n, h ^ n • coeff L κ β γ S u₀ n) := by
    rw [hsum.tsum_eq_zero_add, ← (hasSum_rhs hL κ β γ S hK hlam hc hlh).tsum_eq]
    simp only [CharP.cast_eq_zero, zero_mul, zero_smul, zero_add]
    refine tsum_congr fun m => ?_
    rw [← coeff_recursion, smul_smul, Nat.add_sub_cancel]
    congr 1
    push_cast
    ring
  rw [key] at hD
  exact hD

/-- The physical field is Lipschitz on every ball. -/
theorem physField_lipschitz (hL : 0 < L) (κ β γ : ℝ) (S : Finset Z2) {Ω R : ℝ} (hΩ : 0 ≤ Ω)
    (hS : ∀ k ∈ S, om L κ k ≤ Ω) :
    LipschitzOnWith (Real.toNNReal (Ω + LF L β γ R)) (physField L κ β γ S)
      (Metric.closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Metric.mem_closedBall, dist_zero_right] at hx hy
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (add_nonneg hΩ (LF_nonneg L β γ R))]
  unfold physField
  rw [← smul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul, add_sub_add_comm, ← map_sub,
    ← trunc_sub]
  calc ‖Aop L κ S (x - y) + trunc S (Fnl L β γ x - Fnl L β γ y)‖
      ≤ ‖Aop L κ S (x - y)‖ + ‖trunc S (Fnl L β γ x - Fnl L β γ y)‖ := norm_add_le _ _
    _ ≤ Ω * ‖x - y‖ + LF L β γ R * ‖x - y‖ :=
        add_le_add (norm_Aop_le L κ S hΩ hS _)
          ((trunc_norm_le S _).trans (norm_Fnl_sub_le hL β γ hx hy))
    _ = (Ω + LF L β γ R) * ‖x - y‖ := by ring

/-- **Identification: the actual trajectory is the sum of its Taylor series.** For any solution
of the physical-picture Galerkin system with `‖u(t)‖ ≤ K` and `λ r ≤ 1/2`,
`u(t₀ + h) = Σ_n h^n c_n(u(t₀))` for all `t₀` and `|h| < r`. -/
theorem galerkin_taylor_series (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    {K Ω : ℝ} (hK : 0 ≤ K) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω)
    (hbd : ∀ t, ‖u t‖ ≤ K) (t₀ : ℝ) {r : ℝ} (hr : 0 < r)
    (hlr : rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * r ≤ 1/2) {h : ℝ} (hh : |h| < r) :
    HasSum (fun n => h ^ n • coeff L κ β γ S (u t₀) n) (u (t₀ + h)) := by
  have hC := CA_nonneg hL
  have hlam : 0 ≤ rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) :=
    rate_nonneg hΩ (by positivity) (by positivity)
  have hc := coeff_dom hL κ β γ S hK hΩ hS (hbd t₀)
  have hlh : ∀ y ∈ Set.Ioo (-r) r, rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * |y| ≤ 1 := by
    intro y hy
    have : |y| ≤ r := (abs_lt.mpr ⟨hy.1, hy.2⟩).le
    have := mul_le_mul_of_nonneg_left this hlam
    linarith
  have hmem : h ∈ Set.Ioo (-r) r := ⟨by linarith [neg_abs_le h], lt_of_le_of_lt (le_abs_self h) hh⟩
  have hEq : Set.EqOn (fun y => u (t₀ + y)) (fun y => ∑' n, y ^ n • coeff L κ β γ S (u t₀) n)
      (Set.Ioo (-r) r) := by
    refine ODE_solution_unique_of_mem_Ioo (v := fun _ => physField L κ β γ S)
      (s := fun _ => Metric.closedBall 0 (2 * K)) (K := Real.toNNReal (Ω + LF L β γ (2 * K)))
      (t₀ := 0) (fun _ _ => physField_lipschitz hL κ β γ S hΩ hS) ⟨by linarith, hr⟩
      (fun y _ => ⟨?_, ?_⟩) (fun y hy => ⟨?_, ?_⟩) ?_
    · have h1 := (hu (t₀ + y)).scomp y ((hasDerivAt_id y).const_add t₀)
      rw [one_smul] at h1
      exact h1
    · rw [Metric.mem_closedBall, dist_zero_right]
      linarith [hbd (t₀ + y)]
    · exact series_solves hL κ β γ S hK hΩ hS (hbd t₀) hr hlr hy
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_series_le hK hlam hc (hlh y hy)
    · show u (t₀ + 0) = ∑' n, (0:ℝ) ^ n • coeff L κ β γ S (u t₀) n
      rw [add_zero, series_zero, coeff_zero]
  have e := hEq hmem
  simp only at e
  rw [e]
  exact hc.hasSum hK hlam (hlh h hmem)

/-- **Taylor polynomial error.** -/
theorem taylor_poly_error (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {u : ℝ → ℓ2}
    (hu : ∀ t, HasDerivAt u (physField L κ β γ S (u t)) t)
    {K Ω : ℝ} (hK : 0 ≤ K) (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω)
    (hbd : ∀ t, ‖u t‖ ≤ K) (t₀ : ℝ) {r : ℝ} (hr : 0 < r)
    (hlr : rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * r ≤ 1/2) {h : ℝ} (hh : |h| < r)
    (q : ℕ) :
    ‖u (t₀ + h) - ∑ n ∈ range (q+1), h ^ n • coeff L κ β γ S (u t₀) n‖ ≤
      2 * K * (rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * |h|) ^ (q+1) := by
  have hC := CA_nonneg hL
  have hlam : 0 ≤ rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) :=
    rate_nonneg hΩ (by positivity) (by positivity)
  have hc := coeff_dom hL κ β γ S hK hΩ hS (hbd t₀)
  have hlh : rate K Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * |h| ≤ 1/2 := by
    have := mul_le_mul_of_nonneg_left hh.le hlam
    linarith
  have hs := galerkin_taylor_series hL hu hK hΩ hS hbd t₀ hr hlr hh
  have htail := (hasSum_nat_add_iff' (q+1)).mpr hs
  have e : u (t₀ + h) - ∑ n ∈ range (q+1), h ^ n • coeff L κ β γ S (u t₀) n =
      ∑' i, h ^ (i + (q+1)) • coeff L κ β γ S (u t₀) (i + (q+1)) := htail.tsum_eq.symm
  rw [e]
  have hsn : Summable fun i => ‖h ^ (i + (q+1)) • coeff L κ β γ S (u t₀) (i + (q+1))‖ :=
    (summable_nat_add_iff (f := fun n => ‖h ^ n • coeff L κ β γ S (u t₀) n‖) (q+1)).mpr
      (hc.summable hK hlam (by linarith))
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) (fun N => ?_)
  have ht := taylor_tail_le (a := fun n => ‖coeff L κ β γ S (u t₀) n‖) hK hlam (abs_nonneg h)
    hlh hc q (q + 1 + N)
  rw [Finset.sum_Ico_eq_sum_range, show q + 1 + N - (q + 1) = N by omega] at ht
  calc ∑ i ∈ range N, ‖h ^ (i + (q+1)) • coeff L κ β γ S (u t₀) (i + (q+1))‖
      = ∑ k ∈ range N, ‖coeff L κ β γ S (u t₀) (q + 1 + k)‖ * |h| ^ (q + 1 + k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_smul, norm_pow, Real.norm_eq_abs, mul_comm, add_comm k (q+1)]
    _ ≤ _ := ht

/-- An explicit admissible radius: `r = 1/(2λ + 1)`. -/
theorem radius_admissible {lam : ℝ} (hlam : 0 ≤ lam) :
    0 < 1 / (2 * lam + 1) ∧ lam * (1 / (2 * lam + 1)) ≤ 1/2 := by
  refine ⟨by positivity, ?_⟩
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  linarith

/-- **The actual frozen Galerkin trajectory is analytic in time, uniformly in `S`.** The global
trajectory of `exists_uniform_galerkin` has, in the physical picture, Taylor expansions at every
time with radius at least `1/(2λ+1)`. Here `λ` uses the `S`-independent bound
`K = uniformRadius L κ β γ B` and any bound `Ω` for the dispersion on `S`. -/
theorem actual_galerkin_taylor (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) (S : Finset Z2)
    {u₀ : ℓ2} {B : ℝ} (hB : ‖u₀‖ ≤ B) {Ω : ℝ} (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω) :
    ∃ W : ℝ → ℓ2, W 0 = trunc S u₀ ∧ (∀ t, Supported S (W t)) ∧
      (∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t) ∧
      ∀ (t₀ h : ℝ) (q : ℕ),
        |h| < 1 / (2 * rate (uniformRadius L κ β γ B) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) + 1) →
        HasSum (fun n => h ^ n • coeff L κ β γ S (U L κ t₀ (W t₀)) n)
            (U L κ (t₀ + h) (W (t₀ + h))) ∧
          ‖U L κ (t₀ + h) (W (t₀ + h)) -
              ∑ n ∈ range (q+1), h ^ n • coeff L κ β γ S (U L κ t₀ (W t₀)) n‖ ≤
            2 * uniformRadius L κ β γ B *
              (rate (uniformRadius L κ β γ B) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) * |h|) ^ (q+1) := by
  obtain ⟨W, h0, hs, hd, hbd⟩ := exists_uniform_galerkin (κ := κ) (β := β) hL hγ S hB
  refine ⟨W, h0, hs, hd, fun t₀ h q hh => ?_⟩
  have hC := CA_nonneg hL
  have hK := uniformRadius_nonneg L κ β γ B
  have hlam : 0 ≤ rate (uniformRadius L κ β γ B) Ω (|β| * CA L ^ 2) (|γ| * CA L ^ 4) :=
    rate_nonneg hΩ (by positivity) (by positivity)
  obtain ⟨hr, hlr⟩ := radius_admissible hlam
  have hu : ∀ t, HasDerivAt (fun s => U L κ s (W s))
      (physField L κ β γ S (U L κ t (W t))) t := hasDerivAt_phys hL hs hd
  have hb : ∀ t, ‖U L κ t (W t)‖ ≤ uniformRadius L κ β γ B := fun t => by
    rw [norm_U]; exact hbd t
  exact ⟨galerkin_taylor_series (u := fun s => U L κ s (W s)) hL hu hK hΩ hS hb t₀ hr hlr hh,
    taylor_poly_error (u := fun s => U L κ s (W s)) hL hu hK hΩ hS hb t₀ hr hlr hh q⟩

/-- **Every actual Galerkin trajectory is analytic in time.** No existence statement is involved:
for any interaction-picture Galerkin trajectory `W` supported in `S`, the physical state
`U(t)W(t)` is the sum of its Taylor series at every time. The radius is at least `1/(2λ+1)`, and
`K` is the a priori bound from the conserved mass and Hamiltonian of `W(0)`. -/
theorem galerkin_trajectory_taylor (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) {S : Finset Z2}
    {W : ℝ → ℓ2} (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    {Ω : ℝ} (hΩ : 0 ≤ Ω) (hS : ∀ k ∈ S, om L κ k ≤ Ω) (t₀ h : ℝ) (q : ℕ)
    (hh : |h| < 1 / (2 * rate (Rap κ β γ (mass L (W 0)) (ham L κ β γ (W 0))) Ω
      (|β| * CA L ^ 2) (|γ| * CA L ^ 4) + 1)) :
    HasSum (fun n => h ^ n • coeff L κ β γ S (U L κ t₀ (W t₀)) n)
        (U L κ (t₀ + h) (W (t₀ + h))) ∧
      ‖U L κ (t₀ + h) (W (t₀ + h)) -
          ∑ n ∈ range (q+1), h ^ n • coeff L κ β γ S (U L κ t₀ (W t₀)) n‖ ≤
        2 * Rap κ β γ (mass L (W 0)) (ham L κ β γ (W 0)) *
          (rate (Rap κ β γ (mass L (W 0)) (ham L κ β γ (W 0))) Ω (|β| * CA L ^ 2)
            (|γ| * CA L ^ 4) * |h|) ^ (q+1) := by
  have hC := CA_nonneg hL
  have hK := Rap_nonneg κ β γ (mass L (W 0)) (ham L κ β γ (W 0))
  have hlam : 0 ≤ rate (Rap κ β γ (mass L (W 0)) (ham L κ β γ (W 0))) Ω (|β| * CA L ^ 2)
      (|γ| * CA L ^ 4) := rate_nonneg hΩ (by positivity) (by positivity)
  obtain ⟨hr, hlr⟩ := radius_admissible hlam
  have hu : ∀ t, HasDerivAt (fun s => U L κ s (W s))
      (physField L κ β γ S (U L κ t (W t))) t := hasDerivAt_phys hL hs hW
  have hb : ∀ t, ‖U L κ t (W t)‖ ≤ Rap κ β γ (mass L (W 0)) (ham L κ β γ (W 0)) := fun t => by
    rw [norm_U]; exact galerkin_apriori hL hγ S hs hW t
  exact ⟨galerkin_taylor_series (u := fun s => U L κ s (W s)) hL hu hK hΩ hS hb t₀ hr hlr hh,
    taylor_poly_error (u := fun s => U L κ s (W s)) hL hu hK hΩ hS hb t₀ hr hlr hh q⟩

end PVNP.GalerkinTaylor
