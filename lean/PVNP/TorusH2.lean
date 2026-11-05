import PVNP.TorusSeries

/-!
# `H²(T_L²)`: Sobolev embedding, the algebra property, the free propagator and the nonlinearity

Continuation of `PVNP.TorusSeries`.  The state space is `ℓ2 = ℓ²(ℤ²)`: an element `v` represents
the `H²(T_L²)` function `field L (co L v)` whose Fourier coefficients (orthonormal-basis
normalisation) are `co L v k = v k / w_k`, `w_k = 1 + |ξ_k|²`.  Thus
`‖v‖² = Σ_k (1 + |ξ_k|²)² |ψ̂_k|² = ‖ψ‖²_{L²} + 2‖∇ψ‖²_{L²} + ‖Δψ‖²_{L²}`, the `H²` norm of the
physical field on the torus of side `L` with Lebesgue measure.

* Explicit lattice sums: `sum_inv_one_add_sq_le` (`Σ_{m ∈ ℤ} (1 + c²m²)⁻¹ ≤ 1 + π/c`, by
  comparison with `arctan`), hence `SL L = Σ_k w_k⁻² ≤ (1 + L/2)²` (`SL_le`).
* Sobolev embedding `H² ⊂ ℓ¹ ⊂ C(T_L²)`: `tsum_norm_co_le` (`Σ|ψ̂_k| ≤ √(SL L) ‖v‖`) and
  `norm_field_co_le` (`‖ψ‖_∞ ≤ L⁻¹ √(SL L) ‖ψ‖_{H²}`).  The constant `L⁻¹ √(SL L) ≤ L⁻¹ + 1/2`
  is **uniform for `L ≥ 1`** (`sobolev_const_le`).
* Young's inequality `ℓ² ⋆ ℓ¹ → ℓ²` (`young`) and the **algebra property**
  `‖ψφ‖_{H²} ≤ CA L ‖ψ‖_{H²} ‖φ‖_{H²}` with `CA L = 4 √(SL L) / L` (`norm_mulH_le`), again
  uniform for `L ≥ 1` (`CA_le`).
* The free propagator `U L κ t = exp(−i t (Δ+κ)²)` (`U`): a strongly continuous unitary group
  (`norm_U`, `U_add`, `U_zero`, `continuous_U_uncurry`).
* The cubic–quintic nonlinearity `F(ψ) = −β|ψ|²ψ + γ|ψ|⁴ψ` on `H²` (`Fnl`), equal *pointwise*
  to the physical nonlinearity of the field (`field_Fnl`), locally Lipschitz with the explicit
  constant `LF L β γ R = |β|·3·CA²R² + |γ|·5·CA⁴R⁴` (`norm_Fnl_sub_le`).
-/

open Complex Set Filter Topology
open scoped Real ENNReal NNReal

namespace PVNP.Torus

variable {L : ℝ}

/-! ### Cauchy–Schwarz for nonnegative series -/

theorem tsum_mul_le_sqrt {ι : Type*} {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hx2 : Summable fun i => x i ^ 2) (hy2 : Summable fun i => y i ^ 2) :
    Summable (fun i => x i * y i) ∧
      ∑' i, x i * y i ≤ Real.sqrt (∑' i, x i ^ 2) * Real.sqrt (∑' i, y i ^ 2) := by
  have hx2' : Summable fun i => x i ^ (2 : ℝ) := by simpa [Real.rpow_two] using hx2
  have hy2' : Summable fun i => y i ^ (2 : ℝ) := by simpa [Real.rpow_two] using hy2
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hx hy hx2' hy2'
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  simp only [Real.rpow_two] at h2
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-! ### Weights and lattice sums -/

/-- The `H²` weight `w_k = 1 + |ξ_k|²`. -/
noncomputable def wt (L : ℝ) (k : Z2) : ℝ := 1 + qf L k

theorem one_le_wt (L : ℝ) (k : Z2) : 1 ≤ wt L k := by
  unfold wt; linarith [qf_nonneg L k]

theorem wt_pos (L : ℝ) (k : Z2) : 0 < wt L k := lt_of_lt_of_le one_pos (one_le_wt L k)

theorem wt_ne_zero (L : ℝ) (k : Z2) : (wt L k : ℂ) ≠ 0 := by
  exact_mod_cast (wt_pos L k).ne'

theorem xi1_add (L : ℝ) (k j : Z2) : xi1 L (k + j) = xi1 L k + xi1 L j := by
  simp only [xi1, Prod.fst_add]; push_cast; ring

theorem xi2_add (L : ℝ) (k j : Z2) : xi2 L (k + j) = xi2 L k + xi2 L j := by
  simp only [xi2, Prod.snd_add]; push_cast; ring

theorem xi1_neg (L : ℝ) (k : Z2) : xi1 L (-k) = -xi1 L k := by
  simp only [xi1, Prod.fst_neg]; push_cast; ring

theorem xi2_neg (L : ℝ) (k : Z2) : xi2 L (-k) = -xi2 L k := by
  simp only [xi2, Prod.snd_neg]; push_cast; ring

theorem qf_neg (L : ℝ) (k : Z2) : qf L (-k) = qf L k := by
  simp only [qf, xi1_neg, xi2_neg]; ring

theorem wt_neg (L : ℝ) (k : Z2) : wt L (-k) = wt L k := by
  simp only [wt, qf_neg]

theorem qf_add_le (L : ℝ) (k j : Z2) : qf L (k + j) ≤ 2 * qf L k + 2 * qf L j := by
  simp only [qf, xi1_add, xi2_add]
  nlinarith [sq_nonneg (xi1 L k - xi1 L j), sq_nonneg (xi2 L k - xi2 L j)]

/-- `w_k ≤ 2 w_{k−j} + 2 w_j`. -/
theorem wt_le (L : ℝ) (k j : Z2) : wt L k ≤ 2 * wt L (k - j) + 2 * wt L j := by
  have h := qf_add_le L (k - j) j
  rw [sub_add_cancel] at h
  unfold wt
  linarith

theorem one_div_one_add_le_slope {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    1 / (1 + c ^ 2 * (x + 1) ^ 2) ≤ (Real.arctan (c * (x + 1)) - Real.arctan (c * x)) / c := by
  have hd : ∀ y ∈ Ioo x (x + 1), HasDerivAt (fun y => Real.arctan (c * y))
      (1 / (1 + (c * y) ^ 2) * c) y := by
    intro y _
    have h := (Real.hasDerivAt_arctan (c * y)).comp y ((hasDerivAt_id y).const_mul c)
    simpa using h
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun y => Real.arctan (c * y))
    (fun y => 1 / (1 + (c * y) ^ 2) * c) (lt_add_one x)
    ((Real.continuous_arctan.comp (continuous_const.mul continuous_id)).continuousOn) hd
  rw [show x + 1 - x = 1 by ring, div_one] at hξe
  rw [← hξe]
  have hξ0 : 0 ≤ ξ := le_trans hx hξ.1.le
  have hle : (c * ξ) ^ 2 ≤ c ^ 2 * (x + 1) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hξ0 hξ.2.le 2) (sq_nonneg c)
  rw [mul_div_assoc, div_self hc.ne', mul_one]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem sum_range_inv_le {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / (1 + c ^ 2 * ((n : ℝ) + 1) ^ 2) ≤ π / 2 / c := by
  calc ∑ n ∈ Finset.range N, 1 / (1 + c ^ 2 * ((n : ℝ) + 1) ^ 2)
      ≤ ∑ n ∈ Finset.range N, (Real.arctan (c * ((n : ℝ) + 1)) - Real.arctan (c * n)) / c :=
        Finset.sum_le_sum fun n _ => one_div_one_add_le_slope hc (Nat.cast_nonneg n)
    _ = (Real.arctan (c * N) - Real.arctan (c * 0)) / c := by
        rw [← Finset.sum_div]
        congr 1
        have := Finset.sum_range_sub (fun n : ℕ => Real.arctan (c * n)) N
        simpa using this
    _ ≤ π / 2 / c := by
        rw [mul_zero, Real.arctan_zero, sub_zero]
        exact div_le_div_of_nonneg_right (Real.arctan_lt_pi_div_two _).le hc.le

theorem summable_inv_nat {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => 1 / (1 + c ^ 2 * ((n : ℝ) + 1) ^ 2) :=
  summable_of_sum_range_le (fun n => by positivity) (sum_range_inv_le hc)

theorem tsum_inv_nat_le {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, 1 / (1 + c ^ 2 * ((n : ℝ) + 1) ^ 2) ≤ π / 2 / c :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_range_inv_le hc)

/-- `f_c(m) = 1/(1 + c²m²)`. -/
noncomputable def finv (c : ℝ) (m : ℤ) : ℝ := 1 / (1 + c ^ 2 * (m : ℝ) ^ 2)

theorem finv_nonneg (c : ℝ) (m : ℤ) : 0 ≤ finv c m := by unfold finv; positivity

theorem finv_succ (c : ℝ) (n : ℕ) :
    finv c ((n + 1 : ℕ) : ℤ) = 1 / (1 + c ^ 2 * ((n : ℝ) + 1) ^ 2) := by
  simp only [finv]; push_cast; ring

theorem finv_neg_succ (c : ℝ) (n : ℕ) :
    finv c (-((n : ℤ) + 1)) = 1 / (1 + c ^ 2 * ((n : ℝ) + 1) ^ 2) := by
  simp only [finv]; push_cast; ring

theorem summable_finv_nat {c : ℝ} (hc : 0 < c) : Summable fun n : ℕ => finv c n := by
  refine (summable_nat_add_iff 1).1 ?_
  refine (summable_inv_nat hc).congr fun n => ?_
  rw [← finv_succ]

theorem summable_finv_neg {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => finv c (-((n : ℤ) + 1)) :=
  (summable_inv_nat hc).congr fun n => (finv_neg_succ c n).symm

theorem summable_finv {c : ℝ} (hc : 0 < c) : Summable (finv c) :=
  Summable.of_nat_of_neg_add_one (f := finv c) (summable_finv_nat hc) (summable_finv_neg hc)

/-- **`Σ_{m ∈ ℤ} 1/(1 + c²m²) ≤ 1 + π/c`.** -/
theorem tsum_finv_le {c : ℝ} (hc : 0 < c) : ∑' m : ℤ, finv c m ≤ 1 + π / c := by
  rw [tsum_of_nat_of_neg_add_one (f := finv c) (summable_finv_nat hc) (summable_finv_neg hc),
    (summable_finv_nat hc).tsum_eq_zero_add]
  have e1 : ∑' n : ℕ, finv c ((n + 1 : ℕ) : ℤ) = ∑' n : ℕ, 1 / (1 + c ^ 2 * ((n : ℝ) + 1) ^ 2) :=
    tsum_congr fun n => finv_succ c n
  have e2 : ∑' n : ℕ, finv c (-((n : ℤ) + 1)) =
      ∑' n : ℕ, 1 / (1 + c ^ 2 * ((n : ℝ) + 1) ^ 2) :=
    tsum_congr fun n => finv_neg_succ c n
  rw [e1, e2]
  have h3 := tsum_inv_nat_le hc
  have h0 : finv c ((0 : ℕ) : ℤ) = 1 := by simp [finv]
  rw [h0]
  have : π / 2 / c + π / 2 / c = π / c := by ring
  linarith

/-- `w_k⁻² ≤ f_c(k₁) f_c(k₂)` with `c = 2π/L`. -/
theorem wt_inv_sq_le (L : ℝ) (k : Z2) :
    (wt L k)⁻¹ ^ 2 ≤ finv (2 * π / L) k.1 * finv (2 * π / L) k.2 := by
  have e : wt L k = 1 + (2 * π / L) ^ 2 * ((k.1 : ℤ) : ℝ) ^ 2 +
      (2 * π / L) ^ 2 * ((k.2 : ℤ) : ℝ) ^ 2 := by
    simp only [wt, qf, xi1, xi2]; ring
  set A := (2 * π / L) ^ 2 * ((k.1 : ℤ) : ℝ) ^ 2 with hA
  set B := (2 * π / L) ^ 2 * ((k.2 : ℤ) : ℝ) ^ 2 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  simp only [finv]
  rw [e, inv_pow, ← one_div, div_mul_div_comm, one_mul, ← hA, ← hB]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [mul_nonneg hA0 hB0]

/-- The lattice sum `SL L = Σ_k w_k⁻²`. -/
noncomputable def SL (L : ℝ) : ℝ := ∑' k : Z2, (wt L k)⁻¹ ^ 2

theorem summable_finv_norm {c : ℝ} (hc : 0 < c) : Summable fun m : ℤ => ‖finv c m‖ :=
  (summable_finv hc).congr fun m => by rw [Real.norm_eq_abs, abs_of_nonneg (finv_nonneg c m)]

theorem summable_prod_inv (hL : 0 < L) :
    Summable fun k : Z2 => finv (2 * π / L) k.1 * finv (2 * π / L) k.2 := by
  have hc : 0 < 2 * π / L := by positivity
  exact summable_mul_of_summable_norm (f := finv (2 * π / L)) (g := finv (2 * π / L))
    (summable_finv_norm hc) (summable_finv_norm hc)

theorem summable_wt_inv_sq (hL : 0 < L) : Summable fun k : Z2 => (wt L k)⁻¹ ^ 2 :=
  (summable_prod_inv hL).of_nonneg_of_le (fun _ => by positivity) (wt_inv_sq_le L)

theorem SL_nonneg (L : ℝ) : 0 ≤ SL L := tsum_nonneg fun _ => by positivity

/-- **`Σ_k (1 + |ξ_k|²)⁻² ≤ (1 + L/2)²`.** -/
theorem SL_le (hL : 0 < L) : SL L ≤ (1 + L / 2) ^ 2 := by
  have hc : 0 < 2 * π / L := by positivity
  calc SL L ≤ ∑' k : Z2, finv (2 * π / L) k.1 * finv (2 * π / L) k.2 :=
        (summable_wt_inv_sq hL).tsum_le_tsum (wt_inv_sq_le L) (summable_prod_inv hL)
    _ = (∑' m : ℤ, finv (2 * π / L) m) * ∑' m : ℤ, finv (2 * π / L) m :=
        (tsum_mul_tsum_of_summable_norm (f := finv (2 * π / L)) (g := finv (2 * π / L))
          (summable_finv_norm hc) (summable_finv_norm hc)).symm
    _ ≤ (1 + π / (2 * π / L)) * (1 + π / (2 * π / L)) := by
        have h1 := tsum_finv_le hc
        have h0 : 0 ≤ ∑' m : ℤ, finv (2 * π / L) m := tsum_nonneg fun m => finv_nonneg _ m
        exact mul_le_mul h1 h1 h0 (le_trans h0 h1)
    _ = (1 + L / 2) ^ 2 := by
        have : π / (2 * π / L) = L / 2 := by field_simp
        rw [this]; ring

/-! ### The state space `ℓ²(ℤ²)` -/

/-- Square-summable sequences on `ℤ²`. -/
abbrev ℓ2 := lp (fun _ : Z2 => ℂ) 2

theorem two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num

theorem summable_sq (v : ℓ2) : Summable fun k => ‖v k‖ ^ 2 := by
  have h := (lp.memℓp v).summable (by rw [two_toReal]; norm_num)
  simpa [two_toReal, Real.rpow_two] using h

theorem norm_sq_eq (v : ℓ2) : ‖v‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by rw [two_toReal]; norm_num) v
  simpa [two_toReal, Real.rpow_two] using h

theorem norm_eq_sqrt (v : ℓ2) : ‖v‖ = Real.sqrt (∑' k, ‖v k‖ ^ 2) := by
  rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

theorem memℓp_of_sq {f : Z2 → ℂ} (hf : Summable fun k => ‖f k‖ ^ 2) :
    Memℓp (fun k => f k) 2 :=
  (memℓp_gen_iff (by rw [two_toReal]; norm_num)).2 (by simpa [two_toReal, Real.rpow_two] using hf)

/-- Build an element of `ℓ²` from a square-summable sequence. -/
noncomputable def mk (f : Z2 → ℂ) (hf : Summable fun k => ‖f k‖ ^ 2) : ℓ2 := ⟨f, memℓp_of_sq hf⟩

@[simp] theorem mk_apply (f : Z2 → ℂ) (hf : Summable fun k => ‖f k‖ ^ 2) (k : Z2) :
    mk f hf k = f k := rfl

theorem norm_mk_sq (f : Z2 → ℂ) (hf : Summable fun k => ‖f k‖ ^ 2) :
    ‖mk f hf‖ ^ 2 = ∑' k, ‖f k‖ ^ 2 := norm_sq_eq _

theorem norm_le_of_tsum_sq_le (v : ℓ2) {C : ℝ} (hC : 0 ≤ C) (h : ∑' k, ‖v k‖ ^ 2 ≤ C ^ 2) :
    ‖v‖ ≤ C := by
  rw [norm_eq_sqrt]
  exact Real.sqrt_le_iff.2 ⟨hC, h⟩

/-- Domination of square sums. -/
theorem tsum_sq_le_of_le {f : Z2 → ℂ} {g : Z2 → ℝ} (hg : Summable fun k => g k ^ 2)
    (hfg : ∀ k, ‖f k‖ ≤ g k) :
    Summable (fun k => ‖f k‖ ^ 2) ∧ ∑' k, ‖f k‖ ^ 2 ≤ ∑' k, g k ^ 2 := by
  have h1 : ∀ k, ‖f k‖ ^ 2 ≤ g k ^ 2 := fun k => pow_le_pow_left₀ (norm_nonneg _) (hfg k) 2
  have hs : Summable fun k => ‖f k‖ ^ 2 := hg.of_nonneg_of_le (fun _ => by positivity) h1
  exact ⟨hs, hs.tsum_le_tsum h1 hg⟩

/-- The evaluation functional `v ↦ v k`. -/
noncomputable def evalL (k : Z2) : ℓ2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun v => v k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun v => by simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) v k)

@[simp] theorem evalL_apply (k : Z2) (v : ℓ2) : evalL k v = v k := rfl

theorem tsum_apply {f : Z2 → ℓ2} (hf : Summable f) (k : Z2) : (∑' j, f j) k = ∑' j, f j k := by
  have h := (evalL k).map_tsum hf
  simpa using h

/-! ### Diagonal multipliers -/

/-- Multiplication of `ℓ²` sequences by a bounded sequence `m`, `‖m‖_∞ ≤ C`. -/
noncomputable def dmul (m : Z2 → ℂ) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ k, ‖m k‖ ≤ C) : ℓ2 →L[ℂ] ℓ2 :=
  LinearMap.mkContinuous
    { toFun := fun v => mk (fun k => m k * v k)
        ((tsum_sq_le_of_le (g := fun k => C * ‖v k‖) (by
          simpa only [mul_pow] using (summable_sq v).mul_left (C ^ 2))
          (fun k => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _))).1)
      map_add' := fun v w => by
        ext k; simp only [mk_apply, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c v => by
        ext k; simp only [mk_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    C (fun v => by
      have hb := tsum_sq_le_of_le (f := fun k => m k * v k) (g := fun k => C * ‖v k‖) (by
          simpa only [mul_pow] using (summable_sq v).mul_left (C ^ 2))
          (fun k => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _))
      refine norm_le_of_tsum_sq_le _ (by positivity) ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, mk_apply]
      calc ∑' k, ‖m k * v k‖ ^ 2 ≤ ∑' k, (C * ‖v k‖) ^ 2 := hb.2
        _ = (C * ‖v‖) ^ 2 := by
          simp only [mul_pow]
          rw [tsum_mul_left, norm_sq_eq])

@[simp] theorem dmul_apply (m : Z2 → ℂ) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ k, ‖m k‖ ≤ C) (v : ℓ2)
    (k : Z2) : dmul m C hC hm v k = m k * v k := rfl

/-- A unimodular multiplier is an isometry. -/
theorem norm_dmul_of_norm_one (m : Z2 → ℂ) (hm : ∀ k, ‖m k‖ = 1) (v : ℓ2) :
    ‖dmul m 1 zero_le_one (fun k => (hm k).le) v‖ = ‖v‖ := by
  rw [norm_eq_sqrt, norm_eq_sqrt]
  congr 1
  refine tsum_congr fun k => ?_
  rw [dmul_apply, norm_mul, hm, one_mul]

/-! ### Coefficients -/

/-- The Fourier coefficients `ψ̂_k = v_k / w_k` of the `H²` function represented by `v`. -/
noncomputable def co (L : ℝ) (v : ℓ2) (k : Z2) : ℂ := v k / (wt L k : ℂ)

theorem norm_co (L : ℝ) (v : ℓ2) (k : Z2) : ‖co L v k‖ = ‖v k‖ / wt L k := by
  rw [co, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos L k)]

theorem norm_co_le (L : ℝ) (v : ℓ2) (k : Z2) : ‖co L v k‖ ≤ ‖v k‖ := by
  rw [norm_co]
  exact div_le_self (norm_nonneg _) (one_le_wt L k)

theorem wt_mul_co (L : ℝ) (v : ℓ2) (k : Z2) : (wt L k : ℂ) * co L v k = v k := by
  rw [co, mul_div_cancel₀ _ (wt_ne_zero L k)]

theorem wt_mul_norm_co (L : ℝ) (v : ℓ2) (k : Z2) : wt L k * ‖co L v k‖ = ‖v k‖ := by
  rw [norm_co, mul_div_cancel₀ _ (wt_pos L k).ne']

theorem co_add (L : ℝ) (v w : ℓ2) : co L (v + w) = co L v + co L w := by
  funext k; simp only [co, lp.coeFn_add, Pi.add_apply, add_div]

theorem co_sub (L : ℝ) (v w : ℓ2) : co L (v - w) = co L v - co L w := by
  funext k; simp only [co, lp.coeFn_sub, Pi.sub_apply, sub_div]

theorem co_smul (L : ℝ) (c : ℂ) (v : ℓ2) : co L (c • v) = c • co L v := by
  funext k; simp only [co, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

theorem co_zero (L : ℝ) : co L 0 = 0 := by
  funext k; simp [co]

theorem summable_co_sq (L : ℝ) (v : ℓ2) : Summable fun k => ‖co L v k‖ ^ 2 :=
  (tsum_sq_le_of_le (summable_sq v) (fun k => norm_co_le L v k)).1

theorem tsum_co_sq_le (L : ℝ) (v : ℓ2) : ∑' k, ‖co L v k‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_sq_eq]; exact (tsum_sq_le_of_le (summable_sq v) (fun k => norm_co_le L v k)).2

/-- **Sobolev embedding `H² ⊂ ℓ¹`**: `Σ_k |ψ̂_k| ≤ √(SL L) ‖v‖`. -/
theorem L1_co (hL : 0 < L) (v : ℓ2) : L1 (co L v) ∧ ∑' k, ‖co L v k‖ ≤ Real.sqrt (SL L) * ‖v‖ := by
  have e : ∀ k, ‖co L v k‖ = ‖v k‖ * (wt L k)⁻¹ := fun k => by rw [norm_co, div_eq_mul_inv]
  have h := tsum_mul_le_sqrt (x := fun k => ‖v k‖) (y := fun k => (wt L k)⁻¹)
    (fun _ => norm_nonneg _) (fun k => inv_nonneg.2 (wt_pos L k).le) (summable_sq v)
    (summable_wt_inv_sq hL)
  refine ⟨by unfold L1; simp_rw [e]; exact h.1, ?_⟩
  simp_rw [e]
  calc ∑' k, ‖v k‖ * (wt L k)⁻¹ ≤ Real.sqrt (∑' k, ‖v k‖ ^ 2) * Real.sqrt (SL L) := h.2
    _ = Real.sqrt (SL L) * ‖v‖ := by rw [← norm_eq_sqrt, mul_comm]

theorem tsum_norm_co_le (hL : 0 < L) (v : ℓ2) : ∑' k, ‖co L v k‖ ≤ Real.sqrt (SL L) * ‖v‖ :=
  (L1_co hL v).2

/-- **`‖ψ‖_∞ ≤ L⁻¹ √(SL L) ‖ψ‖_{H²}`.** -/
theorem norm_field_co_le (hL : 0 < L) (v : ℓ2) (x : ℝ × ℝ) :
    ‖field L (co L v) x‖ ≤ L⁻¹ * Real.sqrt (SL L) * ‖v‖ := by
  have h := norm_field_le (L := L) (L1_co hL v).1 x
  rw [abs_of_pos hL] at h
  rw [mul_assoc]
  exact h.trans (mul_le_mul_of_nonneg_left (tsum_norm_co_le hL v) (inv_nonneg.2 hL.le))

/-- The Sobolev constant is uniform for `L ≥ 1`: `L⁻¹ √(SL L) ≤ L⁻¹ + 1/2 ≤ 3/2`. -/
theorem sobolev_const_le (hL : 1 ≤ L) : L⁻¹ * Real.sqrt (SL L) ≤ 3 / 2 := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have h1 : Real.sqrt (SL L) ≤ 1 + L / 2 := by
    rw [show 1 + L / 2 = Real.sqrt ((1 + L / 2) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (SL_le hL0)
  calc L⁻¹ * Real.sqrt (SL L) ≤ L⁻¹ * (1 + L / 2) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hL0.le)
    _ = L⁻¹ + 1 / 2 := by field_simp
    _ ≤ 3 / 2 := by
        have : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
        linarith

/-! ### Young's inequality `ℓ² ⋆ ℓ¹ → ℓ²` -/

theorem summable_sq_shift (v : ℓ2) (j : Z2) : Summable fun k => ‖v (k - j)‖ ^ 2 := by
  have h := ((Equiv.subRight j).summable_iff (f := fun k => ‖v k‖ ^ 2)).2 (summable_sq v)
  exact h

/-- Translation `(τ_j v)(k) = v(k − j)`. -/
noncomputable def tr (j : Z2) (v : ℓ2) : ℓ2 := mk (fun k => v (k - j)) (summable_sq_shift v j)

theorem norm_tr (j : Z2) (v : ℓ2) : ‖tr j v‖ = ‖v‖ := by
  have h : ∑' k, ‖(tr j v) k‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 :=
    (Equiv.subRight j).tsum_eq (fun k => ‖v k‖ ^ 2)
  rw [norm_eq_sqrt, norm_eq_sqrt, h]

/-- **Young's inequality** `‖f ⋆ g‖₂ ≤ ‖f‖₂ ‖g‖₁`. -/
theorem young (f : ℓ2) {g : Z2 → ℂ} (hg : L1 g) :
    Summable (fun k => ‖∑' j, g j * f (k - j)‖ ^ 2) ∧
      ∑' k, ‖∑' j, g j * f (k - j)‖ ^ 2 ≤ (‖f‖ * ∑' j, ‖g j‖) ^ 2 := by
  have hs : Summable fun j => g j • tr j f := by
    refine Summable.of_norm ?_
    simp_rw [norm_smul, norm_tr]
    exact hg.mul_right _
  set S : ℓ2 := ∑' j, g j • tr j f with hS
  have hSk : ∀ k, S k = ∑' j, g j * f (k - j) := by
    intro k
    rw [hS, tsum_apply hs]
    refine tsum_congr fun j => ?_
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    simp only [tr, mk_apply]
  have hnorm : ‖S‖ ≤ ‖f‖ * ∑' j, ‖g j‖ := by
    calc ‖S‖ ≤ ∑' j, ‖g j • tr j f‖ := norm_tsum_le_tsum_norm (by
          simp_rw [norm_smul, norm_tr]; exact hg.mul_right _)
      _ = ‖f‖ * ∑' j, ‖g j‖ := by
          simp_rw [norm_smul, norm_tr]
          rw [tsum_mul_right, mul_comm]
  have hsq := norm_sq_eq S
  have e : ∑' k, ‖S k‖ ^ 2 = ∑' k, ‖∑' j, g j * f (k - j)‖ ^ 2 := by simp_rw [hSk]
  refine ⟨?_, ?_⟩
  · have h1 := summable_sq S
    simp_rw [hSk] at h1
    exact h1
  · rw [← e, ← hsq]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Young's inequality for nonnegative real sequences. -/
theorem young_real {x y : Z2 → ℝ} (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k)
    (hx2 : Summable fun k => x k ^ 2) (hy1 : Summable y) :
    Summable (fun k => (∑' j, x (k - j) * y j) ^ 2) ∧
      Real.sqrt (∑' k, (∑' j, x (k - j) * y j) ^ 2) ≤
        Real.sqrt (∑' k, x k ^ 2) * ∑' j, y j := by
  let f : ℓ2 := mk (fun k => (x k : ℂ)) (by
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hx2)
  have hg : L1 fun j => (y j : ℂ) := by
    unfold L1; simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hy _)] using hy1
  have h := young f hg
  have hterm : ∀ k, Summable fun j => x (k - j) * y j := by
    intro k
    have hb : ∀ j, x (k - j) ≤ Real.sqrt (∑' i, x i ^ 2) := by
      intro j
      rw [show x (k - j) = Real.sqrt (x (k - j) ^ 2) by rw [Real.sqrt_sq (hx _)]]
      exact Real.sqrt_le_sqrt (hx2.le_tsum (k - j) (fun i _ => sq_nonneg _))
    exact (hy1.mul_left (Real.sqrt (∑' i, x i ^ 2))).of_nonneg_of_le
      (fun j => mul_nonneg (hx _) (hy _))
      (fun j => by rw [mul_comm (Real.sqrt _)]; exact mul_le_mul_of_nonneg_right (hb j) (hy _)
        |>.trans_eq (mul_comm _ _))
  have e : ∀ k, ‖∑' j, (y j : ℂ) * f (k - j)‖ = ∑' j, x (k - j) * y j := by
    intro k
    have : (∑' j, (y j : ℂ) * f (k - j)) = ((∑' j, x (k - j) * y j : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun j => ?_
      simp only [f, mk_apply]
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg fun j => mul_nonneg (hx _) (hy _))]
  have hfn : ‖f‖ = Real.sqrt (∑' k, x k ^ 2) := by
    rw [norm_eq_sqrt]
    congr 1
    refine tsum_congr fun k => ?_
    simp [f, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hyn : ∑' j, ‖(y j : ℂ)‖ = ∑' j, y j := by
    congr 1; funext j; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hy _)]
  simp_rw [e] at h
  rw [hfn, hyn] at h
  refine ⟨h.1, ?_⟩
  rw [show Real.sqrt (∑' k, x k ^ 2) * ∑' j, y j =
      Real.sqrt ((Real.sqrt (∑' k, x k ^ 2) * ∑' j, y j) ^ 2) by
    rw [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg hy))]]
  exact Real.sqrt_le_sqrt h.2

/-! ### The free propagator `exp(−i t (Δ+κ)²)` -/

/-- The symbol `ω_k = (κ − |ξ_k|²)²` of `(Δ + κ)²`. -/
noncomputable def om (L κ : ℝ) (k : Z2) : ℝ := (κ - qf L k) ^ 2

/-- The phase `exp(−i ω_k t)`. -/
noncomputable def ph (L κ t : ℝ) (k : Z2) : ℂ := Complex.exp (((-(om L κ k * t) : ℝ) : ℂ) * I)

theorem norm_ph (L κ t : ℝ) (k : Z2) : ‖ph L κ t k‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem ph_add (L κ s t : ℝ) (k : Z2) : ph L κ (s + t) k = ph L κ s k * ph L κ t k := by
  rw [ph, ph, ph, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ph_zero (L κ : ℝ) (k : Z2) : ph L κ 0 k = 1 := by simp [ph]

theorem continuous_ph (L κ : ℝ) (k : Z2) : Continuous fun t => ph L κ t k := by
  unfold ph
  fun_prop

theorem hasDerivAt_ph (L κ t : ℝ) (k : Z2) :
    HasDerivAt (fun s => ph L κ s k) (-I * (om L κ k : ℂ) * ph L κ t k) t := by
  have h : HasDerivAt (fun s : ℝ => (((-(om L κ k * s) : ℝ) : ℂ) * I))
      ((((-(om L κ k)) : ℝ) : ℂ) * I) t := by
    have h1 := ((hasDerivAt_id t).const_mul (-(om L κ k))).ofReal_comp
    have h2 := h1.mul_const I
    convert h2 using 1
    · funext s; simp only [id]; push_cast; ring
    · push_cast; ring
  convert h.cexp using 1
  rw [ph]
  push_cast
  ring

/-- The free propagator `U(t) = exp(−i t (Δ+κ)²)` on `ℓ²(ℤ²)`. -/
noncomputable def U (L κ t : ℝ) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (ph L κ t) 1 zero_le_one (fun k => (norm_ph L κ t k).le)

@[simp] theorem U_apply (L κ t : ℝ) (v : ℓ2) (k : Z2) : U L κ t v k = ph L κ t k * v k := rfl

theorem norm_U (L κ t : ℝ) (v : ℓ2) : ‖U L κ t v‖ = ‖v‖ :=
  norm_dmul_of_norm_one _ (fun k => norm_ph L κ t k) v

theorem U_add (L κ s t : ℝ) (v : ℓ2) : U L κ (s + t) v = U L κ s (U L κ t v) := by
  ext k
  simp only [U_apply, ph_add, mul_assoc]

theorem U_zero (L κ : ℝ) (v : ℓ2) : U L κ 0 v = v := by
  ext k
  simp only [U_apply, ph_zero, one_mul]

theorem U_neg_U (L κ t : ℝ) (v : ℓ2) : U L κ (-t) (U L κ t v) = v := by
  rw [← U_add, neg_add_cancel, U_zero]

theorem U_U_neg (L κ t : ℝ) (v : ℓ2) : U L κ t (U L κ (-t) v) = v := by
  rw [← U_add, add_neg_cancel, U_zero]

theorem co_U (L κ t : ℝ) (v : ℓ2) (k : Z2) : co L (U L κ t v) k = ph L κ t k * co L v k := by
  simp only [co, U_apply, mul_div_assoc]

theorem norm_U_sub_sq (L κ s t : ℝ) (v : ℓ2) :
    ‖U L κ s v - U L κ t v‖ ^ 2 = ∑' k, ‖ph L κ s k - ph L κ t k‖ ^ 2 * ‖v k‖ ^ 2 := by
  rw [norm_sq_eq]
  refine tsum_congr fun k => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, U_apply, U_apply, ← sub_mul, norm_mul, mul_pow]

/-- **Strong continuity** of the free group. -/
theorem continuous_U_apply (L κ : ℝ) (v : ℓ2) : Continuous fun t => U L κ t v := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun s => ‖U L κ s v - U L κ t v‖ ^ 2) (𝓝 t) (𝓝 0) := by
    simp_rw [norm_U_sub_sq]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 t)
      (f := fun s k => ‖ph L κ s k - ph L κ t k‖ ^ 2 * ‖v k‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun k => 4 * ‖v k‖ ^ 2) ((summable_sq v).mul_left 4)
      (fun k => by
        have h1 : Tendsto (fun s => ph L κ s k - ph L κ t k) (𝓝 t) (𝓝 0) := by
          have := ((continuous_ph L κ k).tendsto t).sub_const (ph L κ t k)
          simpa using this
        have h2 := ((h1.norm.pow 2).mul_const (‖v k‖ ^ 2))
        simpa using h2)
      (Eventually.of_forall fun s k => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h3 : ‖ph L κ s k - ph L κ t k‖ ≤ 2 := by
          calc ‖ph L κ s k - ph L κ t k‖ ≤ ‖ph L κ s k‖ + ‖ph L κ t k‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_ph, norm_ph]; norm_num
        have h4 : ‖ph L κ s k - ph L κ t k‖ ^ 2 ≤ 4 := by
          calc ‖ph L κ s k - ph L κ t k‖ ^ 2 ≤ 2 ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) h3 2
            _ = 4 := by norm_num
        exact mul_le_mul_of_nonneg_right h4 (by positivity))
    simpa using h
  have h := hsq.sqrt
  simp only [Real.sqrt_zero] at h
  refine h.congr fun s => ?_
  exact Real.sqrt_sq (norm_nonneg _)

theorem continuous_U_uncurry (L κ : ℝ) : Continuous fun p : ℝ × ℓ2 => U L κ p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, v⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun p : ℝ × ℓ2 => ‖p.2 - v‖) (𝓝 (t, v)) (𝓝 0) := by
    have := ((continuous_snd.sub (continuous_const : Continuous fun _ : ℝ × ℓ2 => v)).norm.tendsto
      (t, v))
    simpa using this
  have h2 : Tendsto (fun p : ℝ × ℓ2 => ‖U L κ p.1 v - U L κ t v‖) (𝓝 (t, v)) (𝓝 0) := by
    have := (((continuous_U_apply L κ v).comp continuous_fst).sub
      (continuous_const : Continuous fun _ : ℝ × ℓ2 => U L κ t v)).norm.tendsto (t, v)
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) (by simpa using h1.add h2)
  calc ‖U L κ p.1 p.2 - U L κ t v‖ = ‖U L κ p.1 (p.2 - v) + (U L κ p.1 v - U L κ t v)‖ := by
        rw [map_sub]; abel_nf
    _ ≤ ‖U L κ p.1 (p.2 - v)‖ + ‖U L κ p.1 v - U L κ t v‖ := norm_add_le _ _
    _ = ‖p.2 - v‖ + ‖U L κ p.1 v - U L κ t v‖ := by rw [norm_U]

/-! ### Coefficient operators: `ψ`, `(Δ+κ)ψ`, `Δψ`, `∂ᵢψ` -/

theorem norm_inv_wt_le (L : ℝ) (k : Z2) : ‖(((wt L k)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (wt_pos L k))]
  exact inv_le_one_of_one_le₀ (one_le_wt L k)

/-- The `L²` coefficients `ψ̂` as an element of `ℓ²`. -/
noncomputable def Lc (L : ℝ) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (fun k => (((wt L k)⁻¹ : ℝ) : ℂ)) 1 zero_le_one (norm_inv_wt_le L)

theorem Lc_apply (L : ℝ) (v : ℓ2) (k : Z2) : Lc L v k = co L v k := by
  simp only [Lc, dmul_apply, co]
  push_cast
  ring

theorem norm_Ac_sym_le (L κ : ℝ) (k : Z2) : ‖((((κ - qf L k) / wt L k) : ℝ) : ℂ)‖ ≤ |κ| + 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (wt_pos L k),
    div_le_iff₀ (wt_pos L k)]
  have hq := qf_nonneg L k
  unfold wt
  calc |κ - qf L k| ≤ |κ| + |qf L k| := abs_sub _ _
    _ = |κ| + qf L k := by rw [abs_of_nonneg hq]
    _ ≤ (|κ| + 1) * (1 + qf L k) := by nlinarith [abs_nonneg κ]

/-- The coefficients of `(Δ + κ)ψ`. -/
noncomputable def Ac (L κ : ℝ) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (fun k => ((((κ - qf L k) / wt L k) : ℝ) : ℂ)) (|κ| + 1) (by positivity)
    (norm_Ac_sym_le L κ)

theorem Ac_apply (L κ : ℝ) (v : ℓ2) (k : Z2) : Ac L κ v k = (κ - qf L k : ℝ) * co L v k := by
  simp only [Ac, dmul_apply, co]
  push_cast
  ring

theorem norm_Dc_sym_le (L : ℝ) (k : Z2) : ‖((((-qf L k) / wt L k) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (wt_pos L k), abs_neg,
    abs_of_nonneg (qf_nonneg L k), div_le_one (wt_pos L k)]
  unfold wt; linarith

/-- The coefficients of `Δψ`. -/
noncomputable def Dc (L : ℝ) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (fun k => ((((-qf L k) / wt L k) : ℝ) : ℂ)) 1 zero_le_one (norm_Dc_sym_le L)

theorem Dc_apply (L : ℝ) (v : ℓ2) (k : Z2) : Dc L v k = (-qf L k : ℝ) * co L v k := by
  simp only [Dc, dmul_apply, co]
  push_cast
  ring

theorem norm_G1_sym_le (L : ℝ) (k : Z2) : ‖I * (((xi1 L k / wt L k) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (wt_pos L k), div_le_one (wt_pos L k)]
  exact abs_xi1_le L k

theorem norm_G2_sym_le (L : ℝ) (k : Z2) : ‖I * (((xi2 L k / wt L k) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (wt_pos L k), div_le_one (wt_pos L k)]
  exact abs_xi2_le L k

/-- The coefficients of `∂₁ψ`. -/
noncomputable def G1c (L : ℝ) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (fun k => I * (((xi1 L k / wt L k) : ℝ) : ℂ)) 1 zero_le_one (norm_G1_sym_le L)

/-- The coefficients of `∂₂ψ`. -/
noncomputable def G2c (L : ℝ) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (fun k => I * (((xi2 L k / wt L k) : ℝ) : ℂ)) 1 zero_le_one (norm_G2_sym_le L)

theorem G1c_apply (L : ℝ) (v : ℓ2) (k : Z2) : G1c L v k = (I * xi1 L k) * co L v k := by
  simp only [G1c, dmul_apply, co]
  push_cast
  ring

theorem G2c_apply (L : ℝ) (v : ℓ2) (k : Z2) : G2c L v k = (I * xi2 L k) * co L v k := by
  simp only [G2c, dmul_apply, co]
  push_cast
  ring

theorem Lc_U (L κ t : ℝ) (v : ℓ2) : Lc L (U L κ t v) = U L κ t (Lc L v) := by
  ext k; simp only [Lc, dmul_apply, U_apply]; ring

theorem Ac_U (L κ t : ℝ) (v : ℓ2) : Ac L κ (U L κ t v) = U L κ t (Ac L κ v) := by
  ext k; simp only [Ac, dmul_apply, U_apply]; ring

theorem Dc_U (L κ t : ℝ) (v : ℓ2) : Dc L (U L κ t v) = U L κ t (Dc L v) := by
  ext k; simp only [Dc, dmul_apply, U_apply]; ring

theorem norm_sq_Lc (L : ℝ) (v : ℓ2) : ‖Lc L v‖ ^ 2 = ∑' k, ‖co L v k‖ ^ 2 := by
  rw [norm_sq_eq]; simp only [Lc_apply]

/-- `‖v‖² = ‖ψ‖² + 2‖∇ψ‖² + ‖Δψ‖²` (all in `L²(T_L²)`). -/
theorem norm_sq_decomp (L : ℝ) (v : ℓ2) :
    ‖v‖ ^ 2 = ‖Lc L v‖ ^ 2 + 2 * (‖G1c L v‖ ^ 2 + ‖G2c L v‖ ^ 2) + ‖Dc L v‖ ^ 2 := by
  have hs := summable_co_sq L v
  have hq : Summable fun k => qf L k * ‖co L v k‖ ^ 2 :=
    (summable_sq v).of_nonneg_of_le (fun k => mul_nonneg (qf_nonneg L k) (sq_nonneg _))
      (fun k => by
        rw [← wt_mul_norm_co L v k, mul_pow]
        have : qf L k ≤ wt L k ^ 2 := by unfold wt; nlinarith [qf_nonneg L k]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _))
  have h1 : ‖G1c L v‖ ^ 2 + ‖G2c L v‖ ^ 2 = ∑' k, qf L k * ‖co L v k‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq, ← (summable_sq (G1c L v)).tsum_add (summable_sq (G2c L v))]
    refine tsum_congr fun k => ?_
    rw [G1c_apply, G2c_apply, norm_mul (I * _) (co L v k), norm_mul (I * _) (co L v k),
      norm_I_xi1, norm_I_xi2, mul_pow, mul_pow, sq_abs, sq_abs, qf]
    ring
  rw [norm_sq_Lc, h1, norm_sq_eq (Dc L v), norm_sq_eq v,
    ← tsum_mul_left, ← hs.tsum_add (hq.mul_left 2),
    ← (hs.add (hq.mul_left 2)).tsum_add (summable_sq (Dc L v))]
  refine tsum_congr fun k => ?_
  rw [Dc_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    ← wt_mul_norm_co L v k, mul_pow]
  simp only [wt]
  ring

end PVNP.Torus
