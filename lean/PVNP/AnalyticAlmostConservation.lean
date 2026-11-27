import PVNP.AnalyticSimulation
import PVNP.UniformGalerkinRadius
import PVNP.GalerkinConservation
import PVNP.DetectorPDE

/-!
# Almost conservation of analytic energies: a polynomial lower bound on the analyticity radius

The analytic weight `e^{σ|k|}` almost commutes with products. Measured in `H²`, the commutator
of the complex lift `ṽ = (e^{σ|k|} v_k)_k` with the `H²` product is `O(√σ)`
(`comm_mulH_le`).

**Mechanism.** If `|k| ≤ |k − j| + |j|`, then
`0 ≤ e^{σ|k−j|}e^{σ|j|} − e^{σ|k|} ≤ e^{σ|k−j|}e^{σ|j|}·√(2σ)·√min(|k − j|, |j|)`
(`aw_defect_le`, from `1 − e^{−x} ≤ √x`). The half derivative falls on the factor that does
not carry the `H²` weight. In two dimensions an `H²` function has half a derivative in `ℓ¹`,
`Σ_j √|j| |ψ̂_j| ≤ √(SB) ‖ψ‖_{H²}` with `SB = Σ_k |k|/w_k² < ∞` (`summable_size_wt`). The
lattice sum converges because `|k|/w_k² ≤ (2/c)(1+c²k₁²)^{−3/4}(1+c²k₂²)^{−3/4}`.

Consequences, proved below with constants independent of the Galerkin set `S`:

* `comm_Fnl_le`: `‖(F(u))~ − F(ũ)‖ ≤ √σ · Q(A_σ(u))` for the actual nonlinearity
  `F(ψ) = −β|ψ|²ψ + γ|ψ|⁴ψ`, with the explicit polynomial
  `Q(A) = C_B (2|β| C_A A³ + 4|γ| C_A³ A⁵)`.
* The lifted Galerkin trajectory satisfies the lifted Galerkin equation up to an error of size
  `√σ · Q` (`lift_galerkin_err`). The Galerkin flow conserves mass and Hamiltonian, so their
  values on the **lifted** state change at rate `O(√σ)`.
* Mass and Hamiltonian control the `H²` norm (`TorusGlobal.norm_le_apriori`, `γ > 0`). A
  continuity argument then keeps `A_σ(W(t)) ≤ B` on `[0, T]` whenever `T √σ K ≤ 1`.
* **Polynomial radius** (`galerkin_radius_poly`): for every horizon `T`, the radius
  `σ_T = min(σ₀, (1 + K T)^{−2})` keeps the analytic norm bounded on `[0, T]`, uniformly in `S`.
  The previous bound `σ₀ 4^{−⌊T/τ⌋}` decays exponentially in `T`.
-/

namespace PVNP.Analytic

open Finset Set PVNP.Torus PVNP.TorusGalerkin Complex
open scoped Real

variable {L : ℝ}

/-! ### The weight defect -/

/-- `1 − e^{−x} ≤ √x` for `x ≥ 0`. -/
theorem one_sub_exp_neg_le_sqrt {x : ℝ} (hx : 0 ≤ x) : 1 - Real.exp (-x) ≤ Real.sqrt x := by
  have h1 : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  have h2 : 1 - Real.exp (-x) ≤ 1 := by linarith [Real.exp_pos (-x)]
  have hs := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg x
  rcases le_total x 1 with hx1 | hx1
  · have hs1 : Real.sqrt x ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hx1
    nlinarith
  · have hs1 : 1 ≤ Real.sqrt x := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hx1
    linarith

/-- The weight is submultiplicative with defect `√(2σ)√|j|`:
`e^{σ|k−j|}e^{σ|j|} − e^{σ|k|} ≤ e^{σ|k−j|}e^{σ|j|} √(2σ) √|j|`. -/
theorem aw_defect_le {σ : ℝ} (hσ : 0 ≤ σ) (k j : Z2) :
    aw σ (k - j) * aw σ j - aw σ k ≤
      aw σ (k - j) * aw σ j * (Real.sqrt (2 * σ) * Real.sqrt (size j)) := by
  have hs : size k ≤ size (k - j) + size j := size_le_sub_add k j
  have hs₁ : size (k - j) ≤ size k + size j := by
    have h := size_add_le k (-j)
    rwa [← sub_eq_add_neg, size_neg] at h
  set x := σ * (size (k - j) + size j - size k) with hx
  have hx0 : 0 ≤ x := mul_nonneg hσ (by linarith)
  have hx2 : x ≤ 2 * σ * size j := by
    rw [hx]
    nlinarith
  have e : aw σ k = aw σ (k - j) * aw σ j * Real.exp (-x) := by
    unfold aw
    rw [← Real.exp_add, ← Real.exp_add, hx]
    congr 1
    ring
  rw [e]
  have hpos : 0 ≤ aw σ (k - j) * aw σ j := mul_nonneg (aw_pos σ _).le (aw_pos σ _).le
  have key : 1 - Real.exp (-x) ≤ Real.sqrt (2 * σ) * Real.sqrt (size j) := by
    calc 1 - Real.exp (-x) ≤ Real.sqrt x := one_sub_exp_neg_le_sqrt hx0
      _ ≤ Real.sqrt (2 * σ * size j) := Real.sqrt_le_sqrt hx2
      _ = Real.sqrt (2 * σ) * Real.sqrt (size j) := Real.sqrt_mul (by positivity) _
  nlinarith [mul_le_mul_of_nonneg_left key hpos]

/-- The same defect with the half derivative on the other factor. -/
theorem aw_defect_le_left {σ : ℝ} (hσ : 0 ≤ σ) (k j : Z2) :
    aw σ (k - j) * aw σ j - aw σ k ≤
      aw σ (k - j) * aw σ j * (Real.sqrt (2 * σ) * Real.sqrt (size (k - j))) := by
  have h := aw_defect_le hσ k (k - j)
  rw [sub_sub_cancel, mul_comm (aw σ j)] at h
  exact h

/-! ### The lattice sum `SB = Σ_k |k|/w_k²` -/

/-- `(1 + c²m²)^{−3/4}`. -/
noncomputable def fq (c : ℝ) (m : ℤ) : ℝ := (1 + c ^ 2 * (m : ℝ) ^ 2) ^ (-(3 / 4 : ℝ))

theorem fq_nonneg (c : ℝ) (m : ℤ) : 0 ≤ fq c m := Real.rpow_nonneg (by positivity) _

theorem summable_fq {c : ℝ} (hc : 0 < c) : Summable (fq c) := by
  have hs : Summable fun m : ℤ => c ^ (-(3 / 2 : ℝ)) * |(m : ℝ)| ^ (-(3 / 2 : ℝ)) :=
    (Real.summable_abs_int_rpow (b := 3 / 2) (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset fun m hm => ?_
  simp only [Set.mem_setOf_eq] at hm
  rw [Set.mem_singleton_iff]
  by_contra h0
  apply hm
  rw [Real.norm_eq_abs, abs_of_nonneg (fq_nonneg c m)]
  have hm0 : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h0
  have hpos : 0 < c ^ 2 * (m : ℝ) ^ 2 := by positivity
  have hcm : 0 ≤ c * |(m : ℝ)| := by positivity
  calc fq c m = (1 + c ^ 2 * (m : ℝ) ^ 2) ^ (-(3 / 4 : ℝ)) := rfl
    _ ≤ (c ^ 2 * (m : ℝ) ^ 2) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by norm_num)
    _ = ((c * |(m : ℝ)|) ^ (2 : ℝ)) ^ (-(3 / 4 : ℝ)) := by
        rw [Real.rpow_two, mul_pow, sq_abs]
    _ = (c * |(m : ℝ)|) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_mul hcm]
        norm_num
    _ = c ^ (-(3 / 2 : ℝ)) * |(m : ℝ)| ^ (-(3 / 2 : ℝ)) := Real.mul_rpow hc.le (abs_nonneg _)

/-- `|k|/w_k² ≤ (2/c) f_q(k₁) f_q(k₂)` with `c = 2π/L`. -/
theorem size_div_wt_sq_le (hL : 0 < L) (k : Z2) :
    size k / wt L k ^ 2 ≤ 2 / (2 * π / L) * (fq (2 * π / L) k.1 * fq (2 * π / L) k.2) := by
  set c := 2 * π / L with hcdef
  have hc0 : 0 < c := by positivity
  set a := c * ((k.1 : ℤ) : ℝ) with ha
  set b := c * ((k.2 : ℤ) : ℝ) with hb
  have e : wt L k = 1 + a ^ 2 + b ^ 2 := by
    rw [ha, hb, mul_pow, mul_pow, hcdef]
    simp only [wt, qf, xi1, xi2]
    ring
  set W := wt L k with hW
  have hW1 : 1 ≤ W := one_le_wt L k
  have hW0 : 0 < W := by linarith
  have hP0 : 0 < (1 + a ^ 2) * (1 + b ^ 2) := by positivity
  have hP : (1 + a ^ 2) * (1 + b ^ 2) ≤ W ^ 2 := by
    rw [e]
    nlinarith [sq_nonneg (a * b), sq_nonneg a, sq_nonneg b]
  have hsize : size k = (|a| + |b|) / c := by
    unfold size
    rw [ha, hb, abs_mul, abs_mul, abs_of_pos hc0]
    field_simp
  have hA : |a| ≤ Real.sqrt W := Real.abs_le_sqrt (by rw [e]; nlinarith [sq_nonneg b])
  have hB : |b| ≤ Real.sqrt W := Real.abs_le_sqrt (by rw [e]; nlinarith [sq_nonneg a])
  have key : Real.sqrt W / W ^ 2 = (W ^ 2) ^ (-(3 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two W, ← Real.rpow_mul hW0.le, div_eq_mul_inv,
      ← Real.rpow_neg hW0.le, ← Real.rpow_add hW0]
    norm_num
  have hmono : (W ^ 2) ^ (-(3 / 4 : ℝ)) ≤ ((1 + a ^ 2) * (1 + b ^ 2)) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hP0 hP (by norm_num)
  have hfq : fq c k.1 * fq c k.2 = ((1 + a ^ 2) * (1 + b ^ 2)) ^ (-(3 / 4 : ℝ)) := by
    unfold fq
    rw [Real.mul_rpow (by positivity) (by positivity), ha, hb, mul_pow, mul_pow]
  rw [hfq, hsize]
  have hnum : |a| + |b| ≤ 2 * Real.sqrt W := by linarith
  have hW2 : 0 < W ^ 2 := by positivity
  calc (|a| + |b|) / c / W ^ 2 = (|a| + |b|) / W ^ 2 / c := by ring
    _ ≤ 2 * Real.sqrt W / W ^ 2 / c := by gcongr
    _ = 2 / c * (Real.sqrt W / W ^ 2) := by ring
    _ ≤ 2 / c * ((1 + a ^ 2) * (1 + b ^ 2)) ^ (-(3 / 4 : ℝ)) := by
        rw [key]
        exact mul_le_mul_of_nonneg_left hmono (by positivity)

theorem summable_size_wt (hL : 0 < L) : Summable fun k : Z2 => size k / wt L k ^ 2 := by
  have hc : 0 < 2 * π / L := by positivity
  have hn : Summable fun m : ℤ => ‖fq (2 * π / L) m‖ :=
    (summable_fq hc).congr fun m => (Real.norm_of_nonneg (fq_nonneg _ _)).symm
  have hprod : Summable fun k : Z2 => fq (2 * π / L) k.1 * fq (2 * π / L) k.2 :=
    summable_mul_of_summable_norm (f := fq (2 * π / L)) (g := fq (2 * π / L)) hn hn
  exact (hprod.mul_left _).of_nonneg_of_le
    (fun k => div_nonneg (size_nonneg k) (by positivity)) (size_div_wt_sq_le hL)

/-- The lattice sum `SB = Σ_k |k|/w_k²`. -/
noncomputable def SB (L : ℝ) : ℝ := ∑' k : Z2, size k / wt L k ^ 2

theorem SB_nonneg (L : ℝ) : 0 ≤ SB L :=
  tsum_nonneg fun k => div_nonneg (size_nonneg k) (by positivity)

/-- **Half a derivative in `ℓ¹`**: `Σ_j √|j| |ψ̂_j| ≤ √(SB) ‖ψ‖_{H²}`. -/
theorem tsum_sqrt_size_co_le (hL : 0 < L) (v : ℓ2) :
    Summable (fun j => Real.sqrt (size j) * ‖co L v j‖) ∧
      ∑' j, Real.sqrt (size j) * ‖co L v j‖ ≤ Real.sqrt (SB L) * ‖v‖ := by
  have e : ∀ j, Real.sqrt (size j) * ‖co L v j‖ = ‖v j‖ * (Real.sqrt (size j) / wt L j) := by
    intro j
    rw [norm_co]
    ring
  have hy2 : Summable fun j => (Real.sqrt (size j) / wt L j) ^ 2 :=
    (summable_size_wt hL).congr fun j => by rw [div_pow, Real.sq_sqrt (size_nonneg j)]
  have h := tsum_mul_le_sqrt (x := fun j => ‖v j‖) (y := fun j => Real.sqrt (size j) / wt L j)
    (fun _ => norm_nonneg _) (fun j => div_nonneg (Real.sqrt_nonneg _) (wt_pos L j).le)
    (summable_sq v) hy2
  simp_rw [e]
  refine ⟨h.1, ?_⟩
  have hSB : ∑' j, (Real.sqrt (size j) / wt L j) ^ 2 = SB L := by
    unfold SB
    exact tsum_congr fun j => by rw [div_pow, Real.sq_sqrt (size_nonneg j)]
  calc ∑' j, ‖v j‖ * (Real.sqrt (size j) / wt L j)
      ≤ Real.sqrt (∑' j, ‖v j‖ ^ 2) * Real.sqrt (∑' j, (Real.sqrt (size j) / wt L j) ^ 2) := h.2
    _ = Real.sqrt (SB L) * ‖v‖ := by rw [hSB, ← norm_eq_sqrt, mul_comm]

/-! ### The complex analytic lift -/

/-- The complex lift `ṽ = (e^{σ|k|} v_k)_k`, with `‖ṽ‖ = A_σ(v)`. -/
noncomputable def elift (σ : ℝ) (v : ℓ2) (h : ASum σ v) : ℓ2 :=
  mk (fun k => (aw σ k : ℂ) * v k)
    (h.congr fun k => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (aw_pos σ k)])

theorem elift_apply (σ : ℝ) (v : ℓ2) (h : ASum σ v) (k : Z2) :
    elift σ v h k = (aw σ k : ℂ) * v k := rfl

theorem norm_elift_apply (σ : ℝ) (v : ℓ2) (h : ASum σ v) (k : Z2) :
    ‖elift σ v h k‖ = aw σ k * ‖v k‖ := by
  rw [elift_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (aw_pos σ k)]

theorem norm_elift (σ : ℝ) (v : ℓ2) (h : ASum σ v) : ‖elift σ v h‖ = anorm σ v := by
  have hsq : ‖elift σ v h‖ ^ 2 = asq σ v := by
    rw [norm_sq_eq]
    exact tsum_congr fun k => by rw [norm_elift_apply]
  rw [anorm, ← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem co_elift (σ : ℝ) (v : ℓ2) (h : ASum σ v) (k : Z2) :
    co L (elift σ v h) k = (aw σ k : ℂ) * co L v k := by
  unfold co
  rw [elift_apply, mul_div_assoc]

theorem norm_co_elift (σ : ℝ) (v : ℓ2) (h : ASum σ v) (k : Z2) :
    ‖co L (elift σ v h) k‖ = aw σ k * ‖co L v k‖ := by
  rw [co_elift, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (aw_pos σ k)]

theorem elift_add {σ : ℝ} {v w : ℓ2} (hv : ASum σ v) (hw : ASum σ w) (hvw : ASum σ (v + w)) :
    elift σ (v + w) hvw = elift σ v hv + elift σ w hw := by
  ext k
  simp only [elift_apply, lp.coeFn_add, Pi.add_apply, mul_add]

theorem elift_sub {σ : ℝ} {v w : ℓ2} (hv : ASum σ v) (hw : ASum σ w) (hvw : ASum σ (v - w)) :
    elift σ (v - w) hvw = elift σ v hv - elift σ w hw := by
  ext k
  simp only [elift_apply, lp.coeFn_sub, Pi.sub_apply, mul_sub]

theorem elift_smul {σ : ℝ} (c : ℂ) {v : ℓ2} (hv : ASum σ v) (hcv : ASum σ (c • v)) :
    elift σ (c • v) hcv = c • elift σ v hv := by
  ext k
  simp only [elift_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem elift_conjH {σ : ℝ} {v : ℓ2} (hv : ASum σ v) (hcv : ASum σ (conjH v)) :
    elift σ (conjH v) hcv = conjH (elift σ v hv) := by
  ext k
  rw [elift_apply, conjH_apply, conjH_apply, elift_apply, map_mul, Complex.conj_ofReal, aw_neg]

/-! ### The commutator with the `H²` product -/

/-- The analytic commutator constant `C_B = 4√2 √(SB)/L`. -/
noncomputable def CB (L : ℝ) : ℝ := 4 * Real.sqrt 2 * Real.sqrt (SB L) / L

theorem CB_nonneg (hL : 0 < L) : 0 ≤ CB L := by unfold CB; positivity

set_option maxHeartbeats 400000 in
/-- **The analytic weight almost commutes with the `H²` product**:
`‖(vw)~ − ṽ w̃‖_{H²} ≤ C_B √σ A_σ(v) A_σ(w)`. -/
theorem comm_mulH_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {v w : ℓ2} (hv : ASum σ v)
    (hw : ASum σ w) :
    ‖elift σ (mulH L v w) (asum_mulH hL hσ hv hw).1 - mulH L (elift σ v hv) (elift σ w hw)‖ ≤
      CB L * Real.sqrt σ * anorm σ v * anorm σ w := by
  obtain ⟨V, hV⟩ : ∃ V, V = elift σ v hv := ⟨_, rfl⟩
  obtain ⟨Wt, hWt⟩ : ∃ Wt, Wt = elift σ w hw := ⟨_, rfl⟩
  rw [← hV, ← hWt, ← norm_elift σ v hv, ← norm_elift σ w hw, ← hV, ← hWt]
  have ha : L1 (co L v) := L1_co' hL v
  have hb : L1 (co L w) := L1_co' hL w
  have hA : L1 (co L V) := L1_co' hL V
  have hB : L1 (co L Wt) := L1_co' hL Wt
  -- half-derivative weighted sequences
  obtain ⟨b', hb'⟩ : ∃ b' : Z2 → ℝ, b' = fun j => Real.sqrt (size j) * ‖co L Wt j‖ := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : Z2 → ℝ, a' = fun j => Real.sqrt (size j) * ‖co L V j‖ := ⟨_, rfl⟩
  have hb'0 : ∀ j, 0 ≤ b' j := fun j => by rw [hb']; positivity
  have ha'0 : ∀ j, 0 ≤ a' j := fun j => by rw [ha']; positivity
  obtain ⟨hb'1, hb'sum⟩ := tsum_sqrt_size_co_le hL Wt
  obtain ⟨ha'1, ha'sum⟩ := tsum_sqrt_size_co_le hL V
  rw [← hb'] at hb'1 hb'sum
  rw [← ha'] at ha'1 ha'sum
  -- the two convolutions
  obtain ⟨F, hF⟩ : ∃ F : Z2 → ℝ, F = fun k => ∑' j, ‖V (k - j)‖ * b' j := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Z2 → ℝ, G = fun k => ∑' j, ‖Wt (k - j)‖ * a' j := ⟨_, rfl⟩
  obtain ⟨hF2, hFb⟩ := young_real (x := fun k => ‖V k‖) (y := b')
    (fun _ => norm_nonneg _) hb'0 (summable_sq V) hb'1
  obtain ⟨hG2, hGb⟩ := young_real (x := fun k => ‖Wt k‖) (y := a')
    (fun _ => norm_nonneg _) ha'0 (summable_sq Wt) ha'1
  rw [← norm_eq_sqrt] at hFb hGb
  replace hF2 : Summable fun k => F k ^ 2 := by rw [hF]; exact hF2
  replace hFb : Real.sqrt (∑' k, F k ^ 2) ≤ ‖V‖ * ∑' j, b' j := by rw [hF]; exact hFb
  replace hG2 : Summable fun k => G k ^ 2 := by rw [hG]; exact hG2
  replace hGb : Real.sqrt (∑' k, G k ^ 2) ≤ ‖Wt‖ * ∑' j, a' j := by rw [hG]; exact hGb
  -- fibre summability
  have hVb : ∀ k, Summable fun j => ‖V (k - j)‖ * b' j := fun k =>
    (hb'1.mul_left ‖V‖).of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (hb'0 j))
      (fun j => mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) V _) (hb'0 j))
  have hWa : ∀ k, Summable fun j => ‖Wt (k - j)‖ * a' j := fun k =>
    (ha'1.mul_left ‖Wt‖).of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (ha'0 j))
      (fun j => mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) Wt _) (ha'0 j))
  -- pointwise bound
  have hpt : ∀ k, ‖(elift σ (mulH L v w) (asum_mulH hL hσ hv hw).1 - mulH L V Wt) k‖ ≤
      2 * L⁻¹ * Real.sqrt (2 * σ) * (F k + G k) := by
    intro k
    have hab : Summable fun j => co L v (k - j) * co L w j := summable_conv_fiber ha hb k
    have hAB : Summable fun j => co L V (k - j) * co L Wt j := summable_conv_fiber hA hB k
    have hABn : Summable fun j => ‖co L V (k - j)‖ * ‖co L Wt j‖ :=
      (summable_conv_norm hA hB).prod_factor k
    -- the difference of the two convolutions
    have e1 : (elift σ (mulH L v w) (asum_mulH hL hσ hv hw).1 - mulH L V Wt) k =
        (wt L k : ℂ) * ((L : ℂ)⁻¹ * ∑' j, (((aw σ k : ℂ) - (aw σ (k - j) : ℂ) * (aw σ j : ℂ)) *
          (co L v (k - j) * co L w j))) := by
      rw [lp.coeFn_sub, Pi.sub_apply, elift_apply, mulH_apply hL, mulH_apply hL, pr, pr]
      have hsplit : ∑' j, (((aw σ k : ℂ) - (aw σ (k - j) : ℂ) * (aw σ j : ℂ)) *
            (co L v (k - j) * co L w j)) =
          (aw σ k : ℂ) * ∑' j, co L v (k - j) * co L w j - ∑' j, co L V (k - j) * co L Wt j := by
        rw [← tsum_mul_left, ← (hab.mul_left _).tsum_sub hAB]
        refine tsum_congr fun j => ?_
        rw [hV, hWt, co_elift, co_elift]
        ring
      rw [hsplit]
      ring
    -- the defect as a nonnegative real
    have hD : ∀ j, ‖((aw σ k : ℂ) - (aw σ (k - j) : ℂ) * (aw σ j : ℂ)) *
          (co L v (k - j) * co L w j)‖ =
        (aw σ (k - j) * aw σ j - aw σ k) * (‖co L v (k - j)‖ * ‖co L w j‖) := by
      intro j
      have hle := aw_le_mul hσ k j
      rw [norm_mul, norm_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hDs : Summable fun j => (aw σ (k - j) * aw σ j - aw σ k) *
        (‖co L v (k - j)‖ * ‖co L w j‖) := by
      refine hABn.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      · have hle := aw_le_mul hσ k j
        exact mul_nonneg (by linarith) (by positivity)
      · rw [hV, hWt, norm_co_elift, norm_co_elift]
        have h0 : 0 ≤ ‖co L v (k - j)‖ * ‖co L w j‖ := by positivity
        have h1 : 0 ≤ aw σ k := (aw_pos σ k).le
        nlinarith
    have hnorm : ‖∑' j, (((aw σ k : ℂ) - (aw σ (k - j) : ℂ) * (aw σ j : ℂ)) *
          (co L v (k - j) * co L w j))‖ ≤
        ∑' j, (aw σ (k - j) * aw σ j - aw σ k) * (‖co L v (k - j)‖ * ‖co L w j‖) := by
      refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hD))
      exact hDs.congr fun j => (hD j).symm
    -- pointwise in `j`
    have hj : ∀ j, wt L k * ((aw σ (k - j) * aw σ j - aw σ k) *
          (‖co L v (k - j)‖ * ‖co L w j‖)) ≤
        2 * Real.sqrt (2 * σ) * (‖V (k - j)‖ * b' j + a' (k - j) * ‖Wt j‖) := by
      intro j
      have hle := aw_le_mul hσ k j
      have hD1 := aw_defect_le hσ k j
      have hD2 := aw_defect_le_left hσ k j
      have hwk := wt_le L k j
      have e1' : ‖V (k - j)‖ = aw σ (k - j) * (wt L (k - j) * ‖co L v (k - j)‖) := by
        rw [hV, norm_elift_apply, wt_mul_norm_co]
      have e2' : ‖Wt j‖ = aw σ j * (wt L j * ‖co L w j‖) := by
        rw [hWt, norm_elift_apply, wt_mul_norm_co]
      have e3' : b' j = Real.sqrt (size j) * (aw σ j * ‖co L w j‖) := by
        rw [hb', hWt]
        simp only [norm_co_elift]
      have e4' : a' (k - j) = Real.sqrt (size (k - j)) * (aw σ (k - j) * ‖co L v (k - j)‖) := by
        rw [ha', hV]
        simp only [norm_co_elift]
      rw [e1', e2', e3', e4']
      set D := aw σ (k - j) * aw σ j - aw σ k with hDdef
      set P := aw σ (k - j) * aw σ j with hPdef
      set X := ‖co L v (k - j)‖ * ‖co L w j‖ with hXdef
      have hX0 : 0 ≤ X := by positivity
      have hD0 : 0 ≤ D := by linarith
      have hw1 := (wt_pos L (k - j)).le
      have hw2 := (wt_pos L j).le
      calc wt L k * (D * X) ≤ (2 * wt L (k - j) + 2 * wt L j) * (D * X) :=
            mul_le_mul_of_nonneg_right hwk (mul_nonneg hD0 hX0)
        _ = 2 * wt L (k - j) * X * D + 2 * wt L j * X * D := by ring
        _ ≤ 2 * wt L (k - j) * X * (P * (Real.sqrt (2 * σ) * Real.sqrt (size j))) +
              2 * wt L j * X * (P * (Real.sqrt (2 * σ) * Real.sqrt (size (k - j)))) := by
            gcongr
        _ = 2 * Real.sqrt (2 * σ) *
              (aw σ (k - j) * (wt L (k - j) * ‖co L v (k - j)‖) *
                  (Real.sqrt (size j) * (aw σ j * ‖co L w j‖)) +
                Real.sqrt (size (k - j)) * (aw σ (k - j) * ‖co L v (k - j)‖) *
                  (aw σ j * (wt L j * ‖co L w j‖))) := by
            rw [hPdef, hXdef]
            ring
    -- reindex the second convolution
    have hGk : G k = ∑' j, a' (k - j) * ‖Wt j‖ := by
      rw [hG]
      simp only
      rw [← (Equiv.subLeft k).tsum_eq]
      refine tsum_congr fun j => ?_
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
      ring
    have haW : Summable fun j => a' (k - j) * ‖Wt j‖ := by
      have := hWa k
      rw [← (Equiv.subLeft k).summable_iff] at this
      refine this.congr fun j => ?_
      simp only [Function.comp, Equiv.subLeft_apply, sub_sub_cancel]
      ring
    have hsum : wt L k * ∑' j, (aw σ (k - j) * aw σ j - aw σ k) *
          (‖co L v (k - j)‖ * ‖co L w j‖) ≤ 2 * Real.sqrt (2 * σ) * (F k + G k) := by
      rw [← tsum_mul_left, hGk, hF]
      simp only
      rw [← (hVb k).tsum_add haW, ← tsum_mul_left]
      exact (hDs.mul_left _).tsum_le_tsum hj (((hVb k).add haW).mul_left _)
    have hLi : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
    have hwk0 : 0 ≤ wt L k := (wt_pos L k).le
    rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos L k), norm_mul,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    calc wt L k * (L⁻¹ * ‖∑' j, (((aw σ k : ℂ) - (aw σ (k - j) : ℂ) * (aw σ j : ℂ)) *
            (co L v (k - j) * co L w j))‖)
        ≤ wt L k * (L⁻¹ * ∑' j, (aw σ (k - j) * aw σ j - aw σ k) *
            (‖co L v (k - j)‖ * ‖co L w j‖)) := by
          gcongr
      _ = L⁻¹ * (wt L k * ∑' j, (aw σ (k - j) * aw σ j - aw σ k) *
            (‖co L v (k - j)‖ * ‖co L w j‖)) := by ring
      _ ≤ L⁻¹ * (2 * Real.sqrt (2 * σ) * (F k + G k)) := mul_le_mul_of_nonneg_left hsum hLi
      _ = 2 * L⁻¹ * Real.sqrt (2 * σ) * (F k + G k) := by ring
  -- square sums
  have hF0 : ∀ k, 0 ≤ F k := fun k => by
    rw [hF]; exact tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (hb'0 j)
  have hG0 : ∀ k, 0 ≤ G k := fun k => by
    rw [hG]; exact tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (ha'0 j)
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * L⁻¹ * Real.sqrt (2 * σ) := ⟨_, rfl⟩
  rw [← hc] at hpt
  have hsq : Summable fun k => (c * (F k + G k)) ^ 2 := by
    have : Summable fun k => 2 * c ^ 2 * (F k ^ 2 + G k ^ 2) := (hF2.add hG2).mul_left _
    refine this.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_)
    nlinarith [sq_nonneg (F k - G k), sq_nonneg c]
  obtain ⟨_, hle⟩ := tsum_sq_le_of_le hsq hpt
  obtain ⟨X, hX⟩ : ∃ X, X = Real.sqrt (SB L) * ‖V‖ * ‖Wt‖ := ⟨_, rfl⟩
  have hFX : ∑' k, F k ^ 2 ≤ X ^ 2 := by
    have h1 : Real.sqrt (∑' k, F k ^ 2) ≤ X := by
      calc Real.sqrt (∑' k, F k ^ 2) ≤ ‖V‖ * ∑' j, b' j := hFb
        _ ≤ ‖V‖ * (Real.sqrt (SB L) * ‖Wt‖) := mul_le_mul_of_nonneg_left hb'sum (norm_nonneg _)
        _ = X := by rw [hX]; ring
    have h0 : 0 ≤ ∑' k, F k ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    calc ∑' k, F k ^ 2 = Real.sqrt (∑' k, F k ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ X ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hGX : ∑' k, G k ^ 2 ≤ X ^ 2 := by
    have h1 : Real.sqrt (∑' k, G k ^ 2) ≤ X := by
      calc Real.sqrt (∑' k, G k ^ 2) ≤ ‖Wt‖ * ∑' j, a' j := hGb
        _ ≤ ‖Wt‖ * (Real.sqrt (SB L) * ‖V‖) := mul_le_mul_of_nonneg_left ha'sum (norm_nonneg _)
        _ = X := by rw [hX]; ring
    have h0 : 0 ≤ ∑' k, G k ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    calc ∑' k, G k ^ 2 = Real.sqrt (∑' k, G k ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ X ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  refine norm_le_of_tsum_sq_le _ (by have := CB_nonneg hL; positivity) (hle.trans ?_)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ2 : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ
  have h2σ : Real.sqrt (2 * σ) ^ 2 = 2 * σ := Real.sq_sqrt (by positivity)
  have hSB : Real.sqrt (SB L) ^ 2 = SB L := Real.sq_sqrt (SB_nonneg L)
  have hc0 : 0 ≤ 2 * c ^ 2 := by positivity
  have hstep : 2 * c ^ 2 * (∑' k, F k ^ 2 + ∑' k, G k ^ 2) ≤ 2 * c ^ 2 * (X ^ 2 + X ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add hFX hGX) hc0
  have hfin : 2 * c ^ 2 * (X ^ 2 + X ^ 2) = (CB L * Real.sqrt σ * ‖V‖ * ‖Wt‖) ^ 2 := by
    have hL0 : L ≠ 0 := hL.ne'
    have e1 : 2 * c ^ 2 * (X ^ 2 + X ^ 2) =
        16 * L⁻¹ ^ 2 * Real.sqrt (2 * σ) ^ 2 * Real.sqrt (SB L) ^ 2 * ‖V‖ ^ 2 * ‖Wt‖ ^ 2 := by
      rw [hc, hX]
      ring
    have e2 : (CB L * Real.sqrt σ * ‖V‖ * ‖Wt‖) ^ 2 =
        16 * Real.sqrt 2 ^ 2 * Real.sqrt (SB L) ^ 2 * L⁻¹ ^ 2 * Real.sqrt σ ^ 2 * ‖V‖ ^ 2 *
          ‖Wt‖ ^ 2 := by
      rw [CB, div_eq_mul_inv]
      ring
    rw [e1, e2, h2, hσ2, h2σ, hSB]
    ring
  calc ∑' k, (c * (F k + G k)) ^ 2 ≤ ∑' k, 2 * c ^ 2 * (F k ^ 2 + G k ^ 2) :=
        hsq.tsum_le_tsum (fun k => by nlinarith [sq_nonneg (F k - G k), sq_nonneg c])
          ((hF2.add hG2).mul_left _)
    _ = 2 * c ^ 2 * (∑' k, F k ^ 2 + ∑' k, G k ^ 2) := by rw [tsum_mul_left, hF2.tsum_add hG2]
    _ ≤ 2 * c ^ 2 * (X ^ 2 + X ^ 2) := hstep
    _ = (CB L * Real.sqrt σ * ‖V‖ * ‖Wt‖) ^ 2 := hfin

/-! ### The remainder of the nonlinearity -/

theorem elift_congr {σ : ℝ} {v w : ℓ2} (e : v = w) (hv : ASum σ v) (hw : ASum σ w) :
    elift σ v hv = elift σ w hw := by
  subst e
  rfl

/-- One product step: `‖(ab)~ − XY‖ ≤ C_B √σ A(a)A(b) + C_A ‖ã − X‖ A(b) + C_A ‖X‖ ‖b̃ − Y‖`. -/
theorem comm_step (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) {a b : ℓ2} (ha : ASum σ a) (hb : ASum σ b)
    (X Y : ℓ2) :
    ‖elift σ (mulH L a b) (asum_mulH hL hσ ha hb).1 - mulH L X Y‖ ≤
      CB L * Real.sqrt σ * anorm σ a * anorm σ b + CA L * ‖elift σ a ha - X‖ * anorm σ b +
        CA L * ‖X‖ * ‖elift σ b hb - Y‖ := by
  have e : elift σ (mulH L a b) (asum_mulH hL hσ ha hb).1 - mulH L X Y =
      (elift σ (mulH L a b) (asum_mulH hL hσ ha hb).1 - mulH L (elift σ a ha) (elift σ b hb)) +
        mulH L (elift σ a ha - X) (elift σ b hb) + mulH L X (elift σ b hb - Y) := by
    rw [mulH_sub_left hL, mulH_sub_right hL]
    abel
  rw [e]
  have h1 := comm_mulH_le hL hσ ha hb
  have h2 := norm_mulH_le hL (elift σ a ha - X) (elift σ b hb)
  have h3 := norm_mulH_le hL X (elift σ b hb - Y)
  rw [norm_elift] at h2
  calc _ ≤ ‖elift σ (mulH L a b) (asum_mulH hL hσ ha hb).1 - mulH L (elift σ a ha) (elift σ b hb)‖ +
          ‖mulH L (elift σ a ha - X) (elift σ b hb)‖ + ‖mulH L X (elift σ b hb - Y)‖ :=
        norm_add₃_le
    _ ≤ _ := by linarith

/-- The remainder polynomial `Q(A) = C_B (2|β| C_A A³ + 4|γ| C_A³ A⁵)`. -/
noncomputable def QR (L β γ A : ℝ) : ℝ :=
  CB L * (2 * |β| * CA L * A ^ 3 + 4 * |γ| * CA L ^ 3 * A ^ 5)

theorem QR_nonneg (hL : 0 < L) (β γ : ℝ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ QR L β γ A := by
  have := CB_nonneg hL
  have := CA_nonneg hL
  unfold QR
  positivity

theorem QR_mono (hL : 0 < L) (β γ : ℝ) {A A' : ℝ} (hA : 0 ≤ A) (h : A ≤ A') :
    QR L β γ A ≤ QR L β γ A' := by
  have hB := CB_nonneg hL
  have hC := CA_nonneg hL
  unfold QR
  gcongr

/-- **The remainder of the nonlinearity**: `‖(F(u))~ − F(ũ)‖ ≤ √σ Q(A_σ(u))`. -/
theorem comm_Fnl_le (hL : 0 < L) {σ : ℝ} (hσ : 0 ≤ σ) (β γ : ℝ) {u : ℓ2} (hu : ASum σ u) :
    ‖elift σ (Fnl L β γ u) (anorm_Fnl_le hL hσ β γ hu).1 - Fnl L β γ (elift σ u hu)‖ ≤
      Real.sqrt σ * QR L β γ (anorm σ u) := by
  set A := anorm σ u with hAdef
  set U := elift σ u hu with hUdef
  have hA0 : 0 ≤ A := anorm_nonneg σ u
  have hNU : ‖U‖ = A := norm_elift σ u hu
  have hC := CA_nonneg hL
  have hB := CB_nonneg hL
  have hs := Real.sqrt_nonneg σ
  have hcu : ASum σ (conjH u) := asum_conjH hu
  have hcU : elift σ (conjH u) hcu = conjH U := elift_conjH hu hcu
  have hAc : anorm σ (conjH u) = A := anorm_conjH σ u
  have hP2 : ASum σ (mulH L u u) := (asum_mulH hL hσ hu hu).1
  have hP3 : ASum σ (mulH L (mulH L u u) (conjH u)) := (asum_mulH hL hσ hP2 hcu).1
  have hQ3 : ASum σ (mulH L (mulH L u u) u) := (asum_mulH hL hσ hP2 hu).1
  have hP4 : ASum σ (mulH L (mulH L (mulH L u u) u) (conjH u)) := (asum_mulH hL hσ hQ3 hcu).1
  have hP5 : ASum σ (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u)) :=
    (asum_mulH hL hσ hP4 hcu).1
  -- analytic sizes of the partial products
  have a2 : anorm σ (mulH L u u) ≤ CA L * A * A := anorm_mulH_le hL hσ hu hu
  have a3 : anorm σ (mulH L (mulH L u u) u) ≤ CA L ^ 2 * A ^ 3 := by
    have h := anorm_mulH_le hL hσ hP2 hu
    calc _ ≤ CA L * anorm σ (mulH L u u) * A := h
      _ ≤ CA L * (CA L * A * A) * A := by gcongr
      _ = CA L ^ 2 * A ^ 3 := by ring
  have a4 : anorm σ (mulH L (mulH L (mulH L u u) u) (conjH u)) ≤ CA L ^ 3 * A ^ 4 := by
    have h := anorm_mulH_le hL hσ hQ3 hcu
    rw [hAc] at h
    calc _ ≤ CA L * anorm σ (mulH L (mulH L u u) u) * A := h
      _ ≤ CA L * (CA L ^ 2 * A ^ 3) * A := by gcongr
      _ = CA L ^ 3 * A ^ 4 := by ring
  have n2 : ‖mulH L U U‖ ≤ CA L * A * A := by
    have h := norm_mulH_le hL U U
    rwa [hNU] at h
  have n3 : ‖mulH L (mulH L U U) U‖ ≤ CA L ^ 2 * A ^ 3 := by
    have h := norm_mulH_le hL (mulH L U U) U
    rw [hNU] at h
    calc _ ≤ CA L * ‖mulH L U U‖ * A := h
      _ ≤ CA L * (CA L * A * A) * A := by gcongr
      _ = CA L ^ 2 * A ^ 3 := by ring
  have n4 : ‖mulH L (mulH L (mulH L U U) U) (conjH U)‖ ≤ CA L ^ 3 * A ^ 4 := by
    have h := norm_mulH_le hL (mulH L (mulH L U U) U) (conjH U)
    rw [norm_conjH, hNU] at h
    calc _ ≤ CA L * ‖mulH L (mulH L U U) U‖ * A := h
      _ ≤ CA L * (CA L ^ 2 * A ^ 3) * A := by gcongr
      _ = CA L ^ 3 * A ^ 4 := by ring
  -- the remainders of the partial products
  have d2 : ‖elift σ (mulH L u u) hP2 - mulH L U U‖ ≤ CB L * Real.sqrt σ * A * A :=
    comm_mulH_le hL hσ hu hu
  have d3 : ‖elift σ (mulH L (mulH L u u) (conjH u)) hP3 - mulH L (mulH L U U) (conjH U)‖ ≤
      2 * CA L * CB L * Real.sqrt σ * A ^ 3 := by
    have h := comm_step hL hσ hP2 hcu (mulH L U U) (conjH U)
    rw [hcU, sub_self, norm_zero, mul_zero, add_zero, hAc] at h
    calc _ ≤ CB L * Real.sqrt σ * anorm σ (mulH L u u) * A +
          CA L * ‖elift σ (mulH L u u) hP2 - mulH L U U‖ * A := h
      _ ≤ CB L * Real.sqrt σ * (CA L * A * A) * A + CA L * (CB L * Real.sqrt σ * A * A) * A := by
          gcongr
      _ = 2 * CA L * CB L * Real.sqrt σ * A ^ 3 := by ring
  have d3' : ‖elift σ (mulH L (mulH L u u) u) hQ3 - mulH L (mulH L U U) U‖ ≤
      2 * CA L * CB L * Real.sqrt σ * A ^ 3 := by
    have h := comm_step hL hσ hP2 hu (mulH L U U) U
    rw [← hUdef, sub_self, norm_zero, mul_zero, add_zero] at h
    calc _ ≤ CB L * Real.sqrt σ * anorm σ (mulH L u u) * A +
          CA L * ‖elift σ (mulH L u u) hP2 - mulH L U U‖ * A := h
      _ ≤ CB L * Real.sqrt σ * (CA L * A * A) * A + CA L * (CB L * Real.sqrt σ * A * A) * A := by
          gcongr
      _ = 2 * CA L * CB L * Real.sqrt σ * A ^ 3 := by ring
  have d4 : ‖elift σ (mulH L (mulH L (mulH L u u) u) (conjH u)) hP4 -
      mulH L (mulH L (mulH L U U) U) (conjH U)‖ ≤ 3 * CA L ^ 2 * CB L * Real.sqrt σ * A ^ 4 := by
    have h := comm_step hL hσ hQ3 hcu (mulH L (mulH L U U) U) (conjH U)
    rw [hcU, sub_self, norm_zero, mul_zero, add_zero, hAc] at h
    calc _ ≤ CB L * Real.sqrt σ * anorm σ (mulH L (mulH L u u) u) * A +
          CA L * ‖elift σ (mulH L (mulH L u u) u) hQ3 - mulH L (mulH L U U) U‖ * A := h
      _ ≤ CB L * Real.sqrt σ * (CA L ^ 2 * A ^ 3) * A +
            CA L * (2 * CA L * CB L * Real.sqrt σ * A ^ 3) * A := by gcongr
      _ = 3 * CA L ^ 2 * CB L * Real.sqrt σ * A ^ 4 := by ring
  have d5 : ‖elift σ (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u)) hP5 -
      mulH L (mulH L (mulH L (mulH L U U) U) (conjH U)) (conjH U)‖ ≤
        4 * CA L ^ 3 * CB L * Real.sqrt σ * A ^ 5 := by
    have h := comm_step hL hσ hP4 hcu (mulH L (mulH L (mulH L U U) U) (conjH U)) (conjH U)
    rw [hcU, sub_self, norm_zero, mul_zero, add_zero, hAc] at h
    calc _ ≤ CB L * Real.sqrt σ * anorm σ (mulH L (mulH L (mulH L u u) u) (conjH u)) * A +
          CA L * ‖elift σ (mulH L (mulH L (mulH L u u) u) (conjH u)) hP4 -
            mulH L (mulH L (mulH L U U) U) (conjH U)‖ * A := h
      _ ≤ CB L * Real.sqrt σ * (CA L ^ 3 * A ^ 4) * A +
            CA L * (3 * CA L ^ 2 * CB L * Real.sqrt σ * A ^ 4) * A := by gcongr
      _ = 4 * CA L ^ 3 * CB L * Real.sqrt σ * A ^ 5 := by ring
  -- assemble
  have eF : elift σ (Fnl L β γ u) (anorm_Fnl_le hL hσ β γ hu).1 - Fnl L β γ U =
      (-(β : ℂ)) • (elift σ (mulH L (mulH L u u) (conjH u)) hP3 - mulH L (mulH L U U) (conjH U)) +
        (γ : ℂ) • (elift σ (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u)) hP5 -
          mulH L (mulH L (mulH L (mulH L U U) U) (conjH U)) (conjH U)) := by
    ext k
    simp only [lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, elift_apply, Fnl]
    ring
  rw [eF]
  have nb : ‖(-(β : ℂ))‖ = |β| := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have ng : ‖(γ : ℂ)‖ = |γ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ‖(-(β : ℂ)) • (elift σ (mulH L (mulH L u u) (conjH u)) hP3 -
          mulH L (mulH L U U) (conjH U))‖ +
        ‖(γ : ℂ) • (elift σ (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u)) hP5 -
          mulH L (mulH L (mulH L (mulH L U U) U) (conjH U)) (conjH U))‖ := norm_add_le _ _
    _ = |β| * ‖elift σ (mulH L (mulH L u u) (conjH u)) hP3 - mulH L (mulH L U U) (conjH U)‖ +
        |γ| * ‖elift σ (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u)) hP5 -
          mulH L (mulH L (mulH L (mulH L U U) U) (conjH U)) (conjH U)‖ := by
        rw [norm_smul, norm_smul, nb, ng]
    _ ≤ |β| * (2 * CA L * CB L * Real.sqrt σ * A ^ 3) +
        |γ| * (4 * CA L ^ 3 * CB L * Real.sqrt σ * A ^ 5) := by gcongr
    _ = Real.sqrt σ * QR L β γ A := by unfold QR; ring

/-! ### The lifted Galerkin flow -/

/-- The analytic lift on `S`, a bounded diagonal operator. -/
noncomputable def EL (σ : ℝ) (S : Finset Z2) : ℓ2 →L[ℂ] ℓ2 :=
  dmul (fun k => if k ∈ S then (aw σ k : ℂ) else 0) (∑ k ∈ S, aw σ k)
    (Finset.sum_nonneg fun k _ => (aw_pos σ k).le)
    (fun k => by
      beta_reduce
      split_ifs with hk
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (aw_pos σ k)]
        exact Finset.single_le_sum (fun i _ => (aw_pos σ i).le) hk
      · rw [norm_zero]
        exact Finset.sum_nonneg fun i _ => (aw_pos σ i).le)

theorem EL_apply (σ : ℝ) (S : Finset Z2) (v : ℓ2) (k : Z2) :
    EL σ S v k = (if k ∈ S then (aw σ k : ℂ) else 0) * v k := rfl

theorem EL_eq_elift {σ : ℝ} {S : Finset Z2} {v : ℓ2} (hv : Supported S v) :
    EL σ S v = elift σ v (asum_of_supported hv σ) := by
  ext k
  rw [EL_apply, elift_apply]
  split_ifs with hk
  · rfl
  · rw [hv k hk, mul_zero, mul_zero]

theorem EL_supported (σ : ℝ) (S : Finset Z2) (v : ℓ2) : Supported S (EL σ S v) := by
  intro k hk
  rw [EL_apply, if_neg hk, zero_mul]

theorem norm_EL {σ : ℝ} {S : Finset Z2} {v : ℓ2} (hv : Supported S v) :
    ‖EL σ S v‖ = anorm σ v := by
  rw [EL_eq_elift hv, norm_elift]

theorem EL_trunc_elift {σ : ℝ} (S : Finset Z2) {x : ℓ2} (hx : ASum σ x) :
    EL σ S x = trunc S (elift σ x hx) := by
  ext k
  rw [EL_apply, trunc_apply, elift_apply]
  split_ifs <;> simp

theorem EL_U (σ : ℝ) (S : Finset Z2) (κ t : ℝ) (v : ℓ2) :
    EL σ S (U L κ t v) = U L κ t (EL σ S v) := by
  ext k
  rw [EL_apply, U_apply, U_apply, EL_apply]
  ring

theorem EL_trunc (σ : ℝ) (S : Finset Z2) (v : ℓ2) : EL σ S (trunc S v) = EL σ S v := by
  ext k
  rw [EL_apply, EL_apply, trunc_apply]
  split_ifs <;> simp

theorem anorm_U (σ κ t : ℝ) (v : ℓ2) : anorm σ (U L κ t v) = anorm σ v := by
  unfold anorm
  rw [asq_U]

/-- **The lifted Galerkin field.** For `S`-supported `v`, the lift of the Galerkin field differs
from the Galerkin field of the lift by at most `√σ Q(A_σ(v))`. -/
theorem lift_galerkin_err (hL : 0 < L) {κ β γ σ : ℝ} (hσ : 0 ≤ σ) {S : Finset Z2} {v : ℓ2}
    (hv : Supported S v) (t : ℝ) :
    ‖EL σ S (galerkin S L κ β γ t v) - galerkin S L κ β γ t (EL σ S v)‖ ≤
      Real.sqrt σ * QR L β γ (anorm σ v) := by
  have hus : Supported S (U L κ t v) := supported_U hv κ t
  have hua : ASum σ (U L κ t v) := asum_of_supported hus σ
  have hFa := (anorm_Fnl_le hL hσ β γ hua).1
  have hEv : Supported S (EL σ S v) := EL_supported σ S v
  have g1 : galerkin S L κ β γ t v =
      (-I) • U L κ (-t) (trunc S (Fnl L β γ (U L κ t v))) := by
    unfold galerkin
    rw [supported_trunc_eq hv, Gf, trunc_smul, ← trunc_comm_U]
  have g2 : galerkin S L κ β γ t (EL σ S v) =
      (-I) • U L κ (-t) (trunc S (Fnl L β γ (EL σ S (U L κ t v)))) := by
    unfold galerkin
    rw [supported_trunc_eq hEv, Gf, trunc_smul, ← trunc_comm_U, ← EL_U]
  have key : EL σ S (galerkin S L κ β γ t v) - galerkin S L κ β γ t (EL σ S v) =
      (-I) • U L κ (-t) (trunc S (elift σ (Fnl L β γ (U L κ t v)) hFa -
        Fnl L β γ (elift σ (U L κ t v) hua))) := by
    rw [g1, g2, map_smul, EL_U, EL_trunc, EL_trunc_elift S hFa, EL_eq_elift hus, trunc_sub,
      map_sub, smul_sub]
  rw [key, norm_smul, norm_neg, Complex.norm_I, one_mul, norm_U]
  calc _ ≤ ‖elift σ (Fnl L β γ (U L κ t v)) hFa - Fnl L β γ (elift σ (U L κ t v) hua)‖ :=
        trunc_norm_le _ _
    _ ≤ Real.sqrt σ * QR L β γ (anorm σ (U L κ t v)) := comm_Fnl_le hL hσ β γ hua
    _ = Real.sqrt σ * QR L β γ (anorm σ v) := by rw [anorm_U]

/-! ### Rates of the lifted mass and Hamiltonian -/

/-- The Galerkin field preserves mass: `Re ⟨P v, P G_S(v)⟩ = 0` for `S`-supported `v`. -/
theorem inner_Lc_galerkin (hL : 0 < L) {κ β γ : ℝ} {S : Finset Z2} {v : ℓ2}
    (hv : Supported S v) (t : ℝ) :
    inner ℝ (Lc L v) (Lc L (galerkin S L κ β γ t v)) = 0 := by
  rw [real_inner_eq, galerkin, supported_trunc_eq hv, supported_inner_Lc L hv, Lc_Gf,
    inner_smul_right, inner_U_neg, ← Lc_U, re_neg_I_mul, inner_Lc, inner_Fnl_im hL]

/-- The Galerkin field preserves the Hamiltonian (the derivative expression vanishes). -/
theorem ham_galerkin_zero {κ β γ : ℝ} {S : Finset Z2} {v : ℓ2}
    (hv : Supported S v) (t : ℝ) :
    2 * inner ℝ (Ac L κ v) (Ac L κ (galerkin S L κ β γ t v)) +
      2 * (inner ℂ (Lc L (Fnl L β γ (U L κ t v))) (Lc L (U L κ t (galerkin S L κ β γ t v))) +
        Lw L κ (Fnl L β γ (U L κ t v)) (U L κ t v)).re = 0 := by
  set u := U L κ t v with hu
  have hc := inner_conj_symm (𝕜 := ℂ) (Ac L κ (Fnl L β γ u)) (Ac L κ u)
  have hkin : inner ℂ (Ac L κ v) (Ac L κ (galerkin S L κ β γ t v)) =
      inner ℂ (Ac L κ v) (Ac L κ (Gf L κ β γ t v)) := by
    unfold galerkin
    rw [supported_trunc_eq hv, supported_inner_Ac L κ hv]
  rw [real_inner_eq, hkin, Ac_Gf, inner_smul_right, inner_U_neg, ← Ac_U,
    U_galerkin S t hv, map_smul, inner_smul_right, projected_inner_Lc_self,
    Lw, Complex.add_re, re_neg_I_mul_inner_self, zero_add]
  rw [re_neg_I_mul, re_neg_I_mul, ← hc, Complex.conj_im]
  ring

/-- **Rates of the lifted mass and Hamiltonian.** Along an actual Galerkin trajectory, the mass
and the Hamiltonian of the lifted state change at rate `O(√σ)`, with constants independent of
`S`. -/
theorem lifted_rates (hL : 0 < L) {κ β γ σ : ℝ} (hσ : 0 ≤ σ) {S : Finset Z2} {W : ℝ → ℓ2}
    (hs : ∀ t, Supported S (W t)) (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (t : ℝ) :
    ∃ dm dh : ℝ, HasDerivAt (fun s => mass L (EL σ S (W s))) dm t ∧
      HasDerivAt (fun s => ham L κ β γ (U L κ s (EL σ S (W s)))) dh t ∧
      |dm| ≤ 2 * anorm σ (W t) * (Real.sqrt σ * QR L β γ (anorm σ (W t))) ∧
      |dh| ≤ (2 * (|κ| + 1) ^ 2 * anorm σ (W t) +
          2 * (LF L β γ (anorm σ (W t)) * anorm σ (W t))) *
        (Real.sqrt σ * QR L β γ (anorm σ (W t))) := by
  have hYd : HasDerivAt (fun s => EL σ S (W s)) (EL σ S (galerkin S L κ β γ t (W t))) t :=
    ((EL σ S).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hW t)
  set Y := EL σ S (W t) with hYdef
  set g := galerkin S L κ β γ t Y with hg
  set E := EL σ S (galerkin S L κ β γ t (W t)) - g with hE
  have hsplit : EL σ S (galerkin S L κ β γ t (W t)) = g + E := by rw [hE]; abel
  have hYs : Supported S Y := EL_supported σ S (W t)
  have hNY : ‖Y‖ = anorm σ (W t) := norm_EL (hs t)
  have hEb : ‖E‖ ≤ Real.sqrt σ * QR L β γ (anorm σ (W t)) := lift_galerkin_err hL hσ (hs t) t
  set A := anorm σ (W t) with hA
  have hA0 : 0 ≤ A := anorm_nonneg σ (W t)
  have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
  refine ⟨2 * inner ℝ (Lc L Y) (Lc L (EL σ S (galerkin S L κ β γ t (W t)))),
    2 * inner ℝ (Ac L κ Y) (Ac L κ (EL σ S (galerkin S L κ β γ t (W t)))) +
      2 * (inner ℂ (Lc L (Fnl L β γ (U L κ t Y)))
          (Lc L (U L κ t (EL σ S (galerkin S L κ β γ t (W t))))) +
        Lw L κ (Fnl L β γ (U L κ t Y)) (U L κ t Y)).re, ?_, ?_, ?_, ?_⟩
  · have hm := (hasDerivAt_Lc (L := L) hYd).norm_sq
    simp_rw [mass_eq_norm_Lc]
    exact hm
  · have hk := (hasDerivAt_Ac (L := L) (κ := κ) hYd).norm_sq
    have hp := hasDerivAt_pot_U (β := β) (γ := γ) (κ := κ) hL hYd
    have e : (fun s => ham L κ β γ (U L κ s (EL σ S (W s)))) =
        fun s => ‖Ac L κ (EL σ S (W s))‖ ^ 2 + pot L β γ (U L κ s (EL σ S (W s))) := by
      funext s
      rw [ham_U]
    rw [e]
    exact hk.add hp
  · rw [hsplit, map_add, inner_add_right, inner_Lc_galerkin hL hYs, zero_add, abs_mul,
      abs_two]
    have h1 := abs_real_inner_le_norm (Lc L Y) (Lc L E)
    have h2 := norm_Lc_le L Y
    have h3 := norm_Lc_le L E
    rw [hNY] at h2
    calc 2 * |inner ℝ (Lc L Y) (Lc L E)| ≤ 2 * (A * ‖E‖) := by
          have := mul_le_mul h2 h3 (norm_nonneg _) hA0
          nlinarith [h1]
      _ ≤ 2 * A * (Real.sqrt σ * QR L β γ A) := by nlinarith [mul_le_mul_of_nonneg_left hEb hA0]
  · have hz := ham_galerkin_zero (L := L) (κ := κ) (β := β) (γ := γ) hYs t
    have e2 : 2 * inner ℝ (Ac L κ Y) (Ac L κ (g + E)) +
          2 * (inner ℂ (Lc L (Fnl L β γ (U L κ t Y))) (Lc L (U L κ t (g + E))) +
            Lw L κ (Fnl L β γ (U L κ t Y)) (U L κ t Y)).re =
        (2 * inner ℝ (Ac L κ Y) (Ac L κ g) +
          2 * (inner ℂ (Lc L (Fnl L β γ (U L κ t Y))) (Lc L (U L κ t g)) +
            Lw L κ (Fnl L β γ (U L κ t Y)) (U L κ t Y)).re) +
        (2 * inner ℝ (Ac L κ Y) (Ac L κ E) +
          2 * (inner ℂ (Lc L (Fnl L β γ (U L κ t Y))) (Lc L (U L κ t E))).re) := by
      simp only [map_add, inner_add_right, Complex.add_re]
      ring
    rw [hsplit, e2, hz, zero_add]
    have hK := kinetic_norm_bound L κ Y
    have hKE := kinetic_norm_bound L κ E
    rw [hNY] at hK
    have hF := norm_Fnl_le hL β γ (U L κ t Y)
    rw [norm_U, hNY] at hF
    have i1 := abs_real_inner_le_norm (Ac L κ Y) (Ac L κ E)
    have i2 : |(inner ℂ (Lc L (Fnl L β γ (U L κ t Y))) (Lc L (U L κ t E))).re| ≤
        ‖Fnl L β γ (U L κ t Y)‖ * ‖E‖ := by
      calc _ ≤ ‖inner ℂ (Lc L (Fnl L β γ (U L κ t Y))) (Lc L (U L κ t E))‖ :=
            Complex.abs_re_le_norm _
        _ ≤ ‖Lc L (Fnl L β γ (U L κ t Y))‖ * ‖Lc L (U L κ t E)‖ := norm_inner_le_norm _ _
        _ ≤ ‖Fnl L β γ (U L κ t Y)‖ * ‖E‖ := by
            have := norm_Lc_le L (Fnl L β γ (U L κ t Y))
            have h' := norm_Lc_le L (U L κ t E)
            rw [norm_U] at h'
            exact mul_le_mul this h' (norm_nonneg _) (norm_nonneg _)
    have hk0 : 0 ≤ |κ| + 1 := by positivity
    have hLF := LF_nonneg L β γ A
    have hAc : ‖Ac L κ Y‖ * ‖Ac L κ E‖ ≤ (|κ| + 1) ^ 2 * A * ‖E‖ := by
      have := mul_le_mul hK hKE (norm_nonneg _) (by positivity)
      nlinarith
    have hFE : ‖Fnl L β γ (U L κ t Y)‖ * ‖E‖ ≤ LF L β γ A * A * ‖E‖ :=
      mul_le_mul_of_nonneg_right hF hE0
    have hsum : |2 * inner ℝ (Ac L κ Y) (Ac L κ E) +
        2 * (inner ℂ (Lc L (Fnl L β γ (U L κ t Y))) (Lc L (U L κ t E))).re| ≤
        (2 * (|κ| + 1) ^ 2 * A + 2 * (LF L β γ A * A)) * ‖E‖ := by
      have ha := abs_add_le (2 * inner ℝ (Ac L κ Y) (Ac L κ E))
        (2 * (inner ℂ (Lc L (Fnl L β γ (U L κ t Y))) (Lc L (U L κ t E))).re)
      rw [abs_mul, abs_mul, abs_two] at ha
      calc _ ≤ 2 * |inner ℝ (Ac L κ Y) (Ac L κ E)| +
            2 * |(inner ℂ (Lc L (Fnl L β γ (U L κ t Y))) (Lc L (U L κ t E))).re| := ha
        _ ≤ 2 * ((|κ| + 1) ^ 2 * A * ‖E‖) + 2 * (LF L β γ A * A * ‖E‖) := by
            linarith [i1, hAc, i2, hFE]
        _ = (2 * (|κ| + 1) ^ 2 * A + 2 * (LF L β γ A * A)) * ‖E‖ := by ring
    have hc0 : 0 ≤ 2 * (|κ| + 1) ^ 2 * A + 2 * (LF L β γ A * A) := by positivity
    exact hsum.trans (mul_le_mul_of_nonneg_left hEb hc0)

/-! ### The continuity argument -/

/-- **Bootstrap.** If `f ≤ 2B` on `[0, t)` always forces `f(t) ≤ B`, then `f ≤ B` on `[0, T]`. -/
theorem bootstrap_le {f : ℝ → ℝ} {T B : ℝ} (hB : 0 < B) (hf : ContinuousOn f (Icc 0 T))
    (hstep : ∀ t ∈ Icc 0 T, (∀ s ∈ Ico 0 t, f s ≤ 2 * B) → f t ≤ B) :
    ∀ t ∈ Icc 0 T, f t ≤ B := by
  by_cases hall : ∀ t ∈ Icc 0 T, f t < 2 * B
  · intro t ht
    exact hstep t ht fun s hs => (hall s ⟨hs.1, hs.2.le.trans ht.2⟩).le
  · push_neg at hall
    exfalso
    obtain ⟨t₁, ht₁, hft₁⟩ := hall
    set K := Icc 0 T ∩ f ⁻¹' Ici (2 * B) with hK
    have hKc : IsClosed K := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hKne : K.Nonempty := ⟨t₁, ht₁, hft₁⟩
    have hKb : BddBelow K := ⟨0, fun t ht => ht.1.1⟩
    have hmem := hKc.csInf_mem hKne hKb
    have hlow : ∀ s ∈ Ico 0 (sInf K), f s ≤ 2 * B := by
      intro s hs
      have hsK : s ∉ K := notMem_of_lt_csInf hs.2 hKb
      have hsI : s ∈ Icc 0 T := ⟨hs.1, hs.2.le.trans hmem.1.2⟩
      by_contra hfs
      exact hsK ⟨hsI, (not_le.mp hfs).le⟩
    have h1 := hstep (sInf K) hmem.1 hlow
    have h2 : 2 * B ≤ f (sInf K) := hmem.2
    linarith

/-! ### The polynomial radius -/

/-- The bootstrap constant: it bounds both lifted rates per `√σ` while `A_σ ≤ 2B`. -/
noncomputable def KR (L κ β γ B : ℝ) : ℝ :=
  (4 * B + 4 * (|κ| + 1) ^ 2 * B + 4 * (LF L β γ (2 * B) * B)) * QR L β γ (2 * B)

/-- The a priori bound for the lifted state, from the initial analytic norm `A₀`. -/
noncomputable def BR (L κ β γ A₀ : ℝ) : ℝ :=
  Rap κ β γ (A₀ ^ 2 + 1) (energyBudget L κ β γ A₀ + 1)

theorem Rap_mono {κ β γ M M' H H' : ℝ} (hγ : 0 < γ) (hM : M ≤ M') (hH : H ≤ H') :
    Rap κ β γ M H ≤ Rap κ β γ M' H' := by
  unfold Rap
  have hc : 0 ≤ 3 * β ^ 2 / (16 * γ) := by positivity
  have h1 : Real.sqrt M ≤ Real.sqrt M' := Real.sqrt_le_sqrt hM
  have h2 : Real.sqrt (H + 3 * β ^ 2 / (16 * γ) * M) ≤
      Real.sqrt (H' + 3 * β ^ 2 / (16 * γ) * M') :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hk : 0 ≤ 1 + |κ| := by positivity
  nlinarith

theorem BR_pos (L κ β γ A₀ : ℝ) : 0 < BR L κ β γ A₀ := by
  unfold BR Rap
  have h1 : 1 ≤ Real.sqrt (A₀ ^ 2 + 1) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg A₀])
  have h2 : 1 ≤ 1 + |κ| := by linarith [abs_nonneg κ]
  have h3 := Real.sqrt_nonneg (energyBudget L κ β γ A₀ + 1 + 3 * β ^ 2 / (16 * γ) * (A₀ ^ 2 + 1))
  nlinarith

theorem KR_nonneg (hL : 0 < L) (κ β γ : ℝ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ KR L κ β γ B := by
  have h1 := LF_nonneg L β γ (2 * B)
  have h2 := QR_nonneg hL β γ (by linarith : 0 ≤ 2 * B)
  unfold KR
  positivity

/-- **Almost conservation, uniform in `S`.** Let `W` be an actual Galerkin trajectory on `S` and
`B ≥ BR(A_{σ₀}(W(0)))`. If `σ ≤ σ₀` and `T √σ K_R(B) ≤ 1`, then `A_σ(W(t)) ≤ B` for every
`t ∈ [0, T]`. -/
theorem galerkin_radius_bound (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) {S : Finset Z2}
    {W : ℝ → ℓ2} (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    {σ₀ σ T B : ℝ} (hσ : 0 ≤ σ) (hσσ₀ : σ ≤ σ₀) (hBB : BR L κ β γ (anorm σ₀ (W 0)) ≤ B)
    (hrad : T * Real.sqrt σ * KR L κ β γ B ≤ 1) :
    ∀ t ∈ Icc 0 T, anorm σ (W t) ≤ B := by
  set A₀ := anorm σ₀ (W 0) with hA₀
  have hB : 0 < B := (BR_pos L κ β γ A₀).trans_le hBB
  have hK := KR_nonneg hL κ β γ hB.le
  have hsσ := Real.sqrt_nonneg σ
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hcont : Continuous fun t => ‖EL σ S (W t)‖ := ((EL σ S).continuous.comp hWc).norm
  -- initial data
  have hA0 : anorm σ (W 0) ≤ A₀ := by
    have h := (asq_mono hσσ₀ (asum_of_supported (hs 0) σ₀)).2
    unfold anorm
    exact Real.sqrt_le_sqrt h
  have hm0 : mass L (EL σ S (W 0)) ≤ A₀ ^ 2 := by
    rw [mass_eq_norm_Lc]
    have h := norm_Lc_le L (EL σ S (W 0))
    rw [norm_EL (hs 0)] at h
    have h0 : 0 ≤ ‖Lc L (EL σ S (W 0))‖ := norm_nonneg _
    nlinarith [anorm_nonneg σ (W 0)]
  have hh0 : ham L κ β γ (U L κ 0 (EL σ S (W 0))) ≤ energyBudget L κ β γ A₀ := by
    rw [U_zero]
    exact initial_energy_upper hL κ β γ (by rw [norm_EL (hs 0)]; exact hA0)
  -- the rates
  have hr := fun s => lifted_rates (κ := κ) (β := β) (γ := γ) hL hσ hs hW s
  choose dm dh hdm hdh hbm hbh using hr
  intro t ht
  rw [← norm_EL (hs t)]
  refine bootstrap_le hB hcont.continuousOn (fun t ht hlow => ?_) t ht
  -- rate bounds on `[0, t)`
  have hrate : ∀ s ∈ Ico 0 t, |dm s| ≤ Real.sqrt σ * KR L κ β γ B ∧
      |dh s| ≤ Real.sqrt σ * KR L κ β γ B := by
    intro s hs'
    have hAs : anorm σ (W s) ≤ 2 * B := by rw [← norm_EL (hs s)]; exact hlow s hs'
    have hA0s : 0 ≤ anorm σ (W s) := anorm_nonneg σ (W s)
    have hQ : QR L β γ (anorm σ (W s)) ≤ QR L β γ (2 * B) := QR_mono hL β γ hA0s hAs
    have hQ0 : 0 ≤ QR L β γ (anorm σ (W s)) := QR_nonneg hL β γ hA0s
    have hLFm : LF L β γ (anorm σ (W s)) ≤ LF L β γ (2 * B) := LF_mono hL β γ hA0s hAs
    have hLF0 := LF_nonneg L β γ (anorm σ (W s))
    have hLF2 := LF_nonneg L β γ (2 * B)
    have hQ2 := QR_nonneg hL β γ (by linarith : (0 : ℝ) ≤ 2 * B)
    constructor
    · calc |dm s| ≤ 2 * anorm σ (W s) * (Real.sqrt σ * QR L β γ (anorm σ (W s))) := hbm s
        _ ≤ 2 * (2 * B) * (Real.sqrt σ * QR L β γ (2 * B)) := by gcongr
        _ ≤ Real.sqrt σ * KR L κ β γ B := by
            unfold KR
            have p1 : 0 ≤ (|κ| + 1) ^ 2 * B * (Real.sqrt σ * QR L β γ (2 * B)) := by positivity
            have p2 : 0 ≤ LF L β γ (2 * B) * B * (Real.sqrt σ * QR L β γ (2 * B)) := by
              positivity
            have e : Real.sqrt σ * ((4 * B + 4 * (|κ| + 1) ^ 2 * B + 4 * (LF L β γ (2 * B) * B)) *
                QR L β γ (2 * B)) = 2 * (2 * B) * (Real.sqrt σ * QR L β γ (2 * B)) +
                  4 * ((|κ| + 1) ^ 2 * B * (Real.sqrt σ * QR L β γ (2 * B))) +
                  4 * (LF L β γ (2 * B) * B * (Real.sqrt σ * QR L β γ (2 * B))) := by ring
            rw [e]
            linarith
    · calc |dh s| ≤ (2 * (|κ| + 1) ^ 2 * anorm σ (W s) +
              2 * (LF L β γ (anorm σ (W s)) * anorm σ (W s))) *
            (Real.sqrt σ * QR L β γ (anorm σ (W s))) := hbh s
        _ ≤ (2 * (|κ| + 1) ^ 2 * (2 * B) + 2 * (LF L β γ (2 * B) * (2 * B))) *
            (Real.sqrt σ * QR L β γ (2 * B)) := by gcongr
        _ ≤ Real.sqrt σ * KR L κ β γ B := by
            unfold KR
            have p0 : 0 ≤ B * (Real.sqrt σ * QR L β γ (2 * B)) := by positivity
            have e : Real.sqrt σ * ((4 * B + 4 * (|κ| + 1) ^ 2 * B + 4 * (LF L β γ (2 * B) * B)) *
                QR L β γ (2 * B)) = (2 * (|κ| + 1) ^ 2 * (2 * B) +
                  2 * (LF L β γ (2 * B) * (2 * B))) * (Real.sqrt σ * QR L β γ (2 * B)) +
                  4 * (B * (Real.sqrt σ * QR L β γ (2 * B))) := by ring
            rw [e]
            linarith
  -- mean value on `[0, t]`
  have hmv : ∀ (f f' : ℝ → ℝ), (∀ s, HasDerivAt f (f' s) s) →
      (∀ s ∈ Ico 0 t, |f' s| ≤ Real.sqrt σ * KR L κ β γ B) → f t - f 0 ≤ 1 := by
    intro f f' hf hf'
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (a := 0) (b := t)
      (C := Real.sqrt σ * KR L κ β γ B) (fun x _ => (hf x).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hf' x hx) t ⟨ht.1, le_rfl⟩
    rw [Real.norm_eq_abs, sub_zero] at h
    have htT : t ≤ T := ht.2
    have hC0 : 0 ≤ Real.sqrt σ * KR L κ β γ B := by positivity
    calc f t - f 0 ≤ |f t - f 0| := le_abs_self _
      _ ≤ Real.sqrt σ * KR L κ β γ B * t := h
      _ ≤ Real.sqrt σ * KR L κ β γ B * T := mul_le_mul_of_nonneg_left htT hC0
      _ = T * Real.sqrt σ * KR L κ β γ B := by ring
      _ ≤ 1 := hrad
  have hM := hmv _ _ hdm fun s hs' => (hrate s hs').1
  have hH := hmv _ _ hdh fun s hs' => (hrate s hs').2
  -- coercivity
  have hap := norm_le_apriori (κ := κ) (β := β) hL hγ (U L κ t (EL σ S (W t)))
  rw [norm_U, mass_U] at hap
  calc ‖EL σ S (W t)‖ ≤ Rap κ β γ (mass L (EL σ S (W t)))
        (ham L κ β γ (U L κ t (EL σ S (W t)))) := hap
    _ ≤ Rap κ β γ (A₀ ^ 2 + 1) (energyBudget L κ β γ A₀ + 1) :=
        Rap_mono hγ (by linarith) (by linarith)
    _ ≤ B := hBB

/-- The polynomial radius `σ_T = min(σ₀, (1 + K T)^{−2})`, with `K = K_R(B)` and `B = BR(A₀)`. -/
noncomputable def σpoly (L κ β γ σ₀ A₀ T : ℝ) : ℝ :=
  min σ₀ ((1 + T * KR L κ β γ (BR L κ β γ A₀))⁻¹ ^ 2)

theorem σpoly_spec (hL : 0 < L) (κ β γ : ℝ) {σ₀ A₀ T : ℝ} (hσ₀ : 0 ≤ σ₀) (hT : 0 ≤ T) :
    0 ≤ σpoly L κ β γ σ₀ A₀ T ∧ σpoly L κ β γ σ₀ A₀ T ≤ σ₀ ∧
      T * Real.sqrt (σpoly L κ β γ σ₀ A₀ T) * KR L κ β γ (BR L κ β γ A₀) ≤ 1 := by
  set K := KR L κ β γ (BR L κ β γ A₀) with hKdef
  have hK : 0 ≤ K := KR_nonneg hL κ β γ (BR_pos L κ β γ _).le
  have hpos : 0 < 1 + T * K := by positivity
  have hσT0 : 0 ≤ σpoly L κ β γ σ₀ A₀ T := le_min hσ₀ (by positivity)
  have hσTσ₀ : σpoly L κ β γ σ₀ A₀ T ≤ σ₀ := min_le_left _ _
  have hsq : Real.sqrt (σpoly L κ β γ σ₀ A₀ T) ≤ (1 + T * K)⁻¹ := by
    calc Real.sqrt (σpoly L κ β γ σ₀ A₀ T) ≤ Real.sqrt ((1 + T * K)⁻¹ ^ 2) :=
          Real.sqrt_le_sqrt (min_le_right _ _)
      _ = (1 + T * K)⁻¹ := Real.sqrt_sq (by positivity)
  refine ⟨hσT0, hσTσ₀, ?_⟩
  have h1 : T * Real.sqrt (σpoly L κ β γ σ₀ A₀ T) * K ≤ T * (1 + T * K)⁻¹ * K := by
    have := mul_le_mul_of_nonneg_left hsq hT
    exact mul_le_mul_of_nonneg_right this hK
  have h2 : T * (1 + T * K)⁻¹ * K ≤ 1 := by
    rw [show T * (1 + T * K)⁻¹ * K = T * K / (1 + T * K) by ring, div_le_one hpos]
    linarith
  linarith

/-- **Polynomial lower bound on the analyticity radius, uniformly in `S`.** For every horizon
`T ≥ 0`, the radius `σ_T = σpoly(…, T) = min(σ₀, (1 + K T)^{−2})` keeps
`A_{σ_T}(W(t)) ≤ BR(A_{σ₀}(W(0)))` on `[0, T]`. -/
theorem galerkin_radius_poly (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) {S : Finset Z2}
    {W : ℝ → ℓ2} (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t) {σ₀ T : ℝ} (hσ₀ : 0 ≤ σ₀)
    (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, anorm (σpoly L κ β γ σ₀ (anorm σ₀ (W 0)) T) (W t) ≤
      BR L κ β γ (anorm σ₀ (W 0)) := by
  obtain ⟨h1, h2, h3⟩ := σpoly_spec hL κ β γ (A₀ := anorm σ₀ (W 0)) hσ₀ hT
  exact galerkin_radius_bound hL hγ hs hW h1 h2 le_rfl h3

theorem potBudget_mono (hL : 0 < L) (β γ : ℝ) {A A' : ℝ} (hA : 0 ≤ A) (h : A ≤ A') :
    potBudget L β γ A ≤ potBudget L β γ A' := by
  have hc : 0 ≤ L⁻¹ * Real.sqrt (SL L) := by positivity
  unfold potBudget
  gcongr

theorem energyBudget_mono (hL : 0 < L) (κ β γ : ℝ) {A A' : ℝ} (hA : 0 ≤ A) (h : A ≤ A') :
    energyBudget L κ β γ A ≤ energyBudget L κ β γ A' := by
  have hp := potBudget_mono hL β γ hA h
  have hp0 := potBudget_nonneg L β γ A
  have hp0' := potBudget_nonneg L β γ A'
  unfold energyBudget
  gcongr

theorem BR_mono (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) {A A' : ℝ} (hA : 0 ≤ A) (h : A ≤ A') :
    BR L κ β γ A ≤ BR L κ β γ A' := by
  unfold BR
  exact Rap_mono hγ (by nlinarith) (by linarith [energyBudget_mono hL κ β γ hA h])

theorem anorm_trunc_le {σ : ℝ} (S : Finset Z2) {v : ℓ2} (hv : ASum σ v) :
    anorm σ (trunc S v) ≤ anorm σ v := by
  unfold anorm
  exact Real.sqrt_le_sqrt (asq_trunc_le S hv)

end PVNP.Analytic

/-! ### Detector bounds with the polynomial radius -/

namespace PVNP.DetectorPDE

open Complex PVNP.Torus PVNP.TorusGalerkin PVNP.GalerkinTaylor PVNP.Analytic PVNP.DualResidual
  PVNP.DetectorDynamic PVNP.ContinuumPrecision

variable {L : ℝ}

/-- **The Galerkin detector bound at the polynomial radius.** Coarse and fine Galerkin trajectories
from truncations of one analytic datum `u₀` give readouts within
`C_A A_{σ_T}(χ)(2B) e^{−2σ_T N} ((A_{σ_T}(u₀)² + G(B)²T) e^{(2K_F(B)+1)T})^{1/2}`, where
`σ_T = σpoly(…, T) = min(σ₀, (1 + K T)^{−2})` and `B = BR(A_{σ₀}(u₀))`, uniformly in the fine set. -/
theorem galerkin_detector_poly (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {σ₀ N T : ℝ} (hσ₀ : 0 ≤ σ₀) (hT : 0 ≤ T)
    (hχ : ASum σ₀ χv) {u₀ : ℓ2} (hu₀ : ASum σ₀ u₀) {S S' : Finset Z2} (hSS : S ⊆ S')
    (hS : ∀ k ∉ S, N ≤ size k) {W W' : ℝ → ℓ2}
    (hs : ∀ t, Supported S (W t)) (hs' : ∀ t, Supported S' (W' t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (hW' : ∀ t, HasDerivAt W' (galerkin S' L κ β γ t (W' t)) t)
    (h0 : W 0 = trunc S u₀) (h0' : W' 0 = trunc S' u₀) :
    |Jdet L χv (U L κ T (W' T)) - Jdet L χv (U L κ T (W T))| ≤
      CA L * anorm (σpoly L κ β γ σ₀ (anorm σ₀ u₀) T) χv * (2 * BR L κ β γ (anorm σ₀ u₀)) *
        Real.exp (-(2 * σpoly L κ β γ σ₀ (anorm σ₀ u₀) T * N)) *
        Real.sqrt ((asq (σpoly L κ β γ σ₀ (anorm σ₀ u₀) T) u₀ +
            G L β γ (BR L κ β γ (anorm σ₀ u₀)) ^ 2 * T) *
          Real.exp ((2 * KF L β γ (BR L κ β γ (anorm σ₀ u₀)) + 1) * T)) := by
  obtain ⟨hσP0, hσPle, hradP⟩ := σpoly_spec hL κ β γ (A₀ := anorm σ₀ u₀) hσ₀ hT
  have hbound : ∀ (S₁ : Finset Z2) (V : ℝ → ℓ2), (∀ t, Supported S₁ (V t)) →
      (∀ t, HasDerivAt V (galerkin S₁ L κ β γ t (V t)) t) → V 0 = trunc S₁ u₀ →
      ∀ t ∈ Set.Icc 0 T, anorm (σpoly L κ β γ σ₀ (anorm σ₀ u₀) T) (U L κ t (V t)) ≤
        BR L κ β γ (anorm σ₀ u₀) := by
    intro S₁ V hsV hV hV0 t ht
    have hBB : BR L κ β γ (anorm σ₀ (V 0)) ≤ BR L κ β γ (anorm σ₀ u₀) := by
      apply BR_mono hL hγ (anorm_nonneg _ _)
      rw [hV0]
      exact anorm_trunc_le S₁ hu₀
    rw [anorm_U]
    exact galerkin_radius_bound hL hγ hsV hV hσP0 hσPle hBB hradP t ht
  have hχP : ASum (σpoly L κ β γ σ₀ (anorm σ₀ u₀) T) χv := (asq_mono hσPle hχ).1
  have huP : ASum (σpoly L κ β γ σ₀ (anorm σ₀ u₀) T) u₀ := (asq_mono hσPle hu₀).1
  have h := galerkin_detector_dynamic_data (u := fun t => U L κ t (W t))
    (w := fun t => U L κ t (W' t)) hL hreal hσP0 hT hSS hS
    (fun t => supported_U (hs t) κ t) (fun t => supported_U (hs' t) κ t)
    (hasDerivAt_phys hL hs hW) (hasDerivAt_phys hL hs' hW') (hbound S W hs hW h0)
    (hbound S' W' hs' hW' h0') hχP huP
    (by show U L κ 0 (W 0) = trunc S u₀; rw [U_zero, h0])
    (by show U L κ 0 (W' 0) = trunc S' u₀; rw [U_zero, h0'])
  simp only at h
  exact h

/-- **The continuum detector theorem at the polynomial radius.** The detector-specific bound
holds for the actual frozen PDE solution with the radius `σ_T = σpoly(…, T)`, polynomial in `T`.
The hypotheses `M, R, B` are those of `pde_detector_dynamic`; they are used only to pass to the
continuum limit. No `H²` bound is assumed on the coarse trajectory. -/
theorem pde_detector_poly (hL : 0 < L) {κ β γ : ℝ} (hγ : 0 < γ) {χv : ℓ2}
    (hreal : rev (co L χv) = co L χv) {σ₀ M R B T N : ℝ} (hσ₀ : 0 < σ₀) (hM : 0 < M)
    (hT : 0 ≤ T) (hχ : ASum σ₀ χv) {w : ℝ → ℓ2}
    (hw : ∀ t, HasDerivAt w (Gf L κ β γ t (w t)) t) (hB : ‖w 0‖ ≤ B)
    (hRw : ∀ t, ‖w t‖ ≤ R) (hRB : uniformRadius L κ β γ B ≤ R) (hRM : 2 * R ≤ M)
    (ha : ASum σ₀ (w 0)) (h0 : asq σ₀ (w 0) ≤ M ^ 2)
    {S : Finset Z2} (hS : ∀ k ∉ S, N ≤ size k) {W : ℝ → ℓ2} (hs : ∀ t, Supported S (W t))
    (hW : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t) (hW0 : W 0 = trunc S (w 0)) :
    |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W T))| ≤
      CA L * anorm (σpoly L κ β γ σ₀ (anorm σ₀ (w 0)) T) χv *
        (2 * BR L κ β γ (anorm σ₀ (w 0))) *
        Real.exp (-(2 * σpoly L κ β γ σ₀ (anorm σ₀ (w 0)) T * N)) *
        Real.sqrt ((asq (σpoly L κ β γ σ₀ (anorm σ₀ (w 0)) T) (w 0) +
            G L β γ (BR L κ β γ (anorm σ₀ (w 0))) ^ 2 * T) *
          Real.exp ((2 * KF L β γ (BR L κ β γ (anorm σ₀ (w 0))) + 1) * T)) := by
  have hτ := tstep_pos L β γ M
  have hσT : 0 < σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊) := by positivity
  have hR : 0 ≤ R := (norm_nonneg _).trans (hRw 0)
  have hC := Cdet_nonneg hL χv
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = CA L * anorm (σpoly L κ β γ σ₀ (anorm σ₀ (w 0)) T) χv *
      (2 * BR L κ β γ (anorm σ₀ (w 0))) *
      Real.exp (-(2 * σpoly L κ β γ σ₀ (anorm σ₀ (w 0)) T * N)) *
      Real.sqrt ((asq (σpoly L κ β γ σ₀ (anorm σ₀ (w 0)) T) (w 0) +
          G L β γ (BR L κ β γ (anorm σ₀ (w 0))) ^ 2 * T) *
        Real.exp ((2 * KF L β γ (BR L κ β γ (anorm σ₀ (w 0))) + 1) * T)) := ⟨_, rfl⟩
  rw [← hΦ]
  have key : ∀ ε, 0 < ε →
      |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W T))| ≤ Φ + Cdet L χv * (R + R) * ε := by
    intro ε hε
    obtain ⟨S', hSS', hS'⟩ := exists_finer_set S (max 0
      ((LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε)) /
        (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊))))
    obtain ⟨W', hW'0, hs', hW', hRW'⟩ := exists_uniform_galerkin (κ := κ) (β := β) hL hγ S' hB
    have hRW'' : ∀ t, ‖W' t‖ ≤ R := fun t => (hRW' t).trans hRB
    have hN : LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε) ≤
        σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊) * max 0
          ((LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε)) /
            (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊))) := by
      have h := le_max_right (0 : ℝ) ((LF L β γ R * T + Real.log (Mtot L β γ M * (1 + T) / ε)) /
        (σ₀ / 4 ^ (⌊T / tstep L β γ M⌋₊)))
      rw [div_le_iff₀ hσT] at h
      linarith
    have herr := analytic_galerkin_pde_error hL hs' hW' hw hW'0 hσ₀ hM hRW'' hRw hRM ha h0 hT hε
      (le_max_left _ _) hS' hN
    have hdyn := galerkin_detector_poly (N := N) hL hγ hreal hσ₀.le hT hχ ha hSS' hS hs hs' hW
      hW' hW0 hW'0
    rw [← hΦ] at hdyn
    have hlip := weak_detector_lipschitz hL hreal (U L κ T (w T)) (U L κ T (W' T))
    have hLc : ∀ x, ‖Lc L (U L κ T x)‖ ≤ ‖x‖ := fun x => by
      rw [Lc_U, norm_U]; exact norm_Lc_le L x
    have hdiff : ‖Lc L (U L κ T (w T) - U L κ T (W' T))‖ ≤ ε := by
      rw [← map_sub, Lc_U, norm_U, map_sub, norm_sub_rev, ← map_sub]; exact herr
    have hl2 : |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W' T))| ≤
        Cdet L χv * (R + R) * ε :=
      hlip.trans (mul_le_mul (mul_le_mul_of_nonneg_left
        (add_le_add ((hLc _).trans (hRw T)) ((hLc _).trans (hRW'' T))) hC) hdiff
        (norm_nonneg _) (mul_nonneg hC (by linarith)))
    calc |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W T))|
        ≤ |Jdet L χv (U L κ T (w T)) - Jdet L χv (U L κ T (W' T))| +
          |Jdet L χv (U L κ T (W' T)) - Jdet L χv (U L κ T (W T))| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc1 : 0 < Cdet L χv * (R + R) + 1 := by
    have := mul_nonneg hC (by linarith : (0 : ℝ) ≤ R + R); linarith
  have h := key (ε / (Cdet L χv * (R + R) + 1)) (div_pos hε hc1)
  have h2 : Cdet L χv * (R + R) * (ε / (Cdet L χv * (R + R) + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hc1]
    nlinarith [mul_nonneg hC (by linarith : (0 : ℝ) ≤ R + R)]
  linarith

end PVNP.DetectorPDE
