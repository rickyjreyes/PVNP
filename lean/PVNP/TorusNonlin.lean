import PVNP.TorusH2

/-!
# The cubic–quintic nonlinearity on `H²(T_L²)`

* `mulH` (product of fields) with the **algebra estimate** `‖ψφ‖_{H²} ≤ CA L ‖ψ‖_{H²} ‖φ‖_{H²}`,
  `CA L = 4 √(SL L) / L` (`norm_mulH_le`), and the pointwise identity `field_mulH`.
* `conjH` (complex conjugation), an isometry with `field_conjH`.
* `Fnl L β γ` represents `F(ψ) = −β|ψ|²ψ + γ|ψ|⁴ψ`: `field_Fnl` identifies it *pointwise* with
  the physical nonlinearity `fnl β γ` (the same function as `MathBridge.fnl`/`WCTLattice.nlin`).
  Explicit local Lipschitz bound `norm_Fnl_sub_le` with
  `LF L β γ R = |β|·3·CA²R² + |γ|·5·CA⁴R⁴`.
* `inner_Fnl_im`: `Im ⟨ψ, F(ψ)⟩ = 0` (the identity behind mass conservation).
* The potential energy `pot L β γ v = ∫_{[0,L]²} (−β/2|ψ|⁴ + γ/3|ψ|⁶)`, its integrated Taylor
  estimate `pot_taylor` and the **coercivity** `pot_add_mass_nonneg`
  (`pot + (3β²/16γ)·mass ≥ 0`, `γ > 0`), uniform in `L`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ENNReal NNReal

namespace PVNP.Torus

variable {L : ℝ}

/-! ### Bilinearity of `pr` -/

theorem pr_add_left {a a' b : Z2 → ℂ} (ha : L1 a) (ha' : L1 a') (hb : L1 b) :
    pr L (a + a') b = pr L a b + pr L a' b := by
  funext k
  simp only [pr, Pi.add_apply, add_mul]
  rw [(summable_conv_fiber ha hb k).tsum_add (summable_conv_fiber ha' hb k), mul_add]

theorem pr_add_right {a b b' : Z2 → ℂ} (ha : L1 a) (hb : L1 b) (hb' : L1 b') :
    pr L a (b + b') = pr L a b + pr L a b' := by
  funext k
  simp only [pr, Pi.add_apply, mul_add]
  rw [(summable_conv_fiber ha hb k).tsum_add (summable_conv_fiber ha hb' k), mul_add]

theorem pr_smul_left (c : ℂ) (a b : Z2 → ℂ) : pr L (c • a) b = c • pr L a b := by
  funext k
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [tsum_mul_left]
  ring

theorem pr_smul_right (c : ℂ) (a b : Z2 → ℂ) : pr L a (c • b) = c • pr L a b := by
  funext k
  simp only [pr, Pi.smul_apply, smul_eq_mul]
  rw [show (fun j => a (k - j) * (c * b j)) = fun j => c * (a (k - j) * b j) by
    funext j; ring, tsum_mul_left]
  ring

/-! ### The product on `H²` -/

/-- The algebra constant `CA L = 4 √(SL L) / L`. -/
noncomputable def CA (L : ℝ) : ℝ := 4 * Real.sqrt (SL L) / L

theorem CA_nonneg (hL : 0 < L) : 0 ≤ CA L := by unfold CA; positivity

/-- The algebra constant is uniform for `L ≥ 1`: `CA L ≤ 6`. -/
theorem CA_le (hL : 1 ≤ L) : CA L ≤ 6 := by
  have h := sobolev_const_le hL
  unfold CA
  rw [mul_div_assoc, div_eq_inv_mul]
  linarith

/-- **The `H²` algebra estimate** (pointwise square sums). -/
theorem mulH_est (hL : 0 < L) (v w : ℓ2) :
    Summable (fun k => ‖(wt L k : ℂ) * pr L (co L v) (co L w) k‖ ^ 2) ∧
      ∑' k, ‖(wt L k : ℂ) * pr L (co L v) (co L w) k‖ ^ 2 ≤ (CA L * ‖v‖ * ‖w‖) ^ 2 := by
  obtain ⟨ha, hasum⟩ := L1_co hL v
  obtain ⟨hb, hbsum⟩ := L1_co hL w
  set a := co L v
  set b := co L w
  -- the two convolutions
  set F : Z2 → ℝ := fun k => ∑' j, ‖v (k - j)‖ * ‖b j‖ with hF
  set G : Z2 → ℝ := fun k => ∑' j, ‖w (k - j)‖ * ‖a j‖ with hG
  obtain ⟨hF2, hFb⟩ := young_real (x := fun k => ‖v k‖) (y := fun k => ‖b k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (summable_sq v) hb
  obtain ⟨hG2, hGb⟩ := young_real (x := fun k => ‖w k‖) (y := fun k => ‖a k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (summable_sq w) ha
  rw [← norm_eq_sqrt] at hFb hGb
  -- pointwise bound
  have hvb : ∀ k, Summable fun j => ‖v (k - j)‖ * ‖b j‖ := fun k =>
    (hb.mul_left ‖v‖).of_nonneg_of_le (fun _ => by positivity)
      (fun j => mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) v _) (norm_nonneg _))
  have hwa : ∀ k, Summable fun j => ‖w (k - j)‖ * ‖a j‖ := fun k =>
    (ha.mul_left ‖w‖).of_nonneg_of_le (fun _ => by positivity)
      (fun j => mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) w _) (norm_nonneg _))
  have hpt : ∀ k, ‖(wt L k : ℂ) * pr L a b k‖ ≤ 2 * L⁻¹ * (F k + G k) := by
    intro k
    have h1 := norm_pr_le (L := L) ha hb k
    rw [abs_of_pos hL] at h1
    have hGk : G k = ∑' j, ‖a (k - j)‖ * ‖w j‖ := by
      rw [hG]
      simp only
      rw [← (Equiv.subLeft k).tsum_eq]
      refine tsum_congr fun j => ?_
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
      ring
    have hab : Summable fun j => ‖a (k - j)‖ * ‖b j‖ := (summable_conv_norm ha hb).prod_factor k
    have haw : Summable fun j => ‖a (k - j)‖ * ‖w j‖ := by
      have := hwa k
      rw [← (Equiv.subLeft k).summable_iff] at this
      refine this.congr fun j => ?_
      simp only [Function.comp, Equiv.subLeft_apply, sub_sub_cancel]
      ring
    have key : wt L k * ∑' j, ‖a (k - j)‖ * ‖b j‖ ≤ 2 * (F k + G k) := by
      rw [← tsum_mul_left, hGk, hF]
      simp only
      rw [mul_add, ← tsum_mul_left, ← tsum_mul_left, ← (hvb k).mul_left 2 |>.tsum_add
        ((haw).mul_left 2)]
      refine (hab.mul_left _).tsum_le_tsum (fun j => ?_) (((hvb k).mul_left 2).add (haw.mul_left 2))
      have hw := wt_le L k j
      have e1 : ‖v (k - j)‖ = wt L (k - j) * ‖a (k - j)‖ := (wt_mul_norm_co L v (k - j)).symm
      have e2 : ‖w j‖ = wt L j * ‖b j‖ := (wt_mul_norm_co L w j).symm
      rw [e1, e2]
      have h0 : 0 ≤ ‖a (k - j)‖ * ‖b j‖ := by positivity
      nlinarith
    calc ‖(wt L k : ℂ) * pr L a b k‖ = wt L k * ‖pr L a b k‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos L k)]
      _ ≤ wt L k * (L⁻¹ * ∑' j, ‖a (k - j)‖ * ‖b j‖) :=
          mul_le_mul_of_nonneg_left h1 (wt_pos L k).le
      _ = L⁻¹ * (wt L k * ∑' j, ‖a (k - j)‖ * ‖b j‖) := by ring
      _ ≤ L⁻¹ * (2 * (F k + G k)) := mul_le_mul_of_nonneg_left key (inv_nonneg.2 hL.le)
      _ = 2 * L⁻¹ * (F k + G k) := by ring
  -- square sums
  have hF0 : ∀ k, 0 ≤ F k := fun k => tsum_nonneg fun _ => by positivity
  have hG0 : ∀ k, 0 ≤ G k := fun k => tsum_nonneg fun _ => by positivity
  have hsq : Summable fun k => (2 * L⁻¹ * (F k + G k)) ^ 2 := by
    have : Summable fun k => 8 * L⁻¹ ^ 2 * (F k ^ 2 + G k ^ 2) := (hF2.add hG2).mul_left _
    refine this.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_)
    nlinarith [sq_nonneg (F k - G k), sq_nonneg L⁻¹]
  obtain ⟨hs, hle⟩ := tsum_sq_le_of_le hsq hpt
  refine ⟨hs, hle.trans ?_⟩
  set X := Real.sqrt (SL L) * ‖v‖ * ‖w‖ with hX
  have hFX : ∑' k, F k ^ 2 ≤ X ^ 2 := by
    have h1 : Real.sqrt (∑' k, F k ^ 2) ≤ X := by
      calc Real.sqrt (∑' k, F k ^ 2) ≤ ‖v‖ * ∑' j, ‖b j‖ := hFb
        _ ≤ ‖v‖ * (Real.sqrt (SL L) * ‖w‖) := mul_le_mul_of_nonneg_left hbsum (norm_nonneg _)
        _ = X := by rw [hX]; ring
    have h0 : 0 ≤ ∑' k, F k ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    calc ∑' k, F k ^ 2 = Real.sqrt (∑' k, F k ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ X ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hGX : ∑' k, G k ^ 2 ≤ X ^ 2 := by
    have h1 : Real.sqrt (∑' k, G k ^ 2) ≤ X := by
      calc Real.sqrt (∑' k, G k ^ 2) ≤ ‖w‖ * ∑' j, ‖a j‖ := hGb
        _ ≤ ‖w‖ * (Real.sqrt (SL L) * ‖v‖) := mul_le_mul_of_nonneg_left hasum (norm_nonneg _)
        _ = X := by rw [hX]; ring
    have h0 : 0 ≤ ∑' k, G k ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    calc ∑' k, G k ^ 2 = Real.sqrt (∑' k, G k ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ X ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  calc ∑' k, (2 * L⁻¹ * (F k + G k)) ^ 2 ≤ ∑' k, 8 * L⁻¹ ^ 2 * (F k ^ 2 + G k ^ 2) :=
        hsq.tsum_le_tsum (fun k => by nlinarith [sq_nonneg (F k - G k), sq_nonneg L⁻¹])
          ((hF2.add hG2).mul_left _)
    _ = 8 * L⁻¹ ^ 2 * (∑' k, F k ^ 2 + ∑' k, G k ^ 2) := by
        rw [tsum_mul_left, hF2.tsum_add hG2]
    _ ≤ 8 * L⁻¹ ^ 2 * (X ^ 2 + X ^ 2) := by gcongr
    _ = (CA L * ‖v‖ * ‖w‖) ^ 2 := by
        rw [hX, CA]
        have hS : Real.sqrt (SL L) ^ 2 = SL L := Real.sq_sqrt (SL_nonneg L)
        field_simp
        ring_nf

/-- The `H²` state of the product of two fields. -/
noncomputable def mulH (L : ℝ) (v w : ℓ2) : ℓ2 :=
  if hL : 0 < L then mk (fun k => (wt L k : ℂ) * pr L (co L v) (co L w) k) (mulH_est hL v w).1
  else 0

theorem mulH_apply (hL : 0 < L) (v w : ℓ2) (k : Z2) :
    mulH L v w k = (wt L k : ℂ) * pr L (co L v) (co L w) k := by
  rw [mulH, dif_pos hL]; rfl

theorem co_mulH (hL : 0 < L) (v w : ℓ2) : co L (mulH L v w) = pr L (co L v) (co L w) := by
  funext k
  rw [co, mulH_apply hL, mul_div_cancel_left₀ _ (wt_ne_zero L k)]

/-- **`‖ψφ‖_{H²} ≤ CA L ‖ψ‖_{H²} ‖φ‖_{H²}`.** -/
theorem norm_mulH_le (hL : 0 < L) (v w : ℓ2) : ‖mulH L v w‖ ≤ CA L * ‖v‖ * ‖w‖ := by
  refine norm_le_of_tsum_sq_le _ (by have := CA_nonneg hL; positivity) ?_
  simpa only [mulH_apply hL] using (mulH_est hL v w).2

/-- The product of `H²` functions is the pointwise product of fields. -/
theorem field_mulH (hL : 0 < L) (v w : ℓ2) (x : ℝ × ℝ) :
    field L (co L (mulH L v w)) x = field L (co L v) x * field L (co L w) x := by
  rw [co_mulH hL, field_mul (L1_co hL v).1 (L1_co hL w).1]

theorem mulH_add_left (hL : 0 < L) (v v' w : ℓ2) :
    mulH L (v + v') w = mulH L v w + mulH L v' w := by
  ext k
  simp only [mulH_apply hL, lp.coeFn_add, Pi.add_apply]
  rw [co_add, pr_add_left (L1_co hL v).1 (L1_co hL v').1 (L1_co hL w).1, Pi.add_apply, mul_add]

theorem mulH_add_right (hL : 0 < L) (v w w' : ℓ2) :
    mulH L v (w + w') = mulH L v w + mulH L v w' := by
  ext k
  simp only [mulH_apply hL, lp.coeFn_add, Pi.add_apply]
  rw [co_add, pr_add_right (L1_co hL v).1 (L1_co hL w).1 (L1_co hL w').1, Pi.add_apply, mul_add]

theorem mulH_smul_left (hL : 0 < L) (c : ℂ) (v w : ℓ2) :
    mulH L (c • v) w = c • mulH L v w := by
  ext k
  simp only [mulH_apply hL, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [co_smul, pr_smul_left, Pi.smul_apply, smul_eq_mul]
  ring

theorem mulH_smul_right (hL : 0 < L) (c : ℂ) (v w : ℓ2) :
    mulH L v (c • w) = c • mulH L v w := by
  ext k
  simp only [mulH_apply hL, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [co_smul, pr_smul_right, Pi.smul_apply, smul_eq_mul]
  ring

theorem mulH_neg_left (hL : 0 < L) (v w : ℓ2) : mulH L (-v) w = -mulH L v w := by
  have h := mulH_smul_left hL (-1) v w
  simpa using h

theorem mulH_neg_right (hL : 0 < L) (v w : ℓ2) : mulH L v (-w) = -mulH L v w := by
  have h := mulH_smul_right hL (-1) v w
  simpa using h

theorem mulH_sub_left (hL : 0 < L) (v v' w : ℓ2) :
    mulH L (v - v') w = mulH L v w - mulH L v' w := by
  rw [sub_eq_add_neg, mulH_add_left hL, mulH_neg_left hL, ← sub_eq_add_neg]

theorem mulH_sub_right (hL : 0 < L) (v w w' : ℓ2) :
    mulH L v (w - w') = mulH L v w - mulH L v w' := by
  rw [sub_eq_add_neg, mulH_add_right hL, mulH_neg_right hL, ← sub_eq_add_neg]

theorem mulH_zero_left (hL : 0 < L) (w : ℓ2) : mulH L 0 w = 0 := by
  have h := mulH_smul_left hL 0 0 w
  simpa using h

/-- `‖ab − a'b'‖ ≤ CA (‖a − a'‖‖b‖ + ‖a'‖‖b − b'‖)`. -/
theorem norm_mulH_sub_le (hL : 0 < L) (a b a' b' : ℓ2) :
    ‖mulH L a b - mulH L a' b'‖ ≤ CA L * (‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖) := by
  have e : mulH L a b - mulH L a' b' = mulH L (a - a') b + mulH L a' (b - b') := by
    rw [mulH_sub_left hL, mulH_sub_right hL]; abel
  rw [e]
  calc ‖mulH L (a - a') b + mulH L a' (b - b')‖ ≤ ‖mulH L (a - a') b‖ + ‖mulH L a' (b - b')‖ :=
        norm_add_le _ _
    _ ≤ CA L * ‖a - a'‖ * ‖b‖ + CA L * ‖a'‖ * ‖b - b'‖ :=
        add_le_add (norm_mulH_le hL _ _) (norm_mulH_le hL _ _)
    _ = CA L * (‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖) := by ring

/-! ### Complex conjugation -/

theorem summable_sq_neg (v : ℓ2) : Summable fun k => ‖(starRingEnd ℂ) (v (-k))‖ ^ 2 := by
  have h := ((Equiv.neg Z2).summable_iff (f := fun k => ‖v k‖ ^ 2)).2 (summable_sq v)
  simpa only [Complex.norm_conj] using h

/-- Complex conjugation of the represented field. -/
noncomputable def conjH (v : ℓ2) : ℓ2 := mk (fun k => (starRingEnd ℂ) (v (-k))) (summable_sq_neg v)

theorem conjH_apply (v : ℓ2) (k : Z2) : conjH v k = (starRingEnd ℂ) (v (-k)) := rfl

theorem norm_conjH (v : ℓ2) : ‖conjH v‖ = ‖v‖ := by
  have h : ∑' k, ‖conjH v k‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 := by
    simp only [conjH_apply, Complex.norm_conj]
    exact (Equiv.neg Z2).tsum_eq (fun k => ‖v k‖ ^ 2)
  rw [norm_eq_sqrt, norm_eq_sqrt, h]

theorem conjH_sub (v w : ℓ2) : conjH (v - w) = conjH v - conjH w := by
  ext k
  simp only [conjH_apply, lp.coeFn_sub, Pi.sub_apply, map_sub]

theorem conjH_zero : conjH 0 = 0 := by
  ext k; simp [conjH_apply]

theorem co_conjH (L : ℝ) (v : ℓ2) : co L (conjH v) = rev (co L v) := by
  funext k
  simp only [co, conjH_apply, rev, map_div₀, Complex.conj_ofReal, wt_neg]

theorem field_conjH (v : ℓ2) (x : ℝ × ℝ) :
    field L (co L (conjH v)) x = (starRingEnd ℂ) (field L (co L v) x) := by
  rw [co_conjH, field_rev]

theorem norm_conjH_sub (v w : ℓ2) : ‖conjH v - conjH w‖ = ‖v - w‖ := by
  rw [← conjH_sub, norm_conjH]

/-! ### The nonlinearity -/

/-- The cubic–quintic nonlinearity `f(z) = −β|z|²z + γ|z|⁴z`, written with `z z z̄`. -/
noncomputable def fnl (β γ : ℝ) (z : ℂ) : ℂ :=
  (-(β : ℂ)) * (z * z * (starRingEnd ℂ) z) +
    (γ : ℂ) * (z * z * z * (starRingEnd ℂ) z * (starRingEnd ℂ) z)

theorem fnl_eq (β γ : ℝ) (z : ℂ) :
    fnl β γ z = ((-β * ‖z‖ ^ 2 + γ * ‖z‖ ^ 4 : ℝ) : ℂ) * z := by
  have h : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  unfold fnl
  have e1 : z * z * (starRingEnd ℂ) z = (z * (starRingEnd ℂ) z) * z := by ring
  have e2 : z * z * z * (starRingEnd ℂ) z * (starRingEnd ℂ) z =
      (z * (starRingEnd ℂ) z) * (z * (starRingEnd ℂ) z) * z := by ring
  rw [e1, e2, h]
  push_cast
  ring

/-- **The nonlinearity `F(ψ) = −β|ψ|²ψ + γ|ψ|⁴ψ` on `H²(T_L²)`.** -/
noncomputable def Fnl (L β γ : ℝ) (u : ℓ2) : ℓ2 :=
  (-(β : ℂ)) • mulH L (mulH L u u) (conjH u) +
    (γ : ℂ) • mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u)

theorem L1_co' (hL : 0 < L) (v : ℓ2) : L1 (co L v) := (L1_co hL v).1

/-- **The nonlinearity is the physical one, pointwise**:
`field (F(ψ)) = −β|ψ|²ψ + γ|ψ|⁴ψ` at every point of the torus. -/
theorem field_Fnl (hL : 0 < L) (β γ : ℝ) (u : ℓ2) (x : ℝ × ℝ) :
    field L (co L (Fnl L β γ u)) x = fnl β γ (field L (co L u) x) := by
  unfold Fnl fnl
  rw [co_add, co_smul, co_smul,
    field_add (L1_smul _ (L1_co' hL _)) (L1_smul _ (L1_co' hL _)), field_smul, field_smul]
  simp only [field_mulH hL, field_conjH]

/-- Fourier coefficients of the physical nonlinearity of the field. -/
theorem fc_fnl (hL : 0 < L) (β γ : ℝ) (u : ℓ2) (k : Z2) :
    fc L (fun x => fnl β γ (field L (co L u) x)) k = co L (Fnl L β γ u) k := by
  have e : (fun x => fnl β γ (field L (co L u) x)) = field L (co L (Fnl L β γ u)) := by
    funext x; rw [field_Fnl hL]
  rw [e, fc_field hL (L1_co' hL _)]

/-! ### Lipschitz bounds -/

/-- The local Lipschitz constant of `F` on the `H²` ball of radius `R`. -/
noncomputable def LF (L β γ R : ℝ) : ℝ :=
  |β| * (3 * CA L ^ 2 * R ^ 2) + |γ| * (5 * CA L ^ 4 * R ^ 4)

theorem LF_nonneg (L β γ R : ℝ) : 0 ≤ LF L β γ R := by unfold LF; positivity

theorem LF_mono (hL : 0 < L) (β γ : ℝ) {R R' : ℝ} (hR : 0 ≤ R) (h : R ≤ R') :
    LF L β γ R ≤ LF L β γ R' := by
  have hc := CA_nonneg hL
  unfold LF
  gcongr

/-- One multiplication step of a Lipschitz estimate. -/
theorem lip_mul (hL : 0 < L) {X Y X' Y' : ℓ2} {d a A b B : ℝ} (hd : 0 ≤ d) (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hX : ‖X - X'‖ ≤ a * d) (hXb : ‖X'‖ ≤ A) (hY : ‖Y - Y'‖ ≤ b * d) (hYb : ‖Y‖ ≤ B) :
    ‖mulH L X Y - mulH L X' Y'‖ ≤ CA L * (a * B + A * b) * d := by
  have hc := CA_nonneg hL
  calc ‖mulH L X Y - mulH L X' Y'‖ ≤ CA L * (‖X - X'‖ * ‖Y‖ + ‖X'‖ * ‖Y - Y'‖) :=
        norm_mulH_sub_le hL _ _ _ _
    _ ≤ CA L * (a * d * B + A * (b * d)) := by
        gcongr
    _ = CA L * (a * B + A * b) * d := by ring

theorem norm_mulH_le' (hL : 0 < L) {X Y : ℓ2} {A B : ℝ} (hX : ‖X‖ ≤ A) (hY : ‖Y‖ ≤ B) :
    ‖mulH L X Y‖ ≤ CA L * A * B := by
  have hc := CA_nonneg hL
  calc ‖mulH L X Y‖ ≤ CA L * ‖X‖ * ‖Y‖ := norm_mulH_le hL _ _
    _ ≤ CA L * A * B := by
        have hA : 0 ≤ A := (norm_nonneg _).trans hX
        gcongr

/-- **Local Lipschitz bound** `‖F(u) − F(v)‖ ≤ LF R ‖u − v‖` on the ball of radius `R`. -/
theorem norm_Fnl_sub_le (hL : 0 < L) (β γ : ℝ) {u v : ℓ2} {R : ℝ} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖Fnl L β γ u - Fnl L β γ v‖ ≤ LF L β γ R * ‖u - v‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hu
  have hc := CA_nonneg hL
  set d := ‖u - v‖
  set C := CA L
  have hcu : ‖conjH u‖ ≤ R := by rw [norm_conjH]; exact hu
  have hcv : ‖conjH v‖ ≤ R := by rw [norm_conjH]; exact hv
  have hcd : ‖conjH u - conjH v‖ ≤ 1 * d := by rw [norm_conjH_sub, one_mul]
  have hd : ‖u - v‖ ≤ 1 * d := by rw [one_mul]
  -- P2 = u u
  have p2 : ‖mulH L u u - mulH L v v‖ ≤ C * (1 * R + R * 1) * d := lip_mul hL (norm_nonneg _) zero_le_one hR hd hv hd hu
  have b2u : ‖mulH L u u‖ ≤ C * R * R := norm_mulH_le' hL hu hu
  have b2v : ‖mulH L v v‖ ≤ C * R * R := norm_mulH_le' hL hv hv
  -- cubic
  have p3 : ‖mulH L (mulH L u u) (conjH u) - mulH L (mulH L v v) (conjH v)‖ ≤
      C * (C * (1 * R + R * 1) * R + C * R * R * 1) * d :=
    lip_mul hL (norm_nonneg _) (by positivity) (by positivity) p2 b2v hcd hcu
  -- quintic chain
  have q3 : ‖mulH L (mulH L u u) u - mulH L (mulH L v v) v‖ ≤
      C * (C * (1 * R + R * 1) * R + C * R * R * 1) * d :=
    lip_mul hL (norm_nonneg _) (by positivity) (by positivity) p2 b2v hd hu
  have b3u : ‖mulH L (mulH L u u) u‖ ≤ C * (C * R * R) * R := norm_mulH_le' hL b2u hu
  have b3v : ‖mulH L (mulH L v v) v‖ ≤ C * (C * R * R) * R := norm_mulH_le' hL b2v hv
  have q4 : ‖mulH L (mulH L (mulH L u u) u) (conjH u) -
      mulH L (mulH L (mulH L v v) v) (conjH v)‖ ≤
      C * (C * (C * (1 * R + R * 1) * R + C * R * R * 1) * R + C * (C * R * R) * R * 1) * d :=
    lip_mul hL (norm_nonneg _) (by positivity) (by positivity) q3 b3v hcd hcu
  have b4v : ‖mulH L (mulH L (mulH L v v) v) (conjH v)‖ ≤ C * (C * (C * R * R) * R) * R :=
    norm_mulH_le' hL b3v hcv
  have b4u : ‖mulH L (mulH L (mulH L u u) u) (conjH u)‖ ≤ C * (C * (C * R * R) * R) * R :=
    norm_mulH_le' hL b3u hcu
  have q5 : ‖mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u) -
      mulH L (mulH L (mulH L (mulH L v v) v) (conjH v)) (conjH v)‖ ≤
      C * (C * (C * (C * (1 * R + R * 1) * R + C * R * R * 1) * R + C * (C * R * R) * R * 1) * R +
        C * (C * (C * R * R) * R) * R * 1) * d :=
    lip_mul hL (norm_nonneg _) (by positivity) (by positivity) q4 b4v hcd hcu
  have e : Fnl L β γ u - Fnl L β γ v =
      (-(β : ℂ)) • (mulH L (mulH L u u) (conjH u) - mulH L (mulH L v v) (conjH v)) +
      (γ : ℂ) • (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u) -
        mulH L (mulH L (mulH L (mulH L v v) v) (conjH v)) (conjH v)) := by
    unfold Fnl; rw [smul_sub, smul_sub]; abel
  rw [e]
  have hd0 : 0 ≤ d := norm_nonneg _
  calc _ ≤ ‖(-(β : ℂ)) • (mulH L (mulH L u u) (conjH u) - mulH L (mulH L v v) (conjH v))‖ +
        ‖(γ : ℂ) • (mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u) -
          mulH L (mulH L (mulH L (mulH L v v) v) (conjH v)) (conjH v))‖ := norm_add_le _ _
    _ = |β| * ‖mulH L (mulH L u u) (conjH u) - mulH L (mulH L v v) (conjH v)‖ +
        |γ| * ‖mulH L (mulH L (mulH L (mulH L u u) u) (conjH u)) (conjH u) -
          mulH L (mulH L (mulH L (mulH L v v) v) (conjH v)) (conjH v)‖ := by
        rw [norm_smul, norm_smul, norm_neg, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |β| * (C * (C * (1 * R + R * 1) * R + C * R * R * 1) * d) +
        |γ| * (C * (C * (C * (C * (1 * R + R * 1) * R + C * R * R * 1) * R +
          C * (C * R * R) * R * 1) * R + C * (C * (C * R * R) * R) * R * 1) * d) := by
        gcongr
    _ = LF L β γ R * d := by unfold LF; ring

theorem Fnl_zero (hL : 0 < L) (β γ : ℝ) : Fnl L β γ 0 = 0 := by
  unfold Fnl
  simp [mulH_zero_left hL, conjH_zero]

theorem norm_Fnl_le (hL : 0 < L) (β γ : ℝ) (u : ℓ2) :
    ‖Fnl L β γ u‖ ≤ LF L β γ ‖u‖ * ‖u‖ := by
  have h := norm_Fnl_sub_le hL β γ (le_refl ‖u‖) (by rw [norm_zero]; exact norm_nonneg u)
    (u := u) (v := 0)
  rwa [Fnl_zero hL, sub_zero, sub_zero] at h

theorem continuous_Fnl (hL : 0 < L) (β γ : ℝ) : Continuous (Fnl L β γ) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hev : ∀ᶠ v in 𝓝 u, ‖v‖ ≤ ‖u‖ + 1 :=
    (continuous_norm.tendsto u).eventually (ge_mem_nhds (lt_add_one _))
  have hlim : Tendsto (fun v => LF L β γ (‖u‖ + 1) * ‖v - u‖) (𝓝 u) (𝓝 0) := by
    have := ((continuous_id.sub (continuous_const : Continuous fun _ : ℓ2 => u)).norm.tendsto
      u).const_mul (LF L β γ (‖u‖ + 1))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hev] with v hv
  exact norm_Fnl_sub_le hL β γ hv (by linarith)

/-! ### Realness of `⟨ψ, F(ψ)⟩` -/

theorem conj_mul_fnl (β γ : ℝ) (z : ℂ) :
    (starRingEnd ℂ) z * fnl β γ z = ((-β * ‖z‖ ^ 4 + γ * ‖z‖ ^ 6 : ℝ) : ℂ) := by
  rw [fnl_eq, mul_comm, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **`Im ⟨ψ, F(ψ)⟩ = 0`.** -/
theorem inner_Fnl_im (hL : 0 < L) (β γ : ℝ) (u : ℓ2) :
    (∑' k, (starRingEnd ℂ) (co L u k) * co L (Fnl L β γ u) k).im = 0 := by
  rw [← integral_conj_mul hL (L1_co' hL u) (L1_co' hL _)]
  simp_rw [field_Fnl hL, conj_mul_fnl]
  rw [integral_complex_ofReal, Complex.ofReal_im]

/-! ### The potential energy -/

/-- The potential density `n(z) = −(β/2)|z|⁴ + (γ/3)|z|⁶`. -/
noncomputable def nfun (β γ : ℝ) (z : ℂ) : ℝ := -β / 2 * ‖z‖ ^ 4 + γ / 3 * ‖z‖ ^ 6

/-- `2 Re (z̄ δ) = |z + δ|² − |z|² − |δ|²`. -/
theorem two_re_conj_mul (z δ : ℂ) :
    2 * ((starRingEnd ℂ) z * δ).re = ‖z + δ‖ ^ 2 - ‖z‖ ^ 2 - ‖δ‖ ^ 2 := by
  have h := @norm_add_sq ℂ ℂ _ _ _ z δ
  simp only [RCLike.inner_apply, RCLike.re_to_complex] at h
  rw [h, mul_comm ((starRingEnd ℂ) z) δ]
  ring

/-- **Pointwise Taylor estimate** (ported verbatim from `rickyjreyes/math@30a5ddc`,
`ReyesMath.Sobolev.nfun_taylor`; a statement about complex numbers only). -/
theorem nfun_taylor (β γ : ℝ) {z w : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    |nfun β γ w - nfun β γ z - 2 * ((starRingEnd ℂ) (fnl β γ z) * (w - z)).re| ≤
      (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * ‖w - z‖ ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  set s := ‖z‖ ^ 2 with hs
  set t := ‖w‖ ^ 2 with ht
  set b := ‖w - z‖ ^ 2 with hb
  have hs0 : 0 ≤ s := sq_nonneg _
  have ht0 : 0 ≤ t := sq_nonneg _
  have hb0 : 0 ≤ b := sq_nonneg _
  have hsR : s ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have htR : t ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hlin : 2 * ((starRingEnd ℂ) (fnl β γ z) * (w - z)).re =
      (-β * s + γ * s ^ 2) * (t - s - b) := by
    rw [fnl_eq, map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    have h := two_re_conj_mul z (w - z)
    rw [add_sub_cancel, ← hs, ← ht, ← hb] at h
    rw [show ‖z‖ ^ 4 = s ^ 2 by rw [hs]; ring, ← hs]
    rw [show 2 * ((-β * s + γ * s ^ 2) * ((starRingEnd ℂ) z * (w - z)).re) =
      (-β * s + γ * s ^ 2) * (2 * ((starRingEnd ℂ) z * (w - z)).re) by ring, h]
  have hts : (t - s) ^ 2 ≤ 4 * R ^ 2 * b := by
    have h1 : |‖w‖ - ‖z‖| ≤ ‖w - z‖ := abs_norm_sub_norm_le w z
    have h2 : t - s = (‖w‖ - ‖z‖) * (‖w‖ + ‖z‖) := by rw [ht, hs]; ring
    have h3 : (‖w‖ + ‖z‖) ^ 2 ≤ (2 * R) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [h2, mul_pow]
    have h4 : (‖w‖ - ‖z‖) ^ 2 ≤ b := by
      rw [hb, ← sq_abs (‖w‖ - ‖z‖)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (‖w‖ - ‖z‖), sq_nonneg (‖w‖ + ‖z‖)]
  have hn : nfun β γ w - nfun β γ z - 2 * ((starRingEnd ℂ) (fnl β γ z) * (w - z)).re =
      -β / 2 * ((t - s) ^ 2 + 2 * s * b) + γ / 3 * ((t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b) := by
    rw [hlin, nfun, nfun, show ‖w‖ ^ 4 = t ^ 2 by rw [ht]; ring,
      show ‖w‖ ^ 6 = t ^ 3 by rw [ht]; ring, show ‖z‖ ^ 4 = s ^ 2 by rw [hs]; ring,
      show ‖z‖ ^ 6 = s ^ 3 by rw [hs]; ring]
    ring
  rw [hn]
  have q1 : 0 ≤ (t - s) ^ 2 + 2 * s * b := by positivity
  have q2 : (t - s) ^ 2 + 2 * s * b ≤ 6 * R ^ 2 * b := by nlinarith
  have q3 : 0 ≤ (t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b := by positivity
  have q4 : (t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b ≤ 15 * R ^ 4 * b := by
    have h5 : t + 2 * s ≤ 3 * R ^ 2 := by linarith
    have h6 : (t - s) ^ 2 * (t + 2 * s) ≤ 4 * R ^ 2 * b * (3 * R ^ 2) :=
      mul_le_mul hts h5 (by positivity) (by positivity)
    have h7 : s ^ 2 ≤ R ^ 4 := by
      calc s ^ 2 ≤ (R ^ 2) ^ 2 := pow_le_pow_left₀ hs0 hsR 2
        _ = R ^ 4 := by ring
    nlinarith
  calc |-β / 2 * ((t - s) ^ 2 + 2 * s * b) + γ / 3 * ((t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b)|
      ≤ |-β / 2 * ((t - s) ^ 2 + 2 * s * b)| +
          |γ / 3 * ((t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b)| := abs_add_le _ _
    _ = |β| / 2 * ((t - s) ^ 2 + 2 * s * b) +
          |γ| / 3 * ((t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b) := by
        rw [abs_mul, abs_mul, abs_of_nonneg q1, abs_of_nonneg q3, abs_div, abs_div, abs_neg,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ ≤ |β| / 2 * (6 * R ^ 2 * b) + |γ| / 3 * (15 * R ^ 4 * b) := by gcongr
    _ = (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * b := by ring

/-- The potential energy `∫_{[0,L]²} (−β/2|ψ|⁴ + γ/3|ψ|⁶)`. -/
noncomputable def pot (L β γ : ℝ) (v : ℓ2) : ℝ := ∫ x, nfun β γ (field L (co L v) x) ∂box L

/-- The mass `‖ψ‖²_{L²} = Σ_k |ψ̂_k|²`. -/
noncomputable def mass (L : ℝ) (v : ℓ2) : ℝ := ∑' k, ‖co L v k‖ ^ 2

theorem mass_eq_integral (hL : 0 < L) (v : ℓ2) :
    mass L v = ∫ x, ‖field L (co L v) x‖ ^ 2 ∂box L :=
  (integral_norm_sq hL (L1_co' hL v)).symm

theorem mass_eq_norm_Lc (L : ℝ) (v : ℓ2) : mass L v = ‖Lc L v‖ ^ 2 := (norm_sq_Lc L v).symm

theorem continuous_nfun (β γ : ℝ) : Continuous (nfun β γ) := by
  unfold nfun; fun_prop

theorem integrable_of_continuous_bounded {f : ℝ × ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f (box L) :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem integrable_nfun (hL : 0 < L) (β γ : ℝ) (v : ℓ2) :
    Integrable (fun x => nfun β γ (field L (co L v) x)) (box L) := by
  set S := L⁻¹ * Real.sqrt (SL L) * ‖v‖
  refine integrable_of_continuous_bounded ((continuous_nfun β γ).comp
    (continuous_field (L1_co' hL v))) (C := |β| / 2 * S ^ 4 + |γ| / 3 * S ^ 6) (fun x => ?_)
  have h := norm_field_co_le hL v x
  have h0 : 0 ≤ ‖field L (co L v) x‖ := norm_nonneg _
  unfold nfun
  calc |-β / 2 * ‖field L (co L v) x‖ ^ 4 + γ / 3 * ‖field L (co L v) x‖ ^ 6|
      ≤ |-β / 2 * ‖field L (co L v) x‖ ^ 4| + |γ / 3 * ‖field L (co L v) x‖ ^ 6| := abs_add_le _ _
    _ = |β| / 2 * ‖field L (co L v) x‖ ^ 4 + |γ| / 3 * ‖field L (co L v) x‖ ^ 6 := by
        rw [abs_mul, abs_mul, abs_div, abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖field L (co L v) x‖ ^ 4),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖field L (co L v) x‖ ^ 6)]
        norm_num
    _ ≤ |β| / 2 * S ^ 4 + |γ| / 3 * S ^ 6 := by gcongr

theorem integrable_of_cont_bdd {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f (box L) :=
  (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hC)

theorem norm_fnl_le (β γ : ℝ) {z : ℂ} {S : ℝ} (hz : ‖z‖ ≤ S) :
    ‖fnl β γ z‖ ≤ |β| * S ^ 3 + |γ| * S ^ 5 := by
  rw [fnl_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h0 := norm_nonneg z
  calc |-β * ‖z‖ ^ 2 + γ * ‖z‖ ^ 4| * ‖z‖ ≤ (|β| * ‖z‖ ^ 2 + |γ| * ‖z‖ ^ 4) * ‖z‖ := by
        gcongr
        calc |-β * ‖z‖ ^ 2 + γ * ‖z‖ ^ 4| ≤ |-β * ‖z‖ ^ 2| + |γ * ‖z‖ ^ 4| := abs_add_le _ _
          _ = |β| * ‖z‖ ^ 2 + |γ| * ‖z‖ ^ 4 := by
              rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2),
                abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 4)]
    _ ≤ (|β| * S ^ 2 + |γ| * S ^ 4) * S := by gcongr
    _ = |β| * S ^ 3 + |γ| * S ^ 5 := by ring

theorem continuous_fnl (β γ : ℝ) : Continuous (fnl β γ) := by
  have hc : Continuous fun z : ℂ => (starRingEnd ℂ) z := Complex.continuous_conj
  unfold fnl
  fun_prop

/-- **Integrated Taylor estimate for the potential energy.** -/
theorem pot_taylor (hL : 0 < L) (β γ : ℝ) {e f : ℓ2} {R : ℝ} (he : ‖e‖ ≤ R) (hf : ‖f‖ ≤ R) :
    |pot L β γ f - pot L β γ e -
        2 * (∑' k, (starRingEnd ℂ) (co L (Fnl L β γ e) k) * (co L f k - co L e k)).re| ≤
      (3 * |β| * (L⁻¹ * Real.sqrt (SL L) * R) ^ 2 + 5 * |γ| * (L⁻¹ * Real.sqrt (SL L) * R) ^ 4) *
        ∑' k, ‖co L f k - co L e k‖ ^ 2 := by
  set S := L⁻¹ * Real.sqrt (SL L) * R
  set C := 3 * |β| * S ^ 2 + 5 * |γ| * S ^ 4
  have hcf : Continuous (field L (co L f)) := continuous_field (L1_co' hL f)
  have hce : Continuous (field L (co L e)) := continuous_field (L1_co' hL e)
  have hd : L1 (co L f - co L e) := by rw [← co_sub]; exact L1_co' hL _
  have hfd : ∀ x, field L (co L f - co L e) x = field L (co L f) x - field L (co L e) x :=
    fun x => field_sub (L1_co' hL f) (L1_co' hL e) x
  have hlin : (∑' k, (starRingEnd ℂ) (co L (Fnl L β γ e) k) * (co L f k - co L e k)) =
      ∫ x, (starRingEnd ℂ) (fnl β γ (field L (co L e) x)) *
        (field L (co L f) x - field L (co L e) x) ∂box L := by
    have h := integral_conj_mul hL (L1_co' hL (Fnl L β γ e)) hd
    simp only [Pi.sub_apply] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [field_Fnl hL, hfd]
  have hsq : ∑' k, ‖co L f k - co L e k‖ ^ 2 =
      ∫ x, ‖field L (co L f) x - field L (co L e) x‖ ^ 2 ∂box L := by
    have h := integral_norm_sq hL hd
    simp only [Pi.sub_apply] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hfd]
  have hbf : ∀ x, ‖field L (co L f) x‖ ≤ S := fun x =>
    (norm_field_co_le hL f x).trans (mul_le_mul_of_nonneg_left hf
      (mul_nonneg (inv_nonneg.2 hL.le) (Real.sqrt_nonneg (SL L))))
  have hbe : ∀ x, ‖field L (co L e) x‖ ≤ S := fun x =>
    (norm_field_co_le hL e x).trans (mul_le_mul_of_nonneg_left he
      (mul_nonneg (inv_nonneg.2 hL.le) (Real.sqrt_nonneg (SL L))))
  have hdiff : ∀ x, ‖field L (co L f) x - field L (co L e) x‖ ≤ 2 * S := fun x =>
    (norm_sub_le _ _).trans (by linarith [hbf x, hbe x])
  have hint1 := integrable_nfun hL β γ e
  have hint2 := integrable_nfun hL β γ f
  have hcN : Continuous fun x => fnl β γ (field L (co L e) x) := (continuous_fnl β γ).comp hce
  have hI : Integrable (fun x => (starRingEnd ℂ) (fnl β γ (field L (co L e) x)) *
      (field L (co L f) x - field L (co L e) x)) (box L) :=
    integrable_of_cont_bdd ((Complex.continuous_conj.comp hcN).mul (hcf.sub hce))
      (C := (|β| * S ^ 3 + |γ| * S ^ 5) * (2 * S))
      (fun x => by
        rw [norm_mul, Complex.norm_conj]
        have hS0 : 0 ≤ S := (norm_nonneg _).trans (hbe x)
        exact mul_le_mul (norm_fnl_le β γ (hbe x)) (hdiff x) (norm_nonneg _) (by positivity))
  have hre : (∫ x, (starRingEnd ℂ) (fnl β γ (field L (co L e) x)) *
      (field L (co L f) x - field L (co L e) x) ∂box L).re =
      ∫ x, ((starRingEnd ℂ) (fnl β γ (field L (co L e) x)) *
        (field L (co L f) x - field L (co L e) x)).re ∂box L :=
    (integral_re hI).symm
  have hB : Integrable (fun x => 2 * ((starRingEnd ℂ) (fnl β γ (field L (co L e) x)) *
      (field L (co L f) x - field L (co L e) x)).re) (box L) := by
    have := hI.re.const_mul 2
    simpa using this
  have hA : Integrable (fun x => nfun β γ (field L (co L f) x) - nfun β γ (field L (co L e) x))
      (box L) := hint2.sub hint1
  have hsqI : Integrable (fun x => ‖field L (co L f) x - field L (co L e) x‖ ^ 2) (box L) :=
    integrable_of_cont_bdd (by fun_prop) (C := (2 * S) ^ 2) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hdiff x) 2)
  have key : pot L β γ f - pot L β γ e -
      2 * (∫ x, (starRingEnd ℂ) (fnl β γ (field L (co L e) x)) *
        (field L (co L f) x - field L (co L e) x) ∂box L).re =
      ∫ x, (nfun β γ (field L (co L f) x) - nfun β γ (field L (co L e) x) -
        2 * ((starRingEnd ℂ) (fnl β γ (field L (co L e) x)) *
          (field L (co L f) x - field L (co L e) x)).re) ∂box L := by
    rw [hre, integral_sub hA hB, integral_sub hint2 hint1, integral_const_mul]
    rfl
  rw [hlin, key, hsq, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae (hA.sub hB).abs
    (hsqI.const_mul C) ?_)
  filter_upwards with x
  exact nfun_taylor β γ (hbe x) (hbf x)

/-- **Coercivity of the potential** (uniform in `L`): `pot + (3β²/16γ)·mass ≥ 0`. -/
theorem pot_add_mass_nonneg (hL : 0 < L) (β γ : ℝ) (hγ : 0 < γ) (v : ℓ2) :
    0 ≤ pot L β γ v + 3 * β ^ 2 / (16 * γ) * mass L v := by
  rw [mass_eq_integral hL, pot, ← integral_const_mul,
    ← integral_add (integrable_nfun hL β γ v)]
  · refine integral_nonneg fun x => ?_
    simp only [nfun]
    set s := ‖field L (co L v) x‖ ^ 2 with hs
    have hs0 : 0 ≤ s := sq_nonneg _
    have e4 : ‖field L (co L v) x‖ ^ 4 = s ^ 2 := by rw [hs]; ring
    have e6 : ‖field L (co L v) x‖ ^ 6 = s ^ 3 := by rw [hs]; ring
    rw [e4, e6]
    have key : -β / 2 * s ^ 2 + γ / 3 * s ^ 3 + 3 * β ^ 2 / (16 * γ) * s =
        γ / 3 * s * (s - 3 * β / (4 * γ)) ^ 2 := by
      field_simp; ring
    rw [key]
    positivity
  · exact (integrable_of_cont_bdd (by
      have := continuous_field (L := L) (L1_co' hL v); fun_prop)
      (C := (L⁻¹ * Real.sqrt (SL L) * ‖v‖) ^ 2) (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_field_co_le hL v x) 2)).const_mul _

end PVNP.Torus
