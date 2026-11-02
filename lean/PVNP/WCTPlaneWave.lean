import Mathlib

/-!
# Exact plane-wave solutions of the frozen WCT PDE on expanding tori (O4, O6, issue #10)

The maintained projection-free WCT Hamiltonian PDE on a 2-D domain is
`i ∂ₜu = (Δ+κ)²u − β|u|²u + γ|u|⁴u`.  Here the operators are the classical
ones: `∂ₜ`, `∂₁`, `∂₂` are derivatives along coordinate lines (`deriv`),
`Δ = ∂₁∂₁ + ∂₂∂₂`, and `(Δ+κ)² = ΔΔ + 2κΔ + κ²`.

* `plane_wave_solves`: for every amplitude `A ∈ ℂ` and wave number `k`,
  `u(t,x) = A e^{i(k x₁ − ω t)}` with
  `ω = (κ − k²)² − β|A|² + γ|A|⁴` is an **exact global solution**, verified
  pointwise with genuine derivatives.
* `wave_periodic`: for `k = 2πm/L` it is `L`-periodic in `x₁` (and constant
  in `x₂`), hence a solution on the torus `(ℝ/Lℤ)²`.
* `mass_box`, `curvature_box`, `hamiltonian_box`: on the fundamental box
  `[0,L]²`, exact Lebesgue integrals of `|u|²`, `|Δu|²`, and the Hamiltonian
  density `|(Δ+κ)u|² − (β/2)|u|⁴ + (γ/3)|u|⁶`, at every time.
* `expanding_domain_countermodel`: with fixed mass `M`, `|A|² = M/L²` and
  `k = 2π/L`, every `L > 0` gives an exact solution of mass exactly `M` and
  curvature energy `(2π/L)⁴ M`, which tends to `0`; the Hamiltonian is
  `M(κ − (2π/L)²)² − βM²/(2L²) + γM³/(3L⁴)`.

This upgrades the "analytic only" PDE part of
`pvnp/proofs/expanding-domain-hamiltonian-mode.md` to kernel-checked
mathematics.  It is an explicit solution family, **not** a general
well-posedness theorem.
-/

open Complex Real MeasureTheory

namespace PVNP.WCTPlaneWave

/-- Time derivative of a time-dependent field. -/
noncomputable def dt (v : ℝ → ℝ × ℝ → ℂ) (t : ℝ) (x : ℝ × ℝ) : ℂ := deriv (fun s => v s x) t

/-- Partial derivative in `x₁`. -/
noncomputable def d1 (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := deriv (fun s => f (s, x.2)) x.1

/-- Partial derivative in `x₂`. -/
noncomputable def d2 (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := deriv (fun s => f (x.1, s)) x.2

/-- The Laplacian `∂₁∂₁ + ∂₂∂₂`. -/
noncomputable def lap (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun x => d1 (d1 f) x + d2 (d2 f) x

/-- `(Δ + κ) f`. -/
noncomputable def shifted (κ : ℝ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun x => lap f x + κ * f x

/-- `(Δ + κ)² f = ΔΔf + 2κΔf + κ²f`. -/
noncomputable def opK (κ : ℝ) (f : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => lap (lap f) x + 2 * κ * lap f x + κ ^ 2 * f x

/-- Plane-wave profile `c · e^{i(k x₁ − θ)}`. -/
noncomputable def wave (c : ℂ) (k θ : ℝ) : ℝ × ℝ → ℂ :=
  fun x => c * exp (I * ((k * x.1 - θ : ℝ) : ℂ))

theorem hasDerivAt_wave1 (c : ℂ) (k θ x2 s : ℝ) :
    HasDerivAt (fun s : ℝ => wave c k θ (s, x2)) (I * k * wave c k θ (s, x2)) s := by
  have h1 : HasDerivAt (fun s : ℝ => ((k * s - θ : ℝ) : ℂ)) (k : ℂ) s := by
    have := (((hasDerivAt_id s).const_mul k).sub_const θ).ofReal_comp
    simpa using this
  have h2 := ((h1.const_mul I).cexp).const_mul c
  convert h2 using 1
  simp only [wave]; ring

theorem d1_wave (c : ℂ) (k θ : ℝ) : d1 (wave c k θ) = wave (I * k * c) k θ := by
  funext x
  simp only [d1]
  rw [(hasDerivAt_wave1 c k θ x.2 x.1).deriv]
  simp only [wave]; ring

theorem d2_wave (c : ℂ) (k θ : ℝ) : d2 (wave c k θ) = fun _ => 0 := by
  funext x
  simp only [d2, wave]
  exact deriv_const _ _

theorem d2_zero : d2 (fun _ : ℝ × ℝ => (0 : ℂ)) = fun _ => 0 := by
  funext x; simp [d2]

theorem lap_wave (c : ℂ) (k θ : ℝ) : lap (wave c k θ) = wave (-(k : ℂ) ^ 2 * c) k θ := by
  funext x
  simp only [lap, d1_wave, d2_wave, d2_zero, add_zero]
  simp only [wave]
  rw [show I * (k : ℂ) * (I * k * c) = -(k : ℂ) ^ 2 * c by ring_nf; rw [I_sq]; ring]

theorem shifted_wave (κ : ℝ) (c : ℂ) (k θ : ℝ) (x : ℝ × ℝ) :
    shifted κ (wave c k θ) x = ((κ : ℂ) - (k : ℂ) ^ 2) * wave c k θ x := by
  simp only [shifted, lap_wave, wave]; ring

theorem opK_wave (κ : ℝ) (c : ℂ) (k θ : ℝ) (x : ℝ × ℝ) :
    opK κ (wave c k θ) x = ((κ : ℂ) - (k : ℂ) ^ 2) ^ 2 * wave c k θ x := by
  simp only [opK, lap_wave, wave]; ring

theorem norm_wave (c : ℂ) (k θ : ℝ) (x : ℝ × ℝ) : ‖wave c k θ x‖ = ‖c‖ := by
  simp only [wave, norm_mul]
  rw [mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem hasDerivAt_time (A : ℂ) (k ω : ℝ) (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => wave A k (ω * s) x) (-I * ω * wave A k (ω * t) x) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((k * x.1 - ω * s : ℝ) : ℂ)) (-(ω : ℂ)) t := by
    have := (((hasDerivAt_id t).const_mul ω).const_sub (k * x.1)).ofReal_comp
    simpa using this
  have h2 := ((h1.const_mul I).cexp).const_mul A
  convert h2 using 1
  simp only [wave]; ring

/-- The derivatives in `dt`, `d1`, `d2` are genuine (`HasDerivAt`) derivatives
for plane waves, and every iterated spatial derivative is again a plane wave;
so `plane_wave_solves` is a classical (pointwise, everywhere differentiable)
solution, not an artefact of `deriv` returning `0`. -/
theorem classical_derivatives (A c : ℂ) (k ω θ : ℝ) :
    (∀ t x, HasDerivAt (fun s => wave A k (ω * s) x) (dt (fun s => wave A k (ω * s)) t x) t) ∧
    (∀ x, HasDerivAt (fun s => wave c k θ (s, x.2)) (d1 (wave c k θ) x) x.1) ∧
    (∀ x, HasDerivAt (fun s => wave c k θ (x.1, s)) (d2 (wave c k θ) x) x.2) := by
  refine ⟨fun t x => ?_, fun x => ?_, fun x => ?_⟩
  · have h := hasDerivAt_time A k ω x t
    rw [show dt (fun s => wave A k (ω * s)) t x = _ from h.deriv]; exact h
  · have h := hasDerivAt_wave1 c k θ x.2 x.1
    rw [show d1 (wave c k θ) x = _ from h.deriv]; exact h
  · rw [d2_wave]
    simp only [wave]
    exact hasDerivAt_const _ _

/-- **Exact solution of the frozen WCT PDE.** -/
theorem plane_wave_solves (A : ℂ) (k κ β γ : ℝ) (t : ℝ) (x : ℝ × ℝ) :
    let ω := (κ - k ^ 2) ^ 2 - β * ‖A‖ ^ 2 + γ * ‖A‖ ^ 4
    let u := fun s : ℝ => wave A k (ω * s)
    I * dt u t x =
      opK κ (u t) x - (β : ℂ) * ((‖u t x‖ ^ 2 : ℝ) : ℂ) * u t x
        + (γ : ℂ) * ((‖u t x‖ ^ 4 : ℝ) : ℂ) * u t x := by
  intro ω u
  simp only [u, dt]
  rw [(hasDerivAt_time A k ω x t).deriv, opK_wave, norm_wave]
  simp only [ω]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The plane wave with `k = 2πm/L` is `L`-periodic in `x₁`. -/
theorem wave_periodic (c : ℂ) (m : ℤ) {L : ℝ} (hL : L ≠ 0) (θ : ℝ) (x : ℝ × ℝ) :
    wave c (2 * π * m / L) θ (x.1 + L, x.2) = wave c (2 * π * m / L) θ x := by
  simp only [wave]
  have : I * (((2 * π * m / L) * (x.1 + L) - θ : ℝ) : ℂ) =
      I * (((2 * π * m / L) * x.1 - θ : ℝ) : ℂ) + (m : ℂ) * (2 * π * I) := by
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    push_cast; field_simp; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Integrals over the fundamental box `[0,L]²` -/

theorem volume_box {L : ℝ} (hL : 0 ≤ L) :
    (volume (Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L)).toReal = L ^ 2 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Integral of a function of constant value over the box. -/
theorem integral_box_const {L : ℝ} (hL : 0 ≤ L) (F : ℝ × ℝ → ℝ) (C : ℝ) (hF : ∀ x, F x = C) :
    ∫ x in Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L, F x = C * L ^ 2 := by
  have : F = fun _ => C := funext hF
  rw [this, setIntegral_const, smul_eq_mul, measureReal_def, volume_box hL, mul_comm]

/-- Mass `∫ |u|² = |A|² L²` at every time. -/
theorem mass_box (A : ℂ) (k θ : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L, ‖wave A k θ x‖ ^ 2 = ‖A‖ ^ 2 * L ^ 2 :=
  integral_box_const hL _ _ fun x => by rw [norm_wave]

/-- Curvature energy `∫ |Δu|² = k⁴ |A|² L²` at every time. -/
theorem curvature_box (A : ℂ) (k θ : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L, ‖lap (wave A k θ) x‖ ^ 2 =
      k ^ 4 * ‖A‖ ^ 2 * L ^ 2 :=
  integral_box_const hL _ _ fun x => by
    rw [lap_wave, norm_wave, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, ← pow_mul, show 2 * 2 = 4 from rfl, Even.pow_abs ⟨2, rfl⟩]

/-- Hamiltonian density `|(Δ+κ)u|² − (β/2)|u|⁴ + (γ/3)|u|⁶`. -/
noncomputable def hamDensity (κ β γ : ℝ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℝ :=
  ‖shifted κ f x‖ ^ 2 - β / 2 * ‖f x‖ ^ 4 + γ / 3 * ‖f x‖ ^ 6

theorem hamiltonian_box (A : ℂ) (k θ κ β γ : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L, hamDensity κ β γ (wave A k θ) x =
      ((κ - k ^ 2) ^ 2 * ‖A‖ ^ 2 - β / 2 * ‖A‖ ^ 4 + γ / 3 * ‖A‖ ^ 6) * L ^ 2 :=
  integral_box_const hL _ _ fun x => by
    simp only [hamDensity]
    rw [shifted_wave, norm_mul, norm_wave]
    have : ‖((κ : ℂ) - (k : ℂ) ^ 2)‖ = |κ - k ^ 2| := by
      rw [show ((κ : ℂ) - (k : ℂ) ^ 2) = ((κ - k ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [this, mul_pow, sq_abs]

/-- **Expanding-domain countermodel with genuine solutions.** For fixed mass
`M ≥ 0` and every side `L > 0`, the field
`u_L = (√M/L) e^{i(2π x₁/L − ω_L t)}` is an exact solution of the frozen PDE
on the torus of side `L`, with mass exactly `M`, curvature energy
`(2π/L)⁴ M` and the stated Hamiltonian, at every time.  The curvature energy
tends to `0` as `L → ∞` while the mass stays fixed. -/
theorem expanding_domain_countermodel (M κ β γ : ℝ) (hM : 0 ≤ M) {L : ℝ} (hL : 0 < L) :
    let A : ℂ := ((Real.sqrt M / L : ℝ) : ℂ)
    let k : ℝ := 2 * π / L
    let ω := (κ - k ^ 2) ^ 2 - β * ‖A‖ ^ 2 + γ * ‖A‖ ^ 4
    (∀ t x, I * dt (fun s => wave A k (ω * s)) t x =
      opK κ (wave A k (ω * t)) x - (β : ℂ) * ((‖wave A k (ω * t) x‖ ^ 2 : ℝ) : ℂ) * wave A k (ω * t) x
        + (γ : ℂ) * ((‖wave A k (ω * t) x‖ ^ 4 : ℝ) : ℂ) * wave A k (ω * t) x) ∧
    (∀ t x, wave A k (ω * t) (x.1 + L, x.2) = wave A k (ω * t) x) ∧
    (∀ t, ∫ x in Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L, ‖wave A k (ω * t) x‖ ^ 2 = M) ∧
    (∀ t, ∫ x in Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L, ‖lap (wave A k (ω * t)) x‖ ^ 2 =
      (2 * π / L) ^ 4 * M) ∧
    (∀ t, ∫ x in Set.Icc (0 : ℝ) L ×ˢ Set.Icc (0 : ℝ) L, hamDensity κ β γ (wave A k (ω * t)) x =
      M * (κ - (2 * π / L) ^ 2) ^ 2 - β * M ^ 2 / (2 * L ^ 2) + γ * M ^ 3 / (3 * L ^ 4)) := by
  intro A k ω
  have hA : ‖A‖ ^ 2 = M / L ^ 2 := by
    simp only [A, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hM]
  have hL0 : L ≠ 0 := hL.ne'
  refine ⟨fun t x => plane_wave_solves A k κ β γ t x, fun t x => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_⟩
  · have := wave_periodic A 1 hL0 (ω * t) x
    simpa [k] using this
  · rw [mass_box _ _ _ hL.le, hA]; field_simp
  · rw [curvature_box _ _ _ hL.le, hA]; simp only [k]; field_simp
  · rw [hamiltonian_box _ _ _ _ _ _ hL.le]
    have h4 : ‖A‖ ^ 4 = (M / L ^ 2) ^ 2 := by rw [← hA]; ring
    have h6 : ‖A‖ ^ 6 = (M / L ^ 2) ^ 3 := by rw [← hA]; ring
    rw [hA, h4, h6]; simp only [k]; field_simp

/-- The curvature energy of the expanding-domain solutions tends to zero. -/
theorem curvature_energy_vanishes (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, (2 * π / L) ^ 4 * M < ε := by
  refine ⟨(2 * π) * (M / ε + 1), by positivity, fun L hL => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have h1 : 2 * π / L ≤ 1 / (M / ε + 1) := by
    rw [div_le_div_iff₀ hL0 (by positivity)]; linarith
  have h2 : 0 ≤ 2 * π / L := by positivity
  have h3 : 1 / (M / ε + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [div_nonneg hM hε.le]
  have h4 : (2 * π / L) ^ 4 ≤ 1 / (M / ε + 1) := by
    calc (2 * π / L) ^ 4 ≤ (2 * π / L) ^ 1 :=
          pow_le_pow_of_le_one h2 (le_trans h1 h3) (by norm_num)
      _ ≤ 1 / (M / ε + 1) := by simpa using h1
  calc (2 * π / L) ^ 4 * M ≤ 1 / (M / ε + 1) * M := mul_le_mul_of_nonneg_right h4 hM
    _ < ε := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
      have : M = ε * (M / ε) := by field_simp
      nlinarith
end PVNP.WCTPlaneWave
