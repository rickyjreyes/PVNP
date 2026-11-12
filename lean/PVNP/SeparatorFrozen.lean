import PVNP.WCTPlaneWave
import PVNP.PartIIIAnalytic

/-!
# I-31: the uniform separator price fails for the frozen WCT trajectory class

Part I, Hypothesis `lem:separator-price`:

> For all admissible fields used by a specified class of machines,
> `Φ(ψ) ≥ κ₀ 𝓗^{d-1}(∂𝓡_ψ)` with `κ₀ > 0` independent of the input length and encoding.

Here `Φ(ψ) = ∫ (|∇ψ|² + |Θ[ψ]|²)` is the manuscript's cumulative curvature functional
(Part I, "Semantic Curvature Complexity"), `Θ` a curvature operator, and `∂𝓡_ψ` the decision
interface. In the frozen model `WCT-Phys` (`pvnp/proofs/physical-model-freeze.md`) the field lives
on the torus of side `L_n`, a declared function of the input length, and evolves by
`i∂ₜψ = (Δ+κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ`.

This module shows that no such `κ₀` exists for the frozen trajectory class, **at fixed readout
contrast**:

* `traj κ β γ A L` is the exact plane-wave solution `A e^{i(2πx₁/L − ωt)}` of the frozen PDE on the
  torus of side `L` (`traj_solves`, `traj_periodic`). Its amplitude `|A|` does not depend on `L`.
* Its quadrature readout `Re ψ` takes the values `|A|` and `−|A|` inside the fundamental domain at
  every time (`traj_contrast`), so both decisions are present with the same margin for every `L`.
* `Phi_traj_le`: `Φ(ψ_t) ≤ 4π²|A|² + 16π⁴c²|A|²/L²` for every curvature operator `Θ` with
  `|Θ[ψ]| ≤ c|Δψ|` pointwise. This covers `Θ = Δ` (`c = 1`), the complex-safe
  `Θ_ε = −Δψ ψ̄/(|ψ|²+ε²)` of Part III (`c = 1/(2ε)`) and `Δψ/g` with `g ≥ g₀ > 0`.
* `interface_ge`: the Euclidean `𝓗¹` of the frontier of the decision region `{Re ψ_t > 0}` inside
  the fundamental domain is at least `L`, at every time.
* `no_uniform_separator_price`: for every `κ₀ > 0` there is `L₀` such that every state of every
  such trajectory on a torus of side `L ≥ L₀` violates `Φ(ψ) ≥ κ₀ 𝓗¹(∂𝓡_ψ)`.
* `stripe_device_decides`: these fields are used by a decider. The encoder writes amplitude `+1`
  or `−1` (the decision bit, as in the charged encoders of `PhysicalAudit`), and the sign of
  `Re ψ` at the origin at time `0` is the answer. Every state of every run violates the price once
  `L ≥ L₀`.

The price fails because the transition between the two readout values is spread over a width
proportional to `L`. `layer_price` is the corrected statement: a transition from `≤ −η` to `≥ η`
across a layer of width `w` costs at least `4η²/w` per unit of interface length, and the bound is
attained by linear profiles. A uniform `κ₀` therefore needs a uniform bound on transition widths,
which the frozen model does not impose.

Measure conventions. `Φ` is a Lebesgue integral in `ℝ≥0∞`, so its upper bounds need no
integrability hypotheses. The interface is measured with the Hausdorff measure `μH[1]` of
`EuclideanSpace ℝ (Fin 2)`, i.e. Euclidean length, after the coordinate map `toE`.
-/

namespace PVNP.SeparatorFrozen

open PVNP.WCTPlaneWave MeasureTheory Complex Real Filter Topology
open scoped ENNReal

/-! ## Definitions -/

/-- The fundamental domain `[0, L)²` of the torus of side `L`. -/
def box (L : ℝ) : Set (ℝ × ℝ) := Set.Ico 0 L ×ˢ Set.Ico 0 L

/-- Decision region of the quadrature readout `Re ψ` at threshold `0`. -/
def region (ψ : ℝ × ℝ → ℂ) : Set (ℝ × ℝ) := {x | 0 < (ψ x).re}

/-- Euclidean coordinates of a point of the plane. -/
noncomputable def toE (x : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[x.1, x.2]

/-- The manuscript's cumulative curvature functional `Φ(ψ) = ∫ (|∇ψ|² + |Θ[ψ]|²)` over the
fundamental domain, with curvature operator `Θ`. -/
noncomputable def Phi (L : ℝ) (Θ : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ) (ψ : ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x in box L, ENNReal.ofReal (‖d1 ψ x‖ ^ 2 + ‖d2 ψ x‖ ^ 2 + ‖Θ ψ x‖ ^ 2)

/-- Frequency of the plane wave of amplitude `A` and wave number `2π/L`. -/
noncomputable def omega (κ β γ : ℝ) (A : ℂ) (L : ℝ) : ℝ :=
  (κ - (2 * π / L) ^ 2) ^ 2 - β * ‖A‖ ^ 2 + γ * ‖A‖ ^ 4

/-- The exact plane-wave trajectory of amplitude `A` on the torus of side `L`. -/
noncomputable def traj (κ β γ : ℝ) (A : ℂ) (L t : ℝ) : ℝ × ℝ → ℂ :=
  wave A (2 * π / L) (omega κ β γ A L * t)

/-! ## The trajectory is an exact solution of the frozen PDE -/

theorem traj_solves (κ β γ : ℝ) (A : ℂ) (L t : ℝ) (x : ℝ × ℝ) :
    I * dt (traj κ β γ A L) t x =
      opK κ (traj κ β γ A L t) x
        - (β : ℂ) * ((‖traj κ β γ A L t x‖ ^ 2 : ℝ) : ℂ) * traj κ β γ A L t x
        + (γ : ℂ) * ((‖traj κ β γ A L t x‖ ^ 4 : ℝ) : ℂ) * traj κ β γ A L t x :=
  plane_wave_solves A (2 * π / L) κ β γ t x

theorem traj_periodic (κ β γ : ℝ) (A : ℂ) {L : ℝ} (hL : L ≠ 0) (t : ℝ) (x : ℝ × ℝ) :
    traj κ β γ A L t (x.1 + L, x.2) = traj κ β γ A L t x := by
  have := wave_periodic A 1 hL (omega κ β γ A L * t) x
  simpa [traj] using this

/-- The pointwise amplitude is `|A|` for every side `L`: the readout contrast is fixed. -/
theorem traj_norm (κ β γ : ℝ) (A : ℂ) (L t : ℝ) (x : ℝ × ℝ) : ‖traj κ β γ A L t x‖ = ‖A‖ :=
  norm_wave _ _ _ _

/-! ## The readout -/

theorem wave_re (B : ℂ) (k θ : ℝ) (x : ℝ × ℝ) :
    (wave B k θ x).re = ‖B‖ * Real.cos (k * x.1 - θ + arg B) := by
  have hB := Complex.norm_mul_exp_arg_mul_I B
  have h : wave B k θ x = (‖B‖ : ℂ) * exp (((k * x.1 - θ + arg B : ℝ) : ℂ) * I) := by
    simp only [wave]
    conv_lhs => rw [← hB]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Points of the fundamental domain at which the phase `k x₁ − θ + arg B` takes a prescribed value
modulo `2π`. -/
theorem phase_point {L : ℝ} (hL : 0 < L) (B : ℂ) (θ φ : ℝ) :
    ∃ s ∈ Set.Ico 0 L, ∃ n : ℤ, 2 * π / L * s - θ + arg B = φ - n * (2 * π) := by
  have hk : 0 < 2 * π / L := by positivity
  set u := (φ + θ - arg B) / (2 * π / L) with hu
  refine ⟨L * Int.fract (u / L), ⟨by have := Int.fract_nonneg (u / L); positivity, ?_⟩,
    ⌊u / L⌋, ?_⟩
  · have := Int.fract_lt_one (u / L)
    calc L * Int.fract (u / L) < L * 1 := by gcongr
      _ = L := mul_one L
  · rw [← Int.self_sub_floor, hu]
    field_simp
    ring

/-- The readout reaches `|A|` and `−|A|` inside the fundamental domain at every time. -/
theorem traj_contrast (κ β γ : ℝ) (A : ℂ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (∃ x ∈ box L, (traj κ β γ A L t x).re = ‖A‖) ∧
      (∃ x ∈ box L, (traj κ β γ A L t x).re = -‖A‖) := by
  have h0 : (0 : ℝ) ∈ Set.Ico 0 L := ⟨le_rfl, hL⟩
  obtain ⟨s, hs, n, hn⟩ := phase_point hL A (omega κ β γ A L * t) 0
  obtain ⟨s', hs', n', hn'⟩ := phase_point hL A (omega κ β γ A L * t) π
  refine ⟨⟨(s, 0), ⟨hs, h0⟩, ?_⟩, ⟨(s', 0), ⟨hs', h0⟩, ?_⟩⟩
  · simp only [traj]
    rw [wave_re, hn, Real.cos_sub_int_mul_two_pi, Real.cos_zero, mul_one]
  · simp only [traj]
    rw [wave_re, hn', Real.cos_sub_int_mul_two_pi, Real.cos_pi, mul_neg_one]

/-! ## The interface -/

/-- A full vertical segment of the fundamental domain lies on the decision interface. -/
theorem segment_subset {L : ℝ} (hL : 0 < L) (B : ℂ) (hB : B ≠ 0) (θ : ℝ) :
    ∃ s₀ ∈ Set.Ico 0 L,
      {s₀} ×ˢ Set.Ico 0 L ⊆ frontier (region (wave B (2 * π / L) θ)) ∩ box L := by
  have hk : 0 < 2 * π / L := by positivity
  obtain ⟨s₀, hs₀, n, hn⟩ := phase_point hL B θ (π / 2)
  refine ⟨s₀, hs₀, ?_⟩
  rintro ⟨x1, y⟩ ⟨hx1, hy⟩
  rw [Set.mem_singleton_iff] at hx1
  subst hx1
  refine ⟨?_, ⟨hs₀, hy⟩⟩
  rw [frontier_eq_closure_inter_closure]
  refine ⟨?_, subset_closure ?_⟩
  · apply mem_closure_of_tendsto (f := fun ε : ℝ => (x1 - ε, y)) (b := 𝓝[>] 0)
    · have hc : Continuous (fun ε : ℝ => (x1 - ε, y)) := by fun_prop
      have := hc.tendsto 0
      simp only [sub_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / (2 * π / L) by positivity)]
        with ε hε
      show 0 < (wave B (2 * π / L) θ (x1 - ε, y)).re
      rw [wave_re]
      have hph : 2 * π / L * (x1 - ε, y).1 - θ + arg B =
          (π / 2 - 2 * π / L * ε) - n * (2 * π) := by
        simp only
        linarith [hn]
      rw [hph, Real.cos_sub_int_mul_two_pi, Real.cos_pi_div_two_sub]
      apply mul_pos (norm_pos_iff.2 hB)
      apply Real.sin_pos_of_pos_of_lt_pi (by have := hε.1; positivity)
      have h2 := hε.2
      rw [lt_div_iff₀ hk] at h2
      linarith
  · show ¬ (0 < (wave B (2 * π / L) θ (x1, y)).re)
    rw [wave_re, hn, Real.cos_sub_int_mul_two_pi, Real.cos_pi_div_two, mul_zero]
    exact lt_irrefl 0

/-- A vertical segment of length `L` has Euclidean length `L`. -/
theorem hausdorff_segment (s₀ L : ℝ) :
    μH[1] (toE '' ({s₀} ×ˢ Set.Ico 0 L)) = ENNReal.ofReal L := by
  have hiso : Isometry (fun y : ℝ => toE (s₀, y)) := by
    apply Isometry.of_dist_eq
    intro y y'
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [toE, Real.dist_eq, Real.sqrt_sq_eq_abs]
  have himg : toE '' ({s₀} ×ˢ Set.Ico 0 L) = (fun y : ℝ => toE (s₀, y)) '' Set.Ico 0 L := by
    ext p
    simp only [Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨rfl, hb⟩, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨s₀, b, ⟨rfl, hb⟩, rfl⟩
  rw [himg, hiso.hausdorffMeasure_image (Or.inl zero_le_one), hausdorffMeasure_real,
    Real.volume_Ico, sub_zero]

/-- **Interface lower bound.** The decision interface of `wave B (2π/L) θ` inside the
fundamental domain has Euclidean length at least `L`. -/
theorem interface_ge {L : ℝ} (hL : 0 < L) (B : ℂ) (hB : B ≠ 0) (θ : ℝ) :
    ENNReal.ofReal L ≤
      μH[1] (toE '' (frontier (region (wave B (2 * π / L) θ)) ∩ box L)) := by
  obtain ⟨s₀, -, hsub⟩ := segment_subset hL B hB θ
  rw [← hausdorff_segment s₀ L]
  exact measure_mono (Set.image_mono hsub)

/-! ## The curvature functional -/

theorem volume_box {L : ℝ} (hL : 0 ≤ L) : volume (box L) = ENNReal.ofReal (L ^ 2) := by
  rw [box, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, sub_zero,
    ← ENNReal.ofReal_mul hL, sq]

theorem Phi_wave_le {L c : ℝ} (hL : 0 ≤ L) {Θ : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ}
    (hΘ : ∀ ψ x, ‖Θ ψ x‖ ≤ c * ‖lap ψ x‖) (B : ℂ) (k θ : ℝ) :
    Phi L Θ (wave B k θ) ≤
      ENNReal.ofReal ((k ^ 2 * ‖B‖ ^ 2 + c ^ 2 * k ^ 4 * ‖B‖ ^ 2) * L ^ 2) := by
  have hpt : ∀ x, ‖d1 (wave B k θ) x‖ ^ 2 + ‖d2 (wave B k θ) x‖ ^ 2 + ‖Θ (wave B k θ) x‖ ^ 2 ≤
      k ^ 2 * ‖B‖ ^ 2 + c ^ 2 * k ^ 4 * ‖B‖ ^ 2 := by
    intro x
    have h1 : ‖d1 (wave B k θ) x‖ ^ 2 = k ^ 2 * ‖B‖ ^ 2 := by
      rw [d1_wave, norm_wave, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
    have h2 : ‖d2 (wave B k θ) x‖ = 0 := by rw [d2_wave, norm_zero]
    have hlap : ‖lap (wave B k θ) x‖ = k ^ 2 * ‖B‖ := by
      rw [lap_wave, norm_wave, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
    have h3 : ‖Θ (wave B k θ) x‖ ≤ c * (k ^ 2 * ‖B‖) := hlap ▸ hΘ _ x
    have h3' : ‖Θ (wave B k θ) x‖ ^ 2 ≤ (c * (k ^ 2 * ‖B‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [h1, h2]
    nlinarith [h3']
  calc Phi L Θ (wave B k θ)
      ≤ ∫⁻ _ in box L, ENNReal.ofReal (k ^ 2 * ‖B‖ ^ 2 + c ^ 2 * k ^ 4 * ‖B‖ ^ 2) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (k ^ 2 * ‖B‖ ^ 2 + c ^ 2 * k ^ 4 * ‖B‖ ^ 2) * volume (box L) :=
        setLIntegral_const _ _
    _ = _ := by rw [volume_box hL, ← ENNReal.ofReal_mul (by positivity)]

/-- **The curvature functional stays bounded at fixed contrast:**
`Φ(ψ_t) ≤ 4π²|A|² + 16π⁴c²|A|²/L²` at every time. -/
theorem Phi_traj_le (κ β γ : ℝ) {L c : ℝ} (hL : 0 < L)
    {Θ : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ} (hΘ : ∀ ψ x, ‖Θ ψ x‖ ≤ c * ‖lap ψ x‖) (A : ℂ) (t : ℝ) :
    Phi L Θ (traj κ β γ A L t) ≤
      ENNReal.ofReal (4 * π ^ 2 * ‖A‖ ^ 2 + 16 * π ^ 4 * c ^ 2 * ‖A‖ ^ 2 / L ^ 2) := by
  refine (Phi_wave_le hL.le hΘ A _ _).trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

/-! ## The hypothesis fails -/

/-- **No uniform separator price for the frozen trajectory class.** For every curvature operator
dominated by the Laplacian, every amplitude bound `a` and every `κ₀ > 0` there is a side `L₀` such
that, on every torus of side `L ≥ L₀`, every state of every exact plane-wave trajectory with
`0 < |A| ≤ a` violates `Φ(ψ) ≥ κ₀ 𝓗¹(∂𝓡_ψ)`. -/
theorem no_uniform_separator_price (κ β γ : ℝ) {c : ℝ}
    {Θ : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ} (hΘ : ∀ ψ x, ‖Θ ψ x‖ ≤ c * ‖lap ψ x‖) (a κ₀ : ℝ)
    (hκ₀ : 0 < κ₀) :
    ∃ L₀ ≥ 1, ∀ L ≥ L₀, ∀ A : ℂ, A ≠ 0 → ‖A‖ ≤ a → ∀ t : ℝ,
      Phi L Θ (traj κ β γ A L t) <
        ENNReal.ofReal κ₀ * μH[1] (toE '' (frontier (region (traj κ β γ A L t)) ∩ box L)) := by
  set C₁ := 4 * π ^ 2 * a ^ 2 + 16 * π ^ 4 * c ^ 2 * a ^ 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨max 1 (C₁ / κ₀ + 1), le_max_left _ _, fun L hL A hA hAa t => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hLC : C₁ / κ₀ + 1 ≤ L := (le_max_right _ _).trans hL
  have hlt : C₁ < κ₀ * L := by
    have : C₁ / κ₀ < L := by linarith
    rwa [div_lt_iff₀ hκ₀, mul_comm] at this
  have hA2 : ‖A‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hAa 2
  have hcost : 4 * π ^ 2 * ‖A‖ ^ 2 + 16 * π ^ 4 * c ^ 2 * ‖A‖ ^ 2 / L ^ 2 ≤ C₁ := by
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hdiv : 16 * π ^ 4 * c ^ 2 * ‖A‖ ^ 2 / L ^ 2 ≤ 16 * π ^ 4 * c ^ 2 * ‖A‖ ^ 2 :=
      div_le_self (by positivity) hL2
    have h1 : 4 * π ^ 2 * ‖A‖ ^ 2 ≤ 4 * π ^ 2 * a ^ 2 := by gcongr
    have h2 : 16 * π ^ 4 * c ^ 2 * ‖A‖ ^ 2 ≤ 16 * π ^ 4 * c ^ 2 * a ^ 2 := by gcongr
    linarith
  calc Phi L Θ (traj κ β γ A L t)
      ≤ ENNReal.ofReal (4 * π ^ 2 * ‖A‖ ^ 2 + 16 * π ^ 4 * c ^ 2 * ‖A‖ ^ 2 / L ^ 2) :=
        Phi_traj_le κ β γ hL0 hΘ A t
    _ ≤ ENNReal.ofReal C₁ := ENNReal.ofReal_le_ofReal hcost
    _ < ENNReal.ofReal (κ₀ * L) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt
    _ = ENNReal.ofReal κ₀ * ENNReal.ofReal L := ENNReal.ofReal_mul hκ₀.le
    _ ≤ ENNReal.ofReal κ₀ * μH[1] (toE '' (frontier (region (traj κ β γ A L t)) ∩ box L)) :=
        mul_le_mul_left' (interface_ge hL0 A hA _) _

/-- `lem:separator-price` in negated form: no `κ₀ > 0` bounds the interface measure by the
curvature functional along the frozen plane-wave trajectories of a fixed amplitude. -/
theorem separator_price_hypothesis_false (κ β γ : ℝ) {c : ℝ}
    {Θ : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ} (hΘ : ∀ ψ x, ‖Θ ψ x‖ ≤ c * ‖lap ψ x‖) (A : ℂ) (hA : A ≠ 0) :
    ¬ ∃ κ₀ > 0, ∀ L ≥ 1, ∀ t : ℝ,
      ENNReal.ofReal κ₀ * μH[1] (toE '' (frontier (region (traj κ β γ A L t)) ∩ box L)) ≤
        Phi L Θ (traj κ β γ A L t) := by
  rintro ⟨κ₀, hκ₀, hprice⟩
  obtain ⟨L₀, hL₀, hbad⟩ := no_uniform_separator_price κ β γ hΘ ‖A‖ κ₀ hκ₀
  have := hbad L₀ le_rfl A hA le_rfl 0
  exact absurd (hprice L₀ hL₀ 0) (not_le.2 this)

/-! ## The manuscript's curvature operators -/

/-- `Θ = Δ` (the manuscript's `Θ` with `g ≡ 1`) is dominated with `c = 1`. -/
theorem lap_dominated (ψ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ‖lap ψ x‖ ≤ 1 * ‖lap ψ x‖ := by
  rw [one_mul]

/-- The complex-safe `Θ_ε = −Δψ ψ̄/(|ψ|²+ε²)` of Part III is dominated with `c = 1/(2ε)`. -/
theorem thetaEps_dominated {ε : ℝ} (hε : 0 < ε) (ψ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    ‖PartIIIAnalytic.theta ε ψ (lap ψ) x‖ ≤ 1 / (2 * ε) * ‖lap ψ x‖ := by
  have := PartIIIAnalytic.theta_pointwise_le hε ψ (lap ψ) x
  rw [div_eq_mul_inv, mul_comm] at this
  rw [one_div]
  exact this

/-- The hypothesis fails for `Φ = ∫ (|∇ψ|² + |Θ_ε[ψ]|²)` with the operator of Part III. -/
theorem separator_price_false_thetaEps (κ β γ : ℝ) {ε : ℝ} (hε : 0 < ε) (A : ℂ) (hA : A ≠ 0) :
    ¬ ∃ κ₀ > 0, ∀ L ≥ 1, ∀ t : ℝ,
      ENNReal.ofReal κ₀ * μH[1] (toE '' (frontier (region (traj κ β γ A L t)) ∩ box L)) ≤
        Phi L (fun ψ x => PartIIIAnalytic.theta ε ψ (lap ψ) x) (traj κ β γ A L t) :=
  separator_price_hypothesis_false κ β γ (thetaEps_dominated hε) A hA

/-! ## The fields are used by a decider -/

open Classical in
/-- Encoder of the stripe device: amplitude `+1` on members of `Lang`, `−1` otherwise. -/
noncomputable def stripeAmp (Lang : Set (List Bool)) (x : List Bool) : ℂ :=
  if x ∈ Lang then 1 else -1

theorem stripeAmp_ne_zero (Lang : Set (List Bool)) (x : List Bool) : stripeAmp Lang x ≠ 0 := by
  classical
  unfold stripeAmp
  split_ifs <;> norm_num

theorem stripeAmp_norm (Lang : Set (List Bool)) (x : List Bool) : ‖stripeAmp Lang x‖ = 1 := by
  classical
  unfold stripeAmp
  split_ifs <;> simp

/-- **The stripe device decides `Lang`:** the sign of the readout `Re ψ` at the origin at the
declared readout time `0` is the membership bit. -/
theorem stripe_device_decides (κ β γ : ℝ) (Lang : Set (List Bool)) (L : ℝ) (x : List Bool) :
    0 < (traj κ β γ (stripeAmp Lang x) L 0 (0, 0)).re ↔ x ∈ Lang := by
  classical
  simp only [traj, wave, mul_zero, sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one]
  unfold stripeAmp
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Every state of every run of the stripe device violates the separator price once `L ≥ L₀`. -/
theorem stripe_device_violates (κ β γ : ℝ) {c : ℝ}
    {Θ : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ} (hΘ : ∀ ψ x, ‖Θ ψ x‖ ≤ c * ‖lap ψ x‖) (κ₀ : ℝ) (hκ₀ : 0 < κ₀)
    (Lang : Set (List Bool)) :
    ∃ L₀ ≥ 1, ∀ L ≥ L₀, ∀ x : List Bool, ∀ t : ℝ,
      Phi L Θ (traj κ β γ (stripeAmp Lang x) L t) <
        ENNReal.ofReal κ₀ *
          μH[1] (toE '' (frontier (region (traj κ β γ (stripeAmp Lang x) L t)) ∩ box L)) := by
  obtain ⟨L₀, hL₀, h⟩ := no_uniform_separator_price κ β γ hΘ 1 κ₀ hκ₀
  exact ⟨L₀, hL₀, fun L hL x t =>
    h L hL _ (stripeAmp_ne_zero Lang x) (stripeAmp_norm Lang x).le t⟩

/-! ## A modulus readout fails the price as well

The counterexample does not depend on reading the quadrature `Re ψ`. The initial datum
`g(x) = (a/2)(1 + cos(2πx₁/L))` has three Fourier modes, so a polynomial-time encoder writes it
exactly, and its modulus readout `{|g| > a/2}` has the same kind of interface. -/

/-- Three-mode initial datum with modulus between `0` and `a`. -/
noncomputable def bump (a L : ℝ) (x : ℝ × ℝ) : ℂ :=
  ((a / 2 * (1 + Real.cos (2 * π / L * x.1)) : ℝ) : ℂ)

/-- Decision region of the modulus readout at threshold `τ`. -/
def modRegion (τ : ℝ) (ψ : ℝ × ℝ → ℂ) : Set (ℝ × ℝ) := {x | τ < ‖ψ x‖}

theorem hasDerivAt_bump1 (a k : ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ((a / 2 * (1 + Real.cos (k * s)) : ℝ) : ℂ))
      (((-(a / 2 * k * Real.sin (k * s))) : ℝ) : ℂ) s := by
  have h : HasDerivAt (fun s : ℝ => a / 2 * (1 + Real.cos (k * s)))
      (a / 2 * (-(Real.sin (k * s) * k))) s :=
    ((((hasDerivAt_id s).const_mul k).cos).const_add 1).const_mul (a / 2) |>.congr_deriv
      (by simp)
  have := h.ofReal_comp
  convert this using 2
  ring

theorem hasDerivAt_bump1' (a k : ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (((-(a / 2 * k * Real.sin (k * s))) : ℝ) : ℂ))
      (((-(a / 2 * k * (Real.cos (k * s) * k))) : ℝ) : ℂ) s := by
  have h : HasDerivAt (fun s : ℝ => -(a / 2 * k * Real.sin (k * s)))
      (-(a / 2 * k * (Real.cos (k * s) * k))) s :=
    ((((hasDerivAt_id s).const_mul k).sin).const_mul (a / 2 * k)).neg |>.congr_deriv (by simp)
  exact h.ofReal_comp

theorem d1_bump (a L : ℝ) (x : ℝ × ℝ) :
    d1 (bump a L) x = ((-(a / 2 * (2 * π / L) * Real.sin (2 * π / L * x.1)) : ℝ) : ℂ) := by
  simp only [d1, bump]
  exact (hasDerivAt_bump1 a (2 * π / L) x.1).deriv

theorem d2_bump (a L : ℝ) (x : ℝ × ℝ) : d2 (bump a L) x = 0 := by
  simp only [d2, bump]
  exact deriv_const _ _

theorem lap_bump (a L : ℝ) (x : ℝ × ℝ) :
    lap (bump a L) x =
      ((-(a / 2 * (2 * π / L) * (Real.cos (2 * π / L * x.1) * (2 * π / L))) : ℝ) : ℂ) := by
  have h1 : d1 (bump a L) = fun y : ℝ × ℝ =>
      ((-(a / 2 * (2 * π / L) * Real.sin (2 * π / L * y.1)) : ℝ) : ℂ) := funext (d1_bump a L)
  have h2 : d2 (bump a L) = fun _ => 0 := funext (d2_bump a L)
  simp only [lap]
  rw [h1, h2]
  simp only [d1, d2]
  rw [(hasDerivAt_bump1' a (2 * π / L) x.1).deriv, deriv_const, add_zero]

theorem Phi_bump_le {L c a : ℝ} (hL : 0 < L) {Θ : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ}
    (hΘ : ∀ ψ x, ‖Θ ψ x‖ ≤ c * ‖lap ψ x‖) :
    Phi L Θ (bump a L) ≤ ENNReal.ofReal (π ^ 2 * a ^ 2 + 4 * π ^ 4 * c ^ 2 * a ^ 2 / L ^ 2) := by
  set k := 2 * π / L with hk
  have hpt : ∀ x, ‖d1 (bump a L) x‖ ^ 2 + ‖d2 (bump a L) x‖ ^ 2 + ‖Θ (bump a L) x‖ ^ 2 ≤
      a ^ 2 * k ^ 2 / 4 + c ^ 2 * (a ^ 2 * k ^ 4 / 4) := by
    intro x
    have hs := Real.sin_sq_le_one (k * x.1)
    have hc := Real.cos_sq_le_one (k * x.1)
    have h1 : ‖d1 (bump a L) x‖ ^ 2 = (a / 2 * k * Real.sin (k * x.1)) ^ 2 := by
      rw [d1_bump, Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
    have hl : ‖lap (bump a L) x‖ ^ 2 = (a / 2 * k * (Real.cos (k * x.1) * k)) ^ 2 := by
      rw [lap_bump, Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
    have h3 : ‖Θ (bump a L) x‖ ^ 2 ≤ c ^ 2 * ‖lap (bump a L) x‖ ^ 2 := by
      have := hΘ (bump a L) x
      have h0 : 0 ≤ ‖Θ (bump a L) x‖ := norm_nonneg _
      calc ‖Θ (bump a L) x‖ ^ 2 ≤ (c * ‖lap (bump a L) x‖) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = c ^ 2 * ‖lap (bump a L) x‖ ^ 2 := by ring
    rw [h1, d2_bump, norm_zero]
    have hl' : ‖lap (bump a L) x‖ ^ 2 ≤ a ^ 2 * k ^ 4 / 4 := by
      rw [hl]
      have : (a / 2 * k * (Real.cos (k * x.1) * k)) ^ 2 = a ^ 2 * k ^ 4 / 4 * Real.cos (k * x.1) ^ 2 := by
        ring
      rw [this]
      have h0 : 0 ≤ a ^ 2 * k ^ 4 / 4 := by positivity
      calc a ^ 2 * k ^ 4 / 4 * Real.cos (k * x.1) ^ 2 ≤ a ^ 2 * k ^ 4 / 4 * 1 :=
            mul_le_mul_of_nonneg_left hc h0
        _ = a ^ 2 * k ^ 4 / 4 := mul_one _
    have h1' : (a / 2 * k * Real.sin (k * x.1)) ^ 2 ≤ a ^ 2 * k ^ 2 / 4 := by
      have : (a / 2 * k * Real.sin (k * x.1)) ^ 2 = a ^ 2 * k ^ 2 / 4 * Real.sin (k * x.1) ^ 2 := by
        ring
      rw [this]
      have h0 : 0 ≤ a ^ 2 * k ^ 2 / 4 := by positivity
      calc a ^ 2 * k ^ 2 / 4 * Real.sin (k * x.1) ^ 2 ≤ a ^ 2 * k ^ 2 / 4 * 1 :=
            mul_le_mul_of_nonneg_left hs h0
        _ = a ^ 2 * k ^ 2 / 4 := mul_one _
    have h3' : c ^ 2 * ‖lap (bump a L) x‖ ^ 2 ≤ c ^ 2 * (a ^ 2 * k ^ 4 / 4) :=
      mul_le_mul_of_nonneg_left hl' (sq_nonneg c)
    nlinarith [h1', h3, h3']
  calc Phi L Θ (bump a L)
      ≤ ∫⁻ _ in box L, ENNReal.ofReal (a ^ 2 * k ^ 2 / 4 + c ^ 2 * (a ^ 2 * k ^ 4 / 4)) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (a ^ 2 * k ^ 2 / 4 + c ^ 2 * (a ^ 2 * k ^ 4 / 4)) * volume (box L) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal (π ^ 2 * a ^ 2 + 4 * π ^ 4 * c ^ 2 * a ^ 2 / L ^ 2) := by
        rw [volume_box hL.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hk]
        field_simp
        ring

/-- The modulus readout `|g| > a/2` of the three-mode datum has an interface of length at least
`L` inside the fundamental domain. -/
theorem bump_interface_ge {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    ENNReal.ofReal L ≤ μH[1] (toE '' (frontier (modRegion (a / 2) (bump a L)) ∩ box L)) := by
  have hk : 0 < 2 * π / L := by positivity
  have hnorm : ∀ x, ‖bump a L x‖ = a / 2 * (1 + Real.cos (2 * π / L * x.1)) := by
    intro x
    rw [bump, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    have := Real.neg_one_le_cos (2 * π / L * x.1)
    have : 0 ≤ 1 + Real.cos (2 * π / L * x.1) := by linarith
    positivity
  have hq : L / 4 ∈ Set.Ico 0 L := ⟨by positivity, by linarith⟩
  have hph : 2 * π / L * (L / 4) = π / 2 := by field_simp; ring
  have hsub : {L / 4} ×ˢ Set.Ico 0 L ⊆ frontier (modRegion (a / 2) (bump a L)) ∩ box L := by
    rintro ⟨x1, y⟩ ⟨hx1, hy⟩
    rw [Set.mem_singleton_iff] at hx1
    subst hx1
    refine ⟨?_, ⟨hq, hy⟩⟩
    rw [frontier_eq_closure_inter_closure]
    refine ⟨?_, subset_closure ?_⟩
    · apply mem_closure_of_tendsto (f := fun ε : ℝ => (L / 4 - ε, y)) (b := 𝓝[>] 0)
      · have hc : Continuous (fun ε : ℝ => (L / 4 - ε, y)) := by fun_prop
        have := hc.tendsto 0
        simp only [sub_zero] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / (2 * π / L) by positivity)]
          with ε hε
        show a / 2 < ‖bump a L (L / 4 - ε, y)‖
        rw [hnorm]
        have h1 : 2 * π / L * (L / 4 - ε, y).1 = π / 2 - 2 * π / L * ε := by
          simp only
          rw [mul_sub, hph]
        rw [h1, Real.cos_pi_div_two_sub]
        have hsin : 0 < Real.sin (2 * π / L * ε) := by
          apply Real.sin_pos_of_pos_of_lt_pi (by have := hε.1; positivity)
          have h2 := hε.2
          rw [lt_div_iff₀ hk] at h2
          linarith
        nlinarith
    · show ¬ (a / 2 < ‖bump a L (L / 4, y)‖)
      rw [hnorm, hph, Real.cos_pi_div_two, add_zero, mul_one]
      exact lt_irrefl _
  rw [← hausdorff_segment (L / 4) L]
  exact measure_mono (Set.image_mono hsub)

/-- **Modulus readout:** for every `κ₀ > 0` there is `L₀` such that on every torus of side
`L ≥ L₀` the three-mode initial datum of amplitude `a` violates `Φ(ψ) ≥ κ₀ 𝓗¹(∂𝓡_ψ)` for the
modulus readout at threshold `a/2`. -/
theorem no_uniform_price_modulus {c : ℝ} {Θ : (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ}
    (hΘ : ∀ ψ x, ‖Θ ψ x‖ ≤ c * ‖lap ψ x‖) {a : ℝ} (ha : 0 < a) (κ₀ : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ L₀ ≥ 1, ∀ L ≥ L₀,
      Phi L Θ (bump a L) <
        ENNReal.ofReal κ₀ * μH[1] (toE '' (frontier (modRegion (a / 2) (bump a L)) ∩ box L)) := by
  set C₁ := π ^ 2 * a ^ 2 + 4 * π ^ 4 * c ^ 2 * a ^ 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨max 1 (C₁ / κ₀ + 1), le_max_left _ _, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hLC : C₁ / κ₀ + 1 ≤ L := (le_max_right _ _).trans hL
  have hlt : C₁ < κ₀ * L := by
    have : C₁ / κ₀ < L := by linarith
    rwa [div_lt_iff₀ hκ₀, mul_comm] at this
  have hcost : π ^ 2 * a ^ 2 + 4 * π ^ 4 * c ^ 2 * a ^ 2 / L ^ 2 ≤ C₁ := by
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have : 4 * π ^ 4 * c ^ 2 * a ^ 2 / L ^ 2 ≤ 4 * π ^ 4 * c ^ 2 * a ^ 2 :=
      div_le_self (by positivity) hL2
    linarith
  calc Phi L Θ (bump a L)
      ≤ ENNReal.ofReal (π ^ 2 * a ^ 2 + 4 * π ^ 4 * c ^ 2 * a ^ 2 / L ^ 2) := Phi_bump_le hL0 hΘ
    _ ≤ ENNReal.ofReal C₁ := ENNReal.ofReal_le_ofReal hcost
    _ < ENNReal.ofReal (κ₀ * L) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt
    _ = ENNReal.ofReal κ₀ * ENNReal.ofReal L := ENNReal.ofReal_mul hκ₀.le
    _ ≤ _ := mul_le_mul_left' (bump_interface_ge hL0 ha) _

/-! ## The corrected statement: a width-dependent price -/

/-- Cauchy–Schwarz on an interval: `(∫ f)² ≤ (b − a) ∫ f²`. -/
theorem sq_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp
  have hba : 0 < b - a := sub_pos.2 h
  set m := (∫ x in a..b, f x) / (b - a)
  have hnn : 0 ≤ ∫ x in a..b, (f x - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  have hexp : ∫ x in a..b, (f x - m) ^ 2 =
      (∫ x in a..b, f x ^ 2) - 2 * m * (∫ x in a..b, f x) + m ^ 2 * (b - a) := by
    have h1 : (fun x => (f x - m) ^ 2) = fun x => (f x ^ 2 - 2 * m * f x) + m ^ 2 := by
      funext x; ring
    rw [h1, intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hf.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp] at hnn
  have hm : m * (b - a) = ∫ x in a..b, f x := by
    simp only [m]; field_simp
  have key : (∫ x in a..b, f x) ^ 2 = m ^ 2 * (b - a) ^ 2 := by rw [← hm]; ring
  rw [key]
  nlinarith [hnn, hm, hba]

/-- **Layer price (corrected statement).** If a readout profile passes from `≤ −η` to `≥ η`
across a layer of width `w = b − a`, then `∫ |f'|² ≥ 4η²/w`; equivalently
`4η² ≤ w ∫ |f'|²`. Integrated along the interface this is a price of `4η²/w` per unit length, so a
uniform `κ₀` needs a uniform bound on `w`. -/
theorem layer_price {f f' : ℝ → ℝ} {a b η : ℝ} (hab : a ≤ b) (hη : 0 ≤ η)
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b)
    (hint2 : IntervalIntegrable (fun x => f' x ^ 2) volume a b)
    (ha : f a ≤ -η) (hb : η ≤ f b) :
    4 * η ^ 2 ≤ (b - a) * ∫ x in a..b, f' x ^ 2 := by
  have hftc : ∫ x in a..b, f' x = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hf hint
  have hD : 2 * η ≤ ∫ x in a..b, f' x := by rw [hftc]; linarith
  have hcs := sq_integral_le hab hint hint2
  nlinarith [hD, hcs]

/-- The layer price is attained: the linear profile from `−η` to `η` on `[a, b]` has
`(b − a) ∫ |f'|² = 4η²`. -/
theorem layer_price_sharp {a b η : ℝ} (hab : a < b) :
    (b - a) * ∫ _ in a..b, (2 * η / (b - a)) ^ 2 = 4 * η ^ 2 := by
  rw [intervalIntegral.integral_const, smul_eq_mul]
  have : b - a ≠ 0 := (sub_pos.2 hab).ne'
  field_simp
  ring

end PVNP.SeparatorFrozen
