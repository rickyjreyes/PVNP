import PVNP.SeparatorFrozen
import PVNP.PhysicalModelAudit
import PVNP.CookLevinUniform

/-!
# I-32: encoding-uniform expander interface growth is as hard as `P_TM ≠ NP_TM`

Part I, Hypothesis `prop:locked-expander-full`:

> For every permitted decider and encoding of a hard-instance family, there is a worst-case input
> whose required field trajectory incurs separator measure at least `c₀ 2^{γn}` with constants
> independent of the algorithm.

The separator measure of a field is the Euclidean length of its decision interface
`∂{Re ψ > 0}` in the fundamental domain (`sep`, the same measure as in `SeparatorFrozen`).
`ExpanderGrowth` states the hypothesis for a class of devices in its weakest form: the bound is
required only for infinitely many input lengths.

The frozen model contains the charged constant devices of `PhysicalAudit`: amplitude
`A(x) ∈ {0, 1}` given by a polynomial-time indicator, evolving as the exact solution
`A e^{-iωt}`. Their fields are constant in space, so their separator measure is `0` at every
time (`sep_const`). Consequently:

* `expanderGrowth_const_iff`: for the class of charged constant devices,
  `ExpanderGrowth Lang ↔ Lang ∉ P_TM`, for every language.
* `expanderGrowth_SAT_iff`: for dense SAT, `ExpanderGrowth ↔ P_TM ≠ NP_TM` (uniform Cook–Levin).
* `expanderGrowth_implies_P_ne_NP`: for **any** device class that contains the charged constant
  devices, `ExpanderGrowth SAT_dense → P_TM ≠ NP_TM`.
* `expanderGrowth_false_of_mem_P`: for every language in `P_TM` the hypothesis fails. A
  "hard-instance family" whose language is polynomial-time decidable cannot satisfy it.

So the hypothesis cannot be proved without proving `P_TM ≠ NP_TM`, and in the charged constant
model it cannot be refuted without proving `P_TM = NP_TM`. This does not decide it.
-/

namespace PVNP.ExpanderInterface

open PVNP.SeparatorFrozen PVNP.PhysicalAudit PVNP.WCTPlaneWave PVNP.Discrete MeasureTheory
open scoped ENNReal

/-- Separator measure of a field on the torus of side `L`: the Euclidean length of its decision
interface in the fundamental domain. -/
noncomputable def sep (L : ℝ) (ψ : ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  μH[1] (toE '' (frontier (region ψ) ∩ box L))

/-- **Hypothesis `prop:locked-expander-full`** for a device class, in its weakest form: there are
`c₀, γ > 0` such that every device deciding `Lang` has, beyond every length `N`, an input `x` and
a time `t` at which its field has separator measure at least `c₀ 2^{γ|x|}`. -/
def ExpanderGrowth {Dev : Type*} (Decides : Dev → Set (List Bool) → Prop) (side : Dev → ℕ → ℝ)
    (traj : Dev → List Bool → ℝ → ℝ × ℝ → ℂ) (Lang : Set (List Bool)) : Prop :=
  ∃ c₀ > 0, ∃ γ > 0, ∀ D, Decides D Lang → ∀ N : ℕ, ∃ x : List Bool, N ≤ x.length ∧
    ∃ t : ℝ, ENNReal.ofReal (c₀ * 2 ^ (γ * x.length)) ≤ sep (side D x.length) (traj D x t)

/-- The form with a worst-case input at every length implies the weak form. -/
theorem expanderGrowth_of_every_length {Dev : Type*} {Decides : Dev → Set (List Bool) → Prop}
    {side : Dev → ℕ → ℝ} {traj : Dev → List Bool → ℝ → ℝ × ℝ → ℂ} {Lang : Set (List Bool)}
    (h : ∃ c₀ > 0, ∃ γ > 0, ∀ D, Decides D Lang → ∀ n : ℕ, ∃ x : List Bool, x.length = n ∧
      ∃ t : ℝ, ENNReal.ofReal (c₀ * 2 ^ (γ * x.length)) ≤ sep (side D x.length) (traj D x t)) :
    ExpanderGrowth Decides side traj Lang := by
  obtain ⟨c₀, hc₀, γ, hγ, h⟩ := h
  refine ⟨c₀, hc₀, γ, hγ, fun D hD N => ?_⟩
  obtain ⟨x, hx, t, ht⟩ := h D hD N
  exact ⟨x, hx.ge, t, ht⟩

/-! ## Spatially constant fields have no interface -/

theorem sep_of_const (L : ℝ) {ψ : ℝ × ℝ → ℂ} (hψ : ∀ x y, ψ x = ψ y) : sep L ψ = 0 := by
  have hreg : region ψ = Set.univ ∨ region ψ = ∅ := by
    by_cases h : 0 < (ψ (0, 0)).re
    · left
      ext x
      simp only [region, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rwa [hψ x (0, 0)]
    · right
      ext x
      simp only [region, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rwa [hψ x (0, 0)]
  have hfr : frontier (region ψ) = ∅ := by
    rcases hreg with h | h <;> rw [h]
    · exact frontier_univ
    · exact frontier_empty
  simp [sep, hfr]

/-- The field of a charged constant device is spatially constant. -/
theorem field_const (κ β γ : ℝ) (A : ℂ) (t : ℝ) (x y : ℝ × ℝ) :
    field κ β γ A t x = field κ β γ A t y := by
  simp [PhysicalAudit.field, wave]

/-- **Constant devices have separator measure `0`** at every time and on every torus. -/
theorem sep_const (κ β γ L : ℝ) (A : ℂ) (t : ℝ) : sep L (field κ β γ A t) = 0 :=
  sep_of_const L (field_const κ β γ A t)

/-! ## The charged constant-device class -/

/-- A charged constant device decides `Lang`: its amplitude encoder is a polynomial-time
indicator, the amplitude has norm at most `1`, and the threshold readout gives the answer at
every time (`PhysicalAudit.PhysConst`). -/
def ConstDecides (κ β γ : ℝ) (A : List Bool → ℂ) (Lang : Set (List Bool)) : Prop :=
  A ∈ polyEnc ∧ ∀ x, ‖A x‖ ≤ 1 ∧ ∀ t : ℝ, (1 / 2 < readout κ β γ (A x) t ↔ x ∈ Lang)

/-- The fields of the constant device class, on the unit torus. -/
noncomputable def constTraj (κ β γ : ℝ) (A : List Bool → ℂ) (x : List Bool) (t : ℝ) :
    ℝ × ℝ → ℂ :=
  field κ β γ (A x) t

theorem constDecides_mem_P_TM {κ β γ : ℝ} {A : List Bool → ℂ} {Lang : Set (List Bool)}
    (h : ConstDecides κ β γ A Lang) : Lang ∈ P_TM := by
  rw [← PhysConst_polyEnc_eq_P_TM κ β γ]
  exact ⟨A, h.1, h.2⟩

theorem indicator_constDecides (κ β γ : ℝ) {Lang : Set (List Bool)} (h : Lang ∈ P_TM) :
    ConstDecides κ β γ (indicatorAmp Lang) Lang :=
  ⟨⟨Lang, h, rfl⟩, indicatorAmp_decides κ β γ Lang⟩

/-- **The hypothesis for the charged constant class is exactly `Lang ∉ P_TM`.** -/
theorem expanderGrowth_const_iff (κ β γ : ℝ) (Lang : Set (List Bool)) :
    ExpanderGrowth (ConstDecides κ β γ) (fun _ _ => 1) (constTraj κ β γ) Lang ↔ Lang ∉ P_TM := by
  constructor
  · rintro ⟨c₀, hc₀, γ', -, hgrow⟩ hP
    obtain ⟨x, -, t, ht⟩ := hgrow _ (indicator_constDecides κ β γ hP) 0
    rw [constTraj, sep_const] at ht
    have hpos : 0 < c₀ * 2 ^ (γ' * x.length) := by positivity
    exact absurd ht (not_le.2 (ENNReal.ofReal_pos.2 hpos))
  · intro hP
    exact ⟨1, one_pos, 1, one_pos, fun A hA => absurd (constDecides_mem_P_TM hA) hP⟩

/-- For every language in `P_TM` the hypothesis fails in the charged constant class. -/
theorem expanderGrowth_false_of_mem_P (κ β γ : ℝ) {Lang : Set (List Bool)} (h : Lang ∈ P_TM) :
    ¬ ExpanderGrowth (ConstDecides κ β γ) (fun _ _ => 1) (constTraj κ β γ) Lang :=
  fun hg => (expanderGrowth_const_iff κ β γ Lang).1 hg h

/-- **For dense SAT, the hypothesis in the charged constant class is equivalent to
`P_TM ≠ NP_TM`.** -/
theorem expanderGrowth_SAT_iff (κ β γ : ℝ) :
    ExpanderGrowth (ConstDecides κ β γ) (fun _ _ => 1) (constTraj κ β γ) SATV.SAT_dense ↔
      P_TM ≠ NP_TM :=
  (expanderGrowth_const_iff κ β γ _).trans CookLevin.Gen.satLowerBound_iff_P_ne_NP

/-- **In any device class containing the charged constant devices, the hypothesis for dense SAT
implies `P_TM ≠ NP_TM`.** The class is given by an embedding `ι` of the constant devices that
preserves what they decide and their (zero) separator measure. -/
theorem expanderGrowth_implies_P_ne_NP {Dev : Type*} {Decides : Dev → Set (List Bool) → Prop}
    {side : Dev → ℕ → ℝ} {traj : Dev → List Bool → ℝ → ℝ × ℝ → ℂ} (κ β γ : ℝ)
    (ι : (List Bool → ℂ) → Dev)
    (hdec : ∀ A Lang, ConstDecides κ β γ A Lang → Decides (ι A) Lang)
    (hsep : ∀ A x t, sep (side (ι A) x.length) (traj (ι A) x t) = 0)
    (h : ExpanderGrowth Decides side traj SATV.SAT_dense) : P_TM ≠ NP_TM := by
  rw [← CookLevin.Gen.satLowerBound_iff_P_ne_NP]
  intro hP
  obtain ⟨c₀, hc₀, γ', -, hgrow⟩ := h
  obtain ⟨x, -, t, ht⟩ := hgrow _ (hdec _ _ (indicator_constDecides κ β γ hP)) 0
  rw [hsep] at ht
  have hpos : 0 < c₀ * 2 ^ (γ' * x.length) := by positivity
  exact absurd ht (not_le.2 (ENNReal.ofReal_pos.2 hpos))

end PVNP.ExpanderInterface
