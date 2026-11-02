import PVNP.WCTPlaneWave
import PVNP.SATVerifier

/-!
# What a physical WCT computation model must charge (M1/M2 foundational audit)

A physical decision procedure consists of an **encoder** (input ↦ initial
field), a **physical evolution** (here: exact classical solutions of the frozen
WCT PDE `i∂ₜu = (Δ+κ)²u − β|u|²u + γ|u|⁴u`), and a **decoder** (final field ↦
bit).  This module proves, with the genuine PDE solutions of
`PVNP.WCTPlaneWave`, that the physical part of such a procedure can be made
*trivial* unless the encoder and decoder are charged:

* `device_physics`: the constant-amplitude device `u(t,x) = A e^{-iωt}` is an
  exact classical solution with mass `‖A‖²` on the unit torus, curvature energy
  `0`, and local readout `|u(t,x₀)| = ‖A‖` at every time.
* `unrestricted_encoder_trivializes`: if encoders are arbitrary functions, the
  constant-cost device decides **every** language (including undecidable
  ones): `PhysConst … Set.univ = Set.univ`.
* `unrestricted_decoder_trivializes`: with a fixed *injective* encoder, an
  arbitrary decoder of the local readout decides every language.
* `P_TM_subset_PhysConst`: if the encoder class contains the indicator maps of
  polynomial-time languages (any reasonable "polynomial-time encoder" does),
  then `P_TM ⊆ PhysConst` — with **constant** physical mass, zero curvature
  energy, two distinguishable final states and constant readout.
* `PhysConst_polyEnc_eq_P_TM`: for exactly that encoder class the physical
  class equals `P_TM` (a restricted two-way equivalence).
* `physical_SAT_lower_bound_is_classical`: consequently a proof that dense SAT
  is not decided by such devices would prove `P_TM ≠ NP_TM`.
* `two_states_suffice`: decision never needs more than two physically
  distinguishable final states, for any language.

Interpretation: physical lower bounds cannot come from the PDE resources of
this device class; all computational difficulty sits in the charged encoder.
A universal physical lower bound for SAT (M2) is therefore at least as hard as
classical `P ≠ NP` whenever polynomial-time encoders are admissible.
-/

namespace PVNP.PhysicalAudit

open PVNP.WCTPlaneWave PVNP.Discrete Complex Real MeasureTheory

/-- Frequency of the constant-amplitude (`k = 0`) exact solution. -/
noncomputable def omega0 (κ β γ : ℝ) (A : ℂ) : ℝ := (κ - 0 ^ 2) ^ 2 - β * ‖A‖ ^ 2 + γ * ‖A‖ ^ 4

/-- The constant-amplitude device field `u(t, x) = A e^{-iωt}`. -/
noncomputable def field (κ β γ : ℝ) (A : ℂ) (t : ℝ) : ℝ × ℝ → ℂ := wave A 0 (omega0 κ β γ A * t)

/-- Local readout at the origin. -/
noncomputable def readout (κ β γ : ℝ) (A : ℂ) (t : ℝ) : ℝ := ‖field κ β γ A t (0, 0)‖

theorem readout_eq (κ β γ : ℝ) (A : ℂ) (t : ℝ) : readout κ β γ A t = ‖A‖ := by
  simp [readout, field, norm_wave]

/-- **Physics of the constant device**: exact classical solution, mass `‖A‖²`
on the unit torus, zero curvature energy, at every time. -/
theorem device_physics (κ β γ : ℝ) (A : ℂ) :
    (∀ t x, I * dt (fun s => field κ β γ A s) t x =
      opK κ (field κ β γ A t) x
        - (β : ℂ) * ((‖field κ β γ A t x‖ ^ 2 : ℝ) : ℂ) * field κ β γ A t x
        + (γ : ℂ) * ((‖field κ β γ A t x‖ ^ 4 : ℝ) : ℂ) * field κ β γ A t x) ∧
    (∀ t, ∫ x in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, ‖field κ β γ A t x‖ ^ 2 = ‖A‖ ^ 2) ∧
    (∀ t, ∫ x in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, ‖lap (field κ β γ A t) x‖ ^ 2 = 0) := by
  refine ⟨fun t x => ?_, fun t => ?_, fun t => ?_⟩
  · exact plane_wave_solves A 0 κ β γ t x
  · rw [field, mass_box _ _ _ zero_le_one]; ring
  · rw [field, curvature_box _ _ _ zero_le_one]; ring

/-- Languages decided by constant-cost devices whose encoders lie in `Enc`:
amplitude of norm `≤ 1` (mass `≤ 1`), threshold readout at every time. -/
def PhysConst (κ β γ : ℝ) (Enc : Set (List Bool → ℂ)) : Set (Set (List Bool)) :=
  {L | ∃ A ∈ Enc, ∀ x, ‖A x‖ ≤ 1 ∧ ∀ t : ℝ, (1 / 2 < readout κ β γ (A x) t ↔ x ∈ L)}

open Classical in
/-- Indicator amplitude of a language. -/
noncomputable def indicatorAmp (L : Set (List Bool)) : List Bool → ℂ :=
  fun x => if x ∈ L then 1 else 0

theorem indicatorAmp_decides (κ β γ : ℝ) (L : Set (List Bool)) (x : List Bool) :
    ‖indicatorAmp L x‖ ≤ 1 ∧ ∀ t : ℝ, (1 / 2 < readout κ β γ (indicatorAmp L x) t ↔ x ∈ L) := by
  classical
  by_cases hx : x ∈ L
  · refine ⟨by simp [indicatorAmp, hx], fun t => ?_⟩
    rw [readout_eq]; simp [indicatorAmp, hx]; norm_num
  · refine ⟨by simp [indicatorAmp, hx], fun t => ?_⟩
    rw [readout_eq]; simp [indicatorAmp, hx]

/-- **Unrestricted encoders trivialize the model**: every language is decided
at constant physical cost. -/
theorem unrestricted_encoder_trivializes (κ β γ : ℝ) :
    PhysConst κ β γ Set.univ = Set.univ := by
  ext L
  simp only [Set.mem_univ, iff_true]
  exact ⟨indicatorAmp L, Set.mem_univ _, indicatorAmp_decides κ β γ L⟩

/-- An injective amplitude code of input strings, with values in `[0, 1)`. -/
noncomputable def codeAmp (x : List Bool) : ℂ :=
  (((Encodable.encode x : ℕ) : ℝ) / ((Encodable.encode x : ℕ) + 1) : ℝ)

theorem norm_codeAmp (x : List Bool) :
    ‖codeAmp x‖ = ((Encodable.encode x : ℕ) : ℝ) / ((Encodable.encode x : ℕ) + 1) := by
  rw [codeAmp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem codeAmp_norm_injective : Function.Injective fun x => ‖codeAmp x‖ := by
  intro x y h
  simp only [norm_codeAmp] at h
  have hx : (0 : ℝ) < (Encodable.encode x : ℕ) + 1 := by positivity
  have hy : (0 : ℝ) < (Encodable.encode y : ℕ) + 1 := by positivity
  rw [div_eq_div_iff hx.ne' hy.ne'] at h
  have : ((Encodable.encode x : ℕ) : ℝ) = (Encodable.encode y : ℕ) := by linarith
  exact Encodable.encode_injective (by exact_mod_cast this)

open Classical in
/-- **Unrestricted decoders trivialize the model**: with the fixed injective
encoder `codeAmp`, every language is decided by *some* decoder of the local
readout, at constant physical cost and at every time. -/
theorem unrestricted_decoder_trivializes (κ β γ : ℝ) (L : Set (List Bool)) :
    ∃ dec : ℝ → Bool, ∀ x t, ‖codeAmp x‖ ≤ 1 ∧ (dec (readout κ β γ (codeAmp x) t) = true ↔ x ∈ L) := by
  refine ⟨fun r => decide (∃ y ∈ L, ‖codeAmp y‖ = r), fun x t => ⟨?_, ?_⟩⟩
  · rw [norm_codeAmp, div_le_one (by positivity)]; linarith
  · rw [readout_eq]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rw [← codeAmp_norm_injective hxy]; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩

/-- **`P_TM` sits inside the physical class at constant physical cost**,
whenever encoders may compute a polynomial-time decision bit. -/
theorem P_TM_subset_PhysConst (κ β γ : ℝ) (Enc : Set (List Bool → ℂ))
    (hEnc : ∀ L ∈ P_TM, indicatorAmp L ∈ Enc) : P_TM ⊆ PhysConst κ β γ Enc :=
  fun L hL => ⟨indicatorAmp L, hEnc L hL, indicatorAmp_decides κ β γ L⟩

/-- Polynomial-time indicator encoders. -/
def polyEnc : Set (List Bool → ℂ) := {A | ∃ L ∈ P_TM, A = indicatorAmp L}

/-- **Restricted two-way equivalence**: with polynomial-time indicator encoders
the constant-cost physical class is exactly `P_TM`. -/
theorem PhysConst_polyEnc_eq_P_TM (κ β γ : ℝ) : PhysConst κ β γ polyEnc = P_TM := by
  classical
  ext L
  constructor
  · rintro ⟨A, ⟨L', hL', rfl⟩, hdec⟩
    have : L = L' := by
      ext x
      rw [← (hdec x).2 0, ← (indicatorAmp_decides κ β γ L' x).2 0]
    rw [this]; exact hL'
  · intro hL
    exact P_TM_subset_PhysConst κ β γ polyEnc (fun L hL => ⟨L, hL, rfl⟩) hL

/-- **M2 obstruction**: with any encoder class admitting polynomial-time
decision bits, a physical lower bound for dense SAT would prove `P_TM ≠ NP_TM`. -/
theorem physical_SAT_lower_bound_is_classical (κ β γ : ℝ) (Enc : Set (List Bool → ℂ))
    (hEnc : ∀ L ∈ P_TM, indicatorAmp L ∈ Enc)
    (hlb : PVNP.Discrete.SATV.SAT_dense ∉ PhysConst κ β γ Enc) : P_TM ≠ NP_TM := by
  intro h
  apply hlb
  apply P_TM_subset_PhysConst κ β γ Enc hEnc
  rw [h]; exact PVNP.Discrete.SATV.SAT_dense_mem_NP_TM

/-- **Two physically distinguishable final states suffice for every language**:
the final readouts of the indicator device take only the values `0` and `1`. -/
theorem two_states_suffice (κ β γ : ℝ) (L : Set (List Bool)) (t : ℝ) :
    ∀ x, readout κ β γ (indicatorAmp L x) t = 0 ∨ readout κ β γ (indicatorAmp L x) t = 1 := by
  classical
  intro x
  rw [readout_eq]
  by_cases hx : x ∈ L <;> simp [indicatorAmp, hx]

end PVNP.PhysicalAudit
