import PVNP.SATDynamicsObstruction

/-!
# Forced SAT escape has a positive peak-energy cost

Unlike the monotone trap theorem, these statements allow arbitrary continuous forcing,
energy oscillation and formula-dependent trajectories. They apply to the specified false
well, not to arbitrary preparations or all SAT algorithms. The energy is the dimensionless
sign-blind encoding energy; no identification with SI joules is made.
-/

namespace PVNP.SATDynamics
open PVNP.PartIPsiSat PVNP.InterwovenSAT PVNP.SATFalseWell

/-- Any continuous admissible trajectory staying strictly below the barrier remains trapped,
even when its energy is not monotone. The cap is needed only up to the specified horizon. -/
theorem energy_cap_trapped {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {Ψ : ℝ → ℕ → ℂ} (hadm : ∀ t, Admissible (Ψ t)) (hc0 : Continuous fun t => Ψ t 0)
    (hc1 : Continuous fun t => Ψ t 1) (hc2 : Continuous fun t => Ψ t 2)
    {T : ℝ} (hT : 0 ≤ T) (hb0 : InBox (Ψ 0))
    (hcap : ∀ t ∈ Set.Icc 0 T, energySB trapFormula lam mu (Ψ t) < 17 / 16) :
    InBox (Ψ T) ∧ 1 ≤ energySB trapFormula lam mu (Ψ T) := by
  have hE0 := hcap 0 ⟨le_rfl, hT⟩
  set s : ℕ → ℝ → ℝ := fun i t => (1 + (Ψ t i).re) / 2 with hs_def
  have hs : ∀ i t, sPos (phases (Ψ t)) i = s i t := fun i t => sPos_eq (hadm t) i
  have hsnn : ∀ i t, 0 ≤ s i t := fun i t => by rw [← hs]; exact sPos_nonneg _ i
  set m : ℝ → ℝ := fun t => max (max (s 0 t) (s 1 t)) (s 2 t) with hm_def
  have hcs : ∀ i, Continuous (fun t => Ψ t i) → Continuous (s i) := fun i h =>
    (continuous_const.add (Complex.continuous_re.comp h)).div_const 2
  have hmc : Continuous m := ((hcs 0 hc0).max (hcs 1 hc1)).max (hcs 2 hc2)
  have hbox_iff : ∀ t, InBox (Ψ t) ↔ m t ≤ 1 / 8 := fun t => by
    simp only [InBox, hs, hm_def, max_le_iff, and_assoc]
  have hlow : ∀ t, InBox (Ψ t) →
      1 + (s 0 t + s 1 t + s 2 t) / 2 ≤ energySB trapFormula lam mu (Ψ t) := fun t hb => by
    have h := energy_lower_in_box hlam hmu (hadm t) hb
    rwa [hs, hs, hs] at h
  have hm0 : m 0 < 1 / 8 := by
    have h := hlow 0 hb0
    have h0 := hsnn 0 0
    have h1 := hsnn 1 0
    have h2 := hsnn 2 0
    simp only [hm_def, max_lt_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith
  let t := T
  have ht : 0 ≤ t := hT
  have hmt : m t ≤ 1 / 8 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨τ, hτ, hmτ⟩ := intermediate_value_Icc ht hmc.continuousOn ⟨hm0.le, hgt.le⟩
    have hbτ : InBox (Ψ τ) := (hbox_iff τ).2 hmτ.le
    have hl := hlow τ hbτ
    have hsum : 1 / 8 ≤ s 0 τ + s 1 τ + s 2 τ := by
      rw [← hmτ]
      have h0 := hsnn 0 τ
      have h1 := hsnn 1 τ
      have h2 := hsnn 2 τ
      exact max_le (max_le (by linarith) (by linarith)) (by linarith)
    have hEτ := hcap τ hτ
    linarith
  have hb := (hbox_iff t).2 hmt
  refine ⟨hb, ?_⟩
  have := hlow t hb
  have h0 := hsnn 0 t
  have h1 := hsnn 1 t
  have h2 := hsnn 2 t
  linarith

/-- Successful readout from the false corner requires a peak at least `1/16` above its
initial energy, at some time no later than the readout. No monotonicity is assumed. -/
theorem readout_requires_energy_excursion {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {Ψ : ℝ → ℕ → ℂ} (hadm : ∀ t, Admissible (Ψ t))
    (hc : ∀ i, Continuous fun t => Ψ t i) {T : ℝ} (hT : 0 ≤ T)
    (h0 : Ψ 0 = fieldOf fun _ => false)
    (hread : energySB trapFormula lam mu (Ψ T) < 1 / 8) :
    ∃ t ∈ Set.Icc 0 T,
      1 / 16 ≤ energySB trapFormula lam mu (Ψ t) - energySB trapFormula lam mu (Ψ 0) := by
  by_contra hn
  push_neg at hn
  have hinit : energySB trapFormula lam mu (Ψ 0) = 1 := by
    rw [h0, false_corner_energy hlam hmu]
  have hcap : ∀ t ∈ Set.Icc 0 T, energySB trapFormula lam mu (Ψ t) < 17 / 16 := by
    intro t ht
    have h := hn t ht
    rw [hinit] at h
    linarith
  have hb0 : InBox (Ψ 0) := by rw [h0]; exact false_corner_in_box
  have h := (energy_cap_trapped hlam hmu hadm (hc 0) (hc 1) (hc 2) hT hb0 hcap).2
  linarith

/-- A certified upper bound on injected peak energy below `1/16` excludes successful readout.
This is a limitation of a precisely specified forced extension of energy descent. -/
theorem bounded_forcing_cannot_readout {lam mu budget : ℝ}
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hbudget : budget < 1 / 16)
    {Ψ : ℝ → ℕ → ℂ} (hadm : ∀ t, Admissible (Ψ t))
    (hc : ∀ i, Continuous fun t => Ψ t i) {T : ℝ} (hT : 0 ≤ T)
    (h0 : Ψ 0 = fieldOf fun _ => false)
    (hwork : ∀ t ∈ Set.Icc 0 T,
      energySB trapFormula lam mu (Ψ t) - energySB trapFormula lam mu (Ψ 0) ≤ budget) :
    ¬ energySB trapFormula lam mu (Ψ T) < 1 / 8 := by
  intro hread
  obtain ⟨t, ht, he⟩ := readout_requires_energy_excursion hlam hmu hadm hc hT h0 hread
  have := hwork t ht
  linarith

/-- The forced-escape cost is not special to the all-false preparation: every fixed corner
has a satisfiable polarity-flipped instance with the same necessary energy excursion. -/
theorem every_corner_requires_excursion (a : ℕ → Bool) {lam mu : ℝ}
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    ∃ F, Sat F ∧ ∀ Ψ : ℝ → ℕ → ℂ, (∀ t, Admissible (Ψ t)) →
      (∀ i, Continuous fun t => Ψ t i) → Ψ 0 = fieldOf a →
      ∀ T, 0 ≤ T → energySB F lam mu (Ψ T) < 1 / 8 →
        ∃ t ∈ Set.Icc 0 T, 1 / 16 ≤ energySB F lam mu (Ψ t) - energySB F lam mu (Ψ 0) := by
  refine ⟨flipF a trapFormula, (sat_flipF a _).2 trapFormula_sat, ?_⟩
  intro Ψ hadm hc h0 T hT hread
  let Φ : ℝ → ℕ → ℂ := fun t => flipField a (Ψ t)
  have hE : ∀ t, energySB trapFormula lam mu (Φ t) =
      energySB (flipF a trapFormula) lam mu (Ψ t) := by
    intro t
    have h := energySB_flip (a := a) (admissible_flipField (a := a) (hadm t)) trapFormula lam mu
    rw [flipField_flipField] at h
    exact h.symm
  have hΦc : ∀ i, Continuous fun t => Φ t i := by
    intro i
    simp only [Φ, flipField]
    split_ifs
    · exact (hc i).neg
    · exact hc i
  have hΦ0 : Φ 0 = fieldOf fun _ => false := by
    change flipField a (Ψ 0) = _
    rw [h0, ← flipField_false_corner a, flipField_flipField]
  obtain ⟨t, ht, he⟩ := readout_requires_energy_excursion hlam hmu
    (fun t => admissible_flipField (a := a) (hadm t)) hΦc hT hΦ0 (by rwa [hE])
  exact ⟨t, ht, by simpa only [hE] using he⟩

end PVNP.SATDynamics
