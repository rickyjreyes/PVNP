import PVNP.PhysicalModelAudit
import PVNP.MachineSerialization

/-!
# An exact unrestricted-encoder countermodel for the physical/classical bridge

The flat machine serialization theorem `P_TM_eq_tables` permits an explicit
diagonal language outside `P_TM` without using a separation hypothesis or a
computability assumption about its characteristic function.

The exact constant-amplitude WCT solution from `PhysicalModelAudit`, when
paired with *unrestricted* encoders, decides this diagonal language at constant
physical evolution cost. Thus that particular physical class is not `P_TM`.

This does **not** refute the manuscript's claim under charged polynomial-time
encoders, nor establish anything about the full continuum physical model.
In particular, this is not a proof of `P_TM ≠ NP_TM`.
-/

namespace PVNP.PhysicalAudit

open PVNP.Discrete

/-- A serializable table machine accepts an input at its *first* answer. -/
def tableFirstAccept (t : Table) (x : List Bool) : Prop :=
  ∃ T : ℕ, FirstAnswer ((TM.ofTable t).out x) T true

/-- The first answer cannot have two different values. -/
theorem firstAnswer_value_unique {out : ℕ → Option Bool} {T U : ℕ}
    {b c : Bool} (hb : FirstAnswer out T b) (hc : FirstAnswer out U c) : b = c := by
  obtain ⟨i, -, hi, hi0⟩ := hb
  obtain ⟨j, -, hj, hj0⟩ := hc
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hcontr := hj0 i hlt
    rw [hi] at hcontr
    cases hcontr
  · subst j
    exact Option.some.inj (hi.symm.trans hj)
  · have hcontr := hi0 j hgt
    rw [hj] at hcontr
    cases hcontr

/-- Every language decided by the table machine coincides with its
first-acceptance set, on each input. -/
theorem tableFirstAccept_iff_mem (t : Table) (L : Set (List Bool))
    (p : Polynomial ℕ)
    (h : (TM.ofTable t).Decides L (fun n => p.eval n))
    (x : List Bool) : tableFirstAccept t x ↔ x ∈ L := by
  obtain ⟨b, hb, hmem⟩ := h x
  constructor
  · rintro ⟨T, htrue⟩
    exact hmem.mp (firstAnswer_value_unique hb htrue)
  · intro hx
    have hbtrue : b = true := hmem.mpr hx
    subst b
    exact ⟨p.eval x.length, hb⟩

/-- Diagonalize against each finite table machine on its own canonical code.
Malformed codes do not enter this language. -/
def diagonalLanguage : Set (List Bool) :=
  {x | ∃ t : Table, decodeTable x = some t ∧ ¬ tableFirstAccept t x}

/-- At its own canonical code a table is diagonalized in the opposite
direction to its first-acceptance outcome. -/
theorem diagonal_on_code (t : Table) :
    encodeTable t ∈ diagonalLanguage ↔ ¬ tableFirstAccept t (encodeTable t) := by
  constructor
  · rintro ⟨u, hu, hnot⟩
    have htu : t = u := Option.some.inj ((encodeTable_decodeTable t).symm.trans hu)
    subst u
    exact hnot
  · intro h
    exact ⟨t, encodeTable_decodeTable t, h⟩

/-- An explicit language outside polynomial-time deterministic Turing computation.
This is a diagonal argument, *not* a separation of P and NP. -/
theorem diagonal_not_mem_P_TM : diagonalLanguage ∉ P_TM := by
  intro h
  rw [P_TM_eq_tables] at h
  obtain ⟨t, p, hdec⟩ := h
  have hcorrect :=
    tableFirstAccept_iff_mem t diagonalLanguage p hdec (encodeTable t)
  have hdiag := diagonal_on_code t
  by_cases ha : tableFirstAccept t (encodeTable t)
  · exact (hdiag.mp (hcorrect.mp ha)) ha
  · exact ha (hcorrect.mpr (hdiag.mpr ha))

/-- The same diagonal language is accepted by the exact constant-amplitude
physical solution when *arbitrary* input encoders are allowed. -/
theorem diagonal_mem_unrestricted_phys (κ β γ : ℝ) :
    diagonalLanguage ∈ PhysConst κ β γ Set.univ := by
  rw [unrestricted_encoder_trivializes]
  trivial

/-- I-11 scope test: unrestricted physical encoders cannot give an equality
with polynomial-time Turing languages, regardless of the PDE coefficients. -/
theorem unrestricted_phys_ne_P_TM (κ β γ : ℝ) :
    PhysConst κ β γ Set.univ ≠ P_TM := by
  intro he
  have hmem : diagonalLanguage ∈ P_TM := by
    rw [← he]
    exact diagonal_mem_unrestricted_phys κ β γ
  exact diagonal_not_mem_P_TM hmem

end PVNP.PhysicalAudit
