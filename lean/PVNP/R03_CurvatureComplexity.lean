import PVNP.PartI

/-! R03 (DOI 10.5281/zenodo.17743607).
Logical consequences of the exact Boolean CNF semantics and separation
premises. Does not prove a universal curvature lower bound or P ≠ NP. -/
namespace PVNP.R03

theorem unsatisfied_clause_has_penalty (a b c : Bool)
    (h : PVNP.PartI.clauseTrue a b c = false) :
    PVNP.PartI.clausePenalty a b c = true :=
  (PVNP.PartI.penalty_one_iff_clause_false a b c).2 h

theorem equality_precludes_separation_witness
    {Language : Type*} (P NP : Set Language) (he : P = NP) :
    ¬ ∃ L, L ∈ NP ∧ L ∉ P := by
  rintro ⟨L, hNP, hNotP⟩
  rw [← he] at hNP
  exact hNotP hNP

end PVNP.R03
