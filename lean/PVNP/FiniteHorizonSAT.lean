import PVNP.SATTarget
import PVNP.FiniteModification

/-! Part I takes an infimum over deciders separately at each input size. For
first-answer time a finite table defeats a superlinear bound with that order
of quantifiers. Its description size can depend on the horizon. -/

namespace PVNP.FiniteHorizon

open Discrete Discrete.Sweep PartIITuring CookLevin.Gen SATTarget CrossingSAT

/-- A globally correct machine can tabulate *all* words through a chosen length.
The same linear time bound works at every horizon; the finite control may grow. -/
theorem fast_through_horizon {L : Set (List Bool)} {M : TM} (hM : Correct M L) (N : ℕ) :
    ∃ D : TM, Correct D L ∧ ∀ x : List Bool, x.length ≤ N → ftime D x ≤ 2*x.length+5 := by
  classical
  let S := ofTM M
  let τ : List Bool → Bool := fun x => decide (x ∈ L)
  let P := fmProg S (N+1) τ
  have short (x : List Bool) (hx : x.length ≤ N) :
      FirstAnswer (P.toTM.out x) (2*x.length+5) (τ x) := by
    have hs := fm_short S (N+1) τ x (by omega)
    have cost := tripCost_le' P P.start (x.map P.lift)
    obtain ⟨t, ht, ha, hb⟩ := Prog.toTM_firstAnswer P x (.last hs)
    simp only [List.length_map] at cost
    exact ⟨t, by dsimp only at ht; omega, ha, hb⟩
  refine ⟨P.toTM, fun x => ?_, fun x hx => (ftime_spec (short x hx)).1⟩
  by_cases hx : x.length ≤ N
  · exact ⟨_, τ x, short x hx, by simp [τ]⟩
  · obtain ⟨B, hB⟩ := hM x
    obtain ⟨⟨t, _, hhalt⟩, hacc⟩ := OfTM.ofTM_decides M hB
    obtain ⟨cost,hc,_⟩ := fm_long S (N+1) τ x (by omega) hhalt
    exact ⟨cost+2, _, Prog.toTM_firstAnswer P x hc, by
      rw [decide_eq_true_iff, ← S.accepts_iff_of_firstHalt hhalt]; exact hacc⟩

/-- Even a witness chosen adversarially *after* seeing the decider cannot defeat
the tabulation inside a fixed finite ball. A single machine for all lengths is
the distinct quantifier order in the manuscript's SAT lower-bound target. -/
theorem no_common_hard_horizon {L : Set (List Bool)} {M : TM} (hM : Correct M L) (N : ℕ) :
    ¬ ∀ D : TM, Correct D L → ∃ x : List Bool, x.length ≤ N ∧ 2*N+5 < ftime D x := by
  obtain ⟨D,hD,hfast⟩ := fast_through_horizon hM N
  intro h
  obtain ⟨x,hx,ht⟩ := h D hD
  have := hfast x hx
  omega

end PVNP.FiniteHorizon
