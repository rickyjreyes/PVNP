import PVNP.PartISeparation
import PVNP.PartIIUniformEquiv
import PVNP.CookLevinUniform
import PVNP.TwoPhaseFixedWord

/-!
# I-16 and I-2: what the two separation conjectures amount to

## I-16, `conj:wcc_depth`

`PartISeparation.WCCDepth_iff_not_P_TM` already shows that the conjecture for a language `L` is
exactly `L ∉ P_TM`. With the uniform Cook–Levin theorem
(`CookLevin.Gen.satLowerBound_iff_P_ne_NP`) this becomes, for dense SAT:

* `wccDepth_SAT_iff`: `WCCDepth SAT_dense ↔ P_TM ≠ NP_TM` (one-dimensional radius-one model);
* `wccdDepth_SAT_iff`: the same on `ℤ^(1+d)` for every `d`;
* `uniform_depth_SAT_iff`: the same for the uniform model of `def:wcc_machine`.

So I-16 is the classical P versus NP question in each discrete model. It is not decided here.

## I-2, the Symbolic Separation Program

The conjecture asks for "a coherent target state in `NP_st \ P_st`" under one fixed preparation,
verification and resource model. If states are explicit finite descriptions and constructors are
machines of `def:tm` started on a trivial input, the conjecture is false whatever the verifier:
`TwoPhaseFixedWord.literalMTM` writes any fixed word `s` in `|s| + 1` transitions, independently
of the input (`explicit_state_constructible`). In the construction model `explicitModel V`,
`NPst \ Pst = ∅` for every verification predicate `V` (`explicit_no_separation`). This is the
construction-side companion of I-20's size obstruction `K_D(s) ≤ |s| + c`.

A non-trivial reading needs a different notion of state (families indexed by the input length,
or physical fields with a specified preparation model); the manuscript does not fix one.
-/

namespace PVNP.DepthBarrier

open PVNP.Discrete PVNP.PartISeparation PVNP.PartIITuring PVNP.PartIIUniform

/-! ## I-16 -/

/-- **I-16 for dense SAT is exactly `P_TM ≠ NP_TM`.** -/
theorem wccDepth_SAT_iff : WCCDepth SATV.SAT_dense ↔ P_TM ≠ NP_TM :=
  (WCCDepth_iff_not_P_TM _).trans CookLevin.Gen.satLowerBound_iff_P_ne_NP

/-- The same on the lattice `ℤ^(1+d)`. -/
theorem wccdDepth_SAT_iff (d : ℕ) : WCCDDepth d SATV.SAT_dense ↔ P_TM ≠ NP_TM :=
  (WCCDDepth_iff_not_P_TM d _).trans CookLevin.Gen.satLowerBound_iff_P_ne_NP

/-- The same for the uniform model of `def:wcc_machine`: no uniform discrete WCC machine decides
dense SAT in polynomial time iff `P_TM ≠ NP_TM`. -/
theorem uniform_depth_SAT_iff : SATV.SAT_dense ∉ P_disc ↔ P_TM ≠ NP_TM := by
  rw [P_disc_eq_P_TM]
  exact CookLevin.Gen.satLowerBound_iff_P_ne_NP

/-! ## I-2 in the explicit-state reading -/

/-- Every explicit state is written by a fixed machine in linear time, on every input. -/
theorem explicit_state_constructible (s : List Bool) :
    ∃ M : MTM, ∀ z : List Bool, M.Outputs z s (s.length + 1) :=
  ⟨TwoPhaseFixedWord.literalMTM s, fun z => TwoPhaseFixedWord.literalMTM_outputs s z⟩

/-- The construction model of explicit states. A state is a word. A constructor is named by the
word `w` it hard-codes and is the machine `literalMTM w` of `def:tm`; it produces `s` if it writes
`s` on the trivial (empty) input within `|s| + 1` transitions. Verification is any predicate `V`.
Restricting the constructors to literal writers only makes `Pst` smaller, so the conclusion below
holds for every larger class of polynomial-time constructors. -/
def explicitModel (V : List Bool → Prop) : ConstructionModel where
  State := List Bool
  Machine := List Bool
  polyTime := fun _ => True
  produces := fun w s => (TwoPhaseFixedWord.literalMTM w).Outputs [] s (s.length + 1)
  verifiable := V

/-- A construction model in which every state has a polynomial-time constructor has no
separation. -/
theorem no_separation_of_all_constructible (M : ConstructionModel)
    (h : ∀ ψ, ∃ m, M.polyTime m ∧ M.produces m ψ) : M.NPst \ M.Pst = ∅ := by
  ext ψ
  simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  exact fun _ => h ψ

/-- **The explicit-state reading of I-2 is false:** every state is constructible, so
`NPst \ Pst` is empty for every verification predicate. -/
theorem explicit_no_separation (V : List Bool → Prop) :
    (explicitModel V).NPst \ (explicitModel V).Pst = ∅ :=
  no_separation_of_all_constructible _ fun s =>
    ⟨s, trivial, TwoPhaseFixedWord.literalMTM_outputs s []⟩

end PVNP.DepthBarrier
