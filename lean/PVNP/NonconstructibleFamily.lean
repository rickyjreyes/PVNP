import PVNP.DepthBarrier
import PVNP.PhysicalDiagonal
import PVNP.WCTSATScaling
import PVNP.ExpanderInterfaceBarrier

/-!
# I-2: what "a verifiable, non-constructible wavefield family" can mean

Part I, "Symbolic Separation Program": "Under one fixed preparation, verification and resource
model, there exists a coherent target state in `NP_st \ P_st`." The manuscript fixes neither the
notion of state nor the preparation model. In the repository's `ConstructionModel`
(`PartISeparation`) a model is a type of states, a type of constructors with a polynomial-time
predicate, a production relation and a verification predicate; `Pst` are the constructible
states and `NPst` the verifiable ones. This module settles every reading that the manuscript's
words allow.

**Reading A — explicit finite states** (`DepthBarrier.explicit_no_separation`, Phase XVIII):
false. Every finite word is written by a fixed machine in linear time.

**Reading B — input-indexed families with unrestricted verification**
(`unrestricted_family_separation`): true, but for a reason with no complexity content. A family
`x ↦ ψ_x ∈ {0, 1}` is constructible iff its language is in `P_TM` (`familyModel_Pst`), and a
diagonal language outside `P_TM` (`PhysicalAudit.diagonal_not_mem_P_TM`) is "verified" by the
trivial predicate.

**Reading C — NP-verified families** (`npFamily_separation_iff`): the verifiable families are the
languages with polynomial-size certificates (`NP_TM`), the constructible ones those decided in
polynomial time. Then `NPst \ Pst ≠ ∅ ⟺ P_TM ≠ NP_TM`, and dense SAT is a witness iff
`P_TM ≠ NP_TM` (`npFamily_SAT_iff`).

**Reading C on the frozen torus — physical wavefield families**
(`wavefield_separation_iff`): states are families of frozen-torus fields `x ↦ ψ_x`, a family is
constructible iff it is prepared by a charged zero-mode device of `WCTSATScaling` (polynomial-time
amplitude-bit machine, exact frozen evolution), and verifiable iff its amplitude-bit language has
polynomial-size certificates. Again `NPst \ Pst ≠ ∅ ⟺ P_TM ≠ NP_TM`.

So the conjecture is false (A), vacuous (B), or exactly the classical separation (C, also for
physical wavefield families). No reading gives an independent route to `P ≠ NP`.

**Cross-connection with I-16 and I-32** (`npFamily_iff_wccDepth`, `npFamily_iff_expanderGrowth`):
reading C of I-2 is equivalent to `conj:wcc_depth` (I-16) for dense SAT, and to the interface-growth
hypothesis `prop:locked-expander-full` (I-32) for dense SAT in the charged constant class.
-/

namespace PVNP.NonconstructibleFamily

open PVNP.Discrete PVNP.PartISeparation PVNP.WCTSATScaling PVNP.Torus PVNP.WCTSATDevice

/-! ### Reading B: input-indexed binary families -/

/-- Families `x ↦ ψ_x ∈ {0, 1}`, given by the set where `ψ_x = 1`. A constructor is named by
the family it outputs, and it is polynomial-time iff some Turing machine outputs `ψ_x` on input
`x` within a polynomial time bound, i.e. iff the family is in `P_TM`; verification is `V`. -/
def familyModel (V : Set (List Bool) → Prop) : ConstructionModel where
  State := Set (List Bool)
  Machine := Set (List Bool)
  polyTime := fun m => m ∈ P_TM
  produces := fun m S => m = S
  verifiable := V

/-- The constructible binary families are exactly the languages of `P_TM`. -/
theorem familyModel_Pst (V : Set (List Bool) → Prop) : (familyModel V).Pst = P_TM := by
  ext S
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hm
  · intro h
    exact ⟨S, h, rfl⟩

theorem familyModel_NPst (V : Set (List Bool) → Prop) : (familyModel V).NPst = {S | V S} := rfl

/-- **Reading B is vacuous.** With unrestricted verification the separation holds, witnessed by
a diagonal family; no NP structure or physics is involved. -/
theorem unrestricted_family_separation :
    PhysicalAudit.diagonalLanguage ∈
      (familyModel fun _ => True).NPst \ (familyModel fun _ => True).Pst := by
  refine ⟨trivial, ?_⟩
  rw [familyModel_Pst]
  exact PhysicalAudit.diagonal_not_mem_P_TM

/-! ### Reading C: NP-verified families -/

/-- Families whose `1`-instances have polynomial-size certificates. -/
def npFamilyModel : ConstructionModel := familyModel (· ∈ NP_TM)

/-- **Reading C is exactly `P_TM ≠ NP_TM`.** -/
theorem npFamily_separation_iff :
    (npFamilyModel.NPst \ npFamilyModel.Pst).Nonempty ↔ P_TM ≠ NP_TM := by
  have hP : npFamilyModel.Pst = P_TM := familyModel_Pst _
  have hNP : npFamilyModel.NPst = NP_TM := rfl
  rw [hP, hNP]
  constructor
  · rintro ⟨S, hS, hnot⟩ heq
    exact hnot (heq ▸ hS)
  · intro hne
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hempty
    exact hne (Set.Subset.antisymm P_TM_subset_NP_TM hempty)

/-- Dense SAT is a verifiable, non-constructible family iff `P_TM ≠ NP_TM`. -/
theorem npFamily_SAT_iff :
    SATV.SAT_dense ∈ npFamilyModel.NPst \ npFamilyModel.Pst ↔ P_TM ≠ NP_TM := by
  have hP : npFamilyModel.Pst = P_TM := familyModel_Pst _
  rw [hP]
  constructor
  · rintro ⟨-, hnot⟩
    exact CookLevin.Gen.satLowerBound_iff_P_ne_NP.1 hnot
  · intro hne
    exact ⟨SATV.SAT_dense_mem_NP_TM, CookLevin.Gen.satLowerBound_iff_P_ne_NP.2 hne⟩

/-! ### Reading C for physical wavefield families on the frozen torus -/

variable {L κ β γ : ℝ}

/-- The prepared amplitude of a charged zero-mode device with amplitude-bit language `A`. -/
noncomputable def ampOf (A : Set (List Bool)) (x : List Bool) : ℂ := by
  classical
  exact if x ∈ A then 2 else 1

/-- The wavefield family of an amplitude-bit language `S`: input `x` is the zero-mode
frozen-torus field of amplitude `2` if `x ∈ S` and `1` otherwise. -/
noncomputable def wavefield (L : ℝ) (S : Set (List Bool)) (x : List Bool) : ℓ2 :=
  mode L 0 (ampOf S x)

/-- Physical wavefield families. A state is a family of frozen-torus fields. A constructor is
named by the amplitude-bit language `A` of a charged zero-mode device of `WCTSATScaling` (a
polynomial-time machine deciding `A`, and the exact frozen evolution); it produces the family of
the device's prepared fields `zeroMode … (ampOf A x) 0`. A family is verifiable iff it is the
wavefield family of a language with polynomial-size certificates. -/
noncomputable def wavefieldModel (L κ β γ : ℝ) : ConstructionModel where
  State := List Bool → ℓ2
  Machine := Set (List Bool)
  polyTime := fun A => ∃ D : ZeroDev, D.A = A
  produces := fun A ψ => ∀ x, ψ x = zeroMode L κ β γ (ampOf A x) 0
  verifiable := fun ψ => ∃ S ∈ NP_TM, ψ = wavefield L S

theorem mode_zero_apply (L : ℝ) (c : ℂ) : (mode L 0 c : ℓ2) 0 = c := by
  simp [mode, lp.single_apply, wt_zero]

theorem zeroMode_zero (L κ β γ : ℝ) (c : ℂ) : zeroMode L κ β γ c 0 = mode L 0 c := by
  simp [zeroMode]

/-- The wavefield family determines its language. -/
theorem wavefield_injective {S T : Set (List Bool)} (h : wavefield L S = wavefield L T) :
    S = T := by
  classical
  ext x
  have h0 := congrArg (fun v : ℓ2 => v 0) (congrFun h x)
  simp only [wavefield, mode_zero_apply, ampOf] at h0
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp only [hS, hT, if_true, if_false] at h0 <;>
    first | exact iff_of_true hS hT | exact iff_of_false hS hT | norm_num at h0

/-- A wavefield family is physically constructible iff its language is in `P_TM`. -/
theorem wavefield_constructible_iff (S : Set (List Bool)) :
    wavefield L S ∈ (wavefieldModel L κ β γ).Pst ↔ S ∈ P_TM := by
  constructor
  · rintro ⟨A, ⟨D, hD⟩, hprod⟩
    have h : wavefield L S = wavefield L A := by
      funext x
      rw [hprod x, zeroMode_zero]
      rfl
    rw [wavefield_injective h, ← hD]
    exact ⟨D.M, D.p, D.hM⟩
  · rintro ⟨M, p, hM⟩
    refine ⟨S, ⟨⟨M, p, S, hM⟩, rfl⟩, fun x => ?_⟩
    rw [zeroMode_zero]
    rfl

/-- **Reading C for physical wavefield families is exactly `P_TM ≠ NP_TM`.** -/
theorem wavefield_separation_iff :
    ((wavefieldModel L κ β γ).NPst \ (wavefieldModel L κ β γ).Pst).Nonempty ↔
      P_TM ≠ NP_TM := by
  constructor
  · rintro ⟨ψ, ⟨S, hS, rfl⟩, hnot⟩ heq
    exact hnot ((wavefield_constructible_iff S).2 (heq ▸ hS))
  · intro hne
    obtain ⟨S, hS, hnot⟩ := (npFamily_separation_iff).2 hne
    refine ⟨wavefield L S, ⟨S, hS, rfl⟩, fun h => hnot ?_⟩
    have := (wavefield_constructible_iff (κ := κ) (β := β) (γ := γ) S).1 h
    have hP : npFamilyModel.Pst = P_TM := familyModel_Pst _
    rw [hP]
    exact this

/-! ### Cross-connection: I-2 (reading C), I-16 and I-32 coincide for dense SAT -/

/-- **I-2 ⟺ I-16.** The NP-verified family separation holds iff `conj:wcc_depth` holds for dense
SAT. -/
theorem npFamily_iff_wccDepth :
    (npFamilyModel.NPst \ npFamilyModel.Pst).Nonempty ↔ WCCDepth SATV.SAT_dense :=
  npFamily_separation_iff.trans DepthBarrier.wccDepth_SAT_iff.symm

/-- **I-2 ⟺ I-32 in the charged constant class.** -/
theorem npFamily_iff_expanderGrowth (κ β γ : ℝ) :
    (npFamilyModel.NPst \ npFamilyModel.Pst).Nonempty ↔
      ExpanderInterface.ExpanderGrowth (ExpanderInterface.ConstDecides κ β γ) (fun _ _ => 1)
        (ExpanderInterface.constTraj κ β γ) SATV.SAT_dense :=
  npFamily_separation_iff.trans (ExpanderInterface.expanderGrowth_SAT_iff κ β γ).symm

end PVNP.NonconstructibleFamily
