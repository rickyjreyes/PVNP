import PVNP.TMtoWCC
import PVNP.WCCtoTM

/-!
# `P_WCC = P_TM` and `NP_WCC = NP_TM` (issue #11 completion gate)

Both inclusions are derived from the explicit simulations:

* `PVNP.Discrete.P_TM_subset_P_WCC` (real time, `PVNP/TMtoWCC.lean`);
* `PVNP.Discrete.P_WCC_subset_P_TM` (time `1 + (p+1)(n + 2p + 5)`,
  `PVNP/WCCtoTM.lean`).

No class relationship is assumed anywhere.  NP in both models is defined by
polynomial-time verifiers *in that model*, with an explicit witness-length
polynomial `q` and the fixed self-delimiting pairing `PVNP.Discrete.pair`.

Scope: these are equalities between *discrete* language classes.  They say
nothing about physical curvature, energy or PDE resources; in particular they
do not decide `P_TM = NP_TM`.  Their consequence for the program is the
transfer theorem `p_vs_np_discrete_transfer`: the discrete WCC P-vs-NP question
is *literally the classical one*.
-/

namespace PVNP.Discrete

/-- **Discrete deterministic class equivalence.** -/
theorem P_WCC_eq_P_TM : P_WCC = P_TM :=
  Set.Subset.antisymm P_WCC_subset_P_TM P_TM_subset_P_WCC

/-- **Discrete verifier-class equivalence**, with identical witness bounds. -/
theorem NP_WCC_eq_NP_TM : NP_WCC = NP_TM := by
  simp only [NP_WCC, NP_TM, P_WCC_eq_P_TM]

/-- Every language in `P` is in `NP` (empty witness), in both models. -/
theorem P_subset_NPOf (C : Set (Set (List Bool)))
    (hC : ∀ L ∈ C, {y | ∃ x w, y = pair x w ∧ x ∈ L} ∈ C) : C ⊆ NPOf C := by
  intro L hL
  refine ⟨_, hC L hL, 0, fun x => ⟨fun hx => ⟨[], by simp, x, [], rfl, hx⟩, ?_⟩⟩
  rintro ⟨w, -, x', w', hp, hx'⟩
  rw [(pair_injective hp).1]; exact hx'

/-- **Transfer theorem.** The discrete WCC P-vs-NP question coincides with the
classical one: neither can be resolved without resolving the other. -/
theorem p_vs_np_discrete_transfer : (P_WCC = NP_WCC) ↔ (P_TM = NP_TM) := by
  rw [P_WCC_eq_P_TM, NP_WCC_eq_NP_TM]

/-- Any superpolynomial *time* lower bound for a language in the discrete WCC
model is a classical TM lower bound for the same language, and conversely. -/
theorem lower_bound_transfer (L : Set (List Bool)) : L ∉ P_WCC ↔ L ∉ P_TM := by
  rw [P_WCC_eq_P_TM]

/-- Explicit polynomial overheads, recorded as a single statement. -/
theorem explicit_simulations :
    (∀ (M : TM) (L : Set (List Bool)) (T : ℕ → ℕ), M.Decides L T → M.toWCC.Decides L T) ∧
    (∀ (A : WCC) (L : Set (List Bool)) (T : ℕ → ℕ), A.Decides L T →
      A.toTM.Decides L (fun n => 1 + (T n + 1) * (n + 2 * T n + 5))) :=
  ⟨fun M _ _ h => M.toWCC_decides h, fun A _ _ h => A.toTM_decides h⟩

end PVNP.Discrete
