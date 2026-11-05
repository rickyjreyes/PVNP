import PVNP.PartISeparation
import PVNP.PhysicalModelAudit

/-!
# WCT/PVNP: minimal physical-to-classical dependency contract

This module isolates the exact logical dependencies from Part I, without
asserting a WCT-specific physical statement as an axiom.

1. A single direction of the simulation bridge, P_TM ⊆ P_phys, plus
   an all-decider resource barrier for SAT_dense implies P_TM ≠ NP_TM.
2. A charged interface price and a uniform all-decider interface-growth
   theorem imply that physical barrier provided the required lower bound
   eventually dominates every polynomial.
3. For the constant-amplitude exact PDE solutions with indicator encoders,
   physical SAT exclusion is exactly classical SAT exclusion.

The hard geometric growth and polynomial-time, fixed-model TM realization
are OPEN mathematical premises, not consequences of WCT's five foundational
postulates, lattice conservation, or experiment.
-/

namespace PVNP.WCTDependencyClosure

open PVNP.Discrete PVNP.PartISeparation

/-- One direction of computational completeness suffices for the classical
bridge: P_TM ⊆ P_phys and a physical barrier for SAT_dense imply P ≠ NP.
The assumptions remain substantive and are not proved in this declaration. -/
theorem physical_hardness_plus_TM_realization (S : PhysSemantics)
    (hrealize : P_TM ⊆ S.Pphys)
    (hbarrier : S.Hard SATV.SAT_dense) :
    P_TM ≠ NP_TM := by
  intro hcollapse
  have hSATtm : SATV.SAT_dense ∈ P_TM := by
    rw [hcollapse]
    exact SATV.SAT_dense_mem_NP_TM
  have hSATphys : SATV.SAT_dense ∈ S.Pphys := hrealize hSATtm
  exact S.not_mem_Pphys_of_hard SATV.SAT_dense hbarrier hSATphys

/-- Quantifier-faithful interface-to-resource theorem.

The area function represents the charged interface measure for a decider
and input, expressed in integral physical resource units. The chosen
resource rail r must pay at least κ * area. For every correct decider,
there are arbitrarily large hard-input lengths whose interface exceeds
B(input length). The growth condition must dominate all polynomial
resource bounds *eventually*.

These are mathematical premises: this theorem does not derive the
interface inequality or algorithm-independent growth from the WCT PDE. -/
theorem interface_growth_implies_hardness
    (S : PhysSemantics) (r : S.Res)
    (κ : ℕ) (B : ℕ → ℕ)
    (area : S.Dec → List Bool → ℕ)
    (hprice : ∀ D x, S.decides D SATV.SAT_dense →
      κ * area D x ≤ S.cost D r x)
    (hinterfaces : ∀ D, S.decides D SATV.SAT_dense →
      ∀ N : ℕ, ∃ x : List Bool, N ≤ x.length ∧ B x.length ≤ area D x)
    (hdom : ∀ p : Polynomial ℕ, ∃ threshold : ℕ,
      ∀ n, threshold ≤ n → p.eval n < κ * B n) :
    S.Hard SATV.SAT_dense := by
  intro D hD p N
  obtain ⟨threshold, hlarge⟩ := hdom (p r)
  obtain ⟨x, hx, harea⟩ := hinterfaces D hD (max N threshold)
  refine ⟨x, le_trans (le_max_left _ _) hx, r, ?_⟩
  have hp : κ * area D x ≤ S.cost D r x := hprice D x hD
  have hq : (p r).eval x.length < κ * B x.length :=
    hlarge _ (le_trans (le_max_right _ _) hx)
  have hg : κ * B x.length ≤ κ * area D x :=
    Nat.mul_le_mul_left κ harea
  exact lt_of_lt_of_le hq (le_trans hg hp)

/-- Conditional composition of the actual interface growth and
physical-realization obligations. -/
theorem full_interface_route
    (S : PhysSemantics) (r : S.Res) (κ : ℕ) (B : ℕ → ℕ)
    (area : S.Dec → List Bool → ℕ)
    (hrealize : P_TM ⊆ S.Pphys)
    (hprice : ∀ D x, S.decides D SATV.SAT_dense →
      κ * area D x ≤ S.cost D r x)
    (hinterfaces : ∀ D, S.decides D SATV.SAT_dense →
      ∀ N : ℕ, ∃ x : List Bool, N ≤ x.length ∧ B x.length ≤ area D x)
    (hdom : ∀ p : Polynomial ℕ, ∃ threshold : ℕ,
      ∀ n, threshold ≤ n → p.eval n < κ * B n) :
    P_TM ≠ NP_TM := by
  exact physical_hardness_plus_TM_realization S hrealize
    (interface_growth_implies_hardness S r κ B area hprice hinterfaces hdom)

/-- Under P_TM = NP_TM, a model containing all P_TM languages cannot
also have a universal SAT resource barrier. -/
theorem no_route_under_classical_collapse (S : PhysSemantics)
    (hcollapse : P_TM = NP_TM) :
    ¬ (P_TM ⊆ S.Pphys ∧ S.Hard SATV.SAT_dense) := by
  rintro ⟨hrealize, hbarrier⟩
  exact (physical_hardness_plus_TM_realization S hrealize hbarrier) hcollapse

/-- For actual constant-amplitude solutions of the frozen Hamiltonian PDE
with polynomial-time indicator encoders, SAT exclusion from the physical
class is equivalent to SAT exclusion from P_TM. -/
theorem indicator_physical_barrier_iff_TM (κ β γ : ℝ) :
    SATV.SAT_dense ∉ PhysicalAudit.PhysConst κ β γ PhysicalAudit.polyEnc ↔
      SATV.SAT_dense ∉ P_TM := by
  rw [PhysicalAudit.PhysConst_polyEnc_eq_P_TM]

end PVNP.WCTDependencyClosure
