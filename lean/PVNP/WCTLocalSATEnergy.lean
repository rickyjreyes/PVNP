import PVNP.MultiStageCausality
import PVNP.InterwovenSAT

/-!
# WCT sign-blind SAT energy: a charged finite-propagation obstruction

This module links two existing, independently formalized facts:

1. `InterwovenSAT.sat_iff_energySB_lt_eighth` proves the exact SAT / low
   sign-blind-energy correspondence with a uniform 1/8 gap.
2. `MultiStageCausality.multistage_required_coverage_for_bit` proves that
   any finite list of charged local preprocessing/computation stages must
   propagate information from a distal input bit into a prefix decoder.

The small CNF family below has SAT truth value equal to a selected raw
input bit. Consequently any such *local physical pipeline*, deciding
whether the family's sign-blind energy is below 1/8 or its ground energy
is zero, requires that bit to lie in the cumulative causal cone:

    j.val < totalReach stages + m.

Every stage's radius and running time is explicitly counted. The decoder
sees only the first m sites, and the input is the raw spatial configuration.

IMPORTANT LIMITATIONS:
* This is a linear locality/latency obstruction for a two-formula family,
  not a superpolynomial SAT bound.
* `distalFormula` is a semantic mapping from one selected bit to a CNF;
  no physical zero-cost construction of that CNF at the decoder is assumed.
* An encoder that rearranges the input nonlocally or knows SAT in advance
  is not represented by these charged finite-radius stages.
* The logical energy is the finite interwoven configuration-space energy,
  not the frozen PDE's Hamiltonian. No new PDE-to-logic equivalence is claimed.
* Neither physical WCT P ≠ NP nor classical P ≠ NP is proved.
-/

namespace PVNP.WCTLocalSATEnergy

open PVNP.PartII PVNP.PartIPsiSat PVNP.InterwovenSAT
open PVNP.RadiusCausality PVNP.MultiStageCausality

/-! ### A concrete SAT family with one distinguished source bit -/

/-- Two fixed 3-CNF formulas. `Fxor` is satisfiable; `G` is not.
The input bit selects which formula's SAT value is queried. -/
def distalFormula (b : Bool) : CNF3 :=
  if b then Fxor else G

/-- Exact Boolean semantics of the two-formula family. -/
theorem distalFormula_sat_iff (b : Bool) :
    Sat (distalFormula b) ↔ b = true := by
  cases b <;> simp [distalFormula, Fxor_sat, G_unsat]

/-- The threshold for the sign-blind WCT energy reproduces the source bit,
for arbitrary nonnegative coupling and curvature coefficients. -/
theorem distalFormula_energy_gap_iff (b : Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    (∃ Ψ : ℕ → ℂ,
      Admissible Ψ ∧ energySB (distalFormula b) lam mu Ψ < (1 : ℝ) / 8) ↔
        b = true :=
  (sat_iff_energySB_lt_eighth (distalFormula b) hlam hmu).symm.trans
    (distalFormula_sat_iff b)

/-- The same logical bit is encoded by zero ground energy. -/
theorem distalFormula_ground_energy_iff (b : Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    EminSB (distalFormula b) lam mu = 0 ↔ b = true :=
  (sat_iff_EminSB_eq_zero (distalFormula b) hlam hmu).symm.trans
    (distalFormula_sat_iff b)

/-! ### Every local input and computation stage is charged -/

/-- Output of an arbitrary finite pipeline of local radius-limited
transformations, observed only on a prefix of m sites. The prefix size
is explicitly checked, and the decoder cannot inspect the distant input
bit except after that information has propagated. -/
def prefixDecision {n m : ℕ} (hm : m ≤ n)
    (stages : List (Stage Bool)) (decode : (Fin m → Bool) → Bool)
    (c : Configuration n Bool) : Bool :=
  decode (fun i => (runStages stages c) ⟨i.val, by omega⟩)

/-- Boolean equality follows from equality of the true predicates.
This avoids assuming an uninterpreted Boolean decoder oracle. -/
private theorem eq_of_true_iff (x y : Bool)
    (h : (x = true) ↔ (y = true)) : x = y := by
  cases x <;> cases y <;> simp_all

/-- **A genuine SAT-specific local causality lower bound.**
If every input configuration is correctly classified by a *fixed*
charged finite-radius pipeline as to whether the selected CNF admits
a sign-blind field of energy less than 1/8, the source bit must belong
to the pipeline's causal cone of the prefix readout. -/
theorem sat_energy_requires_causal_coverage
    (stages : List (Stage Bool)) (n m : ℕ) (j : Fin n)
    (hm : m ≤ n) (decode : (Fin m → Bool) → Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hcorrect : ∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        ∃ Ψ : ℕ → ℂ,
          Admissible Ψ ∧ energySB (distalFormula (c j)) lam mu Ψ < (1 : ℝ) / 8) :
    j.val < totalReach stages + m := by
  apply multistage_required_coverage_for_bit stages n m j hm decode
  intro c
  change prefixDecision hm stages decode c = c j
  apply eq_of_true_iff
  exact (hcorrect c).trans (distalFormula_energy_gap_iff (c j) hlam hmu)

/-- A second resource theorem using exactly the *ground-energy* criterion
`E_min(F) = 0`, rather than its subthreshold state characterization.
It requires the same finite-speed information delivery. -/
theorem sat_ground_energy_requires_causal_coverage
    (stages : List (Stage Bool)) (n m : ℕ) (j : Fin n)
    (hm : m ≤ n) (decode : (Fin m → Bool) → Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hcorrect : ∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        EminSB (distalFormula (c j)) lam mu = 0) :
    j.val < totalReach stages + m := by
  apply multistage_required_coverage_for_bit stages n m j hm decode
  intro c
  change prefixDecision hm stages decode c = c j
  apply eq_of_true_iff
  exact (hcorrect c).trans (distalFormula_ground_energy_iff (c j) hlam hmu)

/-- If the cumulative paid reach is too small, no correct algorithm of
the stated local pipeline class can solve this SAT-energy family.
The quantifier is over *every* decoder and *every* fixed list of charged
local stages, but only for this explicitly restricted input family. -/
theorem no_sat_energy_decider_below_cone
    (stages : List (Stage Bool)) (n m : ℕ) (j : Fin n)
    (hm : m ≤ n) (hfar : totalReach stages + m ≤ j.val)
    (decode : (Fin m → Bool) → Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    ¬ (∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        ∃ Ψ : ℕ → ℂ,
          Admissible Ψ ∧ energySB (distalFormula (c j)) lam mu Ψ < (1 : ℝ) / 8) := by
  intro hc
  have hreach := sat_energy_requires_causal_coverage
    stages n m j hm decode hlam hmu hc
  omega

/-- Read the final cell, giving a concrete linear resource obligation
`n ≤ totalReach + outputWidth` for correct low-energy classification.
No superpolynomial consequence follows from this inequality. -/
theorem last_site_sat_energy_linear_bound
    (stages : List (Stage Bool)) (n m : ℕ) (hn : 0 < n)
    (hm : m ≤ n) (decode : (Fin m → Bool) → Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hcorrect : ∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        ∃ Ψ : ℕ → ℂ,
          Admissible Ψ ∧
            energySB (distalFormula (c ⟨n - 1, by omega⟩)) lam mu Ψ <
              (1 : ℝ) / 8) :
    n ≤ totalReach stages + m := by
  have hreach := sat_energy_requires_causal_coverage
    stages n m ⟨n - 1, by omega⟩ hm decode hlam hmu hcorrect
  omega

end PVNP.WCTLocalSATEnergy
