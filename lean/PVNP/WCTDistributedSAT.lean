import PVNP.WCTLocalSATEnergy

/-!
# Distributed 3-CNF energy readout under charged local transport

Upgrade over the two-formula selector in `WCTLocalSATEnergy`:
an input `c : Fin n → Bool` generates a CNF with exactly n+1 clauses.
Every input bit controls one clause at its own logical index. One fixed
positive unit clause anchors the chosen variable. For each bit there
is a positive unit clause when that bit is true and a negative unit
clause when it is false. Thus the formula is satisfiable exactly when
ALL n source bits are true.

The sign-blind WCT energy-gap theorem then identifies that same Boolean
predicate with existence of an energy-<1/8 field, and with ground
energy exactly zero. The multistage locality theorem proves that any
correct decoder of the first m output cells must be reachable from
every potentially decisive source position j:

    j.val < Σ_s (stage.radius * stage.rounds) + m.

This is a rigorous *linear physical locality* statement with
explicitly charged finite-radius stages. It is NOT a general SAT time
lower bound, not a statement about the conservative torus PDE, and
not a proof of P ≠ NP. The one-variable repeated-clause SAT family is
deliberately easy. The formula is a mathematical interpretation of the
raw spatial input, not a free nonlocal encoder to the measured output.
-/

namespace PVNP.WCTDistributedSAT

open PVNP.PartII PVNP.PartIPsiSat PVNP.InterwovenSAT
open PVNP.MultiStageCausality PVNP.RadiusCausality
open PVNP.WCTLocalSATEnergy

/-- A fixed positive unit clause, or its negative, selected locally
by a Boolean input bit. The three literal slots are identical. -/
def localClause (b : Bool) : Clause3 := if b then gPos else gNeg

/-- A linearly sized CNF. The first clause requires x₀, and each of the
remaining clauses independently requires x₀ or ¬x₀ depending on a
spatially distributed source bit. -/
def formulaOfBits (bs : List Bool) : CNF3 :=
  gPos :: bs.map localClause

/-- A spatially distributed n-bit input interpreted as n+1 CNF clauses. -/
def sourceFormula {n : ℕ} (c : Configuration n Bool) : CNF3 :=
  formulaOfBits (List.ofFn c)

theorem sourceFormula_length {n : ℕ} (c : Configuration n Bool) :
    (sourceFormula c).length = n + 1 := by
  simp [sourceFormula, formulaOfBits]

private theorem pos_clause_eval (a : ℕ → Bool) :
    clauseVal a gPos = a 0 := by
  simp [gPos, clauseVal, litVal]

private theorem neg_clause_eval (a : ℕ → Bool) :
    clauseVal a gNeg = !(a 0) := by
  simp [gNeg, clauseVal, litVal]

/-- The ground truth of this entire n-bit formula is the AND of
the source bits. No unbounded SAT oracle is used in the reduction. -/
theorem formulaOfBits_sat_iff (bs : List Bool) :
    Sat (formulaOfBits bs) ↔ ∀ b ∈ bs, b = true := by
  constructor
  · rintro ⟨a, ha⟩ b hb
    have hpos : a 0 = true := by
      have h := ha gPos (by simp [formulaOfBits])
      simpa [pos_clause_eval] using h
    cases b with
    | true => rfl
    | false =>
        have hm : gNeg ∈ formulaOfBits bs := by
          change gNeg ∈ gPos :: bs.map localClause
          apply List.mem_cons_of_mem
          apply List.mem_map.mpr
          exact ⟨false, hb, rfl⟩
        have hneg : clauseVal a gNeg = true := ha gNeg hm
        rw [neg_clause_eval, hpos] at hneg
        cases hneg
  · intro hall
    refine ⟨fun _ => true, ?_⟩
    intro cl hcl
    change cl ∈ gPos :: bs.map localClause at hcl
    rcases List.mem_cons.mp hcl with h | h
    · rw [h, pos_clause_eval]
      rfl
    · rcases List.mem_map.mp h with ⟨b, hb, hbc⟩
      have hc : cl = gPos := by
        calc
          cl = localClause b := hbc.symm
          _ = gPos := by simp [localClause, hall b hb]
      rw [hc, pos_clause_eval]
      rfl

/-- Unlike the former two-formula selector, every source bit
has its own syntactic clause in this n+1 clause CNF family. -/
theorem sourceFormula_sat_iff {n : ℕ} (c : Configuration n Bool) :
    Sat (sourceFormula c) ↔ ∀ i : Fin n, c i = true := by
  change Sat (formulaOfBits (List.ofFn c)) ↔ ∀ i : Fin n, c i = true
  exact (formulaOfBits_sat_iff (List.ofFn c)).trans
    (List.forall_mem_ofFn_iff)

/-- Uniform all-true input; the associated CNF is satisfiable. -/
def allTrue (n : ℕ) : Configuration n Bool := fun _ => true

/-- Change only the selected raw spatial bit. -/
def oneFalse (n : ℕ) (j : Fin n) : Configuration n Bool :=
  fun i => if i = j then false else true

theorem allTrue_sat (n : ℕ) : Sat (sourceFormula (allTrue n)) :=
  (sourceFormula_sat_iff _).2 (fun _ => rfl)

theorem oneFalse_unsat {n : ℕ} (j : Fin n) :
    ¬ Sat (sourceFormula (oneFalse n j)) := by
  intro h
  have hj := (sourceFormula_sat_iff _).1 h j
  simp [oneFalse] at hj

/-- Inputs differing at exactly the distal position agree throughout
any shorter prefix. -/
theorem sources_agree_before {n k : ℕ} (j : Fin n) (hk : k ≤ j.val) :
    prefixAgree (allTrue n) (oneFalse n j) k := by
  intro i hi
  have hne : i ≠ j := by
    intro heq
    have hv : i.val = j.val := congrArg Fin.val heq
    omega
  simp [allTrue, oneFalse, hne]

/-- **No local SAT classifier below its light cone.**
Any number of finite-radius preprocessing, evolution and
postprocessing stages are allowed; every stage is charged.
Every prefix decoder is quantified. -/
theorem no_distributed_sat_decider_below_cone
    (stages : List (Stage Bool)) (n m : ℕ) (j : Fin n)
    (hm : m ≤ n) (hfar : totalReach stages + m ≤ j.val)
    (decode : (Fin m → Bool) → Bool) :
    ¬ (∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        Sat (sourceFormula c)) := by
  intro hcorrect
  have hagree := sources_agree_before j hfar
  have heq := multistage_decoder_equal stages (allTrue n)
    (oneFalse n j) m hm hagree decode
  change prefixDecision hm stages decode (allTrue n) =
    prefixDecision hm stages decode (oneFalse n j) at heq
  have hyes : prefixDecision hm stages decode (allTrue n) = true :=
    (hcorrect _).2 (allTrue_sat n)
  have hno : prefixDecision hm stages decode (oneFalse n j) ≠ true := by
    intro h
    exact oneFalse_unsat j ((hcorrect _).1 h)
  exact hno (heq ▸ hyes)

/-- Any correct deterministic finite-radius SAT decision pipeline on
this distributed family must bring information from position j
into the observable prefix. -/
theorem distributed_sat_requires_causal_coverage
    (stages : List (Stage Bool)) (n m : ℕ) (j : Fin n)
    (hm : m ≤ n) (decode : (Fin m → Bool) → Bool)
    (hcorrect : ∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        Sat (sourceFormula c)) :
    j.val < totalReach stages + m := by
  by_contra h
  have hfar : totalReach stages + m ≤ j.val := by omega
  exact (no_distributed_sat_decider_below_cone stages n m j hm hfar decode) hcorrect

/-- The same physical locality obligation for a correct
sign-blind low-energy WCT readout at threshold 1/8. -/
theorem distributed_energy_requires_causal_coverage
    (stages : List (Stage Bool)) (n m : ℕ) (j : Fin n)
    (hm : m ≤ n) (decode : (Fin m → Bool) → Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hcorrect : ∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        ∃ Ψ : ℕ → ℂ, Admissible Ψ ∧
          energySB (sourceFormula c) lam mu Ψ < (1 : ℝ) / 8) :
    j.val < totalReach stages + m := by
  apply distributed_sat_requires_causal_coverage stages n m j hm decode
  intro c
  exact (hcorrect c).trans
    (sat_iff_energySB_lt_eighth (sourceFormula c) hlam hmu).symm

/-- Exact ground-energy `EminSB = 0` requires the same cumulative
causal reach in the charged local model. -/
theorem distributed_ground_energy_requires_causal_coverage
    (stages : List (Stage Bool)) (n m : ℕ) (j : Fin n)
    (hm : m ≤ n) (decode : (Fin m → Bool) → Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hcorrect : ∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        EminSB (sourceFormula c) lam mu = 0) :
    j.val < totalReach stages + m := by
  apply distributed_sat_requires_causal_coverage stages n m j hm decode
  intro c
  exact (hcorrect c).trans
    (sat_iff_EminSB_eq_zero (sourceFormula c) hlam hmu).symm

/-- The final site gives a linear lower bound on the cumulative
charged reach, including the output region width. -/
theorem distributed_energy_last_site_linear
    (stages : List (Stage Bool)) (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ n)
    (decode : (Fin m → Bool) → Bool)
    {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hcorrect : ∀ c : Configuration n Bool,
      prefixDecision hm stages decode c = true ↔
        ∃ Ψ : ℕ → ℂ, Admissible Ψ ∧
          energySB (sourceFormula c) lam mu Ψ < (1 : ℝ) / 8) :
    n ≤ totalReach stages + m := by
  have h := distributed_energy_requires_causal_coverage
    stages n m ⟨n - 1, by omega⟩ hm decode hlam hmu hcorrect
  change n - 1 < totalReach stages + m at h
  omega

end PVNP.WCTDistributedSAT
