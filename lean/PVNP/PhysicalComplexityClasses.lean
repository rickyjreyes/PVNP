import PVNP.DiscreteCurvatureRail
import PVNP.PartIIIExtended

/-!
# Part III: resource-model invariance, class logic and exact Boolean identities (issue #12)

* **Representation invariance (proved).** `WCC.relabel_decides`: relabelling a
  discrete WCC's alphabet by any bijection preserves the decided language and
  the exact running time.  Time classes are representation invariant.
* **Representation dependence (counterexample).**
  `curvature_not_representation_invariant`: the discrete curvature functional
  is *not* invariant: the same symbolic configuration has zero curvature under
  one alphabet labelling and nonzero curvature under a relabelling.
* `telescoping_bound` (Part III Theorem `thm:constructibility`): conditional
  telescoping estimate, with the per-step increment bound as an explicit
  premise.
* `conditional_interface_bound` (Part III Proposition `prop:interface`):
  composition of two *assumed* inequalities; labelled conditional.
* `directed_boundary_eq` (Part III Lemma `lem:boundary_variation`):
  `B→(f) = 2ⁿ Var(f)` exactly.
* `parity_total_influence`, `parity_directed_boundary` (Part III WIN-21):
  parity has `Var = n` and `B→ = n 2ⁿ`.
* `variation_class_vacuous` (Part III Corollary `cor:var`).
* `inclusions_do_not_determine` (Part III Proposition "no logical conflict").
* `classical_question_well_posed` (Part III WIN-17): `P_TM = NP_TM` is a
  definite proposition about explicitly defined classes.
-/

namespace PVNP.Discrete

namespace WCC

variable (A : WCC)

/-- Relabel the cell alphabet of a WCC along a bijection. -/
def relabel {S' : Type} [Fintype S'] [DecidableEq S'] (e : A.S ≃ S') : WCC where
  S := S'
  blank := e A.blank
  rule a b c := e (A.rule (e.symm a) (e.symm b) (e.symm c))
  quiescent := by simp [A.quiescent]
  inp b := e (A.inp b)
  origin o := e (A.origin o)
  acc s := A.acc (e.symm s)
  rej s := A.rej (e.symm s)

variable {S' : Type} [Fintype S'] [DecidableEq S'] (e : A.S ≃ S')

theorem relabel_run (x : List Bool) (t : ℕ) :
    (A.relabel e).run ((A.relabel e).init x) t = e ∘ A.run (A.init x) t := by
  induction t with
  | zero =>
    funext i
    simp only [run, Function.iterate_zero, id, init, Function.comp]
    split_ifs <;> rfl
  | succ t ih =>
    rw [run_succ, ih, run_succ]
    funext i
    simp [step, relabel]

open Classical in
theorem relabel_out (x : List Bool) : (A.relabel e).out x = A.out x := by
  funext s
  simp only [out, relabel_run, outCfg]
  congr 2 <;> simp [relabel, Function.comp]

/-- **Time classes are representation invariant.** -/
theorem relabel_decides (L : Set (List Bool)) (T : ℕ → ℕ) :
    (A.relabel e).Decides L T ↔ A.Decides L T := by
  simp only [Decides, relabel_out]

end WCC

/-- The identity CA on the three-letter alphabet. -/
abbrev idWCC3 : WCC where
  S := Fin 3
  blank := 0
  rule _ b _ := b
  quiescent := rfl
  inp _ := 1
  origin _ := 1
  acc _ := false
  rej _ := false

/-- **Curvature is not representation invariant.** The configuration
`…,0,0,1,2,2,…` has zero second difference at the origin under the labelling
`s ↦ s`, while its image under the relabelling swapping `1` and `2` (the same
symbolic computation, cf. `WCC.relabel_decides`) has second difference `-3`. -/
theorem curvature_not_representation_invariant :
    ∃ (e : idWCC3.S ≃ idWCC3.S) (c : ℤ → idWCC3.S),
      idWCC3.lap (fun s : Fin 3 => ((s : ℕ) : ℤ)) c 0 = 0 ∧
      idWCC3.lap (fun s : Fin 3 => ((s : ℕ) : ℤ)) (e ∘ c) 0 ≠ 0 ∧
      (∀ L T, (idWCC3.relabel e).Decides L T ↔ idWCC3.Decides L T) := by
  refine ⟨Equiv.swap (1 : Fin 3) 2,
    fun i => if i < 0 then (0 : Fin 3) else if i = 0 then 1 else 2, ?_, ?_, ?_⟩
  · simp [WCC.lap, idWCC3]
  · simp [WCC.lap, idWCC3, Equiv.swap_apply_def]
  · intro L T; exact idWCC3.relabel_decides _ L T

/-- **Part III Theorem `thm:constructibility`** (conditional telescoping). -/
theorem telescoping_bound (C : ℕ → ℝ) (T : ℕ) (p0 K : ℝ)
    (h0 : C 0 ≤ p0) (hstep : ∀ t < T, |C (t + 1) - C t| ≤ K) :
    C T ≤ p0 + T * K := by
  induction T with
  | zero => simpa using h0
  | succ T ih =>
    have h1 := ih (fun t ht => hstep t (by omega))
    have h2 := (abs_le.1 (hstep T (by omega))).2
    push_cast; linarith

/-- **Part III Proposition "conditional additive storage estimate"**: if a
storage functional is additive over `n` disjoint cells and each cell costs at
least `c₀`, the total is at least `n c₀`.  Both premises are explicit; neither
follows from the curvature functional (`zero_cost_counterexample`). -/
theorem conditional_additive_storage {n : ℕ} (cell : Fin n → ℝ) (total c₀ : ℝ)
    (hadd : total = ∑ j, cell j) (hcell : ∀ j, c₀ ≤ cell j) : n * c₀ ≤ total := by
  rw [hadd]
  calc (n : ℝ) * c₀ = ∑ _j : Fin n, c₀ := by simp
    _ ≤ ∑ j, cell j := Finset.sum_le_sum fun j _ => hcell j

/-- **Part III Proposition `prop:interface`** — conditional composition. -/
theorem conditional_interface_bound {R : Type*} (cost area : R → ℝ) (A κ : ℝ)
    (hκ : 0 ≤ κ) (harea : ∀ ψ, A ≤ area ψ) (hcoerc : ∀ ψ, κ * area ψ ≤ cost ψ) :
    ∀ ψ, κ * A ≤ cost ψ :=
  fun ψ => le_trans (mul_le_mul_of_nonneg_left (harea ψ) hκ) (hcoerc ψ)

/-- **Part III Proposition "no logical conflict"**: inclusions into larger
classes determine neither equality nor separation of the subclasses. -/
theorem inclusions_do_not_determine (Pd NPd : Set (Set (List Bool))) (hNP : NPd.Nonempty) :
    (∃ Pp NPp : Set (Set (List Bool)), Pp ⊆ Pd ∧ NPp ⊆ NPd ∧ Pp = NPp) ∧
    (∃ Pp NPp : Set (Set (List Bool)), Pp ⊆ Pd ∧ NPp ⊆ NPd ∧ Pp ≠ NPp) := by
  obtain ⟨L, hL⟩ := hNP
  refine ⟨⟨∅, ∅, Set.empty_subset _, Set.empty_subset _, rfl⟩,
    ⟨∅, {L}, Set.empty_subset _, Set.singleton_subset_iff.2 hL, ?_⟩⟩
  intro h
  have : L ∈ (∅ : Set (Set (List Bool))) := by rw [h]; exact rfl
  exact this

/-- **Part III WIN-17.** The classical question is a definite proposition
about explicitly defined classes (`DiscreteMachines`); it is decided by the
law of excluded middle *as a proposition*, independently of any physical
resource model.  Nothing here asserts which disjunct holds. -/
theorem classical_question_well_posed : P_TM = NP_TM ∨ P_TM ≠ NP_TM := em _

end PVNP.Discrete

namespace PVNP.PartIII

/-- **Part III Lemma `lem:boundary_variation`.** -/
theorem directed_boundary_eq {n : Nat} (f : Assignment n → Bool) :
    (directedBoundaryCount f : ℚ) = 2 ^ n * normalizedTotalInfluence f := by
  have hc : (Fintype.card (Assignment n) : ℚ) = 2 ^ n := by simp
  unfold directedBoundaryCount normalizedTotalInfluence normalizedInfluence
  rw [hc, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- Parity of an assignment. -/
def parity {n : Nat} (x : Assignment n) : Bool :=
  decide ((∑ i, if x i then (1 : ZMod 2) else 0) = 1)

theorem parity_sum_flip {n : Nat} (x : Assignment n) (i : Fin n) :
    (∑ j, if flip x i j then (1 : ZMod 2) else 0) =
      (∑ j, if x j then (1 : ZMod 2) else 0) + 1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : (∑ j ∈ Finset.univ.erase i, if flip x i j then (1 : ZMod 2) else 0) =
      ∑ j ∈ Finset.univ.erase i, if x j then (1 : ZMod 2) else 0 :=
    Finset.sum_congr rfl fun j hj => by
      simp [flip, Function.update, Finset.ne_of_mem_erase hj]
  rw [hrest]
  have h2 : (1 : ZMod 2) + 1 = 0 := rfl
  cases h : x i <;> simp [flip, h]
  · exact add_comm _ _
  · linear_combination -h2

theorem parity_flip {n : Nat} (x : Assignment n) (i : Fin n) :
    parity x ≠ parity (flip x i) := by
  unfold parity
  rw [parity_sum_flip]
  generalize (∑ j, if x j then (1 : ZMod 2) else 0) = s
  fin_cases s <;> decide

theorem parity_directional (n : Nat) (i : Fin n) :
    directionalBoundaryCount (parity (n := n)) i = 2 ^ n := by
  unfold directionalBoundaryCount
  rw [Finset.filter_true_of_mem (fun x _ => parity_flip x i)]
  simp

/-- **Part III WIN-21.** Parity has total influence exactly `n`. -/
theorem parity_total_influence (n : Nat) : normalizedTotalInfluence (parity (n := n)) = n := by
  unfold normalizedTotalInfluence normalizedInfluence
  simp [parity_directional]

theorem parity_directed_boundary (n : Nat) : directedBoundaryCount (parity (n := n)) = n * 2 ^ n := by
  simp [directedBoundaryCount, parity_directional]

/-- **Part III Corollary `cor:var`.** Every Boolean family has total
influence at most `n¹`; a "polynomial-variation class" contains everything. -/
theorem variation_class_vacuous (F : ∀ n, Assignment n → Bool) :
    ∀ n, normalizedTotalInfluence (F n) ≤ (n : ℚ) ^ 1 := by
  intro n
  rw [pow_one]
  unfold normalizedTotalInfluence
  calc (∑ i, normalizedInfluence (F n) i) ≤ ∑ _i : Fin n, (1 : ℚ) :=
        Finset.sum_le_sum fun i _ => normalized_influence_le_one (F n) i
    _ = n := by simp

end PVNP.PartIII
