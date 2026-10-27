import PVNP.PartIII

/-!
# Part III — exact normalized Boolean hypercube boundary quantities

The defined Boolean hypercube has 2^n vertices. Directional boundary
counts are nonnegative and bounded by the total vertex count. Hence total
normalized influence is at most n, contradicting any exponential-in-n
normalized influence lower bound.
-/

namespace PVNP.PartIII

abbrev Assignment (n : Nat) := Fin n → Bool

def flip {n : Nat} (x : Assignment n) (i : Fin n) : Assignment n :=
  Function.update x i (!x i)

def directionalBoundaryCount {n : Nat}
    (f : Assignment n → Bool) (i : Fin n) : Nat :=
  (Finset.univ.filter (fun x : Assignment n => f x ≠ f (flip x i))).card

def directedBoundaryCount {n : Nat} (f : Assignment n → Bool) : Nat :=
  ∑ i : Fin n, directionalBoundaryCount f i

theorem directional_boundary_le_vertices {n : Nat}
    (f : Assignment n → Bool) (i : Fin n) :
    directionalBoundaryCount f i ≤ Fintype.card (Assignment n) := by
  have hsub :
      (Finset.univ.filter (fun x : Assignment n => f x ≠ f (flip x i))) ⊆
        (Finset.univ : Finset (Assignment n)) := by
    intro x hx
    exact Finset.mem_univ x
  simpa [directionalBoundaryCount] using Finset.card_le_card hsub

theorem directed_boundary_le_n_times_vertices {n : Nat}
    (f : Assignment n → Bool) :
    directedBoundaryCount f ≤ n * Fintype.card (Assignment n) := by
  unfold directedBoundaryCount
  calc
    (∑ i : Fin n, directionalBoundaryCount f i) ≤
        ∑ _i : Fin n, Fintype.card (Assignment n) := by
          exact Finset.sum_le_sum (by
            intro i hi
            exact directional_boundary_le_vertices f i)
    _ = n * Fintype.card (Assignment n) := by simp

def normalizedInfluence {n : Nat} (f : Assignment n → Bool)
    (i : Fin n) : ℚ :=
  (directionalBoundaryCount f i : ℚ) / Fintype.card (Assignment n)

def normalizedTotalInfluence {n : Nat}
    (f : Assignment n → Bool) : ℚ :=
  ∑ i : Fin n, normalizedInfluence f i

theorem normalized_influence_nonnegative {n : Nat}
    (f : Assignment n → Bool) (i : Fin n) :
    0 ≤ normalizedInfluence f i := by
  unfold normalizedInfluence
  positivity

theorem normalized_influence_le_one {n : Nat}
    (f : Assignment n → Bool) (i : Fin n) :
    normalizedInfluence f i ≤ 1 := by
  unfold normalizedInfluence
  have hpos : (0 : ℚ) < Fintype.card (Assignment n) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Assignment n))
  apply (div_le_iff₀ hpos).2
  simpa using (show (directionalBoundaryCount f i : ℚ) ≤
      Fintype.card (Assignment n) from by
        exact_mod_cast directional_boundary_le_vertices f i)

theorem normalized_total_influence_nonnegative {n : Nat}
    (f : Assignment n → Bool) :
    0 ≤ normalizedTotalInfluence f := by
  unfold normalizedTotalInfluence
  exact Finset.sum_nonneg (by
    intro i hi
    exact normalized_influence_nonnegative f i)

theorem normalized_total_influence_le_n {n : Nat}
    (f : Assignment n → Bool) :
    normalizedTotalInfluence f ≤ (n : ℚ) := by
  unfold normalizedTotalInfluence
  calc
    (∑ i : Fin n, normalizedInfluence f i) ≤
      ∑ _i : Fin n, (1 : ℚ) := by
        exact Finset.sum_le_sum (by
          intro i hi
          exact normalized_influence_le_one f i)
    _ = (n : ℚ) := by simp

end PVNP.PartIII
