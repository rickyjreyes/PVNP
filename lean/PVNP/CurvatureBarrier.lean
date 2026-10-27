import Mathlib

/-!
# Polynomial-resource countermodel for Boolean state storage

The finite-state curvature proxy uses amplitudes 1 and 2. These theorems
show that storage of arbitrary assignments has O(n) curvature on a
radius-two-slot stencil, and O(n d²) unregularized graph-Laplacian
energy when maximum graph degree is d.

These DO NOT assert that the states are WCT PDE equilibria or establish
any SAT decision-time upper bound.
-/

namespace PVNP.CurvatureBarrier

def amplitude (b : Bool) : ℚ := if b then 2 else 1

theorem amplitude_injective : Function.Injective amplitude := by
  intro a b hab
  cases a <;> cases b <;> simp_all [amplitude]

/-- Squared regularized radius-one curvature on three binary amplitudes,
with ε = 1 and a strictly positive denominator. -/
def localCurvature (a b c : Bool) : ℚ :=
  ((amplitude a - 2 * amplitude b + amplitude c) /
    (amplitude b + 1)) ^ 2

theorem localCurvature_nonnegative (a b c : Bool) :
    0 ≤ localCurvature a b c := by
  unfold localCurvature
  positivity

theorem localCurvature_le_one (a b c : Bool) :
    localCurvature a b c ≤ 1 := by
  cases a <;> cases b <;> cases c <;>
    norm_num [localCurvature, amplitude]

def localStorageCost {n : Nat} (bits : Fin n → Bool)
    (left right : Fin n → Fin n) : ℚ :=
  ∑ i : Fin n,
    localCurvature (bits (left i)) (bits i) (bits (right i))

/-- Uniform curvature upper bound for EVERY n-bit assignment and
EVERY pair of neighbor selectors. In particular, it holds for a ring. -/
theorem localStorageCost_le_n {n : Nat} (bits : Fin n → Bool)
    (left right : Fin n → Fin n) :
    localStorageCost bits left right ≤ (n : ℚ) := by
  unfold localStorageCost
  calc
    (∑ i : Fin n,
      localCurvature (bits (left i)) (bits i) (bits (right i))) ≤
        ∑ _i : Fin n, (1 : ℚ) := by
          exact Finset.sum_le_sum (by
            intro i hi
            exact localCurvature_le_one _ _ _)
    _ = (n : ℚ) := by simp

theorem amplitude_difference_upper (a b : Bool) :
    amplitude a - amplitude b ≤ 1 := by
  cases a <;> cases b <;> norm_num [amplitude]

theorem amplitude_difference_lower (a b : Bool) :
    -1 ≤ amplitude a - amplitude b := by
  cases a <;> cases b <;> norm_num [amplitude]

/-- Graph Laplacian of the bit amplitudes with an arbitrary finite
neighborhood relation (no expansion assumption). -/
def graphLaplacian {n : Nat}
    (neighbors : Fin n → Finset (Fin n))
    (bits : Fin n → Bool) (i : Fin n) : ℚ :=
  ∑ j ∈ neighbors i, (amplitude (bits j) - amplitude (bits i))

theorem graphLaplacian_upper {n : Nat}
    (neighbors : Fin n → Finset (Fin n)) (bits : Fin n → Bool)
    (i : Fin n) :
    graphLaplacian neighbors bits i ≤
      ((neighbors i).card : ℚ) := by
  unfold graphLaplacian
  calc
    (∑ j ∈ neighbors i, (amplitude (bits j) - amplitude (bits i))) ≤
      ∑ _j ∈ neighbors i, (1 : ℚ) := by
        exact Finset.sum_le_sum (by
          intro j hj
          exact amplitude_difference_upper _ _)
    _ = ((neighbors i).card : ℚ) := by simp

theorem graphLaplacian_lower {n : Nat}
    (neighbors : Fin n → Finset (Fin n)) (bits : Fin n → Bool)
    (i : Fin n) :
    -((neighbors i).card : ℚ) ≤
      graphLaplacian neighbors bits i := by
  unfold graphLaplacian
  calc
    -((neighbors i).card : ℚ) =
      ∑ _j ∈ neighbors i, (-1 : ℚ) := by simp
    _ ≤ ∑ j ∈ neighbors i,
      (amplitude (bits j) - amplitude (bits i)) := by
        exact Finset.sum_le_sum (by
          intro j hj
          exact amplitude_difference_lower _ _)

theorem graphLaplacian_sq_le_degree_sq {n d : Nat}
    (neighbors : Fin n → Finset (Fin n)) (bits : Fin n → Bool)
    (i : Fin n) (hdeg : (neighbors i).card ≤ d) :
    (graphLaplacian neighbors bits i) ^ 2 ≤ (d : ℚ) ^ 2 := by
  have hlow := graphLaplacian_lower neighbors bits i
  have hupp := graphLaplacian_upper neighbors bits i
  have hd : ((neighbors i).card : ℚ) ≤ (d : ℚ) := by
    exact_mod_cast hdeg
  have hp :
      0 ≤ ((d : ℚ) - graphLaplacian neighbors bits i) *
        ((d : ℚ) + graphLaplacian neighbors bits i) := by
    apply mul_nonneg <;> linarith
  nlinarith

def graphStorageCost {n : Nat} (neighbors : Fin n → Finset (Fin n))
    (bits : Fin n → Bool) : ℚ :=
  ∑ i : Fin n, (graphLaplacian neighbors bits i) ^ 2

/-- No bounded-degree graph topology (including a bounded-degree expander)
can force exponential growth of this particular bit-storage energy. -/
theorem graphStorageCost_le_n_mul_d_sq {n d : Nat}
    (neighbors : Fin n → Finset (Fin n))
    (bits : Fin n → Bool)
    (hdegree : ∀ i, (neighbors i).card ≤ d) :
    graphStorageCost neighbors bits ≤ (n : ℚ) * (d : ℚ) ^ 2 := by
  unfold graphStorageCost
  calc
    (∑ i : Fin n, (graphLaplacian neighbors bits i) ^ 2) ≤
      ∑ _i : Fin n, (d : ℚ) ^ 2 := by
        exact Finset.sum_le_sum (by
          intro i hi
          exact graphLaplacian_sq_le_degree_sq neighbors bits i (hdegree i))
    _ = (n : ℚ) * (d : ℚ) ^ 2 := by simp

end PVNP.CurvatureBarrier
