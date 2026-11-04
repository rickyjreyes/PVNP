import PVNP.WCCDFiniteSnapshot

/-!
# D-1: polynomial abstract work bound for finite multidimensional replay

This file counts causal-box cell updates and the constant-size Moore
neighborhood of each cell. For every **fixed** spatial dimension d,
these counts are bounded by an explicit polynomial in input length plus
simulated rounds.

This is an abstract finite-array work bound. It is *not* a single-tape
Turing-machine transition bound: array addressing, serialization,
initialization, and tape head movements have not been compiled and charged.
-/

namespace PVNP.Discrete.WCCD

/-- Size of the finite causal rectangle for an input length n after t rounds. -/
def boxCells (n d t : ℕ) : ℕ :=
  (n + 2 * t + 1) * (2 * t + 1) ^ d

/-- The exact finite cardinality agrees with the abstract size expression. -/
theorem boxCells_card (d : ℕ) (x : List Bool) (t : ℕ) :
    Fintype.card (Box d x t) = boxCells x.length d t := by
  simpa only [boxCells] using box_card d x t

/-- The rectangular causal box cannot shrink with time. -/
theorem boxCells_mono (n d t T : ℕ) (ht : t ≤ T) :
    boxCells n d t ≤ boxCells n d T := by
  unfold boxCells
  gcongr <;> omega

/-- Number of cell values constructed by replaying all snapshots, including
the initialization snapshot. This counts one finite-array cell write per
entry, but does not charge tape-head motion or address lookup. -/
def totalCells (n d : ℕ) : ℕ → ℕ
  | 0 => boxCells n d 0
  | t + 1 => totalCells n d t + boxCells n d (t + 1)

/-- Total finite-array cell writes are at most the number of snapshots
times the final snapshot's size. -/
theorem totalCells_le (n d T : ℕ) :
    totalCells n d T ≤ (T + 1) * boxCells n d T := by
  induction T with
  | zero =>
      simp [totalCells]
  | succ t ih =>
      change totalCells n d t + boxCells n d (t + 1) ≤
        (t + 1 + 1) * boxCells n d (t + 1)
      have hmono := boxCells_mono n d t (t + 1) (Nat.le_succ t)
      calc
        totalCells n d t + boxCells n d (t + 1)
          ≤ (t + 1) * boxCells n d t + boxCells n d (t + 1) :=
            Nat.add_le_add_right ih _
        _ ≤ (t + 1) * boxCells n d (t + 1) + boxCells n d (t + 1) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left (t + 1) hmono) _
        _ = (t + 1 + 1) * boxCells n d (t + 1) := by ring

/-- The same abstract work count is bounded by a polynomial in n+T for
every fixed spatial dimension. No machine simulation is assumed. -/
theorem totalCells_polynomial_bound (n d T : ℕ) :
    totalCells n d T ≤
      2 ^ (d + 2) * (n + T + 1) ^ (d + 2) := by
  have hT := totalCells_le n d T
  have hsize : (T + 1) * boxCells n d T ≤
      (n + 2 * T + 2) ^ (d + 2) := by
    unfold boxCells
    have ha : T + 1 ≤ n + 2 * T + 2 := by omega
    have hb : n + 2 * T + 1 ≤ n + 2 * T + 2 := by omega
    have hc : (2 * T + 1) ^ d ≤ (n + 2 * T + 2) ^ d := by
      gcongr
      omega
    calc
      (T + 1) * ((n + 2 * T + 1) * (2 * T + 1) ^ d)
          ≤ (n + 2 * T + 2) * ((n + 2 * T + 1) *
              (2 * T + 1) ^ d) :=
            Nat.mul_le_mul_right _ ha
      _ ≤ (n + 2 * T + 2) * ((n + 2 * T + 2) *
              (2 * T + 1) ^ d) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb)
      _ ≤ (n + 2 * T + 2) * ((n + 2 * T + 2) *
              (n + 2 * T + 2) ^ d) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
      _ = (n + 2 * T + 2) ^ (d + 2) := by
        simp only [pow_add, pow_two]
        ring
  have hdouble : n + 2 * T + 2 ≤ 2 * (n + T + 1) := by omega
  calc
    totalCells n d T ≤ (T + 1) * boxCells n d T := hT
    _ ≤ (n + 2 * T + 2) ^ (d + 2) := hsize
    _ ≤ (2 * (n + T + 1)) ^ (d + 2) := by gcongr
    _ = 2 ^ (d + 2) * (n + T + 1) ^ (d + 2) := by rw [mul_pow]

/-- Every Moore neighborhood on Z^(1+d) has precisely 3^(d+1) offsets. -/
theorem neighborhood_card (d : ℕ) :
    Fintype.card (Fin 3 × (Fin d → Fin 3)) = 3 ^ (d + 1) := by
  simp [Fintype.card_prod, Fintype.card_fun, pow_succ, mul_comm]

/-- Upper accounting model for reading every neighbor once per cell write.
This does not count the cost of locating a neighbor on a tape. -/
def totalNeighborReads (n d T : ℕ) : ℕ :=
  3 ^ (d + 1) * totalCells n d T

/-- Polynomial number of abstract neighbor reads, for fixed d.
This is NOT a polynomial-time TM simulation theorem. -/
theorem totalNeighborReads_polynomial_bound (n d T : ℕ) :
    totalNeighborReads n d T ≤
      3 ^ (d + 1) * (2 ^ (d + 2) * (n + T + 1) ^ (d + 2)) := by
  unfold totalNeighborReads
  exact Nat.mul_le_mul_left _ (totalCells_polynomial_bound n d T)

end PVNP.Discrete.WCCD
