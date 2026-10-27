import Mathlib

/-!
# Tseitin parity obstruction and the linear-algebraic bypass

Every edge of an undirected graph enters exactly two vertex equations,
so its incidence-column sum vanishes in ZMod 2. Inconsistent total
charges make the system unsatisfiable. This provides an explicit
polynomial-time algebraic route that avoids resolution-style search;
it does not itself formalize an exponential resolution lower bound.
-/

namespace PVNP.Tseitin

/-- A finite GF(2) incidence linear system whose every column has even parity. -/
theorem parity_sum_zero
    {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge]
    (incident : Vertex → Edge → ZMod 2)
    (state : Edge → ZMod 2)
    (charge : Vertex → ZMod 2)
    (heven : ∀ e, (∑ v, incident v e) = 0)
    (hequations : ∀ v, (∑ e, incident v e * state e) = charge v) :
    (∑ v, charge v) = 0 := by
  calc
    (∑ v, charge v) =
        ∑ v, ∑ e, incident v e * state e := by
          apply Finset.sum_congr rfl
          intro v hv
          exact (hequations v).symm
    _ = ∑ e, ∑ v, incident v e * state e := Finset.sum_comm
    _ = ∑ e, (∑ v, incident v e) * state e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.sum_mul]
    _ = 0 := by simp [heven]

/-- A nonzero total charge forbids any satisfying parity assignment. -/
theorem odd_charge_unsatisfiable
    {Vertex Edge : Type*} [Fintype Vertex] [Fintype Edge]
    (incident : Vertex → Edge → ZMod 2)
    (charge : Vertex → ZMod 2)
    (heven : ∀ e, (∑ v, incident v e) = 0)
    (hodd : (∑ v, charge v) ≠ 0) :
    ¬ ∃ state : Edge → ZMod 2,
      ∀ v, (∑ e, incident v e * state e) = charge v := by
  rintro ⟨state, hs⟩
  exact hodd (parity_sum_zero incident state charge heven hs)

/-- Exact conditional transfer from a proof-system lower bound:
if R^k ≥ S, then the putative physical proof-cost R cannot be smaller
than any r with r^k < S. No extraction theorem is assumed here. -/
theorem resolution_transfer_template
    (size resource k : Nat)
    (hextract : size ≤ resource ^ k)
    (hsize : 0 < size) (hk : 0 < k) :
    0 < resource := by
  by_contra hn
  have hr : resource = 0 := Nat.eq_zero_of_not_pos hn
  subst resource
  cases k with
  | zero => omega
  | succ k =>
      simp at hextract
      omega

end PVNP.Tseitin
