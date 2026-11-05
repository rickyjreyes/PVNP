import PVNP.CrossingSplice

/-!
# Diagonal SAT splicing target for real machine crossing records

The SAT fooling family only needs the following mixed-acceptance condition:
if two accepting diagonal inputs have identical machine-derived crossing
records, both crossed pairs must be satisfiable. No global record-only
classifier is assumed. This condition still requires a full machine
crossing-sequence splicing theorem; it is an explicit premise here.
-/

namespace PVNP.CrossingDiagonal

open PVNP.Discrete PVNP.CrossingTrace PVNP.CrossingCapacity
open PVNP.SplitSATCapacity

theorem diagonal_trace_injective
    (M : TM) (cut : ℤ) {n t : Nat}
    (encode : Bits n → Bits n → List Bool)
    (hmixed : ∀ a b : Bits n,
      record M cut (encode a (fun i => !a i)) t =
        record M cut (encode b (fun i => !b i)) t →
      (∃ z : Bits n, splitThreeSat a (fun i => !b i) z) ∧
      (∃ z : Bits n, splitThreeSat b (fun i => !a i) z)) :
    Function.Injective (fun a : Bits n =>
      record M cut (encode a (fun i => !a i)) t) := by
  intro a b heq
  obtain ⟨hab, hba⟩ := hmixed a b heq
  apply PVNP.Communication.cross_disjoint_implies_eq a b
  · exact (split_three_sat_iff_disjoint _ _).1 hab
  · exact (split_three_sat_iff_disjoint _ _).1 hba

/-- Counting of the diagonal fooling family using an actual TM record.
Only the mixed-input splicing consequence is needed. -/
theorem diagonal_trace_capacity
    (M : TM) (cut : ℤ) {n t : Nat}
    (encode : Bits n → Bits n → List Bool)
    (hmixed : ∀ a b : Bits n,
      record M cut (encode a (fun i => !a i)) t =
        record M cut (encode b (fun i => !b i)) t →
      (∃ z : Bits n, splitThreeSat a (fun i => !b i) z) ∧
      (∃ z : Bits n, splitThreeSat b (fun i => !a i) z)) :
    2 ^ n ≤ (Fintype.card (M.Λ × Dir) + 1) ^ t := by
  have hinj := diagonal_trace_injective M cut encode hmixed
  have hcard := Fintype.card_le_of_injective
    (fun a : Bits n => record M cut (encode a (fun i => !a i)) t) hinj
  simpa [Bits, CutRecord, Fintype.card_fun, Fintype.card_option] using hcard

end PVNP.CrossingDiagonal
