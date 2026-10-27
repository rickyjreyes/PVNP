import PVNP.Communication
import Mathlib

/-!
# Curvature and communication: exact restricted bridge, plus a no-go example

A fixed-boundary three-node channel sends a bit as middle amplitude 1 or 2;
the endpoints are zero. Each occupied Boolean slot has normalized
second-difference curvature energy at least 1.

When a deterministic split-input disjointness protocol uses q fixed-length
binary slots and each is physically implemented by such a channel, its
curvature snapshot cost is at least q, hence at least n.

This is NOT a universal curvature lower bound for physical WCC: affine
profiles below have zero curvature while their readouts differ.
-/

namespace PVNP.CurvatureCommunication

/-- Two distinguishable affine snapshots with identically zero second
difference. Distinguishability does not imply positive curvature alone. -/
def affineStart (_ : Bool) : ℚ := 1
def affineMid (b : Bool) : ℚ := if b then 2 else 1
def affineEnd (b : Bool) : ℚ := if b then 3 else 1

def affineSecondDifference (b : Bool) : ℚ :=
  affineStart b - 2 * affineMid b + affineEnd b

theorem affine_curvature_zero (b : Bool) :
    affineSecondDifference b = 0 := by
  cases b <;> norm_num
    [affineSecondDifference, affineStart, affineMid, affineEnd]

theorem affine_receiver_distinguishable :
    affineEnd false ≠ affineEnd true := by
  norm_num [affineEnd]

def bitAmplitude (b : Bool) : ℚ := if b then 2 else 1

/-- Curvature cost at the middle node, with fixed zero endpoints and
regularizer ε = 1. The numerator is the discrete second derivative. -/
def anchoredSlotCost (b : Bool) : ℚ :=
  ((0 - 2 * bitAmplitude b + 0) / (bitAmplitude b + 1)) ^ 2

theorem anchored_slot_cost_ge_one (b : Bool) :
    (1 : ℚ) ≤ anchoredSlotCost b := by
  cases b <;> norm_num [anchoredSlotCost, bitAmplitude]

def anchoredTranscriptCost {q : Nat} (bits : Fin q → Bool) : ℚ :=
  ∑ i : Fin q, anchoredSlotCost (bits i)

theorem anchored_transcript_cost_ge_slots {q : Nat}
    (bits : Fin q → Bool) :
    (q : ℚ) ≤ anchoredTranscriptCost bits := by
  calc
    (q : ℚ) = ∑ _i : Fin q, (1 : ℚ) := by simp
    _ ≤ anchoredTranscriptCost bits := by
      unfold anchoredTranscriptCost
      exact Finset.sum_le_sum (by
        intro i hi
        exact anchored_slot_cost_ge_one (bits i))

/-- The previous fooling-set theorem implies that an exact
deterministic DISJ_n protocol cannot use fewer than n fixed binary
slots. Other communication models can encode information differently. -/
theorem disjointness_requires_n_fixed_slots {n q : Nat}
    (transcript :
      Communication.Bits n → Communication.Bits n → (Fin q → Bool))
    (accepts : (Fin q → Bool) → Prop)
    (hrectangle : ∀ a a' b b',
      transcript a b = transcript a' b' →
        transcript a b' = transcript a b ∧
        transcript a' b = transcript a b)
    (haccept : ∀ a,
      accepts (transcript a (fun i => !a i)))
    (hsound : ∀ a b,
      accepts (transcript a b) → Communication.disjoint a b) :
    n ≤ q := by
  have hcard := Communication.disjointness_transcript_lower_bound
    transcript accepts hrectangle haccept hsound
  have hpow : (2 : Nat) ^ n ≤ 2 ^ q := by
    simpa [Fintype.card_fun] using hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : Nat))).mp hpow

/-- Genuine end-to-end (but model-relative) lower bound. Each of q fixed
binary transcript positions is an independently anchored paid channel,
even if its bit is zero. Under that encoding, every accepting
diagonal transcript consumes at least n units of snapshot curvature. -/
theorem disjointness_anchored_curvature_lower_bound {n q : Nat}
    (transcript :
      Communication.Bits n → Communication.Bits n → (Fin q → Bool))
    (accepts : (Fin q → Bool) → Prop)
    (hrectangle : ∀ a a' b b',
      transcript a b = transcript a' b' →
        transcript a b' = transcript a b ∧
        transcript a' b = transcript a b)
    (haccept : ∀ a,
      accepts (transcript a (fun i => !a i)))
    (hsound : ∀ a b,
      accepts (transcript a b) → Communication.disjoint a b)
    (a : Communication.Bits n) :
    (n : ℚ) ≤
      anchoredTranscriptCost (transcript a (fun i => !a i)) := by
  have hslots := disjointness_requires_n_fixed_slots
    transcript accepts hrectangle haccept hsound
  have hcast : (n : ℚ) ≤ (q : ℚ) := by exact_mod_cast hslots
  exact hcast.trans (anchored_transcript_cost_ge_slots _)

end PVNP.CurvatureCommunication
