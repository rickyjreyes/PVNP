import PVNP.RadiusCausality

/-!
# Arbitrary finite pipelines of charged local computations

Each stage carries its own synchronous finite-radius machine and round
budget. Unlike an uncharged encoder, every intermediate transformation is
included in the total causal radius. This extends the two-stage proof in
RadiusCausality to *any finite list* of heterogeneous local stages.

All conclusions are for the explicitly defined bounded one-dimensional
tape model. They are not classical circuit or P-vs-NP lower bounds.
-/

namespace PVNP.MultiStageCausality

open PVNP.PartII PVNP.LocalityLowerBound PVNP.RadiusCausality

variable {S : Type}

/-- One charged local stage, with a machine-dependent radius and time budget. -/
structure Stage (S : Type) where
  radius : Nat
  rounds : Nat
  machine : RadiusMachine S radius

/-- Run heterogeneous local stages sequentially on a fixed finite tape. -/
def runStages {n : Nat} : List (Stage S) → Configuration n S → Configuration n S
  | [], c => c
  | st :: rest, c =>
      runStages rest (iterate (step st.machine) st.rounds c)

/-- The complete charged information-propagation budget. -/
def totalReach : List (Stage S) → Nat
  | [] => 0
  | st :: rest => st.rounds * st.radius + totalReach rest

/-- Agreement survives arbitrarily many charged local preprocessing,
computation and postprocessing stages, with all radii and rounds counted. -/
theorem multistage_prefix {n : Nat} (stages : List (Stage S))
    (c d : Configuration n S) (m : Nat)
    (h : prefixAgree c d (totalReach stages + m)) :
    prefixAgree (runStages stages c) (runStages stages d) m := by
  induction stages generalizing c d with
  | nil =>
      simpa [runStages, totalReach] using h
  | cons st rest ih =>
      change prefixAgree
        (runStages rest (iterate (step st.machine) st.rounds c))
        (runStages rest (iterate (step st.machine) st.rounds d)) m
      apply ih
      apply prefix_iterate st.machine c d st.rounds (totalReach rest + m)
      simpa only [totalReach, Nat.add_assoc] using h

/-- Every decoder of the first m cells obeys the same cumulative bound. -/
theorem multistage_decoder_equal {n : Nat} (stages : List (Stage S))
    (c d : Configuration n S) (m : Nat) (hm : m ≤ n)
    (h : prefixAgree c d (totalReach stages + m))
    (decode : (Fin m → S) → Bool) :
    decode (fun i => (runStages stages c) ⟨i.val, by omega⟩) =
      decode (fun i => (runStages stages d) ⟨i.val, by omega⟩) := by
  have hp := multistage_prefix stages c d m h
  congr 1
  funext i
  exact hp ⟨i.val, by omega⟩ i.isLt

/-- No finite pipeline of charged radius-limited stages can decide the
last input bit from a prefix decoder when the total causal reach is too
small. This theorem has no restriction on the number of stages. -/
theorem no_multistage_prefix_last_bit
    (stages : List (Stage Bool)) (n m : Nat)
    (hfar : totalReach stages + m < n)
    (decode : (Fin m → Bool) → Bool) :
    ¬ (∀ c : Configuration n Bool,
      decode (fun i => (runStages stages c) ⟨i.val, by omega⟩) =
        c ⟨n - 1, by omega⟩) := by
  intro hall
  have hp : prefixAgree (allFalse n) (oneAt n (n - 1))
      (totalReach stages + m) := by
    intro i hi
    have hne : i.val ≠ n - 1 := by omega
    simp [allFalse, oneAt, hne]
  have heq := multistage_decoder_equal stages (allFalse n)
    (oneAt n (n - 1)) m (by omega) hp decode
  have hz : decode (fun i =>
      (runStages stages (allFalse n)) ⟨i.val, by omega⟩) = false := by
    simpa [allFalse] using (hall (allFalse n))
  have ho : decode (fun i =>
      (runStages stages (oneAt n (n - 1))) ⟨i.val, by omega⟩) = true := by
    simpa [oneAt] using (hall (oneAt n (n - 1)))
  rw [hz, ho] at heq
  cases heq

/-- The positive resource inequality required of *every* correct
finite-stage local pipeline with m output cells. -/
theorem multistage_required_causal_coverage
    (stages : List (Stage Bool)) (n m : Nat)
    (decode : (Fin m → Bool) → Bool)
    (hall : ∀ c : Configuration n Bool,
      decode (fun i => (runStages stages c) ⟨i.val, by omega⟩) =
        c ⟨n - 1, by omega⟩) :
    n ≤ totalReach stages + m := by
  by_contra h
  have hfar : totalReach stages + m < n := by omega
  exact (no_multistage_prefix_last_bit stages n m hfar decode) hall

end PVNP.MultiStageCausality
