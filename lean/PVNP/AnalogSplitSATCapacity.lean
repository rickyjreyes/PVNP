import PVNP.BandlimitedNoisyPacking
import PVNP.SplitSATCapacity

/-!
# Amplitude/noise packing for the split-SAT channel (closes an `analytic_not_lean` item)

`PVNP.SplitSATCapacity` proves, for every exact deterministic split-input
3-CNF protocol with rectangular transcripts and `m` slots over a `q`-letter
alphabet, the all-protocol bound `2ⁿ ≤ qᵐ`.  The step from an *analog*
amplitude channel to `q` was previously analytic only.

* `scalar_level_count`: a set of amplitude levels in `[−A, A]` that are
  pairwise `≥ 2η` apart (so that every received value within error `< η`
  decodes uniquely) has at most `1 + A/η` elements — the one-dimensional case
  of `PVNP.Packing.packing_card_le`.
* `analog_split_sat_capacity`: hence every such protocol whose slots carry
  robustly decodable amplitudes in `[−A, A]` satisfies
  `2ⁿ ≤ (1 + A/η)ᵐ`.

Scope: this is a lower bound on transcript resources for the *split-input*
problem under the rectangle and robust-decoding hypotheses; the split problem
has an `O(n)` centralized solver, so this is not a SAT time lower bound.
-/

namespace PVNP.AnalogSplitSAT

open PVNP.SplitSATCapacity

/-- Robustly separated amplitude levels in `[−A, A]` number at most `1 + A/η`. -/
theorem scalar_level_count (levels : Finset ℝ) {A η : ℝ} (hη : 0 < η) (hA : 0 ≤ A)
    (hrange : ∀ v ∈ levels, |v| ≤ A)
    (hsep : ∀ v ∈ levels, ∀ w ∈ levels, v ≠ w → 2 * η ≤ |v - w|) :
    (levels.card : ℝ) ≤ 1 + A / η := by
  have h := PVNP.Packing.packing_card_le (E := ℝ) levels hη hA
    (fun v hv => by simpa [Real.norm_eq_abs] using hrange v hv)
    (fun v hv w hw hvw => by simpa [Real.dist_eq] using hsep v hv w hw hvw)
  simpa [Module.finrank_self] using h

/-- **Analog split-SAT channel capacity**: `2ⁿ ≤ (1 + A/η)ᵐ`. -/
theorem analog_split_sat_capacity {n m : ℕ} (levels : Finset ℝ) {A η : ℝ} (hη : 0 < η)
    (hA : 0 ≤ A) (hrange : ∀ v ∈ levels, |v| ≤ A)
    (hsep : ∀ v ∈ levels, ∀ w ∈ levels, v ≠ w → 2 * η ≤ |v - w|)
    (protocol : Bits n → Bits n → (Fin m → levels))
    (accepts : (Fin m → levels) → Prop)
    (hrectangle : ∀ a a' b b',
      protocol a b = protocol a' b' →
        protocol a b' = protocol a b ∧ protocol a' b = protocol a b)
    (hcorrect : ∀ a b, accepts (protocol a b) ↔ ∃ z : Bits n, splitThreeSat a b z) :
    (2 : ℝ) ^ n ≤ (1 + A / η) ^ m := by
  have hnat := distributed_three_sat_transcript_capacity protocol accepts hrectangle hcorrect
  have hq := scalar_level_count levels hη hA hrange hsep
  have hcard : (Fintype.card levels : ℝ) = levels.card := by simp
  calc (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((Fintype.card levels ^ m : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (Fintype.card levels : ℝ) ^ m := by push_cast; ring
    _ ≤ (1 + A / η) ^ m := by
        rw [hcard]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hq m

end PVNP.AnalogSplitSAT
