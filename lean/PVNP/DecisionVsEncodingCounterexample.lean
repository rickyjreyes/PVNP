import PVNP.BandlimitedNoisyPacking

/-!
# Decision versus encoding: the packing bound is not a decision lower bound (issue #15)

The packing theorem `PVNP.Packing.complex_receiver_packing` counts
*independently recoverable labels*.  A decision procedure only has to make
**two** outcomes robustly distinguishable.

* `two_codeword_readout`: for every `η > 0` there are two codewords in `ℂ¹`
  of norm `η` (so mass `M = η²`) at distance exactly `2η`.
* `robust_decision_readout`: for **every** language `L` and every input length,
  the readout `x ↦ codeword (x ∈ L)` with nearest-codeword decoding recovers
  membership under every adversarial error of norm `< η`.
* `promoted_bound_false`: the "promoted" claim that every η-robust decision
  readout of `n`-bit inputs must obey the storage bound
  `2ⁿ ≤ (1 + √M/η)^{2D}` is **false** (counterexample `D = 1`, `M = η²`, `n = 3`).
* `decision_forgets_witnesses`: distinct witness sets can produce the same
  decision, so a decider need not identify satisfying assignments; the
  decision map takes at most two values regardless of `n`.
-/

namespace PVNP.DecisionVsEncoding

open PVNP.Packing

/-- Receiver space with one complex mode. -/
abbrev C1 := EuclideanSpace ℂ (Fin 1)

/-- Unit vector of `ℂ¹`. -/
noncomputable def e1 : C1 := EuclideanSpace.single 0 1

theorem norm_e1 : ‖e1‖ = 1 := by simp [e1]

/-- The two decision codewords. -/
noncomputable def codeword (η : ℝ) (b : Bool) : C1 := if b then (η : ℂ) • e1 else (-(η : ℂ)) • e1

theorem norm_codeword {η : ℝ} (hη : 0 ≤ η) (b : Bool) : ‖codeword η b‖ = η := by
  cases b <;> simp [codeword, norm_smul, norm_e1, abs_of_nonneg hη]

theorem dist_codeword {η : ℝ} (hη : 0 ≤ η) : dist (codeword η true) (codeword η false) = 2 * η := by
  rw [dist_eq_norm]
  simp only [codeword, if_true, Bool.false_eq_true, if_false]
  rw [← sub_smul, norm_smul, norm_e1, mul_one]
  have : (η : ℂ) - -(η : ℂ) = ((2 * η : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- Two η-separated codewords of mass `η²` exist in a single complex mode. -/
theorem two_codeword_readout {η : ℝ} (hη : 0 < η) :
    (∀ b, ‖codeword η b‖ ≤ Real.sqrt (η ^ 2)) ∧
      2 * η ≤ dist (codeword η true) (codeword η false) := by
  refine ⟨fun b => by rw [norm_codeword hη.le, Real.sqrt_sq hη.le], ?_⟩
  rw [dist_codeword hη.le]

/-- Nearest-codeword decoder. -/
noncomputable def decode (η : ℝ) (y : C1) : Bool :=
  decide (dist y (codeword η true) < dist y (codeword η false))

theorem decode_correct {η : ℝ} (hη : 0 < η) (b : Bool) (err : C1) (herr : ‖err‖ < η) :
    decode η (codeword η b + err) = b := by
  have hd := dist_codeword hη.le
  have hnear : dist (codeword η b + err) (codeword η b) < η := by
    rw [dist_eq_norm, add_sub_cancel_left]; exact herr
  have hfar : η < dist (codeword η b + err) (codeword η (!b)) := by
    have htri := dist_triangle (codeword η b) (codeword η b + err) (codeword η (!b))
    have hbb : dist (codeword η b) (codeword η (!b)) = 2 * η := by
      cases b
      · rw [dist_comm]; simpa using hd
      · simpa using hd
    rw [dist_comm] at hnear
    linarith
  cases b
  · simp only [decode, decide_eq_false_iff_not, not_lt]
    simp only [Bool.not_false] at hfar
    rw [dist_comm] at hnear
    linarith [dist_comm (codeword η false + err) (codeword η false)]
  · simp only [decode, decide_eq_true_eq]
    simp only [Bool.not_true] at hfar
    linarith

/-- An η-robust decision readout of `L` on inputs of length `n`, through a
complex `D`-mode receiver with mass bound `M`. -/
def RobustDecisionReadout (L : Set (List Bool)) (n D : ℕ) (M η : ℝ)
    (readout : List Bool → EuclideanSpace ℂ (Fin D)) : Prop :=
  (∀ x : List Bool, x.length = n → ‖readout x‖ ≤ Real.sqrt M) ∧
  ∃ dec : EuclideanSpace ℂ (Fin D) → Bool, ∀ x : List Bool, x.length = n →
    ∀ err, ‖err‖ < η → (dec (readout x + err) = true ↔ x ∈ L)

open Classical in
/-- **Every** language has a one-mode, mass-`η²` robust decision readout at
every input length. -/
theorem robust_decision_readout (L : Set (List Bool)) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    RobustDecisionReadout L n 1 (η ^ 2) η (fun x => codeword η (decide (x ∈ L))) := by
  refine ⟨fun x _ => (two_codeword_readout hη).1 _, decode η, fun x _ err herr => ?_⟩
  rw [decode_correct hη _ err herr]
  simp

/-- **The storage bound cannot be promoted to a decision bound.** -/
theorem promoted_bound_false {η : ℝ} (hη : 0 < η) :
    ¬ ∀ (L : Set (List Bool)) (n D : ℕ) (M : ℝ)
        (readout : List Bool → EuclideanSpace ℂ (Fin D)),
        RobustDecisionReadout L n D M η readout →
          (2 : ℝ) ^ n ≤ (1 + Real.sqrt M / η) ^ (2 * D) := by
  classical
  intro h
  have := h ∅ 3 1 (η ^ 2) _ (robust_decision_readout ∅ 3 hη)
  rw [Real.sqrt_sq hη.le, div_self hη.ne'] at this
  norm_num at this

/-- Two different witness sets yield the same decision. -/
theorem decision_forgets_witnesses (n : ℕ) (hn : 0 < n) :
    ∃ S T : Finset (Fin n → Bool), S ≠ T ∧ (S.Nonempty ↔ T.Nonempty) := by
  refine ⟨{fun _ => true}, {fun _ => false}, ?_, by simp⟩
  intro h
  have h1 := Finset.singleton_inj.1 h
  have := congrFun h1 ⟨0, hn⟩
  simp at this

/-- The decision map on any finite input set has at most two values. -/
theorem decision_image_card_le_two {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → Bool) : (Finset.univ.image f).card ≤ 2 := by
  calc (Finset.univ.image f).card ≤ (Finset.univ : Finset Bool).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := by simp

end PVNP.DecisionVsEncoding
