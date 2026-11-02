import PVNP.DecisionVsEncodingCounterexample

/-!
# Uniform sign encoding versus unrestricted receiver computation

The encoder below is *fixed*, coordinatewise, and independent of any
decision language. It stores n bits in n real amplitudes +1 or -1 with total
squared mass n. Under coordinatewise additive error strictly below 1,
the signs recover every bit exactly.

An arbitrary decoder can nonetheless decide ANY predicate after this
encoding, simply by applying the predicate to the recovered input.
This is a countermodel only to decision lower bounds that charge the
encoder and physical storage but fail to charge or restrict the decoder.
It does not assert that an arbitrary predicate is computable or that
a particular decoder runs in polynomial time.
-/

namespace PVNP.DecoderUniformity

variable {n : ℕ}

/-- Language-independent coordinatewise sign encoder. -/
def signCode (x : Fin n → Bool) : Fin n → ℝ :=
  fun i => if x i then 1 else -1

/-- Zero-threshold sign receiver. -/
def signDecode (y : Fin n → ℝ) : Fin n → Bool :=
  fun i => decide (0 < y i)

theorem signDecode_signCode (x : Fin n → Bool) :
    signDecode (signCode x) = x := by
  funext i
  cases hx : x i <;> simp [signDecode, signCode, hx]

/-- Total squared amplitude is exactly n, independent of the input. -/
theorem signCode_mass (x : Fin n → Bool) :
    (∑ i : Fin n, (signCode x i) ^ 2) = (n : ℝ) := by
  have hi : ∀ i : Fin n, (signCode x i) ^ 2 = (1 : ℝ) := by
    intro i
    cases hx : x i <;> norm_num [signCode, hx]
  simp [hi]

theorem signCode_injective : Function.Injective (signCode (n := n)) := by
  intro x y h
  have h' := congrArg (signDecode (n := n)) h
  simpa [signDecode_signCode] using h'

/-- Each coordinate remains decodable under adversarial error |e_i| < 1. -/
theorem signDecode_noise (x : Fin n → Bool) (e : Fin n → ℝ)
    (he : ∀ i, |e i| < 1) :
    signDecode (fun i => signCode x i + e i) = x := by
  funext i
  have hlo : -1 < e i := (abs_lt.mp (he i)).1
  have hhi : e i < 1 := (abs_lt.mp (he i)).2
  cases hx : x i
  · have hs : signCode x i = -1 := by simp [signCode, hx]
    have hnon : ¬ 0 < signCode x i + e i := by rw [hs]; linarith
    simp [signDecode, hx, hnon]
  · have hs : signCode x i = 1 := by simp [signCode, hx]
    have hpos : 0 < signCode x i + e i := by rw [hs]; linarith
    simp [signDecode, hx, hpos]

/-- An unrestricted, potentially noncomputable decoder can decide any
predicate after the same fixed sign encoder, even with bounded noise.
This imposes no runtime bound on the decoder. -/
theorem arbitrary_predicate_has_robust_decoder (L : Set (Fin n → Bool)) :
    ∃ decoder : (Fin n → ℝ) → Bool,
      ∀ x (e : Fin n → ℝ), (∀ i, |e i| < 1) →
        (decoder (fun i => signCode x i + e i) = true ↔ x ∈ L) := by
  classical
  refine ⟨fun y => decide (signDecode y ∈ L), ?_⟩
  intro x e he
  change decide (signDecode (fun i => signCode x i + e i) ∈ L) = true ↔ x ∈ L
  rw [signDecode_noise x e he]
  simp

/-- There are 2^n distinguishable sign-code labels at mass n in n real
coordinates; label count alone yields no superpolynomial mass bound. -/
theorem number_of_labels (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

end PVNP.DecoderUniformity
