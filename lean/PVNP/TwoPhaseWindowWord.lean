import PVNP.TwoPhaseWindowShape

/-!
# Phase XIV: the entire canonical lattice output word

The Phase XIII theorem checked the membership bit at each site.  This
module packages those pointwise results into an exact equality of complete
output words, including unary prefix, separator, and every bitmap bit.

It is a semantic correctness specification for the intended MTM writer,
not yet an `FP` witness.  An `FP` witness additionally requires a concrete
single-tape transducer and a polynomial upper bound on its transition count.
-/

namespace PVNP.TwoPhaseWindowWord

open PVNP.PartIIUniform PVNP.PartIITwoPhase
open PVNP.TwoPhaseDecoder PVNP.TwoPhaseUniform PVNP.TwoPhaseWindowShape

/-- Construct the complete expected output from the unary-radius clock
and a formula for the interior of the bounding box. -/
def windowWord (L : ℕ) : List Bool :=
  List.replicate (L + 1) true ++
    (false :: (List.range (2 * (L + 1) + 1)).map
      (fun j => decide (0 < j ∧ j < 2 * (L + 1))))

/-- Every bit of the encoded bounding-box bitmap agrees with the simple
strict-interior predicate.  No approximation or finite-horizon argument. -/
theorem bitmap_eq_interior (L : ℕ) :
    ((boxIdx 1 (L + 1)).map
      (fun j => decide (site 1 (L + 1) j ∈ window L))) =
    ((List.range (2 * (L + 1) + 1)).map
      (fun j => decide (0 < j ∧ j < 2 * (L + 1)))) := by
  simp only [boxIdx, pow_one, side]
  apply List.map_congr_left
  intro j hj
  exact original_window_bit L j (List.mem_range.mp hj)

/-- Full output identity: prefix + separator + every bitmap position.
The bounded-window prefix is not just a size estimate. -/
theorem windowWord_eq_latCode (L : ℕ) :
    windowWord L = latCode 1 (L + 1) (window L) := by
  unfold windowWord latCode
  rw [bitmap_eq_interior]

/-- The original `W_M` lattice generator has precisely this closed-form
output for every input and every polynomial radius clock. -/
theorem originalWindowCode_eq_windowWord (p : Polynomial ℕ)
    (x : List Bool) :
    originalWindowCode p x = windowWord (p.eval x.length) := by
  change latCode 1 (p.eval x.length + 1) (window (p.eval x.length)) = _
  exact (windowWord_eq_latCode (p.eval x.length)).symm

/-- The canonical writer's complete output length is polynomially bounded
and agrees with the fixed unary-plus-bitmap structure. -/
theorem windowWord_length (L : ℕ) :
    (windowWord L).length = 3 * L + 5 := by
  simp [windowWord]
  omega

/-- The concrete original WCC encoding has the exact claimed length,
now derived from an explicit complete output word. -/
theorem originalWindowCode_length_from_word
    (p : Polynomial ℕ) (x : List Bool) :
    (originalWindowCode p x).length = 3 * p.eval x.length + 5 := by
  rw [originalWindowCode_eq_windowWord, windowWord_length]

end PVNP.TwoPhaseWindowWord
