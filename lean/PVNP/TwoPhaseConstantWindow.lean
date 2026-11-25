import PVNP.TwoPhaseFixedWord

/-!
# Phase XIV: actual MTM output machine for the constant original W_M window

This is a specialization of the generic finite-state, single-tape output writer under the Part II
`MTM.Outputs` convention.  It handles every input, including the empty
word, when the radius polynomial is identically zero.  The target word is
`[1,0,0,1,0]`, namely the complete canonical code

  1^(0+1) 0 0 1^(2*0+1) 0.

Unlike a mere output-length theorem, `zeroWindowCode_fp` exhibits an
explicit Turing machine and a constant transition bound.

The nonconstant polynomial-radius writer, and the original input-encoder
writer, still require their own concrete finite-control transducers.
No general II-10 claim is discharged by this special case.
-/

namespace PVNP.TwoPhaseConstantWindow

open PVNP.PartIITuring PVNP.PartIIUniform
open PVNP.TwoPhaseUniform PVNP.TwoPhaseWindowWord

/-- The fixed five-bit zero-radius machine.  It uses the same one-cell
finite-control transitions as the generic literal writer, specialized to
the original canonical zero-radius W_M output. -/
def zeroWindowMTM : MTM :=
  TwoPhaseFixedWord.literalMTM [true, false, false, true, false]

/-- First-halt output for every input, including the empty input. This is
a specialization of the general fixed-word transition proof, rather than
a six-step full-tape normalization by definitional equality. -/
theorem zeroWindowMTM_outputs (x : List Bool) :
    zeroWindowMTM.Outputs x [true, false, false, true, false] 6 := by
  simpa only [zeroWindowMTM] using
    (TwoPhaseFixedWord.literalMTM_outputs [true, false, false, true, false] x)

/-- The original manuscript definition, not a substitute encoding, gives
the literal word above when the radius polynomial is zero. -/
theorem originalWindowCode_zero (x : List Bool) :
    originalWindowCode (0 : Polynomial ℕ) x =
      [true, false, false, true, false] := by
  simp [originalWindowCode_eq_windowWord, windowWord] <;> decide

/-- An explicit `FP` certificate for the original lattice writer at
the zero polynomial, with actual six-step single-tape transitions. -/
theorem zeroWindowCode_fp :
    FP (originalWindowCode (0 : Polynomial ℕ)) := by
  refine ⟨zeroWindowMTM, Polynomial.C 6, ?_⟩
  intro x
  simpa [originalWindowCode_zero] using zeroWindowMTM_outputs x

end PVNP.TwoPhaseConstantWindow
