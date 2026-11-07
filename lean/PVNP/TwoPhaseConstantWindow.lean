import PVNP.TwoPhaseWindowWord

/-!
# Phase XIV: actual MTM output machine for the constant original W_M window

This is a *real* finite-state, single-tape output writer under the Part II
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
open PVNP.TwoPhaseUniform

/-- Six transitions overwrite cells 0..4 with the canonical word and
write the required blank at cell 5.  The seventh control state is halting.
Remaining input cells to the right are irrelevant to `MTM.Shows`. -/
def zeroWindowMTM : MTM where
  Q := Fin 7
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank := fun _ => Option.some_ne_none _
  δ q a := match q with
    | 0 => (1, some true, .R)
    | 1 => (2, some false, .R)
    | 2 => (3, some false, .R)
    | 3 => (4, some true, .R)
    | 4 => (5, some false, .R)
    | 5 => (6, none, .R)
    | _ => (6, a, .R)
  q0 := 0
  qacc := 6
  qrej := 6

/-- The first halting time is six, independent of the incoming word;
the tape then satisfies the original output convention. -/
theorem zeroWindowMTM_outputs (x : List Bool) :
    zeroWindowMTM.Outputs x [true, false, false, true, false] 6 := by
  refine ⟨6, le_rfl, ⟨Or.inl rfl, fun s hs => ?_⟩, ?_, ?_⟩
  · interval_cases s
    · show ¬ ((0 : Fin 7) = 6 ∨ (0 : Fin 7) = 6); decide
    · show ¬ ((1 : Fin 7) = 6 ∨ (1 : Fin 7) = 6); decide
    · show ¬ ((2 : Fin 7) = 6 ∨ (2 : Fin 7) = 6); decide
    · show ¬ ((3 : Fin 7) = 6 ∨ (3 : Fin 7) = 6); decide
    · show ¬ ((4 : Fin 7) = 6 ∨ (4 : Fin 7) = 6); decide
    · show ¬ ((5 : Fin 7) = 6 ∨ (5 : Fin 7) = 6); decide
  · intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      simp at hi
      omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- The original manuscript definition, not a substitute encoding, gives
the literal word above when the radius polynomial is zero. -/
theorem originalWindowCode_zero (x : List Bool) :
    originalWindowCode (0 : Polynomial ℕ) x =
      [true, false, false, true, false] := by
  simp [originalWindowCode_eq_windowWord, TwoPhaseWindowWord.windowWord]

/-- An explicit `FP` certificate for the original lattice writer at
the zero polynomial, with actual six-step single-tape transitions. -/
theorem zeroWindowCode_fp :
    FP (originalWindowCode (0 : Polynomial ℕ)) := by
  refine ⟨zeroWindowMTM, Polynomial.C 6, ?_⟩
  intro x
  simpa [originalWindowCode_zero] using zeroWindowMTM_outputs x

end PVNP.TwoPhaseConstantWindow
