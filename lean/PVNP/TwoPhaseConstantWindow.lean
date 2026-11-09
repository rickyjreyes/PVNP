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
open PVNP.TwoPhaseUniform PVNP.TwoPhaseWindowWord

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
  let T₀ := zeroWindowMTM.inputTape x
  let T₁ := Function.update T₀ (0 : ℤ) (some true)
  let T₂ := Function.update T₁ (1 : ℤ) (some false)
  let T₃ := Function.update T₂ (2 : ℤ) (some false)
  let T₄ := Function.update T₃ (3 : ℤ) (some true)
  let T₅ := Function.update T₄ (4 : ℤ) (some false)
  let T₆ := Function.update T₅ (5 : ℤ) (none)
  let cfg := zeroWindowMTM.run (zeroWindowMTM.init x)
  have c₀ : cfg 0 = ⟨T₀, 0, (0 : Fin 7)⟩ := rfl
  have c₁ : cfg 1 = ⟨T₁, 1, (1 : Fin 7)⟩ := by
    change zeroWindowMTM.run (zeroWindowMTM.init x) (0+1) = _
    rw [MTM.run_succ]; change zeroWindowMTM.step (cfg 0) = _
    rw [c₀]; rfl
  have c₂ : cfg 2 = ⟨T₂, 2, (2 : Fin 7)⟩ := by
    change zeroWindowMTM.run (zeroWindowMTM.init x) (1+1) = _
    rw [MTM.run_succ]; change zeroWindowMTM.step (cfg 1) = _
    rw [c₁]; rfl
  have c₃ : cfg 3 = ⟨T₃, 3, (3 : Fin 7)⟩ := by
    change zeroWindowMTM.run (zeroWindowMTM.init x) (2+1) = _
    rw [MTM.run_succ]; change zeroWindowMTM.step (cfg 2) = _
    rw [c₂]; rfl
  have c₄ : cfg 4 = ⟨T₄, 4, (4 : Fin 7)⟩ := by
    change zeroWindowMTM.run (zeroWindowMTM.init x) (3+1) = _
    rw [MTM.run_succ]; change zeroWindowMTM.step (cfg 3) = _
    rw [c₃]; rfl
  have c₅ : cfg 5 = ⟨T₅, 5, (5 : Fin 7)⟩ := by
    change zeroWindowMTM.run (zeroWindowMTM.init x) (4+1) = _
    rw [MTM.run_succ]; change zeroWindowMTM.step (cfg 4) = _
    rw [c₄]; rfl
  have c₆ : cfg 6 = ⟨T₆, 6, (6 : Fin 7)⟩ := by
    change zeroWindowMTM.run (zeroWindowMTM.init x) (5+1) = _
    rw [MTM.run_succ]; change zeroWindowMTM.step (cfg 5) = _
    rw [c₅]; rfl
  refine ⟨6, le_rfl, ⟨?_,?_⟩, ?_, ?_⟩
  · change zeroWindowMTM.Halting (cfg 6).q
    rw [c₆]; exact Or.inl rfl
  · intro s hs
    change ¬ zeroWindowMTM.Halting (cfg s).q
    interval_cases s <;> simp only [c₀,c₁,c₂,c₃,c₄,c₅] <;> decide
  · intro i hi
    change (cfg 6).tape i = _
    rw [c₆]
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> rfl
  · change (cfg 6).tape 5 = none
    rw [c₆]; rfl

/-- The original manuscript definition, not a substitute encoding, gives
the literal word above when the radius polynomial is zero. -/
theorem originalWindowCode_zero (x : List Bool) :
    originalWindowCode (0 : Polynomial ℕ) x =
      [true, false, false, true, false] := by
  rw [originalWindowCode_eq_windowWord, Polynomial.eval_zero]
  decide

/-- An explicit `FP` certificate for the original lattice writer at
the zero polynomial, with actual six-step single-tape transitions. -/
theorem zeroWindowCode_fp :
    FP (originalWindowCode (0 : Polynomial ℕ)) := by
  refine ⟨zeroWindowMTM, Polynomial.C 6, ?_⟩
  intro x
  simpa [originalWindowCode_zero] using zeroWindowMTM_outputs x

end PVNP.TwoPhaseConstantWindow
