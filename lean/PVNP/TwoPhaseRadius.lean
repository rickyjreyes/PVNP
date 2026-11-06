import PVNP.CookLevinGen

/-!
# Phase XII: reuse the verified Horner unary counter for the original W_M window

The existing Cook–Levin sweep compiler computes any fixed natural-coefficient
polynomial in the input length as unary marks, with a charged bound on sweep
round trips. This module instantiates it at radius p(n)+1, which is exactly
the margin needed by the author's radius-one two-phase WCC machine.

It does not yet write the complete membership bitmap or establish
`FP (TwoPhaseUniform.originalWindowCode p)`.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim

/-- A verified unary sweep program computes the original two-phase machine's
bounding-box radius `p(n)+1`, in at most the Horner phase's explicit
round-trip count. The program is the same finite-control `Ctrl` compiled
by the established `Prog.toTM` framework. -/
theorem twoPhase_unary_radius (p : Polynomial ℕ) (n : ℕ)
    (l : List Cell) (hl : 0 < l.length) (hi : InpR l n)
    (h1 : Run l .ut 0) (h2 : Run l .st 0) :
    ∃ l' k, RN (hparT p).ctrl.prog ((hparT p).ctrl.start, l) (.fin, l') k ∧
      Run l' .ut (p.eval n + 1) ∧
      k ≤ (hparT p).cs.length * (hparT p).stepBound n := by
  obtain ⟨l', k, hr, hm, _, _, hk⟩ :=
    HPar.horner_phase (P := hparT p) (good_T p) n l hl hi h1 h2
  refine ⟨l', k, hr, ?_, hk⟩
  simpa [hparT, horner_hcoeffs] using hm

end PVNP.CookLevin.Gen
