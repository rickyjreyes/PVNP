import PVNP.WCCGenerality

/-!
# Finite propagation and finite active region on multidimensional WCC lattices

This module formalizes the finite causal region of the frozen quiescent
Moore-neighbourhood cellular automaton on Z^(1+d).  It is a prerequisite for
a polynomial-overhead finite-support single-tape TM simulation (D-1), not
itself a proof of that simulation.
-/

namespace PVNP.Discrete.WCCD

variable {d : ℕ} (A : WCCD d)

/-- A conservative rectangular active region after `t` synchronous steps.
The input occupies the first coordinate axis; the origin is included even
for empty input. -/
def InCone (x : List Bool) (t : ℕ) (p : Site d) : Prop :=
  -(t : ℤ) ≤ p.1 ∧
    p.1 ≤ (x.length : ℤ) + (t : ℤ) ∧
    ∀ i : Fin d, -(t : ℤ) ≤ p.2 i ∧ p.2 i ≤ (t : ℤ)

/-- Every Moore-neighbourhood offset is in `[-1,1]`. -/
theorem off_bounds (u : Fin 3) : -1 ≤ off u ∧ off u ≤ 1 := by
  fin_cases u <;> decide

/-- The initial configuration is blank outside its finite axis segment. -/
theorem init_blank_outside (x : List Bool) (p : Site d)
    (hout : ¬ InCone x 0 p) : A.init x p = A.blank := by
  by_cases haxis : p.2 = 0
  · have hrange : ¬ ((0 : ℤ) ≤ p.1 ∧ p.1 ≤ (x.length : ℤ)) := by
      intro hj
      apply hout
      refine ⟨by simpa [InCone] using hj.1, by simpa [InCone] using hj.2, ?_⟩
      intro i
      have hqi : p.2 i = 0 := congrFun haxis i
      simp [hqi]
    have hbad : p.1 < 0 ∨ (x.length : ℤ) < p.1 := by omega
    rcases hbad with hneg | hhigh
    · simp [WCCD.init, haxis, show p.1 ≠ 0 by omega,
          show ¬(0 < p.1 ∧ p.1 < (x.length : ℤ)) by omega]
    · simp [WCCD.init, haxis, show p.1 ≠ 0 by omega,
          show ¬(0 < p.1 ∧ p.1 < (x.length : ℤ)) by omega]
  · simp [WCCD.init, haxis]

/-- Finite propagation speed: after `t` steps the configuration agrees with
the quiescent blank outside a width-`t` rectangular neighborhood of input. -/
theorem run_blank_outside (x : List Bool) (t : ℕ) (p : Site d)
    (hout : ¬ InCone x t p) :
    A.run (A.init x) t p = A.blank := by
  induction t generalizing p with
  | zero =>
      exact A.init_blank_outside x p hout
  | succ t ih =>
      rw [A.run_succ]
      change A.rule (fun u => A.run (A.init x) t
        (p.1 + off u.1, fun i => p.2 i + off (u.2 i))) = A.blank
      have hneigh : ∀ u : Fin 3 × (Fin d → Fin 3),
          ¬ InCone x t
            (p.1 + off u.1, fun i => p.2 i + off (u.2 i)) := by
        intro u hin
        apply hout
        rcases hin with ⟨hlo, hhi, hq⟩
        have hb := off_bounds u.1
        refine ⟨?_, ?_, ?_⟩
        · dsimp [InCone] at *
          omega
        · dsimp [InCone] at *
          omega
        · intro i
          have hbi := off_bounds (u.2 i)
          have hqi := hq i
          dsimp [InCone] at *
          constructor <;> omega
      have hblank : (fun u : Fin 3 × (Fin d → Fin 3) =>
          A.run (A.init x) t
            (p.1 + off u.1, fun i => p.2 i + off (u.2 i))) =
          (fun _ => A.blank) := by
        funext u
        exact ih _ (hneigh u)
      rw [hblank, A.quiescent]

/-- Explicit leftward causal bound in every fixed spatial dimension. -/
theorem run_blank_left (x : List Bool) (t : ℕ) (p : Site d)
    (hp : p.1 < -(t : ℤ)) :
    A.run (A.init x) t p = A.blank :=
  A.run_blank_outside x t p (fun h => by
    exact (not_le_of_gt hp) h.1)

/-- Explicit rightward causal bound in every fixed spatial dimension. -/
theorem run_blank_right (x : List Bool) (t : ℕ) (p : Site d)
    (hp : (x.length : ℤ) + (t : ℤ) < p.1) :
    A.run (A.init x) t p = A.blank :=
  A.run_blank_outside x t p (fun h => by
    exact (not_le_of_gt hp) h.2)

/-- Explicit transverse causal bound in every fixed spatial dimension. -/
theorem run_blank_transverse (x : List Bool) (t : ℕ) (p : Site d)
    (i : Fin d) (hp : p.2 i < -(t : ℤ) ∨ (t : ℤ) < p.2 i) :
    A.run (A.init x) t p = A.blank :=
  A.run_blank_outside x t p (fun h => by
    rcases hp with hl | hr
    · exact (not_le_of_gt hl) (h.2.2 i).1
    · exact (not_le_of_gt hr) (h.2.2 i).2)

end PVNP.Discrete.WCCD
