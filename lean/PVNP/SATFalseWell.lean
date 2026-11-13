import PVNP.InterwovenSAT

/-!
# Part I, I-3: a satisfiable sign-blind SAT energy with a false local minimum

The sign-blind interwoven energy has an exact global zero-energy SAT
characterization, but that does not imply convergence of local energy
descent to a satisfying configuration.

We construct a seven-clause satisfiable 3-CNF:
 (x0 ∨ x1 ∨ x2)
 ∧ (¬x0 ∨ x1 ∨ x1)^2
 ∧ (¬x1 ∨ x2 ∨ x2)^2
 ∧ (¬x2 ∨ x0 ∨ x0)^2.

For positive-literal scores x, y, z, its logical penalty is
 (1-x)(1-y)(1-z)
 + 2[x(1-y)^2 + y(1-z)^2 + z(1-x)^2].

For 0 ≤ x,y,z ≤ 1/8 this energy is ≥ 1+(x+y+z)/2.
The all-false phase state has scores zero and energy one, whereas
the all-true phase state has energy zero. Since the sign-blind
coupling/curvature penalties are nonnegative and vanish on both binary
fields, the false field remains a *nonglobal local energy minimum* in
the admissible phase configuration model for any λ,μ ≥ 0.

This is a concrete obstruction to the claim that every local minimum of
the static interwoven energy solves SAT. It is NOT a lower bound on all
physical SAT solvers, not an assertion about the frozen Hamiltonian PDE,
and not a theorem about classical P versus NP.
-/

namespace PVNP.SATFalseWell

open PVNP.PartIPsiSat PVNP.InterwovenSAT

/-! ### Explicit 3-CNF -/

def p0 : Lit := ⟨0, true⟩
def p1 : Lit := ⟨1, true⟩
def p2 : Lit := ⟨2, true⟩
def n0 : Lit := ⟨0, false⟩
def n1 : Lit := ⟨1, false⟩
def n2 : Lit := ⟨2, false⟩

def cMain : Clause3 := fun k => if k = 0 then p0 else if k = 1 then p1 else p2
def c01 : Clause3 := fun k => if k = 0 then n0 else p1
def c12 : Clause3 := fun k => if k = 0 then n1 else p2
def c20 : Clause3 := fun k => if k = 0 then n2 else p0

def trapFormula : CNF3 := [cMain, c01, c01, c12, c12, c20, c20]

/-- The all-true assignment satisfies the full seven-clause formula. -/
theorem trapFormula_sat : Sat trapFormula := by
  refine ⟨fun _ => true, ?_⟩
  intro cl hcl
  simp only [trapFormula, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-! ### The exact phase-score energy -/

/-- The positive-literal score, between zero and one. -/
noncomputable def sPos (θ : ℕ → ℝ) (i : ℕ) : ℝ :=
  (1 + Real.cos (θ i)) / 2

theorem sPos_nonneg (θ : ℕ → ℝ) (i : ℕ) : 0 ≤ sPos θ i := by
  simpa [sPos, score, eta] using (score_mem θ ⟨i, true⟩).1

/-- Polynomial form of the actual Part I clause penalty on this 3-CNF. -/
def trapEnergy (x y z : ℝ) : ℝ :=
  (1-x)*(1-y)*(1-z) +
    2*(x*(1-y)^2 + y*(1-z)^2 + z*(1-x)^2)

/-- The identity uses the existing Part I `Elogic`, not a replacement
objective or an assumed correspondence. -/
theorem Elogic_trapFormula (θ : ℕ → ℝ) :
    Elogic θ trapFormula = trapEnergy (sPos θ 0) (sPos θ 1) (sPos θ 2) := by
  simp [Elogic, trapFormula, clausePen, Fin.prod_univ_three,
    score, eta, trapEnergy, sPos,
    cMain, c01, c12, c20, p0, p1, p2, n0, n1, n2]
  ring

/-! ### Exact nonglobal local well -/

/-- Elementary product bound for nonnegative phase scores. -/
private theorem base_lower {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - x - y - z ≤ (1-x)*(1-y)*(1-z) := by
  have hxy : 0 ≤ x*y*(1-z) :=
    mul_nonneg (mul_nonneg hx hy) (sub_nonneg.mpr hz1)
  have hzx : 0 ≤ z*(x+y) := mul_nonneg hz (add_nonneg hx hy)
  nlinarith [hxy, hzx]

/-- Under small scores the squared unsatisfied-literal factor remains
at least three quarters. -/
private theorem weighted_sq_lower {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1/8) :
    (3/4 : ℝ)*x ≤ x*(1-y)^2 := by
  have hs : (3/4 : ℝ) ≤ (1-y)^2 := by nlinarith [sq_nonneg y]
  have hp : 0 ≤ x*((1-y)^2 - 3/4) :=
    mul_nonneg hx (sub_nonneg.mpr hs)
  nlinarith [hp]

/-- In a full phase-score box around the false assignment, the logical
energy is bounded away from the satisfying zero-energy level. -/
theorem trapEnergy_local_lower {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxu : x ≤ 1/8) (hyu : y ≤ 1/8) (hzu : z ≤ 1/8) :
    1 + (x+y+z)/2 ≤ trapEnergy x y z := by
  have hb := base_lower hx hy hz (by linarith : z ≤ 1)
  have h1 := weighted_sq_lower hx hyu
  have h2 := weighted_sq_lower hy hzu
  have h3 := weighted_sq_lower hz hxu
  unfold trapEnergy
  nlinarith [hb, h1, h2, h3]

theorem trapEnergy_false : trapEnergy 0 0 0 = 1 := by norm_num [trapEnergy]
theorem trapEnergy_true : trapEnergy 1 1 1 = 0 := by norm_num [trapEnergy]

/-- The false-score point is a strict minimum within the small box:
energy 1 can only occur at (0,0,0). -/
theorem false_score_is_local_min {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxu : x ≤ 1/8) (hyu : y ≤ 1/8) (hzu : z ≤ 1/8) :
    1 ≤ trapEnergy x y z ∧
      (trapEnergy x y z = 1 → x = 0 ∧ y = 0 ∧ z = 0) := by
  have hl := trapEnergy_local_lower hx hy hz hxu hyu hzu
  constructor
  · nlinarith
  · intro he
    have hs : x + y + z ≤ 0 := by linarith
    constructor
    · linarith
    constructor <;> linarith

/-- The all-false and all-true phase assignments have energies 1 and 0. -/
theorem false_phase_energy :
    Elogic (fun _ => Real.pi) trapFormula = 1 := by
  rw [Elogic_trapFormula]
  norm_num [sPos, trapEnergy]

theorem true_phase_energy :
    Elogic (fun _ => 0) trapFormula = 0 := by
  rw [Elogic_trapFormula]
  norm_num [sPos, trapEnergy]

/-- For every nonnegative sign-blind coupling and curvature strength,
the satisfiable example has a nonglobal positive-energy local well.
The neighborhood is specified by scores s_i ≤ 1/8, hence includes a
phase-torus neighborhood of the all-false configuration. -/
theorem signblind_false_local_well {lam mu : ℝ}
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    Sat trapFormula ∧
      energySB trapFormula lam mu (fieldOf (fun _ => false)) = 1 ∧
      energySB trapFormula lam mu (fieldOf (fun _ => true)) = 0 ∧
      (∀ Ψ : ℕ → ℂ, Admissible Ψ →
        sPos (phases Ψ) 0 ≤ 1/8 →
        sPos (phases Ψ) 1 ≤ 1/8 →
        sPos (phases Ψ) 2 ≤ 1/8 →
        1 ≤ energySB trapFormula lam mu Ψ) := by
  refine ⟨trapFormula_sat, ?_, ?_, ?_⟩
  · rw [energySB_fieldOf]
    simpa [phaseOf] using false_phase_energy
  · rw [energySB_fieldOf]
    simpa [phaseOf] using true_phase_energy
  · intro Ψ hΨ h0 h1 h2
    have hlogical : 1 ≤ Elogic (phases Ψ) trapFormula := by
      rw [Elogic_trapFormula]
      have hl := (false_score_is_local_min
        (sPos_nonneg (phases Ψ) 0)
        (sPos_nonneg (phases Ψ) 1)
        (sPos_nonneg (phases Ψ) 2) h0 h1 h2).1
      exact hl
    have henergy := energySB_ge_Elog trapFormula hlam hmu hΨ
    unfold Elog at henergy
    linarith

end PVNP.SATFalseWell
