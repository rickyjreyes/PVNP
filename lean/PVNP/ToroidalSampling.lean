import PVNP.PhasePenaltyGap
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Smooth phase lifts on a circle with prescribed winding. The samples carry
the manuscript's logical energy; this interpolation does not impose WCT dynamics. -/
namespace PVNP.ToroidalSampling
open PartIPsiSat Polynomial

noncomputable def node (n j : ℕ) : ℝ := Real.arccos ((j : ℝ)/(n+1))
noncomputable def lift (k : ℤ) (p : Polynomial ℝ) (s : ℝ) : ℝ :=
  (k : ℝ)*s + p.eval (Real.cos s)

theorem winding (k : ℤ) (p : Polynomial ℝ) (s : ℝ) :
    lift k p (s+2*Real.pi) = lift k p s + 2*Real.pi*k := by
  simp [lift,Real.cos_add_two_pi]; ring

theorem smooth (k : ℤ) (p : Polynomial ℝ) : ContDiff ℝ (⊤ : ℕ∞) (lift k p) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => p.eval t) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
    | monomial j a =>
      simpa only [Polynomial.eval_monomial] using
        (contDiff_const (c := a)).mul (contDiff_id.pow j)
  exact (contDiff_const.mul contDiff_id).add (hp.comp Real.contDiff_cos)

/-- A trigonometric polynomial correction of the winding lift interpolates
any real values at the n marked sites, for any prescribed integer winding. -/
theorem interpolate (n : ℕ) (k : ℤ) (a : Fin n → ℝ) :
    ∃ p : Polynomial ℝ, ∀ j : Fin n, lift k p (node n j) = a j := by
  classical
  let z := fun j : Fin n => (j.val:ℝ)/(n+1)
  have hz : Function.Injective z := by
    intro i j h
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    have h' : (i.val:ℝ) = (j.val:ℝ) := (div_left_inj' hn).mp h
    exact Fin.ext (by exact_mod_cast h')
  let v := fun j : Fin n => a j - k * node n j
  refine ⟨Lagrange.interpolate Finset.univ z v, fun j => ?_⟩
  have h0 : 0 ≤ z j := by dsimp [z]; positivity
  have h1 : z j ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n:ℝ)+1)).mpr
    exact_mod_cast (by omega : j.val ≤ n+1)
  have hcos : Real.cos (node n j) = z j := Real.cos_arccos (by linarith) h1
  rw [lift,hcos,Lagrange.eval_interpolate_at_node v hz.injOn (Finset.mem_univ j)]
  dsimp [v]; ring

private theorem energy_congr {n : ℕ} {θ η : ℕ → ℝ} (F : CNF3)
    (hF : ∀ c ∈ F, ∀ j, (c j).v < n) (same : ∀ i < n, θ i = η i) :
    Elogic θ F = Elogic η F := by
  unfold Elogic
  congr 1
  apply List.map_congr_left
  intro c hc
  unfold clausePen
  apply Finset.prod_congr rfl
  intro i _
  simp [score,same _ (hF c hc i)]

/-- Every bounded three-CNF admits a zero-energy smooth phase lift of any
prescribed winding exactly when it is satisfiable. The reverse direction also
holds below the existing strict threshold. -/
theorem sat_iff_sampled_zero (n : ℕ) (F : CNF3) (k : ℤ)
    (hF : ∀ c ∈ F, ∀ j, (c j).v < n) :
    Sat F ↔ ∃ p : Polynomial ℝ, Elogic (fun i => lift k p (node n i)) F = 0 := by
  constructor
  · intro h
    obtain ⟨θ,hθ⟩ := (psi_sat_completeness F).2.mp h
    obtain ⟨p,hp⟩ := interpolate n k (fun j => θ j.val)
    refine ⟨p, (energy_congr F hF ?_).trans hθ⟩
    intro i hi; exact hp ⟨i,hi⟩
  · rintro ⟨p,hp⟩; exact (psi_sat_completeness F).2.mpr ⟨_,hp⟩

end PVNP.ToroidalSampling
