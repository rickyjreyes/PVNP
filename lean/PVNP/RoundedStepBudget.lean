import PVNP.UniformGalerkinRadius

/-!
# Resource-counted time stepping: stability bootstrap

A finite time-stepping method must control truncation and rounding errors
without assuming that its numerical iterates stay in the stability ball.
This module isolates the discrete Gronwall argument, including the
radius bootstrap. The local defect and arithmetic costs are separate.
-/

namespace PVNP.TorusGalerkin

noncomputable def stepEnvelope (δ A h q : ℝ) (i : ℕ) : ℝ :=
  (δ + (i : ℝ)*q)*Real.exp (A*h*(i : ℝ))

theorem stepEnvelope_nonneg {δ A h q : ℝ} (hδ : 0 ≤ δ) (hq : 0 ≤ q) (i : ℕ) :
    0 ≤ stepEnvelope δ A h q i := by
  unfold stepEnvelope
  positivity

theorem stepEnvelope_mono {δ A h q : ℝ}
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hh : 0 ≤ h) (hq : 0 ≤ q)
    {i j : ℕ} (hij : i ≤ j) :
    stepEnvelope δ A h q i ≤ stepEnvelope δ A h q j := by
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  unfold stepEnvelope
  apply mul_le_mul
  · exact add_le_add_left (mul_le_mul_of_nonneg_right hij' hq) _
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hij' (mul_nonneg hA hh)
  · positivity
  · positivity

theorem stepEnvelope_succ {δ A h q : ℝ}
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hh : 0 ≤ h) (hq : 0 ≤ q) (i : ℕ) :
    (1+A*h)*stepEnvelope δ A h q i+q ≤ stepEnvelope δ A h q (i+1) := by
  have hbase : 0 ≤ δ+(i:ℝ)*q := by positivity
  have hf : 1+A*h ≤ Real.exp (A*h) := by linarith [Real.add_one_le_exp (A*h)]
  have hfac : 1 ≤ Real.exp (A*h*((i:ℝ)+1)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hexp : Real.exp (A*h*(i:ℝ))*Real.exp (A*h) =
      Real.exp (A*h*((i:ℝ)+1)) := by rw [← Real.exp_add]; congr 1 <;> ring
  unfold stepEnvelope
  rw [Nat.cast_add, Nat.cast_one]
  calc
    _ = (δ+(i:ℝ)*q)*Real.exp (A*h*(i:ℝ))*(1+A*h)+q := by ring
    _ ≤ (δ+(i:ℝ)*q)*Real.exp (A*h*(i:ℝ))*Real.exp (A*h)+q :=
      add_le_add_right (mul_le_mul_of_nonneg_left hf (by positivity)) _
    _ = (δ+(i:ℝ)*q)*Real.exp (A*h*((i:ℝ)+1))+q := by rw [mul_assoc, hexp]
    _ ≤ (δ+(i:ℝ)*q)*Real.exp (A*h*((i:ℝ)+1))+
        q*Real.exp (A*h*((i:ℝ)+1)) := by
      exact add_le_add_left (by simpa using mul_le_mul_of_nonneg_left hfac hq) _
    _ = _ := by ring

/-- The recurrence is only required when the previous error is within
the radius slack. The global budget certifies that it always is. -/
theorem rounded_step_bootstrap {e : ℕ → ℝ} {δ A h q b : ℝ} (N : ℕ)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hh : 0 ≤ h) (hq : 0 ≤ q)
    (h0 : e 0 ≤ δ)
    (hstep : ∀ i < N, e i ≤ b → e (i+1) ≤ (1+A*h)*e i+q)
    (hbudget : stepEnvelope δ A h q N ≤ b) :
    ∀ i ≤ N, e i ≤ stepEnvelope δ A h q i ∧ e i ≤ b := by
  have hmain : ∀ i ≤ N, e i ≤ stepEnvelope δ A h q i := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa [stepEnvelope] using h0
    | succ i ih =>
      intro hi
      have hi' : i ≤ N := by omega
      have he := ih hi'
      have hb := he.trans ((stepEnvelope_mono hδ hA hh hq hi').trans hbudget)
      exact (hstep i (by omega) hb).trans
        ((add_le_add_right (mul_le_mul_of_nonneg_left he (by positivity)) q).trans
          (stepEnvelope_succ hδ hA hh hq i))
  intro i hi
  exact ⟨hmain i hi, (hmain i hi).trans
    ((stepEnvelope_mono hδ hA hh hq hi).trans hbudget)⟩

/-- Explicit budget split: initial error, Euler local error, and
rounding error each receive one third of the pre-amplification budget. -/
theorem rounded_step_budget {δ A h D ξ T ε : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hh : 0 ≤ h)
    (hD : 0 ≤ D) (hξ : 0 ≤ ξ) (hT : (N:ℝ)*h = T)
    (hinit : δ*Real.exp (A*T) ≤ ε/3)
    (hdisc : D*h*T*Real.exp (A*T) ≤ ε/3)
    (hround : (N:ℝ)*ξ*Real.exp (A*T) ≤ ε/3) :
    stepEnvelope δ A h (D*h^2+ξ) N ≤ ε := by
  unfold stepEnvelope
  have ht : A*h*(N:ℝ) = A*T := by rw [← hT]; ring
  rw [ht]
  have he : (N:ℝ)*(D*h^2+ξ) = D*h*T+(N:ℝ)*ξ := by rw [← hT]; ring
  rw [he]
  linarith only [hinit,hdisc,hround]

end PVNP.TorusGalerkin
