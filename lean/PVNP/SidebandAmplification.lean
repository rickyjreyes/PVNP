import Mathlib

/-!
# A genuine exponential mode of the constant-background linearization

The constant plane wave of the frozen PDE gives, on a real cosine
sideband, x' = H*y, y' = -(H+2*c)*x with
H=q²-2κq, c=a²(-β+2γa²).
This module proves the linearized mode algebra and the explicit
growing solution of that two-dimensional system. The connection to
the Fréchet derivative of the full PDE flow is not formalized here.
-/
namespace PVNP.SidebandAmplification

def H (κ q : ℝ) : ℝ := q^2-2*κ*q
def c (a β γ : ℝ) : ℝ := a^2*(-β+2*γ*a^2)
def discriminant (κ q a β γ : ℝ) : ℝ :=
  -H κ q * (H κ q + 2*c a β γ)

theorem growing_rate {h g : ℝ} (hu : 0 < -h*(h+2*g)) :
    ∃ λ : ℝ, 0 < λ ∧ λ^2 = -h*(h+2*g) := by
  exact ⟨Real.sqrt (-h*(h+2*g)), Real.sqrt_pos.2 hu,
    Real.sq_sqrt hu.le⟩

theorem eigenvector {h g λ : ℝ} (hλ : λ^2 = -h*(h+2*g)) :
    h*λ = λ*h ∧ -(h+2*g)*h = λ*λ := by
  constructor
  · ring
  · nlinarith only [hλ]

theorem explicit_growing_sideband :
    H 0 1 = 1 ∧ c 1 2 (1/2) = -1 ∧
    discriminant 0 1 1 2 (1/2) = 1 := by
  norm_num [H,c,discriminant]

theorem exponential_solution (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp s) (H 0 1 * Real.exp t) t ∧
    HasDerivAt (fun s : ℝ => Real.exp s)
      (-(H 0 1 + 2*c 1 2 (1/2))*Real.exp t) t := by
  constructor <;> simpa [H,c] using Real.hasDerivAt_exp t

end PVNP.SidebandAmplification
