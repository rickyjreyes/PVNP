import PVNP.WCTPlaneWave
import PVNP.WCTLattice
import MathProofs.CubicQuinticFlow

/-!
# Definition-match bridge: PVNP's frozen WCT PDE ↔ `rickyjreyes/math` (`ReyesMath.Sobolev`)

`rickyjreyes/math` (commit `30a5ddc9271a107c355024a7241f13d86ec496a9`) proves global
well-posedness, continuous dependence and conservation for
`i ∂ₜu = (Δ + k²)²u − β|u|²u + γ|u|⁴u` in `H²(ℝ²)` (`ReyesMath.Sobolev.global_wellposed`,
`continuous_dependence`, `conservation`).  Before any PVNP claim relies on those theorems we
prove here that the *ingredients* coincide with PVNP's definitions:

* `fnl_eq_pvnp`, `fnl_eq_lattice`: the nonlinearities agree pointwise;
* `d1_comp`, `d2_comp`, `lap_comp`: PVNP's coordinate Laplacian of `ψ ∘ emb` is
  `ReyesMath.Sobolev.lapS ψ` (hence Mathlib's `Δ`) for every Schwartz `ψ` on `ℝ²`;
* `shifted_comp`, `opK_comp`: `(Δ + κ)` and `(Δ + κ)²` agree with `AS k`, `AS k ∘ AS k` for
  `κ = k²`;
* `hamDensity_comp`: PVNP's Hamiltonian density is `|AS k ψ|² + nfun β γ ψ`, the integrand
  of `ReyesMath.Sobolev.Esp`/`H2.energy`.

What does **not** match: the external theory lives on the whole plane `ℝ²` with data in
`H²(ℝ²)`; PVNP's frozen model `WCT-Phys` uses periodic boxes/tori, whose plane-wave states
are not in `H²(ℝ²)`.  The external theorems therefore do not apply to the torus model.
-/

open Complex

namespace PVNP.MathBridge

local notation "R2" => EuclideanSpace ℝ (Fin 2)

open ReyesMath.Sobolev in
/-- Coordinates `(x₁, x₂) ↦ x₁ e₀ + x₂ e₁ ∈ ℝ²`. -/
noncomputable def emb (p : ℝ × ℝ) : R2 := p.1 • ev 0 + p.2 • ev 1

theorem fnl_eq_pvnp (β γ : ℝ) (z : ℂ) :
    ReyesMath.Sobolev.fnl β γ z =
      -(β : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) * z + (γ : ℂ) * ((‖z‖ ^ 4 : ℝ) : ℂ) * z := by
  rw [ReyesMath.Sobolev.fnl_eq]; push_cast; ring

theorem fnl_eq_lattice {N : ℕ} [NeZero N] (β γ : ℝ) (u : PVNP.WCTLattice.Fld N) (j : ZMod N) :
    ReyesMath.Sobolev.fnl β γ (u j) = PVNP.WCTLattice.nlin β γ u j := by
  rw [ReyesMath.Sobolev.fnl_eq]; rfl

theorem nfun_eq (β γ : ℝ) (z : ℂ) :
    ReyesMath.Sobolev.nfun β γ z = -β / 2 * ‖z‖ ^ 4 + γ / 3 * ‖z‖ ^ 6 := rfl

theorem d1_comp (ψ : SchwartzMap R2 ℂ) :
    PVNP.WCTPlaneWave.d1 (fun p => ψ (emb p)) =
      fun p => ReyesMath.Sobolev.dS 0 ψ (emb p) := by
  funext p
  have he : HasDerivAt (fun s : ℝ => emb (s, p.2)) (ReyesMath.Sobolev.ev 0) p.1 := by
    have h := ((hasDerivAt_id p.1).smul_const (ReyesMath.Sobolev.ev (d := 2) 0)).add_const
      (p.2 • ReyesMath.Sobolev.ev (d := 2) 1)
    simpa [emb] using h
  have hψ := (ψ.differentiableAt (x := emb (p.1, p.2))).hasFDerivAt
  show deriv (fun s => ψ (emb (s, p.2))) p.1 = ReyesMath.Sobolev.dS 0 ψ (emb p)
  rw [ReyesMath.Sobolev.dS_apply]
  exact (hψ.comp_hasDerivAt p.1 he).deriv

theorem d2_comp (ψ : SchwartzMap R2 ℂ) :
    PVNP.WCTPlaneWave.d2 (fun p => ψ (emb p)) =
      fun p => ReyesMath.Sobolev.dS 1 ψ (emb p) := by
  funext p
  have he : HasDerivAt (fun s : ℝ => emb (p.1, s)) (ReyesMath.Sobolev.ev 1) p.2 := by
    have h := ((hasDerivAt_id p.2).smul_const (ReyesMath.Sobolev.ev (d := 2) 1)).const_add
      (p.1 • ReyesMath.Sobolev.ev (d := 2) 0)
    simpa [emb] using h
  have hψ := (ψ.differentiableAt (x := emb (p.1, p.2))).hasFDerivAt
  show deriv (fun s => ψ (emb (p.1, s))) p.2 = ReyesMath.Sobolev.dS 1 ψ (emb p)
  rw [ReyesMath.Sobolev.dS_apply]
  exact (hψ.comp_hasDerivAt p.2 he).deriv

/-- **PVNP's coordinate Laplacian is the external (= Mathlib) Laplacian.** -/
theorem lap_comp (ψ : SchwartzMap R2 ℂ) :
    PVNP.WCTPlaneWave.lap (fun p => ψ (emb p)) = fun p => ReyesMath.Sobolev.lapS ψ (emb p) := by
  funext p
  simp only [PVNP.WCTPlaneWave.lap]
  rw [d1_comp, d1_comp (ReyesMath.Sobolev.dS 0 ψ), d2_comp, d2_comp (ReyesMath.Sobolev.dS 1 ψ)]
  simp [ReyesMath.Sobolev.lapS, Fin.sum_univ_two]

theorem lap_comp_mathlib (ψ : SchwartzMap R2 ℂ) (p : ℝ × ℝ) :
    PVNP.WCTPlaneWave.lap (fun p => ψ (emb p)) p = InnerProductSpace.laplacian (⇑ψ) (emb p) := by
  rw [lap_comp]; exact ReyesMath.Sobolev.lapS_apply ψ (emb p)

theorem shifted_comp (k : ℝ) (ψ : SchwartzMap R2 ℂ) :
    PVNP.WCTPlaneWave.shifted (k ^ 2) (fun p => ψ (emb p)) =
      fun p => ReyesMath.Sobolev.AS k ψ (emb p) := by
  funext p
  simp only [PVNP.WCTPlaneWave.shifted, lap_comp, ReyesMath.Sobolev.AS]
  simp

/-- **`(Δ + κ)²` matches `AS k ∘ AS k` for `κ = k²`.** -/
theorem opK_comp (k : ℝ) (ψ : SchwartzMap R2 ℂ) (p : ℝ × ℝ) :
    PVNP.WCTPlaneWave.opK (k ^ 2) (fun p => ψ (emb p)) p =
      ReyesMath.Sobolev.AS k (ReyesMath.Sobolev.AS k ψ) (emb p) := by
  have h1 := lap_comp ψ
  have h2 := lap_comp (ReyesMath.Sobolev.lapS ψ)
  simp only [PVNP.WCTPlaneWave.opK]
  rw [h1, h2]
  simp only [ReyesMath.Sobolev.AS, map_add, map_smul, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **Hamiltonian densities agree**: PVNP's `hamDensity` is the integrand
`|AS k ψ|² + nfun β γ ψ` of the external energy. -/
theorem hamDensity_comp (k β γ : ℝ) (ψ : SchwartzMap R2 ℂ) (p : ℝ × ℝ) :
    PVNP.WCTPlaneWave.hamDensity (k ^ 2) β γ (fun p => ψ (emb p)) p =
      ‖ReyesMath.Sobolev.AS k ψ (emb p)‖ ^ 2 + ReyesMath.Sobolev.nfun β γ (ψ (emb p)) := by
  simp only [PVNP.WCTPlaneWave.hamDensity, shifted_comp, nfun_eq]
  ring

#print axioms opK_comp
#print axioms hamDensity_comp
#print axioms lap_comp_mathlib
#print axioms fnl_eq_pvnp
#print axioms fnl_eq_lattice

end PVNP.MathBridge
