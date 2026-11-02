import PVNP.TransportCalculus

/-!
# The WCT equation on the discrete torus: conservation and a *derived* flux inequality

The method-of-lines discretization of the frozen WCT PDE
`i ∂ₜψ = (Δ + κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ` on the discrete torus `ℤ/Nℤ` with
spacing `h` is the ODE system

`i żⱼ = (A(Az))ⱼ − β|zⱼ|² zⱼ + γ|zⱼ|⁴ zⱼ`,  `(Au)ⱼ = a(u_{j+1} + u_{j−1}) + b uⱼ`,

with `a = 1/h²`, `b = κ − 2/h²` (so `A = Δ_h + κ`).  Everything below holds for
arbitrary real `a, b` and every `N ≥ 1`, i.e. uniformly in the domain size.

* `ip_Aop`: `A` is self-adjoint (summation by parts on `ℤ/Nℤ`).
* `hasDerivAt_mass`, `mass_conserved`: exact conservation of `M = Σ|zⱼ|²`.
* `hasDerivAt_ham`, `ham_conserved`: exact conservation of
  `H = Σ|(Az)ⱼ|² − (β/2)Σ|zⱼ|⁴ + (γ/3)Σ|zⱼ|⁶`.
* `bandpass_le_ham`: `Σ|(Az)ⱼ|² ≤ H + (3β²/16γ)M` (`γ > 0`).
* `hasDerivAt_flux`, `flux_bound`: for a real detector weight `w` with
  `|w_{j+1} − wⱼ| ≤ ω`, the detected mass `J = Σ wⱼ|zⱼ|²` satisfies
  `J' = 2 Im⟨[A,w]z, Az⟩` and `|J'| ≤ 4|a| ω √M ‖Az‖` — **derived from the
  equation**, not assumed: the cubic–quintic term is a real multiple of `z`
  and drops out.
* `lattice_flux_inequality`: along every solution,
  `|J'(t)| ≤ Γ √D(t)` with `D(t) = ‖Az(t)‖` and the explicit constant
  `Γ = 4|a| ω √M₀ (H₀ + 3β²M₀/16γ)^{1/4}` fixed by the initial data.
* `lattice_curvature_time_bound`: hence `∫₀ᵀ ‖Az‖² ≥ δ⁴/(Γ⁴T³)` whenever the
  detected mass changes by `δ` (via `TransportCalculus.curvature_time_lower_bound`).
* `exists_local_solution`: local existence (Picard–Lindelöf, `C¹` field).

Scope: this is the *spatially discrete* model.  Convergence to the continuum
PDE (certified error bounds) and the continuum torus theory are not proved
here; see `pvnp/proofs/remaining-obstructions.md`.
-/

namespace PVNP.WCTLattice

open Complex Finset
open scoped InnerProductSpace

variable {N : ℕ} [NeZero N]

/-- Lattice fields on the discrete torus `ℤ/Nℤ`. -/
abbrev Fld (N : ℕ) := ZMod N → ℂ

/-- Hermitian pairing `⟨u, v⟩ = Σ conj(uⱼ) vⱼ`. -/
noncomputable def ip (u v : Fld N) : ℂ := ∑ j, (starRingEnd ℂ) (u j) * v j

/-- Squared `ℓ²` norm. -/
noncomputable def nsq (u : Fld N) : ℝ := ∑ j, ‖u j‖ ^ 2

/-- The symmetric nearest-neighbour operator `(Au)ⱼ = a(u_{j+1} + u_{j−1}) + b uⱼ`. -/
noncomputable def Aop (a b : ℝ) (u : Fld N) : Fld N :=
  fun j => (a : ℂ) * (u (j + 1) + u (j - 1)) + (b : ℂ) * u j

/-- The cubic–quintic nonlinearity `(−β|uⱼ|² + γ|uⱼ|⁴) uⱼ`. -/
noncomputable def nlin (β γ : ℝ) (u : Fld N) : Fld N :=
  fun j => ((-β * ‖u j‖ ^ 2 + γ * ‖u j‖ ^ 4 : ℝ) : ℂ) * u j

/-- The Hamiltonian gradient `G(u) = A(Au) + N(u)`. -/
noncomputable def grad (a b β γ : ℝ) (u : Fld N) : Fld N :=
  fun j => Aop a b (Aop a b u) j + nlin β γ u j

/-- The vector field `ż = −i G(z)`. -/
noncomputable def vf (a b β γ : ℝ) (u : Fld N) : Fld N := fun j => -I * grad a b β γ u j

/-- Mass. -/
noncomputable def mass (u : Fld N) : ℝ := nsq u

/-- Hamiltonian. -/
noncomputable def ham (a b β γ : ℝ) (u : Fld N) : ℝ :=
  nsq (Aop a b u) + ∑ j, (-β / 2 * (‖u j‖ ^ 2) ^ 2 + γ / 3 * (‖u j‖ ^ 2) ^ 3)

/-- Detected (weighted) mass. -/
noncomputable def J (w : ZMod N → ℝ) (u : Fld N) : ℝ := ∑ j, w j * ‖u j‖ ^ 2

/-- Classical solutions of the lattice WCT system. -/
def IsSol (a b β γ : ℝ) (z : ℝ → Fld N) : Prop :=
  ∀ t j, HasDerivAt (fun s => z s j) (vf a b β γ (z t) j) t

/-! ### Summation by parts -/

theorem shift_pair (u v : Fld N) :
    ∑ j, (starRingEnd ℂ) (u j) * v (j + 1) = ∑ j, (starRingEnd ℂ) (u (j - 1)) * v j :=
  Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ (fun j => by simp)

theorem shift_pair' (u v : Fld N) :
    ∑ j, (starRingEnd ℂ) (u j) * v (j - 1) = ∑ j, (starRingEnd ℂ) (u (j + 1)) * v j :=
  Fintype.sum_equiv (Equiv.subRight (1 : ZMod N)) _ _ (fun j => by simp)

theorem nsq_shift (u : Fld N) (c : ZMod N) : ∑ j, ‖u (j + c)‖ ^ 2 = nsq u :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ (fun j => by simp)

/-- **Self-adjointness of `A`.** -/
theorem ip_Aop (a b : ℝ) (u v : Fld N) : ip u (Aop a b v) = ip (Aop a b u) v := by
  have hL : ip u (Aop a b v) = (a : ℂ) * ∑ j, (starRingEnd ℂ) (u j) * v (j + 1) +
      (a : ℂ) * ∑ j, (starRingEnd ℂ) (u j) * v (j - 1) +
      (b : ℂ) * ∑ j, (starRingEnd ℂ) (u j) * v j := by
    simp only [ip, Aop, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hR : ip (Aop a b u) v = (a : ℂ) * ∑ j, (starRingEnd ℂ) (u (j + 1)) * v j +
      (a : ℂ) * ∑ j, (starRingEnd ℂ) (u (j - 1)) * v j +
      (b : ℂ) * ∑ j, (starRingEnd ℂ) (u j) * v j := by
    simp only [ip, Aop, Finset.mul_sum, ← Finset.sum_add_distrib, map_add, map_mul,
      Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, hR, shift_pair, shift_pair']
  ring

theorem ip_self (u : Fld N) : ip u u = (nsq u : ℂ) := by
  simp only [ip, nsq, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]

theorem re_neg_I_mul_ofReal (r : ℝ) : (-I * (r : ℂ)).re = 0 := by simp

theorem conj_mul_real (x : ℂ) (r : ℝ) :
    (starRingEnd ℂ) x * ((r : ℂ) * x) = ((r * ‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_left_comm, Complex.conj_mul']; push_cast; ring

theorem re_mul_ofReal_mul (x y : ℂ) (r : ℝ) : (x * ((r : ℂ) * y)).re = r * (x * y).re := by
  rw [mul_left_comm, Complex.re_ofReal_mul]

/-! ### Cauchy–Schwarz -/

theorem norm_ip_le (u v : Fld N) : ‖ip u v‖ ≤ Real.sqrt (nsq u) * Real.sqrt (nsq v) := by
  calc ‖ip u v‖ ≤ ∑ j, ‖(starRingEnd ℂ) (u j) * v j‖ := norm_sum_le _ _
    _ = ∑ j, ‖u j‖ * ‖v j‖ := by simp
    _ ≤ Real.sqrt (∑ j, ‖u j‖ ^ 2) * Real.sqrt (∑ j, ‖v j‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-! ### Conservation laws -/

/-- `Σ Re(conj(uⱼ) vf(u)ⱼ) = 0`: the vector field is tangent to mass spheres. -/
theorem sum_inner_vf (a b β γ : ℝ) (u : Fld N) :
    ∑ j, ⟪u j, vf a b β γ u j⟫_ℝ = 0 := by
  have hsplit : ∑ j, (starRingEnd ℂ) (u j) * vf a b β γ u j =
      -I * (ip u (Aop a b (Aop a b u)) + ∑ j, (starRingEnd ℂ) (u j) * nlin β γ u j) := by
    simp only [vf, grad, ip, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring
  have hnl : ∑ j, (starRingEnd ℂ) (u j) * nlin β γ u j =
      ((∑ j, (-β * ‖u j‖ ^ 2 + γ * ‖u j‖ ^ 4) * ‖u j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => conj_mul_real (u j) _
  have hA : ip u (Aop a b (Aop a b u)) = (nsq (Aop a b u) : ℂ) := by
    rw [ip_Aop, ip_self]
  simp only [Complex.inner]
  have : ∑ j, (vf a b β γ u j * (starRingEnd ℂ) (u j)).re =
      (∑ j, (starRingEnd ℂ) (u j) * vf a b β γ u j).re := by
    rw [Complex.re_sum]; exact Finset.sum_congr rfl fun j _ => by ring_nf
  rw [this, hsplit, hA, hnl, ← Complex.ofReal_add, re_neg_I_mul_ofReal]

theorem hasDerivAt_nsq {z : ℝ → Fld N} {z' : Fld N} {t : ℝ}
    (hz : ∀ j, HasDerivAt (fun s => z s j) (z' j) t) :
    HasDerivAt (fun s => nsq (z s)) (∑ j, 2 * ⟪z t j, z' j⟫_ℝ) t := by
  unfold nsq
  have h := HasDerivAt.sum (u := Finset.univ) (A := fun j s => ‖z s j‖ ^ 2)
    fun j _ => (hz j).norm_sq
  convert h using 1
  funext s; simp only [Finset.sum_apply]

/-- **Mass conservation (infinitesimal form)**, at any time where the equation holds. -/
theorem hasDerivAt_mass_of {a b β γ : ℝ} {z : ℝ → Fld N} {t : ℝ}
    (hz : ∀ j, HasDerivAt (fun s => z s j) (vf a b β γ (z t) j) t) :
    HasDerivAt (fun s => mass (z s)) 0 t := by
  have h := hasDerivAt_nsq hz
  rwa [← Finset.mul_sum, sum_inner_vf, mul_zero] at h

theorem hasDerivAt_mass {a b β γ : ℝ} {z : ℝ → Fld N} (hz : IsSol a b β γ z) (t : ℝ) :
    HasDerivAt (fun s => mass (z s)) 0 t :=
  hasDerivAt_mass_of (hz t)

theorem hasDerivAt_Aop {a b : ℝ} {z : ℝ → Fld N} {z' : Fld N} {t : ℝ}
    (hz : ∀ j, HasDerivAt (fun s => z s j) (z' j) t) (j : ZMod N) :
    HasDerivAt (fun s => Aop a b (z s) j) (Aop a b z' j) t := by
  unfold Aop
  exact (((hz (j + 1)).add (hz (j - 1))).const_mul (a : ℂ)).add ((hz j).const_mul (b : ℂ))

/-- `⟪x, -I • y⟫_ℝ`-type identity used for the Hamiltonian. -/
theorem sum_inner_grad_vf (a b β γ : ℝ) (u : Fld N) :
    ∑ j, ⟪grad a b β γ u j, vf a b β γ u j⟫_ℝ = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  simp only [vf, Complex.inner]
  rw [show -I * grad a b β γ u j * (starRingEnd ℂ) (grad a b β γ u j) =
      -I * ((starRingEnd ℂ) (grad a b β γ u j) * grad a b β γ u j) by ring,
    Complex.conj_mul', ← Complex.ofReal_pow, re_neg_I_mul_ofReal]

/-- **Hamiltonian conservation (infinitesimal form).** -/
theorem hasDerivAt_ham_of {a b β γ : ℝ} {z : ℝ → Fld N} {t : ℝ}
    (hz : ∀ j, HasDerivAt (fun s => z s j) (vf a b β γ (z t) j) t) :
    HasDerivAt (fun s => ham a b β γ (z s)) 0 t := by
  have hA : HasDerivAt (fun s => nsq (Aop a b (z s)))
      (∑ j, 2 * ⟪Aop a b (z t) j, Aop a b (vf a b β γ (z t)) j⟫_ℝ) t :=
    hasDerivAt_nsq (z := fun s => Aop a b (z s)) (fun j => hasDerivAt_Aop hz j)
  have hP : ∀ j, HasDerivAt (fun s => -β / 2 * (‖z s j‖ ^ 2) ^ 2 + γ / 3 * (‖z s j‖ ^ 2) ^ 3)
      ((-β * ‖z t j‖ ^ 2 + γ * ‖z t j‖ ^ 4) * (2 * ⟪z t j, vf a b β γ (z t) j⟫_ℝ)) t := by
    intro j
    have hs := (hz j).norm_sq
    have h2 := (hs.pow 2).const_mul (-β / 2)
    have h3 := (hs.pow 3).const_mul (γ / 3)
    convert h2.add h3 using 1
    push_cast
    ring
  have hS : HasDerivAt (fun s => ∑ j, (-β / 2 * (‖z s j‖ ^ 2) ^ 2 + γ / 3 * (‖z s j‖ ^ 2) ^ 3))
      (∑ j, (-β * ‖z t j‖ ^ 2 + γ * ‖z t j‖ ^ 4) * (2 * ⟪z t j, vf a b β γ (z t) j⟫_ℝ)) t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun j (_ : j ∈ Finset.univ) => hP j
    convert h using 1
    funext s; simp only [Finset.sum_apply]
  have h1 : ∑ j, ⟪Aop a b (z t) j, Aop a b (vf a b β γ (z t)) j⟫_ℝ =
      ∑ j, ⟪Aop a b (Aop a b (z t)) j, vf a b β γ (z t) j⟫_ℝ := by
    have e := congrArg Complex.re (ip_Aop a b (Aop a b (z t)) (vf a b β γ (z t)))
    simp only [ip, Complex.re_sum] at e
    simp only [Complex.inner]
    convert e using 1 <;> refine Finset.sum_congr rfl fun j _ => by ring_nf
  have h2 : ∀ j, (-β * ‖z t j‖ ^ 2 + γ * ‖z t j‖ ^ 4) * ⟪z t j, vf a b β γ (z t) j⟫_ℝ =
      ⟪nlin β γ (z t) j, vf a b β γ (z t) j⟫_ℝ := by
    intro j
    simp only [nlin, Complex.inner, map_mul, Complex.conj_ofReal]
    rw [re_mul_ofReal_mul]
  have key : ∑ j, 2 * ⟪Aop a b (z t) j, Aop a b (vf a b β γ (z t)) j⟫_ℝ +
      ∑ j, (-β * ‖z t j‖ ^ 2 + γ * ‖z t j‖ ^ 4) * (2 * ⟪z t j, vf a b β γ (z t) j⟫_ℝ) = 0 := by
    have e2 : ∑ j, (-β * ‖z t j‖ ^ 2 + γ * ‖z t j‖ ^ 4) * (2 * ⟪z t j, vf a b β γ (z t) j⟫_ℝ) =
        2 * ∑ j, ⟪nlin β γ (z t) j, vf a b β γ (z t) j⟫_ℝ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [← h2 j]; ring
    have e3 : ∑ j, ⟪grad a b β γ (z t) j, vf a b β γ (z t) j⟫_ℝ =
        ∑ j, ⟪Aop a b (Aop a b (z t)) j, vf a b β γ (z t) j⟫_ℝ +
          ∑ j, ⟪nlin β γ (z t) j, vf a b β γ (z t) j⟫_ℝ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [grad, inner_add_left]
    rw [← Finset.mul_sum, h1, e2, ← mul_add, ← e3, sum_inner_grad_vf, mul_zero]
  have hsum := hA.add hS
  rw [key] at hsum
  exact hsum

theorem hasDerivAt_ham {a b β γ : ℝ} {z : ℝ → Fld N} (hz : IsSol a b β γ z) (t : ℝ) :
    HasDerivAt (fun s => ham a b β γ (z s)) 0 t :=
  hasDerivAt_ham_of (hz t)

theorem mass_conserved {a b β γ : ℝ} {z : ℝ → Fld N} (hz : IsSol a b β γ z) (t : ℝ) :
    mass (z t) = mass (z 0) :=
  is_const_of_deriv_eq_zero
    (fun s => (hasDerivAt_mass hz s).differentiableAt)
    (fun s => (hasDerivAt_mass hz s).deriv) t 0

theorem ham_conserved {a b β γ : ℝ} {z : ℝ → Fld N} (hz : IsSol a b β γ z) (t : ℝ) :
    ham a b β γ (z t) = ham a b β γ (z 0) :=
  is_const_of_deriv_eq_zero
    (fun s => (hasDerivAt_ham hz s).differentiableAt)
    (fun s => (hasDerivAt_ham hz s).deriv) t 0

/-! ### Local existence and local conservation -/

theorem contDiff_vf (a b β γ : ℝ) : ContDiff ℝ 1 (vf (N := N) a b β γ) := by
  have hp : ∀ i : ZMod N, ContDiff ℝ 1 (fun u : Fld N => u i) := fun i => contDiff_apply ℝ ℂ i
  have hq : ∀ i : ZMod N, ContDiff ℝ 1 (fun u : Fld N => ‖u i‖ ^ 2) := fun i =>
    (contDiff_norm_sq ℝ).comp (hp i)
  have hc : ∀ i : ZMod N, ContDiff ℝ 1
      (fun u : Fld N => (((-β * ‖u i‖ ^ 2 + γ * ‖u i‖ ^ 4 : ℝ)) : ℂ)) := fun i => by
    have h4 : (fun u : Fld N => -β * ‖u i‖ ^ 2 + γ * ‖u i‖ ^ 4) =
        fun u => -β * ‖u i‖ ^ 2 + γ * (‖u i‖ ^ 2) ^ 2 := by
      funext u; ring
    have hr : ContDiff ℝ 1 (fun u : Fld N => -β * ‖u i‖ ^ 2 + γ * ‖u i‖ ^ 4) := by
      rw [h4]; exact (contDiff_const.mul (hq i)).add (contDiff_const.mul ((hq i).pow 2))
    exact Complex.ofRealCLM.contDiff.comp hr
  refine contDiff_pi.2 fun j => ?_
  simp only [vf, grad, Aop, nlin]
  have hA : ∀ i : ZMod N, ContDiff ℝ 1 (fun u : Fld N =>
      (a : ℂ) * (u (i + 1) + u (i - 1)) + (b : ℂ) * u i) := fun i =>
    (contDiff_const.mul ((hp _).add (hp _))).add (contDiff_const.mul (hp i))
  exact contDiff_const.mul (((contDiff_const.mul ((hA _).add (hA _))).add
    (contDiff_const.mul (hA j))).add ((hc j).mul (hp j)))

/-- **Local existence** (Picard–Lindelöf for the `C¹` lattice vector field). -/
theorem exists_local_solution (a b β γ : ℝ) (u₀ : Fld N) :
    ∃ z : ℝ → Fld N, z 0 = u₀ ∧ ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioo (-ε) ε, ∀ j,
      HasDerivAt (fun s => z s j) (vf a b β γ (z t) j) t := by
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      ((contDiff_vf a b β γ).contDiffAt (x := u₀)) 0
  refine ⟨α, hα0, ε, hε, fun t ht j => ?_⟩
  have := hα t (by simpa using ht)
  exact (hasDerivAt_pi.1 this) j

theorem const_of_hasDerivAt_zero_Ioo {f : ℝ → ℝ} {ε : ℝ}
    (hf : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt f 0 t) {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε)
    (h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε) : f t = f 0 := by
  have := (convex_Ioo (-ε) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ => (0 : ℝ)) (C := 0) (fun x hx => (hf x hx).hasDerivWithinAt)
    (fun _ _ => by simp) h0 ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
  exact this

/-- **Local conservation**: every local solution conserves mass and Hamiltonian
on its whole interval of existence (so the conservation laws are not vacuous). -/
theorem local_conservation {a b β γ : ℝ} {z : ℝ → Fld N} {ε : ℝ}
    (hz : ∀ t ∈ Set.Ioo (-ε) ε, ∀ j, HasDerivAt (fun s => z s j) (vf a b β γ (z t) j) t)
    {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε) :
    mass (z t) = mass (z 0) ∧ ham a b β γ (z t) = ham a b β γ (z 0) := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  exact ⟨const_of_hasDerivAt_zero_Ioo (fun s hs => hasDerivAt_mass_of (hz s hs)) ht h0,
    const_of_hasDerivAt_zero_Ioo (fun s hs => hasDerivAt_ham_of (hz s hs)) ht h0⟩

/-! ### Coercivity -/

/-- **Uniform coercivity**: `‖Az‖² ≤ H + (3β²/16γ) M` for every lattice field. -/
theorem bandpass_le_ham (a b β γ : ℝ) (hγ : 0 < γ) (u : Fld N) :
    nsq (Aop a b u) ≤ ham a b β γ u + 3 * β ^ 2 / (16 * γ) * mass u := by
  unfold ham mass nsq
  have hpt : ∀ j : ZMod N, 0 ≤ -β / 2 * (‖u j‖ ^ 2) ^ 2 + γ / 3 * (‖u j‖ ^ 2) ^ 3 +
      3 * β ^ 2 / (16 * γ) * ‖u j‖ ^ 2 := by
    intro j
    have hs : 0 ≤ ‖u j‖ ^ 2 := by positivity
    have key : -β / 2 * (‖u j‖ ^ 2) ^ 2 + γ / 3 * (‖u j‖ ^ 2) ^ 3 +
        3 * β ^ 2 / (16 * γ) * ‖u j‖ ^ 2 =
        γ / 3 * ‖u j‖ ^ 2 * (‖u j‖ ^ 2 - 3 * β / (4 * γ)) ^ 2 := by
      field_simp; ring
    rw [key]; positivity
  have hsum := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hpt j
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith

/-! ### The detected-mass flux -/

/-- Pointwise weight multiplication. -/
noncomputable def wmul (w : ZMod N → ℝ) (u : Fld N) : Fld N := fun j => (w j : ℂ) * u j

/-- The commutator `[A, w]`. -/
noncomputable def comm (a : ℝ) (w : ZMod N → ℝ) (u : Fld N) : Fld N :=
  fun j => (a : ℂ) * (((w (j + 1) - w j : ℝ) : ℂ) * u (j + 1) + ((w (j - 1) - w j : ℝ) : ℂ) * u (j - 1))

theorem Aop_wmul (a b : ℝ) (w : ZMod N → ℝ) (u : Fld N) (j : ZMod N) :
    Aop a b (wmul w u) j = wmul w (Aop a b u) j + comm a w u j := by
  simp only [Aop, wmul, comm]; push_cast; ring

/-- **Exact flux identity**: `J' = 2 Im⟨[A,w]z, Az⟩`. -/
theorem hasDerivAt_flux {a b β γ : ℝ} (w : ZMod N → ℝ) {z : ℝ → Fld N}
    (hz : IsSol a b β γ z) (t : ℝ) :
    HasDerivAt (fun s => J w (z s)) (2 * (ip (comm a w (z t)) (Aop a b (z t))).im) t := by
  have h : HasDerivAt (fun s => J w (z s))
      (∑ j, w j * (2 * ⟪z t j, vf a b β γ (z t) j⟫_ℝ)) t := by
    unfold J
    have h := HasDerivAt.sum (u := Finset.univ) (A := fun j s => w j * ‖z s j‖ ^ 2)
      fun j _ => ((hz t j).norm_sq).const_mul (w j)
    convert h using 1
    funext s; simp only [Finset.sum_apply]
  convert h using 1
  -- the derivative value
  set u := z t
  have e1 : ∑ j, w j * (2 * ⟪u j, vf a b β γ u j⟫_ℝ) =
      2 * (ip (wmul w u) (vf a b β γ u)).re := by
    simp only [ip, wmul, Complex.inner, Complex.re_sum, Finset.mul_sum, map_mul,
      Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (w j : ℂ) * (starRingEnd ℂ) (u j) * vf a b β γ u j =
        (w j : ℂ) * (vf a b β γ u j * (starRingEnd ℂ) (u j)) by ring, Complex.re_ofReal_mul]
    ring
  have e2 : ip (wmul w u) (vf a b β γ u) =
      -I * (ip (wmul w u) (Aop a b (Aop a b u)) + ip (wmul w u) (nlin β γ u)) := by
    simp only [ip, vf, grad, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring
  have e3 : ip (wmul w u) (nlin β γ u) =
      ((∑ j, w j * (-β * ‖u j‖ ^ 2 + γ * ‖u j‖ ^ 4) * ‖u j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (starRingEnd ℂ) ((w j : ℂ) * u j) *
        (((-β * ‖u j‖ ^ 2 + γ * ‖u j‖ ^ 4 : ℝ) : ℂ) * u j) = _
    rw [map_mul, Complex.conj_ofReal, mul_assoc, conj_mul_real]
    push_cast; ring
  have e4 : ip (wmul w u) (Aop a b (Aop a b u)) =
      ip (wmul w (Aop a b u)) (Aop a b u) + ip (comm a w u) (Aop a b u) := by
    rw [ip_Aop]
    simp only [ip, Aop_wmul, map_add, add_mul, Finset.sum_add_distrib]
  have e5 : ip (wmul w (Aop a b u)) (Aop a b u) =
      ((∑ j, w j * ‖Aop a b u j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [ip, wmul, map_mul, Complex.conj_ofReal, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, Complex.conj_mul']; push_cast; ring
  rw [e1, e2, e3, e4, e5]
  simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem nsq_comm_le (a : ℝ) (w : ZMod N → ℝ) (ω : ℝ) (hω : ∀ j, |w (j + 1) - w j| ≤ ω)
    (u : Fld N) : nsq (comm a w u) ≤ 4 * a ^ 2 * ω ^ 2 * nsq u := by
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans (hω 0)
  have hpt : ∀ j, ‖comm a w u j‖ ^ 2 ≤ 2 * a ^ 2 * ω ^ 2 * (‖u (j + 1)‖ ^ 2 + ‖u (j + -1)‖ ^ 2) := by
    intro j
    have h1 : |w (j + 1) - w j| ≤ ω := hω j
    have h2 : |w (j - 1) - w j| ≤ ω := by
      have := hω (j - 1)
      rw [sub_add_cancel, abs_sub_comm] at this; exact this
    have hn : ‖comm a w u j‖ ≤ |a| * (ω * ‖u (j + 1)‖ + ω * ‖u (j + -1)‖) := by
      simp only [comm, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← sub_eq_add_neg]
      gcongr
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
    have hsq : (|a| * (ω * ‖u (j + 1)‖ + ω * ‖u (j + -1)‖)) ^ 2 ≤
        2 * a ^ 2 * ω ^ 2 * (‖u (j + 1)‖ ^ 2 + ‖u (j + -1)‖ ^ 2) := by
      have : (|a| * (ω * ‖u (j + 1)‖ + ω * ‖u (j + -1)‖)) ^ 2 =
          a ^ 2 * ω ^ 2 * (‖u (j + 1)‖ + ‖u (j + -1)‖) ^ 2 := by
        rw [mul_pow, sq_abs]; ring
      rw [this]
      have := two_mul_le_add_sq (‖u (j + 1)‖) (‖u (j + -1)‖)
      have hpos : 0 ≤ a ^ 2 * ω ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hpos]
    calc ‖comm a w u j‖ ^ 2 ≤ (|a| * (ω * ‖u (j + 1)‖ + ω * ‖u (j + -1)‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ _ := hsq
  calc nsq (comm a w u) ≤ ∑ j, 2 * a ^ 2 * ω ^ 2 * (‖u (j + 1)‖ ^ 2 + ‖u (j + -1)‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => hpt j
    _ = 2 * a ^ 2 * ω ^ 2 * (nsq u + nsq u) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, nsq_shift, nsq_shift]
    _ = 4 * a ^ 2 * ω ^ 2 * nsq u := by ring

/-- **Derived flux bound**: `|J'| ≤ 4|a| ω √M ‖Az‖`. -/
theorem flux_bound (a b : ℝ) (w : ZMod N → ℝ) (ω : ℝ) (hω : ∀ j, |w (j + 1) - w j| ≤ ω)
    (u : Fld N) :
    |2 * (ip (comm a w u) (Aop a b u)).im| ≤
      4 * |a| * ω * Real.sqrt (nsq u) * Real.sqrt (nsq (Aop a b u)) := by
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans (hω 0)
  have hnsq : 0 ≤ nsq u := Finset.sum_nonneg fun j _ => by positivity
  have hc : Real.sqrt (nsq (comm a w u)) ≤ 2 * |a| * ω * Real.sqrt (nsq u) := by
    have e : Real.sqrt (4 * a ^ 2 * ω ^ 2 * nsq u) = 2 * |a| * ω * Real.sqrt (nsq u) := by
      rw [Real.sqrt_mul' _ hnsq,
        show 4 * a ^ 2 * ω ^ 2 = (2 * |a| * ω) ^ 2 by rw [mul_pow, mul_pow, sq_abs]; ring,
        Real.sqrt_sq (by positivity)]
    rw [← e]
    exact Real.sqrt_le_sqrt (nsq_comm_le a w ω hω u)
  calc |2 * (ip (comm a w u) (Aop a b u)).im| = 2 * |(ip (comm a w u) (Aop a b u)).im| := by
        rw [abs_mul, abs_two]
    _ ≤ 2 * ‖ip (comm a w u) (Aop a b u)‖ := by gcongr; exact Complex.abs_im_le_norm _
    _ ≤ 2 * (Real.sqrt (nsq (comm a w u)) * Real.sqrt (nsq (Aop a b u))) := by
        gcongr; exact norm_ip_le _ _
    _ ≤ 2 * (2 * |a| * ω * Real.sqrt (nsq u) * Real.sqrt (nsq (Aop a b u))) := by
        gcongr
    _ = 4 * |a| * ω * Real.sqrt (nsq u) * Real.sqrt (nsq (Aop a b u)) := by ring

/-- The explicit flux constant fixed by the initial data. -/
noncomputable def Gam (a b β γ : ℝ) (ω : ℝ) (u₀ : Fld N) : ℝ :=
  4 * |a| * ω * Real.sqrt (mass u₀) *
    Real.sqrt (Real.sqrt (ham a b β γ u₀ + 3 * β ^ 2 / (16 * γ) * mass u₀))

/-- **The flux inequality `|J'(t)| ≤ Γ √D(t)` along every solution**, with
`D(t) = ‖Az(t)‖` and `Γ = Gam … (z 0)`: derived from the equation, the
conservation laws and the coercivity bound. -/
theorem lattice_flux_inequality {a b β γ : ℝ} (hγ : 0 < γ) (w : ZMod N → ℝ) (ω : ℝ)
    (hω : ∀ j, |w (j + 1) - w j| ≤ ω) {z : ℝ → Fld N} (hz : IsSol a b β γ z) (t : ℝ) :
    |2 * (ip (comm a w (z t)) (Aop a b (z t))).im| ≤
      Gam a b β γ ω (z 0) * Real.sqrt (Real.sqrt (nsq (Aop a b (z t)))) := by
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans (hω 0)
  have hb := flux_bound a b w ω hω (z t)
  set D := Real.sqrt (nsq (Aop a b (z t))) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  set K := Real.sqrt (ham a b β γ (z 0) + 3 * β ^ 2 / (16 * γ) * mass (z 0)) with hK
  have hDK : D ≤ K := by
    rw [hD, hK]
    apply Real.sqrt_le_sqrt
    have := bandpass_le_ham a b β γ hγ (z t)
    rwa [ham_conserved hz t, mass_conserved hz t] at this
  have hsplit : D = Real.sqrt D * Real.sqrt D := (Real.mul_self_sqrt hD0).symm
  have hDle : D ≤ Real.sqrt K * Real.sqrt D := by
    calc D = Real.sqrt D * Real.sqrt D := hsplit
      _ ≤ Real.sqrt K * Real.sqrt D := by gcongr
  have hM : Real.sqrt (nsq (z t)) = Real.sqrt (mass (z 0)) := by
    rw [← mass_conserved hz t]; rfl
  calc |2 * (ip (comm a w (z t)) (Aop a b (z t))).im|
      ≤ 4 * |a| * ω * Real.sqrt (nsq (z t)) * D := hb
    _ ≤ 4 * |a| * ω * Real.sqrt (nsq (z t)) * (Real.sqrt K * Real.sqrt D) := by gcongr
    _ = Gam a b β γ ω (z 0) * Real.sqrt D := by
        rw [Gam, hM]; ring

theorem continuous_comp {a b β γ : ℝ} {z : ℝ → Fld N} (hz : IsSol a b β γ z) (j : ZMod N) :
    Continuous fun t => z t j :=
  continuous_iff_continuousAt.2 fun t => (hz t j).continuousAt

/-- **Curvature–time bound on the lattice**: if the detected mass changes by
`δ` in time `T`, then `∫₀ᵀ ‖Az‖² ≥ δ⁴/(Γ⁴T³)` with the explicit `Γ`. -/
theorem lattice_curvature_time_bound {a b β γ : ℝ} (hγ : 0 < γ) (w : ZMod N → ℝ) (ω : ℝ)
    (hω : ∀ j, |w (j + 1) - w j| ≤ ω) {z : ℝ → Fld N} (hz : IsSol a b β γ z)
    {T δ : ℝ} (hT : 0 < T) (hΓ : 0 < Gam a b β γ ω (z 0)) (hδ : 0 ≤ δ)
    (hchange : δ ≤ |J w (z T) - J w (z 0)|) :
    δ ^ 4 / (Gam a b β γ ω (z 0) ^ 4 * T ^ 3) ≤
      ∫ t in (0 : ℝ)..T, Real.sqrt (nsq (Aop a b (z t))) ^ 2 := by
  have hc := continuous_comp hz
  have hcA : ∀ j, Continuous fun t => Aop a b (z t) j := fun j => by
    unfold Aop; fun_prop
  have hDc : Continuous fun t => Real.sqrt (nsq (Aop a b (z t))) := by
    unfold nsq; fun_prop
  have hcC : ∀ j, Continuous fun t => comm a w (z t) j := fun j => by
    unfold comm; fun_prop
  have hJ'c : Continuous fun t => 2 * (ip (comm a w (z t)) (Aop a b (z t))).im := by
    unfold ip
    exact continuous_const.mul (Complex.continuous_im.comp (continuous_finset_sum _
      fun j _ => (Complex.continuous_conj.comp (hcC j)).mul (hcA j)))
  exact PVNP.TransportCalculus.curvature_time_lower_bound
    (fun t => J w (z t)) (fun t => 2 * (ip (comm a w (z t)) (Aop a b (z t))).im)
    (fun t => Real.sqrt (nsq (Aop a b (z t)))) hT hΓ
    (fun t _ => hasDerivAt_flux w hz t) hJ'c.continuousOn hDc.continuousOn
    (fun t _ => Real.sqrt_nonneg _) (fun t _ => lattice_flux_inequality hγ w ω hω hz t) hδ hchange

end PVNP.WCTLattice
