import PVNP.InterwovenSAT
import PVNP.WCTSATDevice

/-!
# I-37 on the physical spatial torus: locking configurations of frozen-WCT fields

Part I, §12.3: "a toroidal locking witness for a 3-SAT instance is a curvature-locked
configuration encoding a toroidal ψ–electron structure whose phase-locking and flux constraints
correspond to the satisfaction of all clauses. Nonexistence of such a locking configuration is
equivalent to unsatisfiability." The manuscript does not define the ψ–electron structure; it uses
the phrase only in this sentence. `InterwovenSAT.toroidal_locking_iff_unsat` proved the equivalence
on the configuration torus `|ψᵢ| = 1`. Here the structure is realized on the **spatial** torus
`T_L² = (ℝ/Lℤ)²` of the frozen WCT equation.

**The field.** `Ψ : ℕ → ℓ2` is a family of frozen-torus `H²` states: component `0` is a
reference (ψ–electron) field, component `i + 1` carries Boolean variable `i`. Its value at a point
`x ∈ ℝ²` is `pt L Ψ x i = field L (co L (Ψ i)) x`, the actual torus field of `PVNP.Torus`.

**The constraints** (all local in `x`):

* *amplitude:* `|ψᵢ(x)| = 1` at every point (`UnitField`);
* *phase locking and flux:* the local density `dens F λ μ L Ψ x` is the sign-blind interwoven
  energy (clause penalties plus sign-blind coupling and curvature) of the gauge-invariant
  relative field `ψ_{i+1}(x) · conj ψ₀(x)`; it must vanish at every point;
* *Boolean phase consistency:* every component has zero gradient energy
  `∫|∇ψᵢ|² = Σ_k |ξ_k|² |ψ̂ᵢ,k|²` (`grad2`).

A **locking configuration** (`Locked`) satisfies all three.

**Results.**

* `sat_iff_locked`: `SAT(F) ⟺ ∃ locking configuration`, for every formula, every torus `L > 0`
  and all `λ, μ ≥ 0`. Equivalently, no locking configuration exists iff `F` is unsatisfiable
  (`no_locked_iff_unsat`) — the sentence of §12.3.
* `locked_iff`: the locking configurations are exactly the constant fields `ψᵢ ≡ cᵢ/L` with
  `|cᵢ| = L` whose relative phases have zero clause energy. Consistency is forced by the gradient
  term (`eq_mode_of_grad2_eq_zero`).
* *Curvature-locked under the frozen evolution* (`locked_frozen_flow`, `frozen_flow_preserves_locks`):
  every component of a locking configuration evolves by the exact frozen solution
  `cᵢ e^{−iΩt}/L` with one common frequency, the configuration stays locked for all times, and the
  Laplacian vanishes identically (`Dc ≡ 0`), so the regularized curvature `W_ψ` is identically
  zero along the evolution.

The dynamical question — whether the frozen flow can *reach* a lock — is settled in the second
half of the module.
-/

open Complex Filter Topology MeasureTheory
open scoped Real

namespace PVNP.SpatialLocking

open PVNP.Torus PVNP.PartIPsiSat PVNP.InterwovenSAT PVNP.WCTSATDevice

variable {L κ β γ : ℝ}

/-! ### The spatial field and its constraints -/

/-- A multi-component field on the spatial torus: component `0` is the reference field and
component `i + 1` carries variable `i`; each component is a frozen-torus `H²` state. -/
abbrev MField := ℕ → ℓ2

/-- The values of all components at a point of the torus. -/
noncomputable def pt (L : ℝ) (Ψ : MField) (x : ℝ × ℝ) : ℕ → ℂ :=
  fun i => Torus.field L (co L (Ψ i)) x

/-- The gauge-invariant relative field: variable `i ↦ ψ_{i+1} · conj ψ₀`. -/
noncomputable def rel (z : ℕ → ℂ) : ℕ → ℂ := fun i => z (i + 1) * (starRingEnd ℂ) (z 0)

/-- Unit amplitude of every component at every point. -/
def UnitField (L : ℝ) (Ψ : MField) : Prop := ∀ i x, ‖pt L Ψ x i‖ = 1

/-- The local energy density: the sign-blind interwoven energy (clause penalties, sign-blind
coupling and curvature) of the relative field at `x`. -/
noncomputable def dens (F : CNF3) (lam mu L : ℝ) (Ψ : MField) (x : ℝ × ℝ) : ℝ :=
  energySB F lam mu (rel (pt L Ψ x))

/-- The gradient energy `∫_{T_L²} |∇ψ|² = Σ_k |ξ_k|² |ψ̂_k|²` of a component. -/
noncomputable def grad2 (L : ℝ) (v : ℓ2) : ℝ := ∑' k, qf L k * ‖co L v k‖ ^ 2

/-- **A toroidal locking configuration** of `F`: unit amplitude, vanishing local density at every
point, and vanishing gradient energy in every component. -/
def Locked (F : CNF3) (lam mu L : ℝ) (Ψ : MField) : Prop :=
  UnitField L Ψ ∧ (∀ x, dens F lam mu L Ψ x = 0) ∧ ∀ i, grad2 L (Ψ i) = 0

/-! ### Basic facts -/

theorem rel_admissible {z : ℕ → ℂ} (hz : ∀ i, ‖z i‖ = 1) : Admissible (rel z) := by
  intro i
  rw [rel, norm_mul, Complex.norm_conj, hz, hz, mul_one]

theorem qf_pos (hL : 0 < L) {k : Z2} (hk : k ≠ 0) : 0 < qf L k := by
  unfold qf xi1 xi2
  have hc : 0 < 2 * π / L := by positivity
  have hk' : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (Prod.ext h.1 h.2)
  rcases hk' with h1 | h2
  · have hne : 2 * π / L * (k.1 : ℝ) ≠ 0 := mul_ne_zero hc.ne' (by exact_mod_cast h1)
    have := mul_self_pos.mpr hne
    nlinarith [sq_nonneg (2 * π / L * (k.2 : ℝ))]
  · have hne : 2 * π / L * (k.2 : ℝ) ≠ 0 := mul_ne_zero hc.ne' (by exact_mod_cast h2)
    have := mul_self_pos.mpr hne
    nlinarith [sq_nonneg (2 * π / L * (k.1 : ℝ))]

theorem summable_grad2 (L : ℝ) (v : ℓ2) : Summable fun k => qf L k * ‖co L v k‖ ^ 2 := by
  refine (summable_sq v).of_nonneg_of_le
    (fun k => mul_nonneg (qf_nonneg L k) (sq_nonneg _)) (fun k => ?_)
  rw [norm_co, div_pow]
  have hw := wt_pos L k
  have h1 := one_le_wt L k
  have hq : qf L k ≤ wt L k := by unfold wt; linarith
  have hv := sq_nonneg ‖v k‖
  calc qf L k * (‖v k‖ ^ 2 / wt L k ^ 2) ≤ wt L k * (‖v k‖ ^ 2 / wt L k ^ 2) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ = ‖v k‖ ^ 2 / wt L k := by field_simp
    _ ≤ ‖v k‖ ^ 2 := div_le_self hv h1

theorem grad2_nonneg (L : ℝ) (v : ℓ2) : 0 ≤ grad2 L v :=
  tsum_nonneg fun k => mul_nonneg (qf_nonneg L k) (sq_nonneg _)

theorem grad2_mode_zero (L : ℝ) (c : ℂ) : grad2 L (mode L 0 c) = 0 := by
  unfold grad2
  rw [co_mode]
  have h : (fun k => qf L k * ‖(Pi.single (0 : Z2) c : Z2 → ℂ) k‖ ^ 2) = fun _ => 0 := by
    funext k
    by_cases hk : k = 0
    · subst hk
      rw [qf_zero, zero_mul]
    · rw [Pi.single_eq_of_ne hk, norm_zero]
      ring
  rw [h, tsum_zero]

/-- **Boolean phase consistency.** A component with zero gradient energy is a zero-mode
(spatially constant) state. -/
theorem eq_mode_of_grad2_eq_zero (hL : 0 < L) {v : ℓ2} (h : grad2 L v = 0) :
    v = mode L 0 (co L v 0) := by
  have hs := summable_grad2 L v
  have hnn : ∀ k, 0 ≤ qf L k * ‖co L v k‖ ^ 2 :=
    fun k => mul_nonneg (qf_nonneg L k) (sq_nonneg _)
  have hsum : HasSum (fun k => qf L k * ‖co L v k‖ ^ 2) 0 := by
    have := hs.hasSum
    unfold grad2 at h
    rwa [h] at this
  have hzero := (hasSum_zero_iff_of_nonneg hnn).1 hsum
  ext k
  rw [mode, lp.single_apply]
  by_cases hk : k = 0
  · subst hk
    rw [Pi.single_eq_same, wt_zero, Complex.ofReal_one, one_mul, co, wt_zero, Complex.ofReal_one,
      div_one]
  · rw [Pi.single_eq_of_ne hk]
    have hk0 := congrFun hzero k
    simp only [Pi.zero_apply] at hk0
    rcases mul_eq_zero.1 hk0 with h1 | h1
    · exact absurd h1 (qf_pos hL hk).ne'
    · have hc : co L v k = 0 := by
        have : ‖co L v k‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
        exact norm_eq_zero.1 this
      rw [← wt_mul_co L v k, hc, mul_zero]

theorem pt_mode (L : ℝ) (c : ℕ → ℂ) (x : ℝ × ℝ) :
    pt L (fun i => mode L 0 (c i)) x = fun i => (L : ℂ)⁻¹ * c i := by
  funext i
  rw [pt, co_mode, field_single_zero]

theorem dens_nonneg (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) {Ψ : MField}
    (hU : UnitField L Ψ) (x : ℝ × ℝ) : 0 ≤ dens F lam mu L Ψ x :=
  (Elog_nonneg F _).trans (energySB_ge_Elog F hlam hmu (rel_admissible fun i => hU i x))

/-! ### The spatial locking equivalence -/

/-- The bit field of an assignment, with the reference field `1` in component `0`. -/
noncomputable def bitField (a : ℕ → Bool) : ℕ → ℂ
  | 0 => 1
  | i + 1 => fieldOf a i

theorem rel_bitField (a : ℕ → Bool) : rel (bitField a) = fieldOf a := by
  funext i
  simp [rel, bitField]

theorem norm_bitField (a : ℕ → Bool) (i : ℕ) : ‖bitField a i‖ = 1 := by
  cases i with
  | zero => simp [bitField]
  | succ j => exact fieldOf_admissible a j

/-- **I-37 on the spatial torus.** A formula is satisfiable iff its toroidal locking
configuration exists, for every torus `L > 0` and all `λ, μ ≥ 0`. -/
theorem sat_iff_locked (F : CNF3) (hL : 0 < L) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    Sat F ↔ ∃ Ψ, Locked F lam mu L Ψ := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i => mode L 0 ((L : ℂ) * bitField a i), ⟨fun i x => ?_, fun x => ?_, fun i => ?_⟩⟩
    · rw [pt_mode]
      show ‖(L : ℂ)⁻¹ * ((L : ℂ) * bitField a i)‖ = 1
      rw [inv_mul_cancel_left₀ hL0, norm_bitField]
    · rw [dens, pt_mode]
      have : (fun i => (L : ℂ)⁻¹ * ((L : ℂ) * bitField a i)) = bitField a := by
        funext i
        rw [inv_mul_cancel_left₀ hL0]
      rw [this, rel_bitField, energySB_fieldOf]
      exact (Elogic_phaseOf_eq_zero_iff a F).2 ha
    · exact grad2_mode_zero L _
  · rintro ⟨Ψ, hU, hd, -⟩
    exact (sat_iff_zero_energySB F hlam hmu).2
      ⟨_, rel_admissible fun i => hU i 0, hd 0⟩

/-- The sentence of §12.3: no locking configuration exists iff the formula is unsatisfiable. -/
theorem no_locked_iff_unsat (F : CNF3) (hL : 0 < L) {lam mu : ℝ} (hlam : 0 ≤ lam)
    (hmu : 0 ≤ mu) : (¬ ∃ Ψ, Locked F lam mu L Ψ) ↔ ¬ Sat F :=
  not_congr (sat_iff_locked F hL hlam hmu).symm

/-- **The locking configurations, exactly.** They are the constant fields `ψᵢ ≡ cᵢ/L` with
`|cᵢ| = L` whose relative field has zero sign-blind energy. -/
theorem locked_iff (F : CNF3) (hL : 0 < L) {lam mu : ℝ} (Ψ : MField) :
    Locked F lam mu L Ψ ↔ ∃ c : ℕ → ℂ, (∀ i, Ψ i = mode L 0 (c i) ∧ ‖c i‖ = L) ∧
      energySB F lam mu (rel fun i => (L : ℂ)⁻¹ * c i) = 0 := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hnorm : ∀ c : ℂ, ‖(L : ℂ)⁻¹ * c‖ = ‖c‖ / L := fun c => by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    field_simp
  constructor
  · rintro ⟨hU, hd, hg⟩
    refine ⟨fun i => co L (Ψ i) 0, fun i => ⟨eq_mode_of_grad2_eq_zero hL (hg i), ?_⟩, ?_⟩
    · have h1 := hU i 0
      rw [pt, eq_mode_of_grad2_eq_zero hL (hg i), co_mode, field_single_zero, hnorm] at h1
      exact (div_eq_one_iff_eq hL.ne').1 h1
    · have h0 := hd 0
      have hΨ : Ψ = fun i => mode L 0 (co L (Ψ i) 0) :=
        funext fun i => eq_mode_of_grad2_eq_zero hL (hg i)
      rw [dens, hΨ, pt_mode] at h0
      simpa [co_mode] using h0
  · rintro ⟨c, hc, h0⟩
    have hΨ : Ψ = fun i => mode L 0 (c i) := funext fun i => (hc i).1
    refine ⟨fun i x => ?_, fun x => ?_, fun i => ?_⟩
    · rw [hΨ, pt_mode, hnorm, (hc i).2, div_self hL.ne']
    · rw [dens, hΨ, pt_mode]
      exact h0
    · rw [(hc i).1]
      exact grad2_mode_zero L _

/-! ### Curvature-locked under the frozen evolution -/

theorem rel_phase (c : ℕ → ℂ) (s : ℝ) :
    rel (fun i => (L : ℂ)⁻¹ * (c i * cexp ((s : ℂ) * I))) = rel (fun i => (L : ℂ)⁻¹ * c i) := by
  funext i
  simp only [rel, map_mul]
  have he : cexp ((s : ℂ) * I) * (starRingEnd ℂ) (cexp ((s : ℂ) * I)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  linear_combination ((L : ℂ)⁻¹ * c (i + 1) * (starRingEnd ℂ) ((L : ℂ)⁻¹) *
    (starRingEnd ℂ) (c 0)) * he

/-- The frozen evolution of a locking configuration: every component is the exact zero-mode
solution, with one common frequency because every amplitude has `|cᵢ| = L`. -/
noncomputable def lockFlow (L κ β γ : ℝ) (c : ℕ → ℂ) (t : ℝ) : MField :=
  fun i => zeroMode L κ β γ (c i) t

/-- **Locks are curvature-locked under the frozen evolution.** Each component of the evolved
configuration is an exact solution, the configuration is locked at every time, and the
Laplacian vanishes identically. -/
theorem locked_frozen_flow (F : CNF3) (hL : 0 < L) {lam mu : ℝ} {c : ℕ → ℂ}
    (hc : ∀ i, ‖c i‖ = L) (h0 : energySB F lam mu (rel fun i => (L : ℂ)⁻¹ * c i) = 0) :
    (∀ i, IsSolution L κ β γ fun t => lockFlow L κ β γ c t i) ∧
    (∀ t, Locked F lam mu L (lockFlow L κ β γ c t)) ∧
    ∀ t i, Dc L (lockFlow L κ β γ c t i) = 0 := by
  refine ⟨fun i => zeroMode_isSolution hL (c i), fun t => ?_, fun t i => Dc_zeroMode _ _ _ _ _ _⟩
  set Ω := Om L κ β γ L
  have hfl : lockFlow L κ β γ c t = fun i => mode L 0 (c i * cexp (((-(Ω * t) : ℝ) : ℂ) * I)) := by
    funext i
    simp only [lockFlow, zeroMode, hc i, Ω]
  rw [hfl, locked_iff F hL]
  refine ⟨fun i => c i * cexp (((-(Ω * t) : ℝ) : ℂ) * I), fun i => ⟨rfl, ?_⟩, ?_⟩
  · rw [norm_amp, hc i]
  · rw [rel_phase]
    exact h0

/-- **The frozen flow preserves locks.** If every component of a family of frozen solutions
starts in a locking configuration, the family is locked at every time (uniqueness of solutions,
`γ > 0`). -/
theorem frozen_flow_preserves_locks (F : CNF3) (hL : 0 < L) (hγ : 0 < γ) {lam mu : ℝ}
    {U : ℕ → ℝ → ℓ2} (hU : ∀ i, IsSolution L κ β γ (U i))
    (h0 : Locked F lam mu L fun i => U i 0) (t : ℝ) :
    Locked F lam mu L fun i => U i t := by
  obtain ⟨c, hc, hE⟩ := (locked_iff F hL _).1 h0
  have heq : ∀ i, U i = fun s => lockFlow L κ β γ c s i := by
    intro i
    obtain ⟨w, -, huniq⟩ := global_wellposed (κ := κ) (β := β) hL hγ (U i 0)
    have h1 := huniq (U i) ⟨rfl, hU i⟩
    have h2 := huniq (fun s => lockFlow L κ β γ c s i)
      ⟨by simp [lockFlow, zeroMode, (hc i).1], zeroMode_isSolution hL (c i)⟩
    rw [h1, h2]
  have hfl := (locked_frozen_flow (κ := κ) (β := β) (γ := γ) F hL (fun i => (hc i).2) hE).2.1 t
  convert hfl using 1
  funext i
  rw [heq i]

/-! ### The frozen flow never approaches a lock from outside

For `κ ≤ 0`, `β ≤ 0` (defocusing cubic term) and `γ ≥ 0`, a zero-mode state is the strict
minimizer of the conserved Hamiltonian among states of its mass. Since mass and Hamiltonian are
conserved and continuous, a frozen trajectory can come close to a zero-mode state only if it is a
zero-mode state itself. No stability hypothesis is used. -/

theorem summable_mass (L : ℝ) (v : ℓ2) : Summable fun k => ‖co L v k‖ ^ 2 :=
  (summable_sq v).of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_co_le L v k) 2)

theorem norm_Ac_sq (L κ : ℝ) (v : ℓ2) (k : Z2) :
    ‖Ac L κ v k‖ ^ 2 = (κ - qf L k) ^ 2 * ‖co L v k‖ ^ 2 := by
  rw [Ac_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The kinetic energy `‖(Δ + κ)ψ‖²` in coefficients. -/
theorem kin_eq (L κ : ℝ) (v : ℓ2) :
    ‖Ac L κ v‖ ^ 2 = ∑' k, (κ - qf L k) ^ 2 * ‖co L v k‖ ^ 2 := by
  rw [norm_sq_eq]
  exact tsum_congr fun k => norm_Ac_sq L κ v k

theorem summable_kin (L κ : ℝ) (v : ℓ2) :
    Summable fun k => (κ - qf L k) ^ 2 * ‖co L v k‖ ^ 2 :=
  (summable_sq (Ac L κ v)).congr fun k => norm_Ac_sq L κ v k

/-- A state whose only nonzero coefficient is at the zero mode. -/
theorem eq_mode_of_coeff {v : ℓ2} (h : ∀ k, k ≠ 0 → co L v k = 0) :
    v = mode L 0 (co L v 0) := by
  ext k
  rw [mode, lp.single_apply]
  by_cases hk : k = 0
  · subst hk
    rw [Pi.single_eq_same, wt_zero, Complex.ofReal_one, one_mul, co, wt_zero, Complex.ofReal_one,
      div_one]
  · rw [Pi.single_eq_of_ne hk, ← wt_mul_co L v k, h k hk, mul_zero]

theorem kin_ge (hκ : κ ≤ 0) (v : ℓ2) : κ ^ 2 * mass L v ≤ ‖Ac L κ v‖ ^ 2 := by
  rw [kin_eq, mass, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) ((summable_mass L v).mul_left _) (summable_kin L κ v)
  have hq := qf_nonneg L k
  have : κ ^ 2 ≤ (κ - qf L k) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

theorem eq_mode_of_kin_eq (hL : 0 < L) (hκ : κ ≤ 0) {v : ℓ2}
    (h : ‖Ac L κ v‖ ^ 2 = κ ^ 2 * mass L v) : v = mode L 0 (co L v 0) := by
  have hs : Summable fun k => ((κ - qf L k) ^ 2 - κ ^ 2) * ‖co L v k‖ ^ 2 :=
    ((summable_kin L κ v).sub ((summable_mass L v).mul_left (κ ^ 2))).congr fun k => by ring
  have hnn : ∀ k, 0 ≤ ((κ - qf L k) ^ 2 - κ ^ 2) * ‖co L v k‖ ^ 2 := fun k => by
    have hq := qf_nonneg L k
    exact mul_nonneg (by nlinarith) (sq_nonneg _)
  have htsum : ∑' k, ((κ - qf L k) ^ 2 - κ ^ 2) * ‖co L v k‖ ^ 2 = 0 := by
    have e : ∑' k, ((κ - qf L k) ^ 2 - κ ^ 2) * ‖co L v k‖ ^ 2 =
        ∑' k, (κ - qf L k) ^ 2 * ‖co L v k‖ ^ 2 - ∑' k, κ ^ 2 * ‖co L v k‖ ^ 2 := by
      rw [← Summable.tsum_sub (summable_kin L κ v) ((summable_mass L v).mul_left _)]
      exact tsum_congr fun k => by ring
    rw [e, ← kin_eq, tsum_mul_left, h, mass, sub_self]
  have hsum : HasSum (fun k => ((κ - qf L k) ^ 2 - κ ^ 2) * ‖co L v k‖ ^ 2) 0 := by
    have := hs.hasSum
    rwa [htsum] at this
  have hzero := (hasSum_zero_iff_of_nonneg hnn).1 hsum
  refine eq_mode_of_coeff fun k hk => ?_
  have hk0 := congrFun hzero k
  simp only [Pi.zero_apply] at hk0
  have hq := qf_pos hL hk
  have hpos : 0 < (κ - qf L k) ^ 2 - κ ^ 2 := by nlinarith
  rcases mul_eq_zero.1 hk0 with h1 | h1
  · exact absurd h1 hpos.ne'
  · exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)

/-- The area of the fundamental box. -/
theorem box_real_univ (hL : 0 < L) : (box L).real Set.univ = L ^ 2 := by
  have h := integral_emode hL (0 : Z2)
  simp only [emode_zero, if_true, integral_const, Complex.real_smul, mul_one] at h
  exact_mod_cast h

theorem bound_field (hL : 0 < L) (v : ℓ2) :
    ∃ B, 0 ≤ B ∧ ∀ x, ‖Torus.field L (co L v) x‖ ≤ B :=
  ⟨|L|⁻¹ * ∑' k, ‖co L v k‖, mul_nonneg (by positivity) (tsum_nonneg fun _ => norm_nonneg _),
    fun x => norm_field_le (L1_co' hL v) x⟩

/-- **The potential energy is minimized by constant amplitude** (`β ≤ 0`, `γ ≥ 0`):
`∫(−β/2|ψ|⁴ + γ/3|ψ|⁶) ≥ −β/2 · M²/L² + γ/3 · M³/L⁴`, `M` the mass. -/
theorem pot_ge (hL : 0 < L) (hβ : β ≤ 0) (hγ : 0 ≤ γ) (v : ℓ2) :
    -β / 2 * mass L v ^ 2 / L ^ 2 + γ / 3 * mass L v ^ 3 / L ^ 4 ≤ pot L β γ v := by
  set f : ℝ × ℝ → ℂ := fun x => Torus.field L (co L v) x with hf
  set M := mass L v with hMdef
  have hfc : Continuous f := continuous_field (L1_co' hL v)
  obtain ⟨B, hB0, hB⟩ := bound_field hL v
  have hM : M = ∫ x, ‖f x‖ ^ 2 ∂box L := mass_eq_integral hL v
  have hM0 : 0 ≤ M := by
    rw [hMdef, mass]
    exact tsum_nonneg fun _ => sq_nonneg _
  have hL2 : 0 < L ^ 2 := by positivity
  set a := M / L ^ 2 with ha_def
  have ha : 0 ≤ a := div_nonneg hM0 hL2.le
  have hint_s : Integrable (fun x => ‖f x‖ ^ 2) (box L) := by
    refine Integrable.mono' (integrable_const (B ^ 2))
      ((continuous_norm.comp hfc).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  have hint_pot : Integrable (fun x => nfun β γ (f x)) (box L) := by
    refine Integrable.mono' (integrable_const (|β| / 2 * B ^ 4 + |γ| / 3 * B ^ 6))
      ((continuous_const.mul ((continuous_norm.comp hfc).pow 4)).add
        (continuous_const.mul ((continuous_norm.comp hfc).pow 6))).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    unfold nfun
    have h4 : ‖f x‖ ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (hB x) 4
    have h6 : ‖f x‖ ^ 6 ≤ B ^ 6 := pow_le_pow_left₀ (norm_nonneg _) (hB x) 6
    have h4' := pow_nonneg (norm_nonneg (f x)) 4
    have h6' := pow_nonneg (norm_nonneg (f x)) 6
    calc ‖-β / 2 * ‖f x‖ ^ 4 + γ / 3 * ‖f x‖ ^ 6‖
        ≤ ‖-β / 2 * ‖f x‖ ^ 4‖ + ‖γ / 3 * ‖f x‖ ^ 6‖ := norm_add_le _ _
      _ = |β| / 2 * ‖f x‖ ^ 4 + |γ| / 3 * ‖f x‖ ^ 6 := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_div, abs_neg,
          abs_of_nonneg h4', abs_of_nonneg h6']
        norm_num
      _ ≤ |β| / 2 * B ^ 4 + |γ| / 3 * B ^ 6 := by gcongr
  have hpt : ∀ x, (-β * a + γ * a ^ 2) * ‖f x‖ ^ 2 + (β / 2 * a ^ 2 - 2 * γ / 3 * a ^ 3) ≤
      nfun β γ (f x) := by
    intro x
    set s := ‖f x‖ ^ 2 with hs_def
    have hs : 0 ≤ s := sq_nonneg _
    unfold nfun
    have e4 : ‖f x‖ ^ 4 = s ^ 2 := by rw [hs_def]; ring
    have e6 : ‖f x‖ ^ 6 = s ^ 3 := by rw [hs_def]; ring
    rw [e4, e6]
    have h1 : 2 * a * s - a ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - a)]
    have h2 : 3 * a ^ 2 * s - 2 * a ^ 3 ≤ s ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (s - a)) (add_nonneg hs (mul_nonneg zero_le_two ha))]
    have hb : 0 ≤ -β / 2 := by linarith
    have hg : 0 ≤ γ / 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hb, mul_le_mul_of_nonneg_left h2 hg]
  have hlow_int : Integrable (fun x => (-β * a + γ * a ^ 2) * ‖f x‖ ^ 2 +
      (β / 2 * a ^ 2 - 2 * γ / 3 * a ^ 3)) (box L) :=
    (hint_s.const_mul _).add (integrable_const _)
  have hmono := integral_mono hlow_int hint_pot hpt
  have hlow : ∫ x, ((-β * a + γ * a ^ 2) * ‖f x‖ ^ 2 + (β / 2 * a ^ 2 - 2 * γ / 3 * a ^ 3))
      ∂box L = (-β * a + γ * a ^ 2) * M + L ^ 2 * (β / 2 * a ^ 2 - 2 * γ / 3 * a ^ 3) := by
    rw [integral_add (hint_s.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, smul_eq_mul, box_real_univ hL, ← hM]
  rw [hlow] at hmono
  have hval : (-β * a + γ * a ^ 2) * M + L ^ 2 * (β / 2 * a ^ 2 - 2 * γ / 3 * a ^ 3) =
      -β / 2 * M ^ 2 / L ^ 2 + γ / 3 * M ^ 3 / L ^ 4 := by
    rw [ha_def]
    field_simp
    ring
  unfold pot
  linarith

/-- The Hamiltonian of a constant field with mass `M`. -/
noncomputable def hstar (L κ β γ M : ℝ) : ℝ :=
  κ ^ 2 * M + (-β / 2 * M ^ 2 / L ^ 2 + γ / 3 * M ^ 3 / L ^ 4)

theorem ham_ge (hL : 0 < L) (hκ : κ ≤ 0) (hβ : β ≤ 0) (hγ : 0 ≤ γ) (v : ℓ2) :
    hstar L κ β γ (mass L v) ≤ ham L κ β γ v := by
  unfold hstar ham
  linarith [kin_ge (L := L) hκ v, pot_ge hL hβ hγ v]

theorem eq_mode_of_ham_eq (hL : 0 < L) (hκ : κ ≤ 0) (hβ : β ≤ 0) (hγ : 0 ≤ γ) {v : ℓ2}
    (h : ham L κ β γ v = hstar L κ β γ (mass L v)) : v = mode L 0 (co L v 0) := by
  refine eq_mode_of_kin_eq hL hκ (le_antisymm ?_ (kin_ge hκ v))
  unfold hstar ham at h
  linarith [pot_ge hL hβ hγ v]

theorem ham_mode (hL : 0 < L) (c : ℂ) :
    ham L κ β γ (mode L 0 c) = hstar L κ β γ (‖c‖ ^ 2) := by
  unfold ham hstar
  congr 1
  · rw [kin_eq, co_mode, tsum_eq_single 0 (fun k hk => by rw [Pi.single_eq_of_ne hk]; simp),
      Pi.single_eq_same, qf_zero, sub_zero]
  · unfold pot
    rw [co_mode]
    simp_rw [field_single_zero]
    rw [integral_const, box_real_univ hL, smul_eq_mul]
    unfold nfun
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    field_simp

/-- **A frozen trajectory approaches a zero-mode state only if it is one** (`κ ≤ 0`, `β ≤ 0`,
`γ ≥ 0`): if `u (tₙ) → (constant field c/L)` along any sequence of times, then `u 0` is itself a
constant field with the same amplitude. -/
theorem approach_zeroMode (hL : 0 < L) (hκ : κ ≤ 0) (hβ : β ≤ 0) (hγ : 0 ≤ γ) {u : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u) {t : ℕ → ℝ} {c : ℂ}
    (h : Tendsto (fun n => u (t n)) atTop (𝓝 (mode L 0 c))) :
    u 0 = mode L 0 (co L (u 0) 0) ∧ ‖co L (u 0) 0‖ = ‖c‖ := by
  have hm : mass L (u 0) = mass L (mode L 0 c) := by
    have h1 := ((continuous_mass L).tendsto _).comp h
    have h2 : (mass L ∘ fun n => u (t n)) = fun _ => mass L (u 0) :=
      funext fun n => (conservation hL hu (t n)).1
    rw [h2] at h1
    exact tendsto_nhds_unique tendsto_const_nhds h1
  have hh : ham L κ β γ (u 0) = ham L κ β γ (mode L 0 c) := by
    have h1 := ((continuous_ham hL κ β γ).tendsto _).comp h
    have h2 : (ham L κ β γ ∘ fun n => u (t n)) = fun _ => ham L κ β γ (u 0) :=
      funext fun n => (conservation hL hu (t n)).2
    rw [h2] at h1
    exact tendsto_nhds_unique tendsto_const_nhds h1
  have hmc : mass L (mode L 0 c) = ‖c‖ ^ 2 := mass_mode L 0 c
  have heq : ham L κ β γ (u 0) = hstar L κ β γ (mass L (u 0)) := by
    rw [hh, ham_mode hL, hm, hmc]
  have hv := eq_mode_of_ham_eq hL hκ hβ hγ heq
  refine ⟨hv, ?_⟩
  have h1 : mass L (u 0) = ‖co L (u 0) 0‖ ^ 2 := by
    conv_lhs => rw [hv]
    exact mass_mode L 0 _
  have h2 : ‖co L (u 0) 0‖ ^ 2 = ‖c‖ ^ 2 := by rw [← h1, hm, hmc]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

theorem mode_apply_zero (L : ℝ) (c : ℂ) : (mode L 0 c : ℓ2) 0 = c := by
  rw [mode, lp.single_apply, Pi.single_eq_same, wt_zero, Complex.ofReal_one, one_mul]

/-- **No attracting locks in the frozen dynamics** (`κ ≤ 0`, `β ≤ 0`, `γ > 0`). If a family of
frozen solutions approaches a locking configuration along any sequence of times, it started in a
locking configuration. So the frozen evolution never brings a non-locked field to a lock, nor even
arbitrarily close to one. -/
theorem no_attracting_locks (F : CNF3) (hL : 0 < L) (hκ : κ ≤ 0) (hβ : β ≤ 0) (hγ : 0 < γ)
    {lam mu : ℝ} {U : ℕ → ℝ → ℓ2} (hU : ∀ i, IsSolution L κ β γ (U i)) {t : ℕ → ℝ}
    {Φ : MField} (hΦ : Locked F lam mu L Φ)
    (h : ∀ i, Tendsto (fun n => U i (t n)) atTop (𝓝 (Φ i))) :
    Locked F lam mu L fun i => U i 0 := by
  obtain ⟨c, hc, hE⟩ := (locked_iff F hL Φ).1 hΦ
  set c₀ : ℕ → ℂ := fun i => co L (U i 0) 0 with hc₀
  have hcomp : ∀ i, U i 0 = mode L 0 (c₀ i) ∧ ‖c₀ i‖ = L := fun i => by
    have h' : Tendsto (fun n => U i (t n)) atTop (𝓝 (mode L 0 (c i))) := by
      rw [← (hc i).1]
      exact h i
    have := approach_zeroMode hL hκ hβ hγ.le (hU i) h'
    exact ⟨this.1, this.2.trans (hc i).2⟩
  have heq : ∀ i, U i = fun s => lockFlow L κ β γ c₀ s i := by
    intro i
    obtain ⟨w, -, huniq⟩ := global_wellposed (κ := κ) (β := β) hL hγ (U i 0)
    have h1 := huniq (U i) ⟨rfl, hU i⟩
    have h2 := huniq (fun s => lockFlow L κ β γ c₀ s i)
      ⟨by simp [lockFlow, zeroMode, ← (hcomp i).1], zeroMode_isSolution hL (c₀ i)⟩
    rw [h1, h2]
  set e : ℕ → ℂ := fun n => cexp (((-(Om L κ β γ L * t n) : ℝ) : ℂ) * I) with he
  have hval : ∀ i n, U i (t n) 0 = c₀ i * e n := by
    intro i n
    rw [heq i]
    simp only [lockFlow, zeroMode, (hcomp i).2, he]
    exact mode_apply_zero L _
  have hlim : ∀ i, Tendsto (fun n => U i (t n) 0) atTop (𝓝 (c i)) := by
    intro i
    have := ((evalL (0 : Z2)).continuous.tendsto _).comp (h i)
    simpa [Function.comp_def, (hc i).1, mode_apply_zero] using this
  have hee : ∀ n, e n * (starRingEnd ℂ) (e n) = 1 := fun n => by
    rw [he, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hprod : ∀ i, c₀ (i + 1) * (starRingEnd ℂ) (c₀ 0) = c (i + 1) * (starRingEnd ℂ) (c 0) := by
    intro i
    have hT : Tendsto (fun n => U (i + 1) (t n) 0 * (starRingEnd ℂ) (U 0 (t n) 0)) atTop
        (𝓝 (c (i + 1) * (starRingEnd ℂ) (c 0))) :=
      (hlim (i + 1)).mul ((Complex.continuous_conj.tendsto _).comp (hlim 0))
    have hconst : (fun n => U (i + 1) (t n) 0 * (starRingEnd ℂ) (U 0 (t n) 0)) =
        fun _ => c₀ (i + 1) * (starRingEnd ℂ) (c₀ 0) := by
      funext n
      rw [hval, hval, map_mul]
      linear_combination (c₀ (i + 1) * (starRingEnd ℂ) (c₀ 0)) * hee n
    rw [hconst] at hT
    exact tendsto_nhds_unique tendsto_const_nhds hT
  refine (locked_iff F hL _).2 ⟨c₀, hcomp, ?_⟩
  have hrel : rel (fun i => (L : ℂ)⁻¹ * c₀ i) = rel (fun i => (L : ℂ)⁻¹ * c i) := by
    funext i
    simp only [rel, map_mul]
    linear_combination ((L : ℂ)⁻¹ * (starRingEnd ℂ) ((L : ℂ)⁻¹)) * hprod i
  rw [hrel]
  exact hE

end PVNP.SpatialLocking
