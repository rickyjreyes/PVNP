import PVNP.TorusWellPosed

/-!
# I-37: the frozen dynamics cannot lock

Part I defines a curvature-locked state through the evolution: `W_ψ = −Δψ/(ψ + εe^{−α|ψ|²})` with
`dS[ψ]/dt → 0` and `∇W_ψ → 0` "under the WCT/WCC evolution rules", and §12.3 asks that a
toroidal locking configuration exist exactly for satisfiable formulas. A physical realization in
the frozen model needs two things from the actual dynamics `i∂ₜψ = (Δ+κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ` on
the torus `T_L²`:

* **convergence**: the trajectory of the encoded initial state approaches the set `Λ` of locked
  states;
* **robust readout**: `Λ` is Lyapunov stable, so that states prepared or perturbed near a lock
  stay near it.

This module proves that the frozen dynamics cannot provide both. The flow is time-reversible:
`conjH`, complex conjugation in Fourier coefficients (`(conjH v)_k = conj v_{−k}`), maps the
solution `t ↦ u t` to the solution `t ↦ conjH (u (−t))` (`isSolution_reverse`). Hence
(`no_locking`): if `Λ` is stable and invariant under `conjH`, a solution that converges to `Λ`
**starts** in the closure of `Λ`. Locking never happens from outside the lock set.

The hypothesis `conjH Λ ⊆ Λ` holds for the binary-phase (real-valued) encodings used by the
ψ-SAT construction (`realStates_conj`) and for the phase orbit of any real-valued state
(`phaseOrbit_conj`), which is the shape of a standing-wave lock.

So in the frozen model a toroidal locking scheme is either not robust (its lock set is unstable),
or trivial (the encoder must already prepare a locked state, and the dynamics computes nothing).
A realization of §12.3 needs dissipation or forcing, which the frozen model excludes.

The same symmetry gives `backward_eq_forward_conj` and `flow_neg`: the state at time `−t` is the
conjugate of the forward evolution of the conjugated state. Running the frozen dynamics backward
adds nothing to running it forward (Part III §8, III-22).
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace PVNP.Torus

variable {L κ β γ : ℝ}

/-! ## Symmetries of the coefficient equations -/

theorem conjH_conjH (v : ℓ2) : conjH (conjH v) = v := by
  ext k
  simp [conjH_apply]

theorem conjH_isometry : Isometry conjH := by
  apply Isometry.of_dist_eq
  intro v w
  rw [dist_eq_norm, dist_eq_norm, norm_conjH_sub]

theorem continuous_conjH : Continuous conjH := conjH_isometry.continuous

theorem conjH_smul (c : ℂ) (v : ℓ2) : conjH (c • v) = (starRingEnd ℂ) c • conjH v := by
  ext k
  simp [conjH_apply, map_mul]

theorem om_neg (L κ : ℝ) (k : Z2) : om L κ (-k) = om L κ k := by
  simp only [om, qf_neg]

theorem fnl_conj (β γ : ℝ) (z : ℂ) :
    fnl β γ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (fnl β γ z) := by
  simp only [fnl, map_add, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]

theorem emode_conj (L : ℝ) (k : Z2) (x : ℝ × ℝ) :
    (starRingEnd ℂ) (emode L (-k) x) = emode L k x := by
  rw [emode_neg, Complex.conj_conj]

/-- The Fourier coefficient of a conjugated function. -/
theorem fc_conj (L : ℝ) (f : ℝ × ℝ → ℂ) (k : Z2) :
    fc L (fun x => (starRingEnd ℂ) (f x)) k = (starRingEnd ℂ) (fc L f (-k)) := by
  unfold fc
  rw [map_mul, map_inv₀, Complex.conj_ofReal, ← integral_conj]
  congr 1
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_conj]
  rw [emode_neg]

/-- **Time reversal.** If `u` solves the frozen equation, so does `t ↦ conjH (u (−t))`. -/
theorem isSolution_reverse {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) :
    IsSolution L κ β γ (fun t => conjH (u (-t))) := by
  refine ⟨continuous_conjH.comp (hu.1.comp continuous_neg), fun t k => ?_⟩
  have h := hu.2 (-t) (-k)
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := by simpa using (hasDerivAt_id t).neg
  have hcomp := h.scomp t hneg
  have hstar := hcomp.star
  simp only [co_conjH]
  convert hstar using 1
  have hfield : (fun x => fnl β γ (field L (rev (co L (u (-t)))) x)) =
      fun x => (starRingEnd ℂ) (fnl β γ (field L (co L (u (-t))) x)) := by
    funext x
    rw [field_rev, fnl_conj]
  rw [hfield, fc_conj, om_neg]
  simp only [rev, neg_smul, one_smul, star_neg, Complex.star_def, map_mul, map_add, map_neg,
    Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **Time translation.** -/
theorem isSolution_shift {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u) (T : ℝ) :
    IsSolution L κ β γ (fun t => u (t + T)) := by
  refine ⟨hu.1.comp (continuous_add_right T), fun t k => ?_⟩
  have h := hu.2 (t + T) k
  have hadd : HasDerivAt (fun s : ℝ => s + T) 1 t := by simpa using (hasDerivAt_id t).add_const T
  have := h.scomp t hadd
  simpa [Function.comp] using this

/-! ## Running the frozen dynamics backward is forward dynamics, conjugated

This is the precise content behind Part III §8 ("inverse dynamics need not efficiently solve
SAT") for the frozen model: the state at time `−t` is obtained by running the *forward* dynamics
for time `t` from the conjugated state and conjugating back. Time-reversed ("retrocausal") readout
is therefore a forward computation with the encoder and decoder composed with `conjH`. -/

/-- **Backward evolution is conjugated forward evolution.** If `u` and `v` solve the frozen
equation and `v 0 = conjH (u 0)`, then `u (−t) = conjH (v t)` for every `t`. -/
theorem backward_eq_forward_conj (hL : 0 < L) (hγ : 0 < γ) {u v : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u) (hv : IsSolution L κ β γ v) (h0 : v 0 = conjH (u 0)) (t : ℝ) :
    u (-t) = conjH (v t) := by
  obtain ⟨w, -, huniq⟩ := global_wellposed (κ := κ) (β := β) hL hγ (conjH (u 0))
  have hrev : (fun s => conjH (u (-s))) = w :=
    huniq _ ⟨by simp, isSolution_reverse hu⟩
  have hvw : v = w := huniq _ ⟨h0, hv⟩
  have := congrFun (hrev.trans hvw.symm) t
  simp only at this
  rw [← this, conjH_conjH]

/-- The frozen flow map `Φ_t`, from global well-posedness. -/
noncomputable def flow (hL : 0 < L) (hγ : 0 < γ) (t : ℝ) (u₀ : ℓ2) : ℓ2 :=
  (global_wellposed (κ := κ) (β := β) hL hγ u₀).choose t

theorem flow_spec (hL : 0 < L) (hγ : 0 < γ) (u₀ : ℓ2) :
    (fun t => flow (κ := κ) (β := β) hL hγ t u₀) 0 = u₀ ∧
      IsSolution L κ β γ (fun t => flow (κ := κ) (β := β) hL hγ t u₀) :=
  (global_wellposed (κ := κ) (β := β) hL hγ u₀).choose_spec.1

/-- **`Φ_{−t} = conjH ∘ Φ_t ∘ conjH`.** -/
theorem flow_neg (hL : 0 < L) (hγ : 0 < γ) (t : ℝ) (u₀ : ℓ2) :
    flow (κ := κ) (β := β) hL hγ (-t) u₀ =
      conjH (flow (κ := κ) (β := β) hL hγ t (conjH u₀)) := by
  have hu := flow_spec (κ := κ) (β := β) hL hγ u₀
  have hv := flow_spec (κ := κ) (β := β) hL hγ (conjH u₀)
  have h0u : flow (κ := κ) (β := β) hL hγ 0 u₀ = u₀ := hu.1
  have h0v : flow (κ := κ) (β := β) hL hγ 0 (conjH u₀) = conjH u₀ := hv.1
  exact backward_eq_forward_conj hL hγ hu.2 hv.2 (by rw [h0v, h0u]) t

/-! ## Locking -/

/-- A set of states is a **stable lock** for the frozen dynamics: solutions that start within `δ`
of it stay within `ε` of it for all later times. -/
def StableLock (L κ β γ : ℝ) (Λ : Set ℓ2) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ v : ℝ → ℓ2, IsSolution L κ β γ v → infDist (v 0) Λ < δ →
    ∀ t ≥ 0, infDist (v t) Λ < ε

theorem infDist_conjH_le {Λ : Set ℓ2} (hΛ : Λ.Nonempty) (hR : ∀ w ∈ Λ, conjH w ∈ Λ) (v : ℓ2) :
    infDist (conjH v) Λ ≤ infDist v Λ := by
  have himg : conjH '' Λ ⊆ Λ := by
    rintro _ ⟨w, hw, rfl⟩
    exact hR w hw
  calc infDist (conjH v) Λ ≤ infDist (conjH v) (conjH '' Λ) :=
        infDist_le_infDist_of_subset himg (hΛ.image _)
    _ = infDist v Λ := Metric.infDist_image conjH_isometry

/-- **No locking.** Let `Λ` be a nonempty stable lock invariant under time reversal. If a
solution of the frozen equation converges to `Λ`, then its initial state already lies in the
closure of `Λ`. -/
theorem no_locking {Λ : Set ℓ2} (hne : Λ.Nonempty) (hstab : StableLock L κ β γ Λ)
    (hR : ∀ w ∈ Λ, conjH w ∈ Λ) {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u)
    (hconv : Tendsto (fun t => infDist (u t) Λ) atTop (𝓝 0)) : u 0 ∈ closure Λ := by
  rw [mem_closure_iff_infDist_zero hne]
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) infDist_nonneg
  obtain ⟨δ, hδ, hstabδ⟩ := hstab ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hconv.eventually (gt_mem_nhds hδ))
  set T := max T₀ 0 with hT
  have hTpos : 0 ≤ T := le_max_right _ _
  have hclose : infDist (u T) Λ < δ := hT₀ T (le_max_left _ _)
  -- the reversed trajectory starting from `conjH (u T)`
  set v : ℝ → ℓ2 := fun t => conjH (u (-t + T)) with hv
  have hvsol : IsSolution L κ β γ v := by
    have h1 := isSolution_shift hu T
    have h2 := isSolution_reverse h1
    simpa [hv] using h2
  have hv0 : infDist (v 0) Λ < δ := by
    simp only [hv, neg_zero, zero_add]
    exact lt_of_le_of_lt (infDist_conjH_le hne hR _) hclose
  have hvT := hstabδ v hvsol hv0 T hTpos
  simp only [hv, neg_add_cancel] at hvT
  have : infDist (u 0) Λ ≤ infDist (conjH (u 0)) Λ := by
    have := infDist_conjH_le hne hR (conjH (u 0))
    rwa [conjH_conjH] at this
  linarith

/-- The dichotomy: a nonempty lock set invariant under time reversal is either unstable or
reached only by trajectories that start in its closure. -/
theorem unstable_or_unreachable {Λ : Set ℓ2} (hne : Λ.Nonempty) (hR : ∀ w ∈ Λ, conjH w ∈ Λ) :
    ¬ StableLock L κ β γ Λ ∨
      ∀ u : ℝ → ℓ2, IsSolution L κ β γ u →
        Tendsto (fun t => infDist (u t) Λ) atTop (𝓝 0) → u 0 ∈ closure Λ := by
  by_cases h : StableLock L κ β γ Λ
  · exact Or.inr fun u hu hconv => no_locking hne h hR hu hconv
  · exact Or.inl h

/-! ## Lock sets invariant under time reversal -/

/-- States whose field is real-valued: the binary-phase (`0`/`π`) encodings of ψ-SAT. -/
def realStates : Set ℓ2 := {w | conjH w = w}

theorem realStates_conj : ∀ w ∈ realStates, conjH w ∈ realStates := by
  intro w hw
  simp only [realStates, mem_setOf_eq] at hw ⊢
  rw [hw, hw]

/-- A state in `realStates` has a real field. -/
theorem field_real_of_realState {w : ℓ2} (hw : w ∈ realStates) (x : ℝ × ℝ) :
    (starRingEnd ℂ) (field L (co L w) x) = field L (co L w) x := by
  rw [← field_conjH]
  simp only [realStates, mem_setOf_eq] at hw
  rw [hw]

/-- The phase orbit `{e^{iθ} v}` of a state: the shape of a standing-wave lock. -/
def phaseOrbit (v : ℓ2) : Set ℓ2 := range fun θ : ℝ => Complex.exp ((θ : ℂ) * I) • v

theorem phaseOrbit_conj {v : ℓ2} (hv : v ∈ realStates) :
    ∀ w ∈ phaseOrbit v, conjH w ∈ phaseOrbit v := by
  rintro _ ⟨θ, rfl⟩
  simp only [realStates, mem_setOf_eq] at hv
  have h1 : conjH (Complex.exp ((θ : ℂ) * I) • v) =
      (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * I)) • v := by
    rw [conjH_smul, hv]
  have h2 : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * I)) = Complex.exp (((-θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  refine ⟨-θ, ?_⟩
  show Complex.exp (((-θ : ℝ) : ℂ) * I) • v = conjH (Complex.exp ((θ : ℂ) * I) • v)
  rw [h1, h2]

/-- **Binary-phase locks are unreachable or unstable.** For the phase orbit of any real-valued
state (in particular of a binary-phase ψ-SAT encoding): if the orbit is a stable lock, no solution
of the frozen equation converges to it unless it starts in its closure. -/
theorem no_locking_phaseOrbit {v : ℓ2} (hv : v ∈ realStates)
    (hstab : StableLock L κ β γ (phaseOrbit v)) {u : ℝ → ℓ2} (hu : IsSolution L κ β γ u)
    (hconv : Tendsto (fun t => infDist (u t) (phaseOrbit v)) atTop (𝓝 0)) :
    u 0 ∈ closure (phaseOrbit v) :=
  no_locking (Λ := phaseOrbit v) ⟨v, 0, by simp⟩ hstab (phaseOrbit_conj hv) hu hconv

/-- The same for the set of all binary-phase (real-valued) states. -/
theorem no_locking_realStates (hstab : StableLock L κ β γ realStates) {u : ℝ → ℓ2}
    (hu : IsSolution L κ β γ u)
    (hconv : Tendsto (fun t => infDist (u t) realStates) atTop (𝓝 0)) :
    u 0 ∈ closure realStates :=
  no_locking (Λ := realStates) ⟨0, by simp [realStates, conjH_zero]⟩ hstab realStates_conj hu hconv

end PVNP.Torus
