import Mathlib

/-!
# Part II: wave–symbol correspondence and curvature-bounded channel capacity

Literal translations of Part II (*Discrete Wave-Constrained Computation and Classical
Complexity*, revised 27 October 2026):

* `wave_symbol_forward`, `wave_symbol_converse`: Theorem `thm:wave-symbol-isomorphism`.
* `compatibility_necessary`: Remark `rem:wave-symbol-obstruction`, with the manuscript's
  counterexample `Z = {−1, ½, 1}`.
* `bandlimit_eff`, `bandlimit_sharp`: Lemma `lem:bandlimit`.
* `spatial_capacity`, `spatial_capacity_energy`: Lemma `lem:spatial_capacity`. The number of
  modes `k ∈ (2π/ℓ)ℤ³` with `‖k‖ ≤ k_max ≥ 2π/ℓ` is at most `C₂ V k_max³` with
  `C₂ = 27/(8π³)` and `V = ℓ³`, hence at most `C₂ V (C₁E_max/(ħc))³` under the sharp cutoff.
* `lane_update_bound`: Lemma `lem:lane_update_bound`.
* `spacetime_capacity`: Theorem `thm:spacetime_capacity` (and the restatement
  `thm:channel_capacity`).
* `phys_step_ceiling`, `rounds_le_events`: Proposition `prop:phys_step_ceiling`.

The physical hypotheses (rest-energy identity, curvature–wavenumber coupling, sharp spectral
support, minimum dwell time, independent lanes, counting premise) enter as explicit
hypotheses, exactly as the manuscript states them.
-/

namespace PVNP.PartIIManuscript

/-! ### Theorem `thm:wave-symbol-isomorphism` -/

section WaveSymbol

variable {Z S Λ N : Type*}

/-- **Theorem `thm:wave-symbol-isomorphism`, forward direction.**  If the field obeys the local
update `Ψ_{t+1}(i) = F(Ψ_t|_{N(i)})` and quantization compatibility
`Q(F(z)) = Q(F(Q̃(Q(z))))` holds on every reached neighbourhood, then `C_t = Q ∘ Ψ_t` obeys the
symbolic rule `U(c) = Q(F(Q̃ ∘ c))`. -/
theorem wave_symbol_forward (F : (N → Z) → Z) (Q : Z → S) (Qt : S → Z) (nb : Λ → N → Λ)
    (Ψ : ℕ → Λ → Z) (hΨ : ∀ t i, Ψ (t + 1) i = F fun v => Ψ t (nb i v))
    (hcompat : ∀ t i, Q (F fun v => Ψ t (nb i v)) = Q (F fun v => Qt (Q (Ψ t (nb i v))))) :
    ∀ t i, Q (Ψ (t + 1) i) = Q (F fun v => Qt (Q (Ψ t (nb i v)))) := by
  intro t i
  rw [hΨ t i, hcompat t i]

/-- **Theorem `thm:wave-symbol-isomorphism`, converse.**  For every symbolic local rule `U`, the
representative evolution `F_U(z) = Q̃(U(Q ∘ z))` started at `Q̃ ∘ C₀` realizes the symbolic
trajectory exactly on the code manifold: `Ψ_t = Q̃ ∘ C_t`. -/
theorem wave_symbol_converse (U : (N → S) → S) (Q : Z → S) (Qt : S → Z)
    (hQ : ∀ s, Q (Qt s) = s) (nb : Λ → N → Λ) (C : ℕ → Λ → S)
    (hC : ∀ t i, C (t + 1) i = U fun v => C t (nb i v)) (Ψ : ℕ → Λ → Z)
    (h0 : ∀ i, Ψ 0 i = Qt (C 0 i))
    (hΨ : ∀ t i, Ψ (t + 1) i = Qt (U fun v => Q (Ψ t (nb i v)))) :
    ∀ t i, Ψ t i = Qt (C t i) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro i
    rw [hΨ t i, hC t i]
    congr 2
    funext v
    rw [ih, hQ]

/-- **Remark `rem:wave-symbol-obstruction`.**  `Z = {−1, ½, 1}` (inside `ℚ`), `S = Bool`,
`Q(z) = [z > 0]`, `Q̃(false) = −1`, `Q̃(true) = 1`, one-cell map `F(−1) = −1`, `F(½) = ½`,
`F(1) = −1`.  For `Ψ₀ = ½`, `Q(F(Ψ₀)) = 1` but `U(Q(Ψ₀)) = Q(F(1)) = 0`. -/
theorem compatibility_necessary :
    let Q : ℚ → Bool := fun z => decide (0 < z)
    let Qt : Bool → ℚ := fun b => if b then 1 else -1
    let F : ℚ → ℚ := fun z => if z = 1 / 2 then 1 / 2 else -1
    (∀ b, Q (Qt b) = b) ∧ F (-1) = -1 ∧ F (1 / 2) = 1 / 2 ∧ F 1 = -1 ∧
      Q (F (1 / 2)) = true ∧ Q (F (Qt (Q (1 / 2)))) = false := by
  refine ⟨fun b => by cases b <;> norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end WaveSymbol

/-! ### Lemma `lem:bandlimit` -/

/-- **Lemma `lem:bandlimit`, effective wavenumber.**  From the rest-energy identity
`E_rest = ħc⟨σ⟩_w`, the coupling `k_eff ≤ C₁⟨σ⟩_w` and `E_rest ≤ E_max`:
`k_eff ≤ C₁ E_max/(ħc)`. -/
theorem bandlimit_eff {ħc C₁ Erest Emax σ keff : ℝ} (hħc : 0 < ħc) (hC₁ : 0 ≤ C₁)
    (hid : Erest = ħc * σ) (hcoup : keff ≤ C₁ * σ) (hE : Erest ≤ Emax) :
    keff ≤ C₁ * (Emax / ħc) := by
  have hσ : σ ≤ Emax / ħc := by rw [le_div_iff₀ hħc]; linarith
  exact hcoup.trans (mul_le_mul_of_nonneg_left hσ hC₁)

/-- **Lemma `lem:bandlimit`, conditional sharp cutoff** (requires the additional coupling
`k_max ≤ C₁⟨σ⟩_w`). -/
theorem bandlimit_sharp {ħc C₁ Erest Emax σ kmax : ℝ} (hħc : 0 < ħc) (hC₁ : 0 ≤ C₁)
    (hid : Erest = ħc * σ) (hcoup : kmax ≤ C₁ * σ) (hE : Erest ≤ Emax) :
    kmax ≤ C₁ * (Emax / ħc) := bandlimit_eff hħc hC₁ hid hcoup hE

/-! ### Lemma `lem:spatial_capacity` -/

/-- Fourier modes of the periodic cube of side `ℓ` with `‖k‖ ≤ kmax`: integer vectors `m` with
`(2π/ℓ)² Σ mᵢ² ≤ kmax²`. -/
def modes (ℓ kmax : ℝ) : Set (Fin 3 → ℤ) :=
  {m | (2 * Real.pi / ℓ) ^ 2 * ∑ i, ((m i : ℤ) : ℝ) ^ 2 ≤ kmax ^ 2}

/-- **Lemma `lem:spatial_capacity`.**  For the periodic cube of side `ℓ > 0` (volume `V = ℓ³`)
and `kmax` at least the fundamental wavenumber `2π/ℓ`, the number of modes with `‖k‖ ≤ kmax`
is at most `C₂ V kmax³` with `C₂ = 27/(8π³)`. -/
theorem spatial_capacity (ℓ kmax : ℝ) (hℓ : 0 < ℓ) (hk : 2 * Real.pi / ℓ ≤ kmax) :
    (modes ℓ kmax).Finite ∧
      ((modes ℓ kmax).ncard : ℝ) ≤ 27 / (8 * Real.pi ^ 3) * ℓ ^ 3 * kmax ^ 3 := by
  set R : ℝ := kmax * ℓ / (2 * Real.pi) with hR
  have hπ : 0 < Real.pi := Real.pi_pos
  have hR1 : 1 ≤ R := by
    rw [hR, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hℓ] at hk
    linarith
  set B : ℕ := ⌊R⌋₊ with hB
  have hBR : (B : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hsub : modes ℓ kmax ⊆ ↑(Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(B : ℤ)) B) := by
    intro m hm
    simp only [modes, Set.mem_setOf_eq] at hm
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hsq : ((m i : ℤ) : ℝ) ^ 2 ≤ R ^ 2 := by
      have h1 : ((m i : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((m j : ℤ) : ℝ) ^ 2 :=
        Finset.single_le_sum (f := fun j => ((m j : ℤ) : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)
      have h2 : (2 * Real.pi / ℓ) ^ 2 * ((m i : ℤ) : ℝ) ^ 2 ≤ kmax ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) hm
      have hR2 : R ^ 2 = kmax ^ 2 / (2 * Real.pi / ℓ) ^ 2 := by rw [hR]; field_simp
      rw [hR2, le_div_iff₀ (by positivity)]
      linarith
    have habs : |((m i : ℤ) : ℝ)| ≤ R := by
      nlinarith [abs_nonneg ((m i : ℤ) : ℝ), sq_abs ((m i : ℤ) : ℝ)]
    have hfl : |m i| ≤ (B : ℤ) := by
      have h1 : (|m i| : ℤ) ≤ ⌊R⌋ := Int.le_floor.2 (by push_cast; exact habs)
      have hfloor : (⌊R⌋ : ℤ) = (B : ℤ) := by
        rw [hB, Int.natCast_floor_eq_floor (by linarith)]
      linarith
    exact abs_le.1 hfl
  have hfin : (modes ℓ kmax).Finite := Set.Finite.subset (Finset.finite_toSet _) hsub
  refine ⟨hfin, ?_⟩
  have hcard : (modes ℓ kmax).ncard ≤ (2 * B + 1) ^ 3 := by
    calc (modes ℓ kmax).ncard ≤ (↑(Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(B : ℤ)) B) :
          Set (Fin 3 → ℤ)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (2 * B + 1) ^ 3 := by
        rw [Set.ncard_coe_finset, Fintype.card_piFinset]
        simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        congr 1
        omega
  calc ((modes ℓ kmax).ncard : ℝ) ≤ ((2 * B + 1) ^ 3 : ℕ) := by exact_mod_cast hcard
    _ = (2 * (B : ℝ) + 1) ^ 3 := by push_cast; ring
    _ ≤ (3 * R) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
    _ = 27 / (8 * Real.pi ^ 3) * ℓ ^ 3 * kmax ^ 3 := by rw [hR]; field_simp; ring

/-- **Lemma `lem:spatial_capacity`, energy form** (equation `spatial_capacity_energy`): with the
conditional sharp cutoff `kmax ≤ C₁E_max/(ħc)` of `lem:bandlimit`,
`N_lanes ≤ C₂ V (C₁E_max/(ħc))³`. -/
theorem spatial_capacity_energy (ℓ kmax C₁ Emax ħc : ℝ) (hℓ : 0 < ℓ)
    (hk : 2 * Real.pi / ℓ ≤ kmax) (hkE : kmax ≤ C₁ * (Emax / ħc)) :
    ((modes ℓ kmax).ncard : ℝ) ≤ 27 / (8 * Real.pi ^ 3) * ℓ ^ 3 * (C₁ * (Emax / ħc)) ^ 3 := by
  have h := (spatial_capacity ℓ kmax hℓ hk).2
  have hk0 : 0 ≤ kmax := le_trans (by positivity) hk
  have h3 : kmax ^ 3 ≤ (C₁ * (Emax / ħc)) ^ 3 := pow_le_pow_left₀ hk0 hkE 3
  calc ((modes ℓ kmax).ncard : ℝ) ≤ 27 / (8 * Real.pi ^ 3) * ℓ ^ 3 * kmax ^ 3 := h
    _ ≤ 27 / (8 * Real.pi ^ 3) * ℓ ^ 3 * (C₁ * (Emax / ħc)) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ### Lemma `lem:lane_update_bound` and Theorem `thm:spacetime_capacity` -/

/-- **Lemma `lem:lane_update_bound`.**  With dwell time `Δt_min ≥ C₃/ω_max` and dispersion
`ω_max ≤ c kmax`, a lane switches at most `T/Δt_min ≤ T c kmax / C₃` times in a window `T`. -/
theorem lane_update_bound {T Δtmin ωmax c kmax C₃ : ℝ} (hT : 0 ≤ T) (hC₃ : 0 < C₃)
    (hω : 0 < ωmax) (hdwell : C₃ / ωmax ≤ Δtmin) (hdisp : ωmax ≤ c * kmax) :
    T / Δtmin ≤ T * c * kmax / C₃ := by
  have hΔ : 0 < Δtmin := lt_of_lt_of_le (by positivity) hdwell
  rw [div_le_div_iff₀ hΔ hC₃]
  have h1 : C₃ ≤ Δtmin * ωmax := by rwa [div_le_iff₀ hω] at hdwell
  have h2 : C₃ ≤ Δtmin * (c * kmax) := h1.trans (mul_le_mul_of_nonneg_left hdisp hΔ.le)
  nlinarith

/-- **Theorem `thm:spacetime_capacity`** (and `thm:channel_capacity`).  If the lanes number at
most `C₂ V kmax³` and each lane switches at most `T c kmax/C₃` times, the total number of lane
updates is at most `C₄ V T kmax⁴` with `C₄ = C₂ c/C₃`; with `kmax ≤ C₁E_max/(ħc)` it is at most
`K V T E_max⁴` with `K = C₄C₁⁴/(ħc)⁴`. -/
theorem spacetime_capacity {Nlanes Nsteps Nupd V T kmax c C₁ C₂ C₃ ħc Emax : ℝ}
    (hV : 0 ≤ V) (hT : 0 ≤ T) (hk : 0 ≤ kmax) (hc : 0 ≤ c) (hC₂ : 0 ≤ C₂) (hC₃ : 0 < C₃)
    (hħc : 0 < ħc) (hsteps0 : 0 ≤ Nsteps)
    (hlanes : Nlanes ≤ C₂ * V * kmax ^ 3) (hsteps : Nsteps ≤ T * c * kmax / C₃)
    (hupd : Nupd ≤ Nlanes * Nsteps) (hkE : kmax ≤ C₁ * (Emax / ħc)) :
    Nupd ≤ (C₂ * c / C₃) * V * T * kmax ^ 4 ∧
      Nupd ≤ ((C₂ * c / C₃) * C₁ ^ 4 / ħc ^ 4) * V * T * Emax ^ 4 := by
  have h1 : Nupd ≤ (C₂ * c / C₃) * V * T * kmax ^ 4 := by
    calc Nupd ≤ Nlanes * Nsteps := hupd
      _ ≤ (C₂ * V * kmax ^ 3) * (T * c * kmax / C₃) :=
          mul_le_mul hlanes hsteps hsteps0 (by positivity)
      _ = (C₂ * c / C₃) * V * T * kmax ^ 4 := by field_simp
  refine ⟨h1, h1.trans ?_⟩
  have hk4 : kmax ^ 4 ≤ (C₁ * (Emax / ħc)) ^ 4 := pow_le_pow_left₀ hk hkE 4
  calc (C₂ * c / C₃) * V * T * kmax ^ 4 ≤ (C₂ * c / C₃) * V * T * (C₁ * (Emax / ħc)) ^ 4 :=
        mul_le_mul_of_nonneg_left hk4 (by positivity)
    _ = ((C₂ * c / C₃) * C₁ ^ 4 / ħc ^ 4) * V * T * Emax ^ 4 := by field_simp

/-! ### Proposition `prop:phys_step_ceiling` -/

/-- **Proposition `prop:phys_step_ceiling`.**  For a polynomial-resource device family
(`V ≤ C_V nᵃ`, `T ≤ C_T nᵇ`, `E_max ≤ C_E nᶜ`), the channel-capacity bound gives
`N_updates(n) ≤ C' n^{a+b+4c}` with `C' = K C_V C_T C_E⁴`. -/
theorem phys_step_ceiling {K CV CT CE : ℝ} {a b c : ℕ} (hK : 0 ≤ K) (hCV : 0 ≤ CV) (hCT : 0 ≤ CT)
    (V T E Nupd : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n) (hT0 : ∀ n, 0 ≤ T n) (hE0 : ∀ n, 0 ≤ E n)
    (hV : ∀ n, V n ≤ CV * (n : ℝ) ^ a) (hT : ∀ n, T n ≤ CT * (n : ℝ) ^ b)
    (hE : ∀ n, E n ≤ CE * (n : ℝ) ^ c) (hcap : ∀ n, Nupd n ≤ K * V n * T n * E n ^ 4) :
    ∀ n, Nupd n ≤ (K * CV * CT * CE ^ 4) * (n : ℝ) ^ (a + b + 4 * c) := by
  intro n
  have hE4 : E n ^ 4 ≤ (CE * (n : ℝ) ^ c) ^ 4 := pow_le_pow_left₀ (hE0 n) (hE n) 4
  calc Nupd n ≤ K * V n * T n * E n ^ 4 := hcap n
    _ ≤ K * (CV * (n : ℝ) ^ a) * (CT * (n : ℝ) ^ b) * (CE * (n : ℝ) ^ c) ^ 4 := by
        apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hV n) hK) (hT n) (hT0 n)
          (by have := hV0 n; positivity)) hE4 (by positivity) (by positivity)
    _ = (K * CV * CT * CE ^ 4) * (n : ℝ) ^ (a + b + 4 * c) := by ring

/-- **Proposition `prop:phys_step_ceiling`, runtime part.**  If every non-halting round incurs at
least one counted event, the number of rounds `T_W` satisfies `T_W ≤ N_updates + 1`. -/
theorem rounds_le_events (TW Nupd : ℕ) (events : ℕ → ℕ) (hpos : ∀ t, t + 1 < TW → 1 ≤ events t)
    (htot : ∑ t ∈ Finset.range (TW - 1), events t ≤ Nupd) : TW ≤ Nupd + 1 := by
  have h : TW - 1 ≤ ∑ t ∈ Finset.range (TW - 1), events t := by
    calc TW - 1 = ∑ _t ∈ Finset.range (TW - 1), 1 := by simp
      _ ≤ ∑ t ∈ Finset.range (TW - 1), events t :=
          Finset.sum_le_sum fun t ht => hpos t (by simp at ht; omega)
  omega

end PVNP.PartIIManuscript
