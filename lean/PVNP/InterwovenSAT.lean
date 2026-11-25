import PVNP.PhasePenaltyGap

/-!
# Interwoven-Ψ SAT: logical, coupling and curvature energies together

A 3-CNF formula `F` over variables `0, 1, 2, …` is encoded by a wavefield family
`Ψ = (ψ₀, ψ₁, …)`, one complex amplitude `ψᵢ = Aᵢ e^{iθᵢ}` per Boolean variable.

* **Binary phase encoding.** `xᵢ = 1 ↔ θᵢ = 0` and `xᵢ = 0 ↔ θᵢ = π`; the field of an assignment
  is `fieldOf a` (values `±1`).
* **Variable-to-field correspondence and shared-variable consistency.** A variable that occurs in
  several clauses is the *same* field `ψᵢ` in all of them, so consistency holds by construction.
* **Clause-to-coupling correspondence.** Clause `c` couples the phases of its three variables
  through the penalty `Πₖ (1 − s(ℓₖ; θ))` of `PartIPsiSat` (`E_logic`).
* **Interaction hypergraph and graph.** Hyperedges are the variable triples of the clauses
  (`hyperedges`); the interaction multigraph has one edge per pair of literal slots of a clause
  (`edges`), on the vertex set `vars`.
* **Coupling energy** `E_coupling = Σ_{edges} (1 − Re ψₐ ψ̄_b)` (an XY coupling; `1 − cos(θₐ − θ_b)`
  for unit fields).
* **Curvature energy** `E_curv = Σ_{edges} |ψₐ − ψ_b|² + Σ_v |(Δψ)_v|²`: the gradient and Laplacian
  terms of the manuscript's `Φ = Σ(|∇ψ|² + |Θψ|²)`, on the interaction graph.
* **Admissible fields** `𝒜`: unit amplitude at every variable (`Admissible`).

`E_F[Ψ] = E_logic + λ E_coupling + μ E_curv` (`energy`).

## Results

**The naive interwoven energy fails.** For the satisfiable formula
`F_xor = (x₀ ∨ x₁ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁ ∨ ¬x₁)`, whose solutions need *opposite* phases on the two
coupled variables:

* `xor_energy_pos`: whenever `4μ + 2λ > 0`, every admissible field has `E > 0`. So
  `SAT ⟺ ∃Ψ ∈ 𝒜, E = 0` fails (phase frustration).
* `xor_energy_ge_quarter`: whenever `4μ + 2λ ≥ 1/12`, every admissible field has `E ≥ 1/4`, and
  `1/4` is attained (`xor_energy_at_I`).
* `single_var_energy`: the *unsatisfiable* formula `G = (x₀ ∨ x₀ ∨ x₀) ∧ (¬x₀ ∨ ¬x₀ ∨ ¬x₀)` also has
  ground energy exactly `1/4`.
* `naive_ground_energy_blind`: hence the ground-state energy of the naive model is the same for a
  satisfiable and an unsatisfiable formula; no threshold on it decides SAT. In particular the
  certificate "energy < 1/8 ⟹ SAT" of `PhasePenaltyGap` does not survive the added terms.
* `min_formulation_vacuous`: "`∃Ψ ∈ 𝒜, E_F[Ψ] = min E_F`" holds for the unsatisfiable `G`, so a
  ground-state criterion needs an `F`-independent reference energy.

* `satisfying_not_ground`: once `4μ + 2λ > 1/16`, every satisfying assignment of `F_xor` has
  more energy than the non-binary field `ψ ≡ i`: a satisfying assignment is not a ground state.
* `naive_Emin`: `E_min(F_xor) = E_min(G) = 1/4`, so `SAT ⟺ E_min = 0` fails.

**Repair: sign-blind coupling and curvature.** Apply the coupling and curvature terms to the
doubled field `Ψ²` (`energySB`); binary phases `0, π` then cost nothing. For every `F` and every
`λ, μ ≥ 0`:

* `sat_iff_zero_energySB`: `SAT(F) ⟺ ∃Ψ ∈ 𝒜, E^{sb}_F[Ψ] = 0`;
* `sat_iff_EminSB_eq_zero`: `SAT(F) ⟺ E_min(F) = 0`, with `E_min(F) = inf_{Ψ ∈ 𝒜} E^{sb}_F[Ψ]`;
* `unsat_iff_EminSB_ge`, `unsat_energySB_gap`: `F` is unsatisfiable iff `E_min(F) ≥ 1/8`;
* `sat_iff_energySB_lt_eighth`: `SAT(F) ⟺ ∃Ψ ∈ 𝒜, E^{sb}_F[Ψ] < 1/8`;
* `measure_satisfies`: reading the signs `[Re ψᵢ ≥ 0]` of any admissible field with
  `E^{sb}_F < 1/8` gives a satisfying assignment.

**When does the correspondence survive added terms?** (`locks_iff_sat_iff`.) For any extra
energy `C ≥ 0` on admissible fields, "zero total energy is attainable ⟺ SAT" holds for every
formula iff every satisfiable formula has a satisfying admissible field at which `C` vanishes;
the UNSAT gap `≥ 1/8` survives every `C ≥ 0` (`unsat_gap_general`). The sign-blind terms meet the
criterion; the naive terms violate it at `F_xor`.

**Manuscript claim I-37** ("nonexistence of a toroidal locking configuration ⟺ unsatisfiability")
with the locking constraints defined: a locking configuration is a point of the phase torus
`|ψᵢ| = 1` at which clause penalties and flux terms vanish (`Locks`). With sign-blind flux terms
the claim holds for every formula (`toroidal_locking_iff_unsat`); with naive sign-sensitive
terms it fails for `F_xor` (`naive_toroidal_locking_fails`).

These are statements about an energy landscape. They say nothing about how long any dynamics or
algorithm takes to find a low-energy field, and they prove no complexity separation.
-/

namespace PVNP.InterwovenSAT

open PVNP.PartIPsiSat Complex

/-! ## The model -/

/-- The interaction multigraph: one edge per pair of literal slots of each clause. -/
def edges (F : CNF3) : List (ℕ × ℕ) :=
  F.flatMap fun c => [((c 0).v, (c 1).v), ((c 0).v, (c 2).v), ((c 1).v, (c 2).v)]

/-- The interaction hypergraph: the variable triple of each clause. -/
def hyperedges (F : CNF3) : List (List ℕ) :=
  F.map fun c => [(c 0).v, (c 1).v, (c 2).v]

/-- The variables of `F`. -/
def vars (F : CNF3) : List ℕ := (hyperedges F).flatten.dedup

/-- Admissible fields: unit amplitude at every variable. -/
def Admissible (Ψ : ℕ → ℂ) : Prop := ∀ i, ‖Ψ i‖ = 1

/-- The logical penalty `E_logic`, through the phases `θᵢ = arg ψᵢ`. -/
noncomputable def Elog (F : CNF3) (Ψ : ℕ → ℂ) : ℝ := Elogic (phases Ψ) F

/-- The XY coupling energy on the interaction graph. -/
noncomputable def Ecoup (F : CNF3) (Ψ : ℕ → ℂ) : ℝ :=
  ((edges F).map fun e => 1 - (Ψ e.1 * (starRingEnd ℂ) (Ψ e.2)).re).sum

/-- The graph Laplacian of `Ψ` at a vertex. -/
noncomputable def glap (F : CNF3) (Ψ : ℕ → ℂ) (v : ℕ) : ℂ :=
  ((edges F).map fun e =>
    (if e.1 = v then Ψ e.2 - Ψ v else 0) + (if e.2 = v then Ψ e.1 - Ψ v else 0)).sum

/-- The geometric curvature energy: gradient plus Laplacian terms on the interaction graph. -/
noncomputable def Ecurv (F : CNF3) (Ψ : ℕ → ℂ) : ℝ :=
  ((edges F).map fun e => Complex.normSq (Ψ e.1 - Ψ e.2)).sum +
    ((vars F).map fun v => Complex.normSq (glap F Ψ v)).sum

/-- The total interwoven energy `E_F[Ψ] = E_logic + λ E_coupling + μ E_curv`. -/
noncomputable def energy (F : CNF3) (lam mu : ℝ) (Ψ : ℕ → ℂ) : ℝ :=
  Elog F Ψ + lam * Ecoup F Ψ + mu * Ecurv F Ψ

/-- The doubled field `Ψ²`, blind to binary phase flips. -/
def sq (Ψ : ℕ → ℂ) : ℕ → ℂ := fun i => Ψ i ^ 2

/-- The repaired energy: coupling and curvature of the doubled field. -/
noncomputable def energySB (F : CNF3) (lam mu : ℝ) (Ψ : ℕ → ℂ) : ℝ :=
  Elog F Ψ + lam * Ecoup F (sq Ψ) + mu * Ecurv F (sq Ψ)

/-! ## Elementary facts -/

theorem Elog_nonneg (F : CNF3) (Ψ : ℕ → ℂ) : 0 ≤ Elog F Ψ := Elogic_nonneg _ _

theorem list_sum_nonneg {l : List ℝ} (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum :=
  List.sum_nonneg h

theorem Ecurv_nonneg (F : CNF3) (Ψ : ℕ → ℂ) : 0 ≤ Ecurv F Ψ := by
  unfold Ecurv
  refine add_nonneg (list_sum_nonneg ?_) (list_sum_nonneg ?_) <;>
  · intro x hx
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
    exact Complex.normSq_nonneg _

theorem coup_term_nonneg {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    0 ≤ 1 - (a * (starRingEnd ℂ) b).re := by
  have h : (a * (starRingEnd ℂ) b).re ≤ ‖a * (starRingEnd ℂ) b‖ := Complex.re_le_norm _
  rw [norm_mul, Complex.norm_conj, ha, hb, one_mul] at h
  linarith

theorem Ecoup_nonneg (F : CNF3) {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) : 0 ≤ Ecoup F Ψ := by
  unfold Ecoup
  refine list_sum_nonneg fun x hx => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact coup_term_nonneg (hΨ _) (hΨ _)

theorem sq_admissible {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) : Admissible (sq Ψ) := by
  intro i
  simp [sq, norm_pow, hΨ i]

theorem energy_ge_Elog (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) : Elog F Ψ ≤ energy F lam mu Ψ := by
  unfold energy
  have h1 := mul_nonneg hlam (Ecoup_nonneg F hΨ)
  have h2 := mul_nonneg hmu (Ecurv_nonneg F Ψ)
  linarith

theorem energySB_ge_Elog (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) : Elog F Ψ ≤ energySB F lam mu Ψ := by
  unfold energySB
  have h1 := mul_nonneg hlam (Ecoup_nonneg F (sq_admissible hΨ))
  have h2 := mul_nonneg hmu (Ecurv_nonneg F (sq Ψ))
  linarith

/-- On a spatially constant family, coupling of unit fields and curvature vanish. -/
theorem Ecurv_const (F : CNF3) (z : ℂ) : Ecurv F (fun _ => z) = 0 := by
  unfold Ecurv glap
  simp

theorem Ecoup_const (F : CNF3) {z : ℂ} (hz : ‖z‖ = 1) : Ecoup F (fun _ => z) = 0 := by
  unfold Ecoup
  have h : (z * (starRingEnd ℂ) z).re = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    simp
  simp [h]

/-! ## The repaired (sign-blind) model -/

theorem fieldOf_admissible (a : ℕ → Bool) : Admissible (fieldOf a) := by
  intro i
  unfold fieldOf
  split_ifs <;> simp

theorem sq_fieldOf (a : ℕ → Bool) : sq (fieldOf a) = fun _ => 1 := by
  funext i
  unfold sq fieldOf
  split_ifs <;> norm_num

theorem energySB_fieldOf (F : CNF3) (lam mu : ℝ) (a : ℕ → Bool) :
    energySB F lam mu (fieldOf a) = Elogic (phaseOf a) F := by
  unfold energySB Elog
  rw [sq_fieldOf, Ecurv_const, Ecoup_const F (by simp), phases_fieldOf]
  ring

/-- **SAT ⟺ a zero-energy admissible field**, for the sign-blind interwoven energy and every
`λ, μ ≥ 0`. -/
theorem sat_iff_zero_energySB (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    Sat F ↔ ∃ Ψ, Admissible Ψ ∧ energySB F lam mu Ψ = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fieldOf a, fieldOf_admissible a, ?_⟩
    rw [energySB_fieldOf]
    exact (Elogic_phaseOf_eq_zero_iff a F).2 ha
  · rintro ⟨Ψ, hΨ, h0⟩
    have hle := energySB_ge_Elog F hlam hmu hΨ
    have hnn := Elog_nonneg F Ψ
    have hz : Elogic (phases Ψ) F = 0 := by
      show Elog F Ψ = 0
      linarith
    exact (psi_sat_completeness F).2.2 ⟨_, hz⟩

/-- **Gap:** an unsatisfiable formula has sign-blind energy at least `1/8` on every admissible
field, for every `λ, μ ≥ 0`. -/
theorem unsat_energySB_gap (F : CNF3) (hF : ¬ Sat F) {lam mu : ℝ} (hlam : 0 ≤ lam)
    (hmu : 0 ≤ mu) {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) : (1 : ℝ) / 8 ≤ energySB F lam mu Ψ :=
  (unsat_logical_energy_gap F hF _).trans (energySB_ge_Elog F hlam hmu hΨ)

/-- **Threshold readout survives the repair:** SAT ⟺ some admissible field has sign-blind energy
below `1/8`. -/
theorem sat_iff_energySB_lt_eighth (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    Sat F ↔ ∃ Ψ, Admissible Ψ ∧ energySB F lam mu Ψ < 1 / 8 := by
  constructor
  · intro h
    obtain ⟨Ψ, hΨ, h0⟩ := (sat_iff_zero_energySB F hlam hmu).1 h
    exact ⟨Ψ, hΨ, by rw [h0]; norm_num⟩
  · rintro ⟨Ψ, hΨ, hlt⟩
    by_contra hF
    exact absurd (unsat_energySB_gap F hF hlam hmu hΨ) (not_le.2 hlt)

/-! ## The naive model fails: phase frustration -/

/-- `(x₀ ∨ x₁ ∨ x₁)`. -/
def cPos : Clause3 := fun k => if k = 0 then ⟨0, true⟩ else ⟨1, true⟩

/-- `(¬x₀ ∨ ¬x₁ ∨ ¬x₁)`. -/
def cNeg : Clause3 := fun k => if k = 0 then ⟨0, false⟩ else ⟨1, false⟩

/-- `F_xor`: satisfiable exactly by `x₀ ≠ x₁`. -/
def Fxor : CNF3 := [cPos, cNeg]

/-- `(x₀ ∨ x₀ ∨ x₀)`. -/
def gPos : Clause3 := fun _ => ⟨0, true⟩

/-- `(¬x₀ ∨ ¬x₀ ∨ ¬x₀)`. -/
def gNeg : Clause3 := fun _ => ⟨0, false⟩

/-- `G`: unsatisfiable. -/
def G : CNF3 := [gPos, gNeg]

theorem Fxor_sat : Sat Fxor := by
  refine ⟨fun i => decide (i = 0), fun c hc => ?_⟩
  simp only [Fxor, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

theorem G_unsat : ¬ Sat G := by
  rintro ⟨a, ha⟩
  have h1 := ha gPos (by simp [G])
  have h2 := ha gNeg (by simp [G])
  simp only [clauseVal, litVal, gPos, gNeg] at h1 h2
  cases a 0 <;> simp_all

/-- For a unit field, `cos (arg ψ) = Re ψ`. -/
theorem cos_phase {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) (i : ℕ) :
    Real.cos (phases Ψ i) = (Ψ i).re := by
  have hne : Ψ i ≠ 0 := by
    intro h
    have := hΨ i
    rw [h, norm_zero] at this
    exact zero_ne_one this
  simp only [phases]
  rw [Complex.cos_arg hne, hΨ i, div_one]

theorem re_bounds {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) (i : ℕ) :
    -1 ≤ (Ψ i).re ∧ (Ψ i).re ≤ 1 := by
  have h := Complex.abs_re_le_norm (Ψ i)
  rw [hΨ i] at h
  exact abs_le.1 h

/-- The logical energy of `F_xor` in terms of the real parts `p = Re ψ₀`, `q = Re ψ₁`. -/
theorem Elog_Fxor {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) :
    Elog Fxor Ψ = (1 + (Ψ 1).re ^ 2 + 2 * (Ψ 0).re * (Ψ 1).re) / 4 := by
  simp only [Elog, Elogic, Fxor, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    clausePen, Fin.prod_univ_three, score, PartIPsiSat.eta, cPos, cNeg]
  simp only [Fin.isValue, if_true, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    if_false, Bool.false_eq_true]
  rw [cos_phase hΨ 0, cos_phase hΨ 1]
  ring

/-- The logical energy of `G` in terms of `p = Re ψ₀`. -/
theorem Elog_G {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) :
    Elog G Ψ = (1 + 3 * (Ψ 0).re ^ 2) / 4 := by
  simp only [Elog, Elogic, G, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    clausePen, Fin.prod_univ_three, score, PartIPsiSat.eta, gPos, gNeg]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [cos_phase hΨ 0]
  ring

theorem edges_Fxor : edges Fxor = [(0, 1), (0, 1), (1, 1), (0, 1), (0, 1), (1, 1)] := by
  simp [edges, Fxor, cPos, cNeg]

theorem edges_G : edges G = [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)] := by
  simp [edges, G, gPos, gNeg]

/-- The gradient part of the curvature of `F_xor` is `4|ψ₀ − ψ₁|²`. -/
theorem Ecurv_Fxor_ge (Ψ : ℕ → ℂ) : 4 * Complex.normSq (Ψ 0 - Ψ 1) ≤ Ecurv Fxor Ψ := by
  unfold Ecurv
  have h2 : 0 ≤ ((vars Fxor).map fun v => Complex.normSq (glap Fxor Ψ v)).sum :=
    list_sum_nonneg fun x hx => by
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
      exact Complex.normSq_nonneg _
  rw [edges_Fxor]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sub_self,
    Complex.normSq_zero]
  linarith

/-- The coupling energy of `F_xor` for unit fields is `2|ψ₀ − ψ₁|²`. -/
theorem Ecoup_Fxor {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) :
    Ecoup Fxor Ψ = 2 * Complex.normSq (Ψ 0 - Ψ 1) := by
  have hself : (Ψ 1 * (starRingEnd ℂ) (Ψ 1)).re = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hΨ 1]
    simp
  have hsub : Complex.normSq (Ψ 0 - Ψ 1) = 2 - 2 * (Ψ 0 * (starRingEnd ℂ) (Ψ 1)).re := by
    rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hΨ 0, hΨ 1]
    ring
  unfold Ecoup
  rw [edges_Fxor]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hself]
  rw [hsub]
  ring

theorem normSq_sub_ge_re (a b : ℂ) : (a.re - b.re) ^ 2 ≤ Complex.normSq (a - b) := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.im - b.im)]

/-- The naive energy of `F_xor` is at least the logical part plus `(4μ + 2λ)(p − q)²`. -/
theorem energy_Fxor_ge {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) {Ψ : ℕ → ℂ}
    (hΨ : Admissible Ψ) :
    (1 + (Ψ 1).re ^ 2 + 2 * (Ψ 0).re * (Ψ 1).re) / 4 +
        (4 * mu + 2 * lam) * ((Ψ 0).re - (Ψ 1).re) ^ 2 ≤ energy Fxor lam mu Ψ := by
  unfold energy
  rw [Elog_Fxor hΨ, Ecoup_Fxor hΨ]
  have hc := Ecurv_Fxor_ge Ψ
  have hr := normSq_sub_ge_re (Ψ 0) (Ψ 1)
  have h1 : mu * (4 * ((Ψ 0).re - (Ψ 1).re) ^ 2) ≤ mu * Ecurv Fxor Ψ :=
    mul_le_mul_of_nonneg_left (by linarith) hmu
  have h2 : lam * (2 * ((Ψ 0).re - (Ψ 1).re) ^ 2) ≤ lam * (2 * Complex.normSq (Ψ 0 - Ψ 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam
  nlinarith [h1, h2]

/-- **Phase frustration.** Whenever the naive coupling or curvature is switched on
(`4μ + 2λ > 0`), the satisfiable formula `F_xor` has no zero-energy admissible field. -/
theorem xor_energy_pos {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hpos : 0 < 4 * mu + 2 * lam)
    {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) : 0 < energy Fxor lam mu Ψ := by
  have hge := energy_Fxor_ge hlam hmu hΨ
  obtain ⟨hp1, hp2⟩ := re_bounds hΨ 0
  obtain ⟨hq1, hq2⟩ := re_bounds hΨ 1
  set p := (Ψ 0).re
  set q := (Ψ 1).re
  -- the logical part is `((p + q)² + (1 − p²))/4 ≥ 0`
  have hp : 0 ≤ 1 - p ^ 2 := by nlinarith
  have hV : 0 ≤ (1 + q ^ 2 + 2 * p * q) / 4 := by nlinarith [sq_nonneg (p + q)]
  by_contra hle
  push_neg at hle
  have hsq : 0 ≤ (4 * mu + 2 * lam) * (p - q) ^ 2 := by positivity
  have hV0 : (1 + q ^ 2 + 2 * p * q) / 4 = 0 := by linarith
  have hd0 : (4 * mu + 2 * lam) * (p - q) ^ 2 = 0 := by linarith
  have hpq : p = q := by
    rcases mul_eq_zero.1 hd0 with h | h
    · linarith
    · nlinarith [sq_nonneg (p - q)]
  rw [hpq] at hV0
  nlinarith [sq_nonneg q]

/-- **The naive ground energy of the satisfiable `F_xor` is at least `1/4`** once
`4μ + 2λ ≥ 1/12`. -/
theorem xor_energy_ge_quarter {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hbig : 1 / 12 ≤ 4 * mu + 2 * lam) {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) :
    (1 : ℝ) / 4 ≤ energy Fxor lam mu Ψ := by
  have hge := energy_Fxor_ge hlam hmu hΨ
  set p := (Ψ 0).re
  set q := (Ψ 1).re
  have hq : (1 / 12) * (p - q) ^ 2 ≤ (4 * mu + 2 * lam) * (p - q) ^ 2 :=
    mul_le_mul_of_nonneg_right hbig (sq_nonneg _)
  nlinarith [sq_nonneg (p + 2 * q)]

/-- The constant field `ψᵢ = i`. -/
def fieldI : ℕ → ℂ := fun _ => Complex.I

theorem fieldI_admissible : Admissible fieldI := fun _ => by simp [fieldI]

theorem xor_energy_at_I (lam mu : ℝ) : energy Fxor lam mu fieldI = 1 / 4 := by
  unfold energy
  rw [Elog_Fxor fieldI_admissible]
  have h1 : Ecoup Fxor fieldI = 0 := Ecoup_const Fxor (z := Complex.I) (by simp)
  have h2 : Ecurv Fxor fieldI = 0 := Ecurv_const _ _
  rw [h1, h2]
  simp only [fieldI, Complex.I_re]
  ring

/-- **The unsatisfiable `G` has ground energy exactly `1/4`** for the naive energy, with any
coefficients: its only variable has no neighbours. -/
theorem single_var_energy (lam mu : ℝ) :
    (∀ Ψ, Admissible Ψ → (1 : ℝ) / 4 ≤ energy G lam mu Ψ) ∧ energy G lam mu fieldI = 1 / 4 := by
  have hcoup : ∀ Ψ, Admissible Ψ → Ecoup G Ψ = 0 := by
    intro Ψ hΨ
    have hself : (Ψ 0 * (starRingEnd ℂ) (Ψ 0)).re = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hΨ 0]
      simp
    unfold Ecoup
    rw [edges_G]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hself]
    norm_num
  have hglap : ∀ Ψ v, glap G Ψ v = 0 := by
    intro Ψ v
    unfold glap
    rw [edges_G]
    by_cases h : 0 = v
    · subst h
      simp
    · simp [h]
  have hcurv : ∀ Ψ, Ecurv G Ψ = 0 := by
    intro Ψ
    unfold Ecurv
    rw [edges_G]
    simp [hglap]
  refine ⟨fun Ψ hΨ => ?_, ?_⟩
  · unfold energy
    rw [Elog_G hΨ, hcoup Ψ hΨ, hcurv Ψ]
    nlinarith [sq_nonneg (Ψ 0).re]
  · unfold energy
    rw [Elog_G fieldI_admissible, hcoup _ fieldI_admissible, hcurv]
    simp [fieldI]

/-- **The naive interwoven energy cannot see satisfiability.** For coefficients with
`4μ + 2λ ≥ 1/12`, the satisfiable `F_xor` and the unsatisfiable `G` have the same ground energy
`1/4`, attained by the same admissible field. -/
theorem naive_ground_energy_blind {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hbig : 1 / 12 ≤ 4 * mu + 2 * lam) :
    Sat Fxor ∧ ¬ Sat G ∧
      (∀ Ψ, Admissible Ψ → (1 : ℝ) / 4 ≤ energy Fxor lam mu Ψ) ∧
      (∀ Ψ, Admissible Ψ → (1 : ℝ) / 4 ≤ energy G lam mu Ψ) ∧
      energy Fxor lam mu fieldI = 1 / 4 ∧ energy G lam mu fieldI = 1 / 4 :=
  ⟨Fxor_sat, G_unsat, fun _ hΨ => xor_energy_ge_quarter hlam hmu hbig hΨ,
    (single_var_energy lam mu).1, xor_energy_at_I lam mu, (single_var_energy lam mu).2⟩

/-- **The naive model breaks the zero-energy correspondence:** `SAT ⟺ ∃Ψ ∈ 𝒜, E = 0` is false
for `F_xor` as soon as `4μ + 2λ > 0`. -/
theorem naive_zero_energy_fails {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hpos : 0 < 4 * mu + 2 * lam) :
    ¬ (Sat Fxor ↔ ∃ Ψ, Admissible Ψ ∧ energy Fxor lam mu Ψ = 0) := by
  intro h
  obtain ⟨Ψ, hΨ, h0⟩ := h.1 Fxor_sat
  exact absurd h0 (ne_of_gt (xor_energy_pos hlam hmu hpos hΨ))

/-- **The naive model breaks the `1/8` certificate:** `SAT ⟺ ∃Ψ ∈ 𝒜, E < 1/8` is false for
`F_xor` once `4μ + 2λ ≥ 1/12`. -/
theorem naive_threshold_fails {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hbig : 1 / 12 ≤ 4 * mu + 2 * lam) :
    ¬ (Sat Fxor ↔ ∃ Ψ, Admissible Ψ ∧ energy Fxor lam mu Ψ < 1 / 8) := by
  intro h
  obtain ⟨Ψ, hΨ, hlt⟩ := h.1 Fxor_sat
  have := xor_energy_ge_quarter hlam hmu hbig hΨ
  linarith

/-- **The minimum formulation is vacuous:** the unsatisfiable `G` attains its minimum energy, so
"`∃Ψ ∈ 𝒜, E_F[Ψ] = min E_F`" cannot characterise SAT. A ground-state criterion needs an
`F`-independent reference value such as `0`. -/
theorem min_formulation_vacuous (lam mu : ℝ) :
    ¬ Sat G ∧ ∃ Ψ, Admissible Ψ ∧ ∀ Φ, Admissible Φ → energy G lam mu Ψ ≤ energy G lam mu Φ :=
  ⟨G_unsat, fieldI, fieldI_admissible, fun Φ hΦ => by
    rw [(single_var_energy lam mu).2]
    exact (single_var_energy lam mu).1 Φ hΦ⟩

/-! ## Measurement -/

/-- **Measurement by phase rounding.** Reading the sign of `Re ψᵢ` at every variable turns any
admissible field of sign-blind energy below `1/8` into a satisfying assignment, for every
`λ, μ ≥ 0`. The readout tolerates every perturbation that keeps the energy below `1/8`. -/
theorem measure_satisfies (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) (h : energySB F lam mu Ψ < 1 / 8) :
    ∀ c ∈ F, clauseVal (fun i => decide (0 ≤ (Ψ i).re)) c = true := by
  have hr : (fun i => decide (0 ≤ (Ψ i).re)) = roundPhase (phases Ψ) := by
    funext i
    unfold roundPhase
    rw [cos_phase hΨ i]
  rw [hr]
  exact roundPhase_satisfies F _ (lt_of_le_of_lt (energySB_ge_Elog F hlam hmu hΨ) h)

/-! ## A satisfying assignment need not be a ground state -/

/-- **A satisfying assignment need not minimise the total energy.** In the naive model with
`4μ + 2λ > 1/16`, every satisfying assignment of `F_xor` has strictly more energy than the
non-binary field `ψ ≡ i`. -/
theorem satisfying_not_ground {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hbig : 1 / 16 < 4 * mu + 2 * lam) {a : ℕ → Bool} (ha : ∀ c ∈ Fxor, clauseVal a c = true) :
    energy Fxor lam mu fieldI < energy Fxor lam mu (fieldOf a) := by
  have hne : a 0 ≠ a 1 := by
    intro heq
    have h1 := ha cPos (by simp [Fxor])
    have h2 := ha cNeg (by simp [Fxor])
    simp only [clauseVal, litVal, cPos, cNeg, Fin.isValue, if_true,
      show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, if_false] at h1 h2
    cases h0 : a 0 <;> simp_all
  have hpq : ((fieldOf a 0).re = 1 ∧ (fieldOf a 1).re = -1) ∨
      ((fieldOf a 0).re = -1 ∧ (fieldOf a 1).re = 1) := by
    unfold fieldOf
    cases h0 : a 0 <;> cases h1 : a 1 <;> simp_all
  have key : ∀ p q : ℝ, (p = 1 ∧ q = -1) ∨ (p = -1 ∧ q = 1) →
      (1 : ℝ) / 4 < (1 + q ^ 2 + 2 * p * q) / 4 + (4 * mu + 2 * lam) * (p - q) ^ 2 := by
    rintro p q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> nlinarith
  rw [xor_energy_at_I]
  exact lt_of_lt_of_le (key _ _ hpq) (energy_Fxor_ge hlam hmu (fieldOf_admissible a))

/-! ## The ground-energy formulation `E_min` -/

/-- The energies of admissible fields under the sign-blind energy. -/
def energiesSB (F : CNF3) (lam mu : ℝ) : Set ℝ :=
  {e | ∃ Ψ, Admissible Ψ ∧ energySB F lam mu Ψ = e}

/-- The ground energy `E_min(F) = inf_{Ψ ∈ 𝒜} E^{sb}_F[Ψ]`. -/
noncomputable def EminSB (F : CNF3) (lam mu : ℝ) : ℝ := sInf (energiesSB F lam mu)

theorem energiesSB_nonempty (F : CNF3) (lam mu : ℝ) : (energiesSB F lam mu).Nonempty :=
  ⟨_, fieldOf fun _ => true, fieldOf_admissible _, rfl⟩

theorem energiesSB_ge (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    ∀ e ∈ energiesSB F lam mu, 0 ≤ e := by
  rintro e ⟨Ψ, hΨ, rfl⟩
  exact (Elog_nonneg F Ψ).trans (energySB_ge_Elog F hlam hmu hΨ)

/-- **SAT ⟺ zero ground energy**, for every `λ, μ ≥ 0`. -/
theorem sat_iff_EminSB_eq_zero (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    Sat F ↔ EminSB F lam mu = 0 := by
  constructor
  · intro h
    obtain ⟨Ψ, hΨ, h0⟩ := (sat_iff_zero_energySB F hlam hmu).1 h
    exact IsLeast.csInf_eq ⟨⟨Ψ, hΨ, h0⟩, energiesSB_ge F hlam hmu⟩
  · intro h
    by_contra hF
    have hge : (1 : ℝ) / 8 ≤ EminSB F lam mu :=
      le_csInf (energiesSB_nonempty F lam mu) (by
        rintro e ⟨Ψ, hΨ, rfl⟩
        exact unsat_energySB_gap F hF hlam hmu hΨ)
    rw [h] at hge
    norm_num at hge

/-- **UNSAT ⟺ ground energy at least `1/8`**, for every `λ, μ ≥ 0`. -/
theorem unsat_iff_EminSB_ge (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    ¬ Sat F ↔ (1 : ℝ) / 8 ≤ EminSB F lam mu := by
  constructor
  · intro hF
    exact le_csInf (energiesSB_nonempty F lam mu) (by
      rintro e ⟨Ψ, hΨ, rfl⟩
      exact unsat_energySB_gap F hF hlam hmu hΨ)
  · intro hge hF
    rw [(sat_iff_EminSB_eq_zero F hlam hmu).1 hF] at hge
    norm_num at hge

/-- The energies of admissible fields under the naive energy. -/
def energies (F : CNF3) (lam mu : ℝ) : Set ℝ :=
  {e | ∃ Ψ, Admissible Ψ ∧ energy F lam mu Ψ = e}

/-- The naive ground energy. -/
noncomputable def Emin (F : CNF3) (lam mu : ℝ) : ℝ := sInf (energies F lam mu)

/-- **The naive ground energies of `F_xor` (satisfiable) and `G` (unsatisfiable) are both `1/4`**
once `4μ + 2λ ≥ 1/12`; so `SAT ⟺ E_min = 0` fails for the naive model. -/
theorem naive_Emin {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hbig : 1 / 12 ≤ 4 * mu + 2 * lam) :
    Sat Fxor ∧ Emin Fxor lam mu = 1 / 4 ∧ ¬ Sat G ∧ Emin G lam mu = 1 / 4 := by
  refine ⟨Fxor_sat, ?_, G_unsat, ?_⟩
  · refine IsLeast.csInf_eq ⟨⟨fieldI, fieldI_admissible, xor_energy_at_I lam mu⟩, ?_⟩
    rintro e ⟨Ψ, hΨ, rfl⟩
    exact xor_energy_ge_quarter hlam hmu hbig hΨ
  · refine IsLeast.csInf_eq ⟨⟨fieldI, fieldI_admissible, (single_var_energy lam mu).2⟩, ?_⟩
    rintro e ⟨Ψ, hΨ, rfl⟩
    exact (single_var_energy lam mu).1 Ψ hΨ

/-! ## General toroidal locking (manuscript claim I-37) -/

/-- A **locking configuration** of `F` for an extra energy `C` (coupling, curvature, flux, …): an
admissible field — a point of the phase torus `|ψᵢ| = 1` — at which the clause penalties and `C`
vanish together. -/
def Locks (C : CNF3 → (ℕ → ℂ) → ℝ) (F : CNF3) (Ψ : ℕ → ℂ) : Prop :=
  Admissible Ψ ∧ Elog F Ψ + C F Ψ = 0

/-- A locking configuration is a satisfiability certificate, for every extra energy `C ≥ 0`. -/
theorem sat_of_locks {C : CNF3 → (ℕ → ℂ) → ℝ} (hC : ∀ F Ψ, Admissible Ψ → 0 ≤ C F Ψ)
    {F : CNF3} {Ψ : ℕ → ℂ} (h : Locks C F Ψ) : Sat F := by
  have h1 := Elog_nonneg F Ψ
  have h2 := hC F Ψ h.1
  have hz : Elogic (phases Ψ) F = 0 := by
    show Elog F Ψ = 0
    linarith [h.2]
  exact (psi_sat_completeness F).2.2 ⟨_, hz⟩

/-- **When does the SAT correspondence survive added terms?** For an extra energy `C ≥ 0` on
admissible fields, "`F` has a locking configuration ⟺ `F` is satisfiable" holds for every
formula **iff** every satisfiable formula has an admissible field with zero clause penalty at
which `C` vanishes. -/
theorem locks_iff_sat_iff (C : CNF3 → (ℕ → ℂ) → ℝ) (hC : ∀ F Ψ, Admissible Ψ → 0 ≤ C F Ψ) :
    (∀ F, Sat F ↔ ∃ Ψ, Locks C F Ψ) ↔
      ∀ F, Sat F → ∃ Ψ, Admissible Ψ ∧ Elog F Ψ = 0 ∧ C F Ψ = 0 := by
  constructor
  · intro h F hF
    obtain ⟨Ψ, hΨ, h0⟩ := (h F).1 hF
    have h1 := Elog_nonneg F Ψ
    have h2 := hC F Ψ hΨ
    exact ⟨Ψ, hΨ, by linarith, by linarith⟩
  · intro h F
    refine ⟨fun hF => ?_, fun ⟨Ψ, hΨ⟩ => sat_of_locks hC hΨ⟩
    obtain ⟨Ψ, hΨ, h1, h2⟩ := h F hF
    exact ⟨Ψ, hΨ, by rw [h1, h2, add_zero]⟩

/-- **The gap survives every extra energy `C ≥ 0`:** an unsatisfiable formula costs at least
`1/8` everywhere on the phase torus. -/
theorem unsat_gap_general {C : CNF3 → (ℕ → ℂ) → ℝ} (hC : ∀ F Ψ, Admissible Ψ → 0 ≤ C F Ψ)
    {F : CNF3} (hF : ¬ Sat F) {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) :
    (1 : ℝ) / 8 ≤ Elog F Ψ + C F Ψ := by
  have h1 := unsat_logical_energy_gap F hF (phases Ψ)
  have h2 := hC F Ψ hΨ
  show (1 : ℝ) / 8 ≤ Elogic (phases Ψ) F + C F Ψ
  linarith

/-- The sign-blind coupling and curvature terms. -/
noncomputable def Csb (lam mu : ℝ) (F : CNF3) (Ψ : ℕ → ℂ) : ℝ :=
  lam * Ecoup F (sq Ψ) + mu * Ecurv F (sq Ψ)

/-- The naive coupling and curvature terms. -/
noncomputable def Cnaive (lam mu : ℝ) (F : CNF3) (Ψ : ℕ → ℂ) : ℝ :=
  lam * Ecoup F Ψ + mu * Ecurv F Ψ

theorem Csb_nonneg {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (F : CNF3) (Ψ : ℕ → ℂ)
    (hΨ : Admissible Ψ) : 0 ≤ Csb lam mu F Ψ :=
  add_nonneg (mul_nonneg hlam (Ecoup_nonneg F (sq_admissible hΨ)))
    (mul_nonneg hmu (Ecurv_nonneg F _))

theorem Cnaive_nonneg {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (F : CNF3) (Ψ : ℕ → ℂ)
    (hΨ : Admissible Ψ) : 0 ≤ Cnaive lam mu F Ψ :=
  add_nonneg (mul_nonneg hlam (Ecoup_nonneg F hΨ)) (mul_nonneg hmu (Ecurv_nonneg F _))

/-- **I-37 with the locking constraints defined.** With sign-blind coupling and curvature as the
flux constraints, a formula has no toroidal locking configuration iff it is unsatisfiable, for
every `λ, μ ≥ 0`. -/
theorem toroidal_locking_iff_unsat (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    (¬ ∃ Ψ, Locks (Csb lam mu) F Ψ) ↔ ¬ Sat F := by
  have h := (locks_iff_sat_iff (Csb lam mu) (Csb_nonneg hlam hmu)).2 (fun F hF => by
    obtain ⟨a, ha⟩ := hF
    refine ⟨fieldOf a, fieldOf_admissible a, ?_, ?_⟩
    · show Elogic (phases (fieldOf a)) F = 0
      rw [phases_fieldOf]
      exact (Elogic_phaseOf_eq_zero_iff a F).2 ha
    · unfold Csb
      rw [sq_fieldOf, Ecurv_const, Ecoup_const F (by simp)]
      ring) F
  exact not_congr h.symm

/-- **I-37 fails for the naive flux constraints:** with sign-sensitive coupling or curvature
(`4μ + 2λ > 0`), the satisfiable `F_xor` has no locking configuration. -/
theorem naive_toroidal_locking_fails {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hpos : 0 < 4 * mu + 2 * lam) :
    Sat Fxor ∧ ¬ ∃ Ψ, Locks (Cnaive lam mu) Fxor Ψ := by
  refine ⟨Fxor_sat, ?_⟩
  rintro ⟨Ψ, hΨ, h0⟩
  have hpos' := xor_energy_pos hlam hmu hpos hΨ
  unfold energy at hpos'
  unfold Cnaive at h0
  linarith

end PVNP.InterwovenSAT
