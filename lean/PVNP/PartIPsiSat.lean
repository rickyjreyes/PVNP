import PVNP.SATVerifier

/-!
# Part I, §ψ-SAT: the exact logical zero-penalty characterization (`thm:psi-sat-completeness`)

Literal translation of Part I, Section "ψ-SAT Encoding" (WIN-01/WIN-02, corrected):

* variable `i` carries a phase `θᵢ`, with `xᵢ = 1 ↔ θᵢ = 0` and `xᵢ = 0 ↔ θᵢ = π`;
* a literal `ℓ` with sign `η_ℓ = ±1` has truth score `s(ℓ;ψ) = (1 + η_ℓ cos θ_{v(ℓ)})/2`;
* a clause `Cⱼ = (ℓⱼ₁ ∨ ℓⱼ₂ ∨ ℓⱼ₃)` has penalty `Vⱼ = ∏ₖ (1 − s(ℓⱼₖ;ψ))`;
* `E_logic[ψ] = Σⱼ Vⱼ`.

`psi_sat_completeness` is the manuscript theorem: for every 3-CNF `F`,
`F` satisfiable ⟺ some binary-phase configuration has `E_logic = 0`
⟺ some configuration with arbitrary phases (all amplitudes nonzero) has `E_logic = 0`.
The field form uses `ψ : ℕ → ℂ` with `θᵢ = arg ψᵢ` (`psi_sat_completeness_field`).

Remark WIN-03 (stationarity is a separate obligation) is made precise by
`zero_penalty_not_stationary`: a configuration with `E_logic = 0` at which
`E_geom + λ E_logic` has nonzero directional derivative for **every** multiplier `λ`.

Appendix proposition "Uniform symbolic verification": `uniform_symbolic_verification`
identifies `𝟏{E_logic[a] = 0}` with the verifier language `V_SAT ∈ P_TM`.
-/

namespace PVNP.PartIPsiSat

open PVNP.Discrete PVNP.Discrete.SATV

/-- A literal: variable index and sign (`pos = true` for `xᵥ`, `false` for `¬xᵥ`). -/
structure Lit where
  v : ℕ
  pos : Bool

/-- A clause of a 3-CNF formula: exactly three literals. -/
abbrev Clause3 := Fin 3 → Lit

/-- A 3-CNF formula. -/
abbrev CNF3 := List Clause3

/-- The sign `η_ℓ ∈ {+1, −1}`. -/
def eta (l : Lit) : ℝ := if l.pos then 1 else -1

/-- Truth score `s(ℓ; θ) = (1 + η_ℓ cos θ_{v(ℓ)}) / 2`. -/
noncomputable def score (θ : ℕ → ℝ) (l : Lit) : ℝ := (1 + eta l * Real.cos (θ l.v)) / 2

/-- Clause penalty `Vⱼ = ∏ₖ (1 − s(ℓⱼₖ))`. -/
noncomputable def clausePen (θ : ℕ → ℝ) (c : Clause3) : ℝ := ∏ k, (1 - score θ (c k))

/-- `E_logic = Σⱼ Vⱼ`. -/
noncomputable def Elogic (θ : ℕ → ℝ) (F : CNF3) : ℝ := (F.map (clausePen θ)).sum

/-- Boolean value of a literal. -/
def litVal (a : ℕ → Bool) (l : Lit) : Bool := if l.pos then a l.v else !(a l.v)

/-- Boolean value of a 3-clause. -/
def clauseVal (a : ℕ → Bool) (c : Clause3) : Bool := litVal a (c 0) || litVal a (c 1) || litVal a (c 2)

/-- Satisfiability of a 3-CNF formula. -/
def Sat (F : CNF3) : Prop := ∃ a : ℕ → Bool, ∀ c ∈ F, clauseVal a c = true

/-- The binary phase of an assignment: `0` for true, `π` for false. -/
noncomputable def phaseOf (a : ℕ → Bool) : ℕ → ℝ := fun i => if a i then 0 else Real.pi

/-- Binary-phase configurations. -/
def IsBinary (θ : ℕ → ℝ) : Prop := ∀ i, θ i = 0 ∨ θ i = Real.pi

/-! ### Elementary facts -/

theorem eta_sq (l : Lit) : eta l * eta l = 1 := by unfold eta; split_ifs <;> norm_num

theorem score_mem (θ : ℕ → ℝ) (l : Lit) : 0 ≤ score θ l ∧ score θ l ≤ 1 := by
  have h1 := Real.neg_one_le_cos (θ l.v)
  have h2 := Real.cos_le_one (θ l.v)
  unfold score eta
  split_ifs <;> constructor <;> linarith

/-- The logical energy is nonnegative on all phase encodings. -/
theorem clausePen_nonneg (θ : ℕ → ℝ) (c : Clause3) : 0 ≤ clausePen θ c :=
  Finset.prod_nonneg fun k _ => by have := (score_mem θ (c k)).2; linarith

theorem Elogic_nonneg (θ : ℕ → ℝ) (F : CNF3) : 0 ≤ Elogic θ F := by
  unfold Elogic
  induction F with
  | nil => simp
  | cons c F ih => simp only [List.map_cons, List.sum_cons]; exact add_nonneg (clausePen_nonneg θ c) ih

theorem Elogic_eq_zero_iff (θ : ℕ → ℝ) (F : CNF3) :
    Elogic θ F = 0 ↔ ∀ c ∈ F, clausePen θ c = 0 := by
  unfold Elogic
  induction F with
  | nil => simp
  | cons c F ih =>
    simp only [List.map_cons, List.sum_cons, List.mem_cons, forall_eq_or_imp]
    have h1 := clausePen_nonneg θ c
    have h2 : 0 ≤ (F.map (clausePen θ)).sum := by
      have := Elogic_nonneg θ F; unfold Elogic at this; exact this
    constructor
    · intro h
      have hc : clausePen θ c = 0 := by linarith
      exact ⟨hc, ih.1 (by linarith)⟩
    · rintro ⟨hc, hF⟩
      rw [hc, ih.2 hF, add_zero]

theorem clausePen_eq_zero_iff (θ : ℕ → ℝ) (c : Clause3) :
    clausePen θ c = 0 ↔ ∃ k, score θ (c k) = 1 := by
  unfold clausePen
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, Finset.mem_univ _, by linarith⟩

/-- `s(ℓ) = 1` forces the phase to be Boolean with the literal's sign. -/
theorem score_eq_one_iff (θ : ℕ → ℝ) (l : Lit) :
    score θ l = 1 ↔ Real.cos (θ l.v) = eta l := by
  unfold score
  constructor
  · intro h
    have h' : eta l * Real.cos (θ l.v) = 1 := by linarith
    have := congrArg (fun r => eta l * r) h'
    simp only [← mul_assoc, eta_sq, one_mul, mul_one] at this
    exact this
  · intro h
    rw [h, eta_sq]; norm_num

theorem score_phaseOf (a : ℕ → Bool) (l : Lit) : score (phaseOf a) l = if litVal a l then 1 else 0 := by
  unfold score phaseOf litVal eta
  cases hp : l.pos <;> cases ha : a l.v <;> simp [Real.cos_pi] <;> norm_num

theorem litVal_of_score (θ : ℕ → ℝ) (l : Lit) (h : score θ l = 1) :
    litVal (fun i => decide (Real.cos (θ i) = 1)) l = true := by
  rw [score_eq_one_iff] at h
  unfold litVal
  unfold eta at h
  cases hp : l.pos
  · simp only [hp, if_false] at h ⊢
    rw [h]; norm_num
  · simp only [hp, if_true] at h ⊢
    simp [h]

/-! ### The manuscript theorem -/

/-- Zero penalty under the binary phase of an assignment is exactly satisfaction. -/
theorem Elogic_phaseOf_eq_zero_iff (a : ℕ → Bool) (F : CNF3) :
    Elogic (phaseOf a) F = 0 ↔ ∀ c ∈ F, clauseVal a c = true := by
  rw [Elogic_eq_zero_iff]
  refine forall₂_congr fun c _ => ?_
  rw [clausePen_eq_zero_iff]
  simp only [score_phaseOf]
  constructor
  · rintro ⟨k, hk⟩
    split_ifs at hk with h
    · unfold clauseVal
      fin_cases k <;> simp_all
    · norm_num at hk
  · intro h
    unfold clauseVal at h
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩

theorem phaseOf_binary (a : ℕ → Bool) : IsBinary (phaseOf a) := by
  intro i; unfold phaseOf; split_ifs <;> simp

/-- **Theorem `thm:psi-sat-completeness` (Part I).**  For every 3-CNF formula `F`:
(1) `F` is satisfiable ⟺ (2) some binary-phase configuration has `E_logic = 0`;
and the same holds when arbitrary real phases are permitted. -/
theorem psi_sat_completeness (F : CNF3) :
    (Sat F ↔ ∃ θ : ℕ → ℝ, IsBinary θ ∧ Elogic θ F = 0) ∧
      (Sat F ↔ ∃ θ : ℕ → ℝ, Elogic θ F = 0) := by
  have back : ∀ θ : ℕ → ℝ, Elogic θ F = 0 → Sat F := by
    intro θ h
    refine ⟨fun i => decide (Real.cos (θ i) = 1), fun c hc => ?_⟩
    obtain ⟨k, hk⟩ := (clausePen_eq_zero_iff θ c).1 ((Elogic_eq_zero_iff θ F).1 h c hc)
    have hl := litVal_of_score θ (c k) hk
    unfold clauseVal
    fin_cases k <;> simp_all
  have fwd : Sat F → ∃ θ : ℕ → ℝ, IsBinary θ ∧ Elogic θ F = 0 := by
    rintro ⟨a, ha⟩
    exact ⟨phaseOf a, phaseOf_binary a, (Elogic_phaseOf_eq_zero_iff a F).2 ha⟩
  refine ⟨⟨fwd, fun ⟨θ, _, h⟩ => back θ h⟩, ⟨fun h => ?_, fun ⟨θ, h⟩ => back θ h⟩⟩
  obtain ⟨θ, -, hθ⟩ := fwd h
  exact ⟨θ, hθ⟩

/-! ### Field form: `ψ : ℕ → ℂ`, nonzero amplitudes, phase `arg ψᵢ` -/

/-- Phases of a field. -/
noncomputable def phases (ψ : ℕ → ℂ) : ℕ → ℝ := fun i => Complex.arg (ψ i)

/-- `E_logic[ψ]` for a field with nonzero amplitudes. -/
noncomputable def ElogicField (ψ : ℕ → ℂ) (F : CNF3) : ℝ := Elogic (phases ψ) F

/-- A binary-phase field: every amplitude is a nonzero real number
(phase `0` if positive, `π` if negative). -/
def IsBinaryField (ψ : ℕ → ℂ) : Prop := ∀ i, ψ i ≠ 0 ∧ (ψ i).im = 0

/-- The binary-phase field of an assignment (unit amplitudes). -/
noncomputable def fieldOf (a : ℕ → Bool) : ℕ → ℂ := fun i => if a i then 1 else -1

theorem phases_fieldOf (a : ℕ → Bool) : phases (fieldOf a) = phaseOf a := by
  funext i; unfold phases fieldOf phaseOf; split_ifs <;> simp

/-- **Theorem `thm:psi-sat-completeness`, field form.**  `F` is satisfiable ⟺ some
binary-phase field has `E_logic = 0` ⟺ some field with all amplitudes nonzero has
`E_logic = 0`. -/
theorem psi_sat_completeness_field (F : CNF3) :
    (Sat F ↔ ∃ ψ : ℕ → ℂ, IsBinaryField ψ ∧ ElogicField ψ F = 0) ∧
      (Sat F ↔ ∃ ψ : ℕ → ℂ, (∀ i, ψ i ≠ 0) ∧ ElogicField ψ F = 0) := by
  have hfwd : Sat F → ∃ ψ : ℕ → ℂ, IsBinaryField ψ ∧ ElogicField ψ F = 0 := by
    rintro ⟨a, ha⟩
    refine ⟨fieldOf a, fun i => ?_, ?_⟩
    · unfold fieldOf; split_ifs <;> simp
    · unfold ElogicField; rw [phases_fieldOf]; exact (Elogic_phaseOf_eq_zero_iff a F).2 ha
  have hback : ∀ ψ : ℕ → ℂ, ElogicField ψ F = 0 → Sat F := fun ψ h =>
    (psi_sat_completeness F).2.2 ⟨_, h⟩
  refine ⟨⟨hfwd, fun ⟨ψ, _, h⟩ => hback ψ h⟩, ⟨fun h => ?_, fun ⟨ψ, _, h⟩ => hback ψ h⟩⟩
  obtain ⟨ψ, hψ, h0⟩ := hfwd h
  exact ⟨ψ, fun i => (hψ i).1, h0⟩

/-! ### Remark WIN-03: zero logical penalty does not imply stationarity -/

/-- The single-clause formula `(x₀ ∨ x₀ ∨ x₀) ∧ (x₁ ∨ x₁ ∨ x₁)`. -/
def F01 : CNF3 := [fun _ => ⟨0, true⟩, fun _ => ⟨1, true⟩]

/-- A two-site lattice geometric (Dirichlet) energy `E_geom[ψ] = |ψ₀ − ψ₁|²`. -/
noncomputable def Egeom (ψ : ℕ → ℂ) : ℝ := Complex.normSq (ψ 0 - ψ 1)

/-- The field `ψ = (1, 2, 1, 1, …)`: positive amplitudes, phases `0`. -/
noncomputable def ψ12 : ℕ → ℂ := fun i => if i = 1 then 2 else 1

/-- The real direction of site `0`. -/
noncomputable def e0 : ℕ → ℂ := fun i => if i = 0 then 1 else 0

theorem ElogicField_shift (s : ℝ) (hs : -1 < s) : ElogicField (ψ12 + s • e0) F01 = 0 := by
  have hph : ∀ i, phases (ψ12 + s • e0) i = 0 := by
    intro i
    unfold phases ψ12 e0
    simp only [Pi.add_apply, Pi.smul_apply]
    by_cases h0 : i = 0
    · subst h0
      have : ((1 : ℂ) + s • (1 : ℂ)) = ((1 + s : ℝ) : ℂ) := by simp
      simp only [show (0 : ℕ) ≠ 1 by decide, if_false, if_true, this]
      exact Complex.arg_ofReal_of_nonneg (by linarith)
    · by_cases h1 : i = 1
      · subst h1; simp
      · simp [h0, h1]
  unfold ElogicField
  have : phases (ψ12 + s • e0) = phaseOf (fun _ => true) := by
    funext i; rw [hph i]; simp [phaseOf]
  rw [this, Elogic_phaseOf_eq_zero_iff]
  intro c hc
  simp only [F01, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [clauseVal, litVal]

theorem Egeom_shift (s : ℝ) : Egeom (ψ12 + s • e0) = (s - 1) ^ 2 := by
  unfold Egeom ψ12 e0
  simp only [Pi.add_apply, Pi.smul_apply, show (0 : ℕ) ≠ 1 by decide, if_false, if_true,
    show (1 : ℕ) ≠ 0 by decide, smul_zero, add_zero]
  rw [show (1 : ℂ) + s • (1 : ℂ) - 2 = ((s - 1 : ℝ) : ℂ) by rw [Complex.real_smul]; push_cast; ring,
    Complex.normSq_ofReal]
  ring

/-- **Remark WIN-03 (Part I), made precise.**  The field `ψ = (1, 2)` encodes a satisfying
assignment of `F01` (`E_logic[ψ] = 0`), yet for **every** multiplier `λ` the functional
`E_geom + λ E_logic` has directional derivative `−2 ≠ 0` at `ψ` along `e₀`: a zero of the
logical penalty need not be stationary for an independently varying geometric energy. -/
theorem zero_penalty_not_stationary :
    ElogicField ψ12 F01 = 0 ∧
      ∀ lam : ℝ, HasDerivAt (fun s : ℝ => Egeom (ψ12 + s • e0) + lam * ElogicField (ψ12 + s • e0) F01)
        (-2) 0 := by
  refine ⟨by simpa using ElogicField_shift 0 (by norm_num), fun lam => ?_⟩
  have h1 : HasDerivAt (fun s : ℝ => (s - 1) ^ 2) (-2) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).sub_const 1).pow 2
    simpa using this
  apply h1.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with s hs
  rw [Egeom_shift, ElogicField_shift s hs, mul_zero, add_zero]

/-! ### Appendix: uniform symbolic verification -/

/-- A 3-clause as a Part I clause (list of signed literals). -/
def toClause (c : Clause3) : PVNP.PartI.Clause := [((c 0).v, (c 0).pos), ((c 1).v, (c 1).pos),
  ((c 2).v, (c 2).pos)]

/-- A 3-CNF as a Part I formula. -/
def toFormula (F : CNF3) : PVNP.PartI.Formula := F.map toClause

theorem evalLiteral_eq (a : ℕ → Bool) (l : Lit) :
    PVNP.PartI.evalLiteral a (l.v, l.pos) = litVal a l := by
  unfold PVNP.PartI.evalLiteral PVNP.PartI.literalTrue litVal
  cases l.pos <;> cases a l.v <;> rfl

theorem evalFormula_toFormula (a : ℕ → Bool) (F : CNF3) :
    PVNP.PartI.evalFormula a (toFormula F) = true ↔ ∀ c ∈ F, clauseVal a c = true := by
  induction F with
  | nil => simp [toFormula, PVNP.PartI.evalFormula]
  | cons c F ih =>
    simp only [toFormula, List.map_cons, PVNP.PartI.evalFormula, Bool.and_eq_true, List.mem_cons,
      forall_eq_or_imp] at ih ⊢
    rw [ih]
    simp [toClause, PVNP.PartI.evalClause, evalLiteral_eq, clauseVal, Bool.or_assoc]

/-- **Proposition "Uniform symbolic verification" (Part I, Appendix).**  For an explicitly
represented 3-CNF formula `F` over the variables `< n` (`n ≥ 1`) and an assignment
`a ∈ {0,1}ⁿ` (the witness bit string), the predicate `𝟏{E_logic[a] = 0}` is exactly
membership of `pair (encDense n F) a` in the verifier language `V_SAT`, which is decided
in polynomial time by an explicit single-tape Turing machine (`V_SAT ∈ P_TM`). -/
theorem uniform_symbolic_verification (n : ℕ) (hn : 1 ≤ n) (F : CNF3) (hF : ∀ c ∈ F, ∀ k, (c k).v < n)
    (a : List Bool) (ha : a.length = n) :
    (pair (encDense n (toFormula F)) a ∈ V_SAT ↔ Elogic (phaseOf fun i => a.getD i false) F = 0) ∧
      V_SAT ∈ P_TM := by
  refine ⟨?_, V_SAT_mem_P_TM⟩
  have hF' : ∀ c ∈ toFormula F, ∀ l ∈ c, l.1 < n := by
    intro c hc l hl
    simp only [toFormula, List.mem_map] at hc
    obtain ⟨c3, hc3, rfl⟩ := hc
    simp only [toClause, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> exact hF c3 hc3 _
  rw [Elogic_phaseOf_eq_zero_iff, ← evalFormula_toFormula]
  constructor
  · rintro ⟨x, w, hxw, hc⟩
    obtain ⟨hx, hw⟩ := pair_injective hxw
    rw [← hx, ← hw, chk_formula a n hn ha _ hF'] at hc
    exact hc
  · intro h
    exact ⟨_, _, rfl, by rw [chk_formula a n hn ha _ hF']; exact h⟩

end PVNP.PartIPsiSat
