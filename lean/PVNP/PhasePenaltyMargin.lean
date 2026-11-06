import PVNP.PartIPsiSat

/-! Sign readout gives a quantitative certificate for the manuscript's logical
energy. The estimate holds at any observation time and allows repeated literals. -/
namespace PVNP.PartIPsiSat

/-- Round a phase at the two truth-score basins; a tie chooses true. -/
noncomputable def roundPhase (θ : ℕ → ℝ) (i : ℕ) : Bool := decide (0 ≤ Real.cos (θ i))

private theorem failed_literal_margin (θ : ℕ → ℝ) (l : Lit)
    (h : litVal (roundPhase θ) l = false) : 1/2 ≤ 1 - score θ l := by
  cases l with | mk i pos =>
    cases pos <;> simp [litVal, roundPhase, score, eta] at h ⊢ <;> linarith

/-- A clause falsified by sign rounding contributes at least one eighth. -/
theorem failed_clause_margin (θ : ℕ → ℝ) (c : Clause3) (h : clauseVal (roundPhase θ) c = false) :
    (1:ℝ)/8 ≤ clausePen θ c := by
  simp only [clauseVal, Bool.or_eq_false_iff] at h
  rw [clausePen, Fin.prod_univ_three]
  have hh (i : Fin 3) : 0 ≤ 1 - score θ (c i) := sub_nonneg.mpr (score_mem _ _).2
  calc (1:ℝ)/8 = (1/2)*(1/2)*(1/2) := by norm_num
       _ ≤ _ := mul_le_mul (mul_le_mul (failed_literal_margin _ _ h.1.1)
            (failed_literal_margin _ _ h.1.2) (by norm_num) (hh 0))
          (failed_literal_margin _ _ h.2) (by norm_num) (mul_nonneg (hh 0) (hh 1))

private theorem clausePen_le_energy (θ : ℕ → ℝ) {F : CNF3} {c : Clause3} (hc : c ∈ F) :
    clausePen θ c ≤ Elogic θ F := by
  induction F with
  | nil => simp at hc
  | cons d F ih =>
    change _ ≤ clausePen θ d + Elogic θ F
    rcases List.mem_cons.mp hc with rfl | h
    · linarith [Elogic_nonneg θ F]
    · linarith [ih h, clausePen_nonneg θ d]

/-- Below the readout threshold a specific, simultaneous assignment satisfies
every clause, even when literals repeat. -/
theorem roundPhase_satisfies (F : CNF3) (θ : ℕ → ℝ) (h : Elogic θ F < 1/8) :
    ∀ c ∈ F, clauseVal (roundPhase θ) c = true := by
  intro c hc
  cases hv : clauseVal (roundPhase θ) c with
  | true => rfl
  | false => exact False.elim ((not_le.mpr h) ((failed_clause_margin θ c hv).trans (clausePen_le_energy θ hc)))

/-- In particular, convergence in logical energy gives satisfying assignments
at every sufficiently late observation. The dynamics must separately establish
the energy convergence. -/
theorem eventually_satisfies_of_energy_tendsto {F : CNF3} {θ : ℕ → ℕ → ℝ}
    (h : Filter.Tendsto (fun t => Elogic (θ t) F) Filter.atTop (nhds 0)) :
    ∀ᶠ t in Filter.atTop, ∀ c ∈ F, clauseVal (roundPhase (θ t)) c = true := by
  filter_upwards [h.eventually_lt_const (show (0:ℝ) < 1/8 by norm_num)] with t ht
  exact roundPhase_satisfies F (θ t) ht

/-- At equality a tripled negative literal can fail after sign rounding. This
is sharp for this decoder, not a claim about the optimum energy of UNSAT. -/
theorem rounding_threshold_attained :
    ∃ (F : CNF3) (θ : ℕ → ℝ) (c : Clause3), c ∈ F ∧
      Elogic θ F = 1/8 ∧ clauseVal (roundPhase θ) c = false := by
  let c : Clause3 := fun _ => ⟨0, false⟩
  refine ⟨[c], fun _ => Real.pi/2, c, by simp, ?_, ?_⟩
  · norm_num [Elogic, clausePen, Fin.prod_univ_three, c, score, eta, Real.cos_pi_div_two]
  · simp [clauseVal, litVal, roundPhase, c, Real.cos_pi_div_two]

end PVNP.PartIPsiSat
