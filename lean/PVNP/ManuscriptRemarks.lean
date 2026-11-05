import Mathlib

/-!
# Remaining structural propositions of Parts I and III

* `valid_telescoping`: Part I Proposition `thm:mass_complexity` in the manuscript's form
  `T ≥ (C_T − C_0)_+ / Δ_max`.
* `padding_stability`: Part I Proposition `thm:padding_stability`. The functional of the padded
  configuration equals that of the formula domain when the padding has zero density and there
  is no interface term.
* `superlinear_padding`: the remark that follows. With superlinear padding `N = n²`, an
  exponent `γn` is eventually below `cN` for every `c > 0`, so `2^{γn}` is not `2^{Ω(N)}`.
* `win13_counterexample`: Part III Remark WIN-13. `ψ = −ε` violates `|ψ + ε| ≥ ε`.
* `p_in_np_phys`: Part III Theorem `thm:p-in-np`, in an abstract physical model whose verifiers
  may ignore their witnesses under the same rails.
* `win16`: Part III Remark WIN-16. `NP^phys = ∅` contradicts a nonempty `P^phys`.
-/

namespace PVNP.ManuscriptRemarks

open MeasureTheory

/-- **Part I, Proposition `thm:mass_complexity` ("Valid telescoping bound").**  If
`C_Θ[ψ_0] ≥ 0` and every allowed update changes `C_Θ` by at most `Δ_max > 0`, then
`T ≥ (C_Θ[ψ_T] − C_Θ[ψ_0])_+ / Δ_max` for every `T`. -/
theorem valid_telescoping (C : ℕ → ℝ) (Δ : ℝ) (hΔ : 0 < Δ) (_h0 : 0 ≤ C 0)
    (hstep : ∀ t, |C (t + 1) - C t| ≤ Δ) (T : ℕ) : max (C T - C 0) 0 / Δ ≤ T := by
  have htel : C T - C 0 ≤ T * Δ := by
    induction T with
    | zero => simp
    | succ T ih =>
      have := (abs_le.1 (hstep T)).2
      push_cast
      linarith
  rw [div_le_iff₀ hΔ]
  exact max_le htel (by positivity)

/-- **Part I, Proposition `thm:padding_stability` ("Conditional additive padding").**  For a
functional given by a density `e` with no interface or cross-coupling term, on a disjoint
decomposition `Ω = Ω_F ⊔ Ω_pad` with zero density on the padding domain, the functional of the
padded configuration equals that of the formula domain. -/
theorem padding_stability {X : Type*} [MeasurableSpace X] (μ : Measure X) (ΩF Ωp : Set X)
    (hd : Disjoint ΩF Ωp) (hm : MeasurableSet Ωp) (e : X → ℝ) (hi : IntegrableOn e ΩF μ)
    (hz : ∀ x ∈ Ωp, e x = 0) : ∫ x in ΩF ∪ Ωp, e x ∂μ = ∫ x in ΩF, e x ∂μ := by
  have hzero : IntegrableOn e Ωp μ := by
    have : Set.EqOn e 0 Ωp := fun x hx => hz x hx
    exact (integrableOn_zero).congr_fun this.symm hm
  rw [setIntegral_union hd hm hi hzero]
  have : ∫ x in Ωp, e x ∂μ = 0 := by
    rw [setIntegral_congr_fun hm (fun x hx => hz x hx)]
    simp
  rw [this, add_zero]

/-- **Remark after `thm:padding_stability`.**  Under the superlinear padding `N = n²` an
exponential bound `2^{γn}` is not `2^{Ω(N)}`: for every `c > 0`, `γ n < c N` for large `n`. -/
theorem superlinear_padding (γ c : ℝ) (hc : 0 < c) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
    γ * n < c * ((n : ℝ) ^ 2) := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (γ / c)
  refine ⟨n₀, fun n hn hpos => ?_⟩
  have hn : γ / c < n := lt_of_lt_of_le hn₀ (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
  rw [div_lt_iff₀ hc] at hn
  nlinarith

/-- **Part III, Remark WIN-13.**  The field value `ψ = −ε` violates the claimed denominator bound
`|ψ + ε| ≥ ε`. -/
theorem win13_counterexample (ε : ℝ) (hε : 0 < ε) : ¬ (ε ≤ |(-ε) + ε|) := by
  intro h
  rw [neg_add_cancel, abs_zero] at h
  linarith

/-- A physical model in which deciders and verifiers are subject to the same rail predicate, and
every decider can be run as a verifier that ignores its witness. -/
structure PhysPair where
  Prog : Type
  /-- `runs P x` is the answer of program `P` on input `x`, respecting the rails. -/
  answer : Prog → List Bool → Bool
  /-- The resource rail predicate (polynomial bounds on all charged resources). -/
  rail : Prog → Prop
  /-- Witness-ignoring wrapper: a decider used as a verifier, with the same answers. -/
  ignore : Prog → Prog
  /-- Verifier answers on a pair `(x, w)`. -/
  vanswer : Prog → List Bool → List Bool → Bool
  ignore_rail : ∀ P, rail P → rail (ignore P)
  ignore_answer : ∀ P x w, vanswer (ignore P) x w = answer P x

namespace PhysPair

variable (M : PhysPair)

/-- `P^phys`: decided by a program within the rails. -/
def Pphys : Set (Set (List Bool)) := {L | ∃ P, M.rail P ∧ ∀ x, (M.answer P x = true ↔ x ∈ L)}

/-- `NP^phys`: verified by a program within the same rails, with polynomial witness bound. -/
def NPphys : Set (Set (List Bool)) :=
  {L | ∃ (V : M.Prog) (q : Polynomial ℕ), M.rail V ∧
    ∀ x, (x ∈ L ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ M.vanswer V x w = true)}

end PhysPair

/-- **Part III, Theorem `thm:p-in-np` ("Verifier inclusion").**  In any model whose verifiers may
ignore their witnesses and whose deciders and verifiers obey the same rails,
`P^phys ⊆ NP^phys`. -/
theorem p_in_np_phys (M : PhysPair) : M.Pphys ⊆ M.NPphys := by
  rintro L ⟨P, hP, hL⟩
  refine ⟨M.ignore P, 0, M.ignore_rail P hP, fun x => ?_⟩
  rw [← hL x]
  constructor
  · intro h; exact ⟨[], by simp, by rw [M.ignore_answer]; exact h⟩
  · rintro ⟨w, -, hw⟩; rwa [M.ignore_answer] at hw

/-- **Part III, Remark WIN-16.**  `NP^phys = ∅` is incompatible with a nonempty `P^phys`. -/
theorem win16 (M : PhysPair) (hP : M.Pphys.Nonempty) : M.NPphys ≠ ∅ := by
  intro h
  obtain ⟨L, hL⟩ := hP
  have := p_in_np_phys M hL
  rw [h] at this
  exact this

end PVNP.ManuscriptRemarks
