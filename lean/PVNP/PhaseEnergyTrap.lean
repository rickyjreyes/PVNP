import PVNP.PhasePenaltyGap

/-! A satisfiable three-CNF with an energy barrier for continuous descent of
Part I's exact logical energy. Repeated clauses carry their literal multiplicity. -/
namespace PVNP.PhaseEnergyTrap

open PartIPsiSat

private def A : Clause3 := fun _ => ⟨0, true⟩
private def B : Clause3 := fun i => if i = 0 then ⟨0, false⟩ else ⟨1,true⟩
private def C : Clause3 := fun i => if i = 0 then ⟨1, false⟩ else ⟨0,true⟩

def formula : CNF3 := A :: (List.replicate 16 B ++ List.replicate 16 C)

theorem sat : Sat formula := by
  refine ⟨fun _ => true, ?_⟩
  intro c hc
  simp [formula] at hc
  rcases hc with h|h|h <;> subst c <;> decide

noncomputable def u (θ : ℕ → ℝ) (i : ℕ) : ℝ := (1 + Real.cos (θ i))/2

private theorem u_nonneg (θ : ℕ → ℝ) (i : ℕ) : 0 ≤ u θ i := by
  unfold u; linarith [Real.neg_one_le_cos (θ i)]

theorem energy (θ : ℕ → ℝ) :
    Elogic θ formula = (1-u θ 0)^3 + 16*u θ 0*(1-u θ 1)^2 + 16*u θ 1*(1-u θ 0)^2 := by
  simp [formula, Elogic, clausePen, A, B, C, Fin.prod_univ_three,
    score, eta, u]
  ring

theorem corner : Elogic (fun _ => Real.pi) formula = 1 := by
  rw [energy]; norm_num [u]

/-- Uniform barrier throughout the false/false quadrant in truth-score coordinates. -/
theorem lower {θ : ℕ → ℝ} (ha : u θ 0 ≤ 1/2) (hb : u θ 1 ≤ 1/2) :
    1 + u θ 0 + 4*u θ 1 ≤ Elogic θ formula := by
  have ha0 : 0 ≤ u θ 0 := u_nonneg θ 0
  have hb0 : 0 ≤ u θ 1 := u_nonneg θ 1
  have hp (a : ℝ) (h : a ≤ 1/2) : 1/4 ≤ (1-a)^2 := by nlinarith [sq_nonneg (a-1/2)]
  have h1 := mul_nonneg ha0 (sub_nonneg.mpr (hp _ hb))
  have h2 := mul_nonneg hb0 (sub_nonneg.mpr (hp _ ha))
  have h3 := mul_nonneg (sq_nonneg (u θ 0)) (show 0 ≤ 3-u θ 0 by linarith)
  rw [energy]; nlinarith

/-- Every continuous path from the false/false corner to a threshold certificate
crosses energy at least 3/2, on this satisfiable formula. Only two samples need be continuous. -/
theorem escape {θ : ℝ → ℕ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hc0 : ContinuousOn (fun t => u (θ t) 0) (Set.Icc 0 T))
    (hc1 : ContinuousOn (fun t => u (θ t) 1) (Set.Icc 0 T))
    (h0 : u (θ 0) 0 = 0) (h1 : u (θ 0) 1 = 0)
    (hend : Elogic (θ T) formula < 1/8) :
    ∃ t ∈ Set.Icc 0 T, (3:ℝ)/2 ≤ Elogic (θ t) formula := by
  let g := fun t => max (u (θ t) 0) (u (θ t) 1)
  have start : g 0 ≤ 1/2 := by simp [g,h0,h1]
  have stop : 1/2 ≤ g T := by
    by_contra! h
    have ha := (le_max_left (u (θ T) 0) (u (θ T) 1)).trans h.le
    have hb := (le_max_right (u (θ T) 0) (u (θ T) 1)).trans h.le
    have hn : 0 ≤ u (θ T) 0 := u_nonneg (θ T) 0
    have hm : 0 ≤ u (θ T) 1 := u_nonneg (θ T) 1
    linarith [lower ha hb]
  obtain ⟨t, ht, htval⟩ := intermediate_value_Icc hT (hc0.sup hc1) ⟨start,stop⟩
  change max (u (θ t) 0) (u (θ t) 1) = 1/2 at htval
  have ha := (le_max_left (u (θ t) 0) (u (θ t) 1)).trans htval.le
  have hb := (le_max_right (u (θ t) 0) (u (θ t) 1)).trans htval.le
  have hn : 0 ≤ u (θ t) 0 := u_nonneg (θ t) 0
  have hm : 0 ≤ u (θ t) 1 := u_nonneg (θ t) 1
  refine ⟨t,ht,?_⟩
  rcases le_total (u (θ t) 0) (u (θ t) 1) with h | h
  · rw [max_eq_right h] at htval; linarith [lower ha hb]
  · rw [max_eq_left h] at htval; linarith [lower ha hb]

end PVNP.PhaseEnergyTrap
