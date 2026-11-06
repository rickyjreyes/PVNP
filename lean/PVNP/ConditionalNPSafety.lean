import PVNP.FiniteModification
import PVNP.CookLevinUniform
import PVNP.PartIIManuscript
import PVNP.PartIIUniformEquiv

/-!
# Part II, Theorem `thm:conditional_np_safety` (II-24)

The manuscript assumes:

* **(i)** the WCT rails and the channel-capacity bound `N_updates ≤ K·V·T·E⁴`, for a device
  family with polynomial resources `V ≤ C_V n^a`, `T ≤ C_T n^b`, `E ≤ C_E n^c`;
* **(ii)** the computation of the device is faithfully modelled by a uniform discrete WCC machine
  `W` (`def:wcc_machine`), each non-halting round costing at least one counted event, so the first
  decision on an input of length `n` comes within `N_updates(n) + 1` rounds
  (`prop:phys_step_ceiling`, `rounds_le_events`);
* **(iii)** `P_Turing ≠ NP_Turing`.

It concludes: there are an NP-complete `L` and a constant `k ≥ 1` such that, for infinitely many
`n`, the system fails to decide `L` on some input of length `n`.

`conditional_np_safety` proves exactly this, with (i)–(iii) as explicit hypotheses. The physical
quantities enter as in II-23 (`phys_step_ceiling`). `conditional_np_safety_all` proves it for every
NP-complete `L`, the manuscript's "in fact any NP-complete language".

NP-completeness is taken in the decision form the manuscript's proof uses (`NPCompleteDec`):
`L ∈ NP_TM`, and `L ∈ P_TM` forces `NP_TM ⊆ P_TM`. `SAT_dense` satisfies it by the uniform
Cook–Levin theorem (`SAT_dense_npComplete`).

The proof needs two closure facts:
* `P^disc ⊆ P_TM` (II-11);
* closure of `P_TM` under finite modification (`P_TM_of_eventually_eq`). A machine that is correct
  on all long inputs can be patched on the finitely many short ones.

None of (i)–(iii) is proved. In particular, (iii) is the open classical separation.
-/

namespace PVNP.PartIIManuscript

open PVNP.Discrete PVNP.PartIIUniform PVNP.PartIITuring PVNP.Discrete.SATV
open PVNP.CookLevin.Gen

/-- **NP-completeness, decision form**: `L ∈ NP_TM`, and a polynomial-time decider for `L` would
put all of `NP_TM` in `P_TM`. -/
def NPCompleteDec (L : Set (List Bool)) : Prop := L ∈ NP_TM ∧ (L ∈ P_TM → NP_TM ⊆ P_TM)

/-- `SAT_dense` is NP-complete in the decision form (uniform Cook–Levin, CL-1). -/
theorem SAT_dense_npComplete : NPCompleteDec SAT_dense :=
  ⟨SAT_dense_mem_NP_TM, NP_TM_subset_P_TM_of_SAT⟩

/-- `W` decides the membership of `x` in `L`: its first decision on `x` is `[x ∈ L]`. -/
def UDecidesAt (W : UWCC) (L : Set (List Bool)) (x : List Bool) : Prop :=
  ∃ b, W.FirstDecision x b ∧ (b = true ↔ x ∈ L)

/-- An NP-complete language is not in `P_TM` when `P_TM ≠ NP_TM`. -/
theorem not_mem_P_TM_of_npComplete {L : Set (List Bool)} (hL : NPCompleteDec L)
    (hsep : P_TM ≠ NP_TM) : L ∉ P_TM := fun h =>
  hsep (Set.Subset.antisymm P_TM_subset_NP_TM (hL.2 h))

/-- **A uniform WCC machine that is eventually correct.**  If every input gets a first decision
within `p(|x|)` rounds, and the decisions are correct for `L` on every input of length at least
`N`, then `L ∈ P_TM`. -/
theorem P_TM_of_wcc_eventually (W : UWCC) (p : Polynomial ℕ)
    (hrun : ∀ x : List Bool, ∃ t ≤ p.eval x.length,
      (∀ s < t, W.dec x.length (W.cfg x s) = none) ∧ (W.dec x.length (W.cfg x t)).isSome)
    (L : Set (List Bool)) (N : ℕ)
    (hdec : ∀ x : List Bool, N ≤ x.length → UDecidesAt W L x) :
    L ∈ P_TM := by
  let LW : Set (List Bool) := {x | W.FirstDecision x true}
  have hLW : LW ∈ P_disc := by
    refine ⟨W, p, fun x => ?_⟩
    obtain ⟨t, ht, hnone, hsome⟩ := hrun x
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨t, ht, hnone, b, hb, ?_⟩
    constructor
    · rintro rfl; exact ⟨t, hnone, hb⟩
    · intro h; exact UWCC.firstDecision_unique ⟨t, hnone, hb⟩ h
  refine P_TM_of_eventually_eq (P_disc_subset_P_TM hLW) N (fun x hx => ?_)
  obtain ⟨b, hfd, hb⟩ := hdec x hx
  constructor
  · intro hxL
    have : b = true := hb.2 hxL
    subst this
    exact hfd
  · intro hxW
    exact hb.1 (UWCC.firstDecision_unique hfd hxW)

/-- Rounds within `K'·n^d + 1` in real arithmetic are within `⌈K'⌉·n^d + 1`. -/
theorem nat_bound_of_real {t n d : ℕ} {K' : ℝ} (h : (t : ℝ) ≤ K' * (n : ℝ) ^ d + 1) :
    t ≤ ⌈K'⌉₊ * n ^ d + 1 := by
  have h1 : K' * (n : ℝ) ^ d ≤ (⌈K'⌉₊ : ℝ) * (n : ℝ) ^ d :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil K') (by positivity)
  have h2 : (t : ℝ) ≤ ((⌈K'⌉₊ * n ^ d + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast h2

variable {K CV CT CE : ℝ} {a b c : ℕ}

/-- **Theorem `thm:conditional_np_safety`, for every NP-complete language.**  Under (i)–(iii),
for every NP-complete `L` there are infinitely many input lengths `n` with an input of length `n`
on which the machine `W` does not decide `L` correctly. -/
theorem conditional_np_safety_all
    -- (iii) the classical separation
    (hsep : P_Turing ≠ NP_Turing)
    -- (i) polynomial resources and the channel-capacity bound
    (hK : 0 ≤ K) (hCV : 0 ≤ CV) (hCT : 0 ≤ CT)
    (V Tp E Nupd : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n) (hT0 : ∀ n, 0 ≤ Tp n) (hE0 : ∀ n, 0 ≤ E n)
    (hV : ∀ n, V n ≤ CV * (n : ℝ) ^ a) (hT : ∀ n, Tp n ≤ CT * (n : ℝ) ^ b)
    (hE : ∀ n, E n ≤ CE * (n : ℝ) ^ c) (hcap : ∀ n, Nupd n ≤ K * V n * Tp n * E n ^ 4)
    -- (ii) the system is a uniform WCC machine whose rounds are counted events
    (W : UWCC) (hrounds : ∀ x : List Bool, ∃ t : ℕ, (t : ℝ) ≤ Nupd x.length + 1 ∧
      (∀ s < t, W.dec x.length (W.cfg x s) = none) ∧ (W.dec x.length (W.cfg x t)).isSome)
    (L : Set (List Bool)) (hL : NPCompleteDec L) :
    ∀ N : ℕ, ∃ n ≥ N, ∃ x : List Bool, x.length = n ∧ ¬ UDecidesAt W L x := by
  have hsep' : P_TM ≠ NP_TM := by rwa [P_Turing_eq_P_TM, NP_Turing_eq_NP_TM] at hsep
  intro N
  by_contra hcon
  push_neg at hcon
  -- the step ceiling
  have hceil := phys_step_ceiling hK hCV hCT V Tp E Nupd hV0 hT0 hE0 hV hT hE hcap
  set d := a + b + 4 * c
  set K' := K * CV * CT * CE ^ 4
  have hrun : ∀ x : List Bool, ∃ t ≤ (Polynomial.C ⌈K'⌉₊ * Polynomial.X ^ d + 1).eval x.length,
      (∀ s < t, W.dec x.length (W.cfg x s) = none) ∧ (W.dec x.length (W.cfg x t)).isSome := by
    intro x
    obtain ⟨t, ht, hnone, hsome⟩ := hrounds x
    refine ⟨t, ?_, hnone, hsome⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    exact nat_bound_of_real (le_trans ht (by linarith [hceil x.length]))
  exact not_mem_P_TM_of_npComplete hL hsep'
    (P_TM_of_wcc_eventually W _ hrun L N (fun x hx => hcon x.length hx x rfl))

/-- **Theorem `thm:conditional_np_safety`.**  Under (i)–(iii) there are an NP-complete language
`L` (here `SAT_dense`) and a constant `k ≥ 1` such that, for infinitely many input lengths `n`, the
system fails to decide `L` on at least one input of length `n`. -/
theorem conditional_np_safety
    (hsep : P_Turing ≠ NP_Turing)
    (hK : 0 ≤ K) (hCV : 0 ≤ CV) (hCT : 0 ≤ CT)
    (V Tp E Nupd : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n) (hT0 : ∀ n, 0 ≤ Tp n) (hE0 : ∀ n, 0 ≤ E n)
    (hV : ∀ n, V n ≤ CV * (n : ℝ) ^ a) (hT : ∀ n, Tp n ≤ CT * (n : ℝ) ^ b)
    (hE : ∀ n, E n ≤ CE * (n : ℝ) ^ c) (hcap : ∀ n, Nupd n ≤ K * V n * Tp n * E n ^ 4)
    (W : UWCC) (hrounds : ∀ x : List Bool, ∃ t : ℕ, (t : ℝ) ≤ Nupd x.length + 1 ∧
      (∀ s < t, W.dec x.length (W.cfg x s) = none) ∧ (W.dec x.length (W.cfg x t)).isSome) :
    ∃ L : Set (List Bool), NPCompleteDec L ∧ ∃ k : ℕ, 1 ≤ k ∧
      ∀ N : ℕ, ∃ n ≥ N, ∃ x : List Bool, x.length = n ∧ ¬ UDecidesAt W L x :=
  ⟨SAT_dense, SAT_dense_npComplete, 1, le_rfl,
    conditional_np_safety_all hsep hK hCV hCT V Tp E Nupd hV0 hT0 hE0 hV hT hE hcap W hrounds
      SAT_dense SAT_dense_npComplete⟩

/-- **The equivalent form.**  Under (i), (ii) and (iii), no such machine decides an NP-complete
language on all inputs. -/
theorem no_np_complete_decider
    (hsep : P_Turing ≠ NP_Turing)
    (hK : 0 ≤ K) (hCV : 0 ≤ CV) (hCT : 0 ≤ CT)
    (V Tp E Nupd : ℕ → ℝ) (hV0 : ∀ n, 0 ≤ V n) (hT0 : ∀ n, 0 ≤ Tp n) (hE0 : ∀ n, 0 ≤ E n)
    (hV : ∀ n, V n ≤ CV * (n : ℝ) ^ a) (hT : ∀ n, Tp n ≤ CT * (n : ℝ) ^ b)
    (hE : ∀ n, E n ≤ CE * (n : ℝ) ^ c) (hcap : ∀ n, Nupd n ≤ K * V n * Tp n * E n ^ 4)
    (W : UWCC) (hrounds : ∀ x : List Bool, ∃ t : ℕ, (t : ℝ) ≤ Nupd x.length + 1 ∧
      (∀ s < t, W.dec x.length (W.cfg x s) = none) ∧ (W.dec x.length (W.cfg x t)).isSome)
    (L : Set (List Bool)) (hL : NPCompleteDec L) :
    ¬ ∀ x : List Bool, UDecidesAt W L x := by
  intro hall
  obtain ⟨n, -, x, -, hx⟩ := conditional_np_safety_all hsep hK hCV hCT V Tp E Nupd hV0 hT0 hE0
    hV hT hE hcap W hrounds L hL 0
  exact hx (hall x)

end PVNP.PartIIManuscript
