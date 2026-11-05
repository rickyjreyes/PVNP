import PVNP.UniformSimMain

/-!
# Part II: the uniform discrete WCC model is equivalent to Turing machines

The sweep program `UniformSim.Spec.prog` simulates any uniform machine `W` of `def:wcc_machine`
(`PartIIUniform.UWCC`): it runs the lattice algorithm and the encoder, loads `C_0`, and then
alternates the decoder with synchronous rounds of the local rule (`UniformSim.Spec.round_spec`).
The compiler `Prog.toTM` turns it into an ordinary single-tape Turing machine.

* `wcc_to_tm`: **`thm:wcc_to_tm` for the uniform model**: an explicit machine `M_W` and a
  polynomial `q_W` with `T_{M_W}(x) ≤ q_W(|x| + T_W(x) + 1)` and the same first answer.
* `P_disc_subset_P_TM`, **`P_disc_eq_P_TM`**: `P^{disc}_{WCC} = P_TM`.
* `NP_disc` (**`def:wcc_verifier`, `def:npwcc`**) and **`NP_disc_eq_NP_TM`** (`thm:np_equiv`).

Reading of `def:wcc_verifier` (binary alphabets, pairs encoded by `pair`): the verifier is a
uniform machine run on the input word `pair x y`; its lattice for that word has at most `p(N)`
cells when `|y| ≤ q(|x|)`, `N = |x| + |y|`; its first decision appears within `p(N)` updates on
every pair (the runtime scaling of `def:tm_verifier`, which bounds the verifier on all pairs);
and `V(x,y)` accepts when its first decision is `1` (the first-halting-output convention of
`def:pwcc`).
-/

namespace PVNP.PartIIUniform

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.UniformSim

/-- The simulation data of a uniform machine, with the format guard on or off. -/
theorem exists_spec (W : UWCC) (guard : Bool) :
    ∃ (σ : Spec) (_ : σ.Correct), σ.W = W ∧ σ.guard = guard := by
  obtain ⟨ML, pL, hL⟩ := W.lat_fp
  obtain ⟨ME, pE, hE⟩ := W.enc_fp
  obtain ⟨MD, pD, hD⟩ := W.dec_fp
  exact ⟨⟨W, ML, ME, MD, guard⟩, ⟨pL, pE, pD, hL, hE, hD⟩, rfl, rfl⟩

/-- The first decision of `W` on the input `z` is `b`. -/
def UWCC.FirstDecision (W : UWCC) (z : List Bool) (b : Bool) : Prop :=
  ∃ t, (∀ s < t, W.dec z.length (W.cfg z s) = none) ∧ W.dec z.length (W.cfg z t) = some b

theorem UWCC.firstDecision_unique {W : UWCC} {z : List Bool} {b b' : Bool}
    (h : W.FirstDecision z b) (h' : W.FirstDecision z b') : b = b' := by
  obtain ⟨t, hn, hb⟩ := h
  obtain ⟨t', hn', hb'⟩ := h'
  rcases lt_trichotomy t t' with hlt | rfl | hgt
  · rw [hn' t hlt] at hb; cases hb
  · rw [hb] at hb'; exact Option.some.inj hb'
  · rw [hn t' hgt] at hb'; cases hb'

/-- **`thm:wcc_to_tm` (uniform model).**  For every uniform machine `W` there are an ordinary
single-tape Turing machine `M_W`, compiled from an explicit sweep program, and a polynomial `q_W`
such that whenever the decoder of `W` first outputs `some b` at time `t` on `x`, the machine
`M_W` first answers `b` within `q_W(|x| + t + 1)` steps. -/
theorem wcc_to_tm (W : UWCC) :
    ∃ (M : TM) (q : Polynomial ℕ), ∀ (x : List Bool) (t : ℕ) (b : Bool),
      (∀ s < t, W.dec x.length (W.cfg x s) = none) → W.dec x.length (W.cfg x t) = some b →
        FirstAnswer (M.out x) (q.eval (x.length + t + 1)) b := by
  obtain ⟨σ, hC, rfl, hg⟩ := exists_spec W false
  exact ⟨σ.prog.toTM, σ.timePoly hC, fun x t b hn hb =>
    σ.toTM_firstAnswer_of_dec hC x (Or.inl hg) t hn b hb⟩

/-- **`P^{disc}_{WCC} ⊆ P_TM`** for the uniform model of `def:wcc_machine`. -/
theorem P_disc_subset_P_TM : P_disc ⊆ P_TM := by
  rintro L ⟨W, p, hW⟩
  obtain ⟨M, q, hM⟩ := wcc_to_tm W
  refine ⟨M, q.comp (Polynomial.X + p + 1), fun x => ?_⟩
  obtain ⟨t, htp, hnone, b, hb, hbL⟩ := hW x
  obtain ⟨s, hs, h1, h2⟩ := hM x t b hnone hb
  refine ⟨b, ⟨s, le_trans hs ?_, h1, h2⟩, hbL⟩
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  exact eval_mono_nat q (by omega)

/-- **`P^{disc}_{WCC} = P_TM`** for the uniform model of `def:wcc_machine`
(`cor:pwcc_equals_pturing`, with the corrected `def:pturing`: `P_Turing = P_TM`). -/
theorem P_disc_eq_P_TM : P_disc = P_TM :=
  Set.Subset.antisymm P_disc_subset_P_TM P_TM_subset_P_disc

/-! ## Uniform WCC verifiers -/

/-- **Definitions `def:wcc_verifier` and `def:npwcc`.**  `L ∈ NP^{disc}_{WCC}` when a uniform
machine `V` and polynomials `p, q` exist such that, with `N = |x| + |y|`:
* for `|y| ≤ q(|x|)`, the lattice of the input `pair x y` has at most `p(N)` cells;
* on every pair, the first decision appears within `p(N)` updates;
* `x ∈ L` iff some witness `y` with `|y| ≤ q(|x|)` makes the first decision `1`. -/
def NP_disc : Set (Set (List Bool)) :=
  {L | ∃ (V : UWCC) (p q : Polynomial ℕ),
    (∀ x y : List Bool, y.length ≤ q.eval x.length →
      (V.Λ (pair x y).length).ncard ≤ p.eval (x.length + y.length)) ∧
    (∀ x y : List Bool, ∃ t ≤ p.eval (x.length + y.length),
      (∀ s < t, V.dec (pair x y).length (V.cfg (pair x y) s) = none) ∧
        V.dec (pair x y).length (V.cfg (pair x y) t) ≠ none) ∧
    ∀ x, (x ∈ L ↔ ∃ y : List Bool, y.length ≤ q.eval x.length ∧ V.FirstDecision (pair x y) true)}

/-- **`NP^{disc}_{WCC} ⊆ NP_TM`.** -/
theorem NP_disc_subset_NP_TM : NP_disc ⊆ NP_TM := by
  rintro L ⟨V, p, q, -, hrun, hL⟩
  obtain ⟨σ, hC, rfl, hg⟩ := exists_spec V true
  -- the verifier language, decided by the guarded simulation
  let Lv : Set (List Bool) := {z | PS.run .tag z = .ok ∧ σ.W.FirstDecision z true}
  have hLv : Lv ∈ P_TM := by
    refine ⟨σ.prog.toTM, (σ.timePoly hC).comp (Polynomial.X + p + 1) + 2 * Polynomial.X + 5,
      fun z => ?_⟩
    by_cases hok : PS.run .tag z = .ok
    · obtain ⟨x, y, rfl⟩ := PS.run_eq_ok z hok
      obtain ⟨t, htp, hnone, hdec⟩ := hrun x y
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hdec
      have hfa := σ.toTM_firstAnswer_of_dec hC (pair x y) (Or.inr hok) t hnone b hb
      obtain ⟨s, hs, h1, h2⟩ := hfa
      refine ⟨b, ⟨s, le_trans hs ?_, h1, h2⟩, ?_⟩
      · have hxy : x.length + y.length ≤ (pair x y).length := by rw [pair_length]; omega
        have ht : t ≤ p.eval (pair x y).length := le_trans htp (eval_mono_nat p hxy)
        simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X,
          Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_ofNat]
        have := eval_mono_nat (σ.timePoly hC) (show (pair x y).length + t + 1 ≤
          (pair x y).length + p.eval (pair x y).length + 1 by omega)
        omega
      · constructor
        · intro hbt
          subst hbt
          exact ⟨hok, t, hnone, hb⟩
        · rintro ⟨-, hfd⟩
          exact UWCC.firstDecision_unique ⟨t, hnone, hb⟩ hfd
    · obtain ⟨C, hH, hCle⟩ := σ.sim_invalid z hg hok
      obtain ⟨s, hs, h1, h2⟩ := Prog.toTM_firstAnswer σ.prog z hH
      refine ⟨false, ⟨s, le_trans hs ?_, h1, h2⟩, ?_⟩
      · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_ofNat]
        omega
      · simp only [Bool.false_eq_true, false_iff]
        exact fun h => hok h.1
  refine ⟨Lv, hLv, q, fun x => ?_⟩
  rw [hL x]
  exact exists_congr fun y => and_congr_right fun _ =>
    ⟨fun h => ⟨PS.run_pair x y, h⟩, fun h => h.2⟩

/-- **`NP_TM ⊆ NP^{disc}_{WCC}`.** -/
theorem NP_TM_subset_NP_disc : NP_TM ⊆ NP_disc := by
  intro L hL
  obtain ⟨V, p, q, hV, hLV⟩ := NP_TM_subset_NP_Turing hL
  obtain ⟨c, k, hc, hk, hle⟩ := poly_le_cmax (2 * Polynomial.X + 2 + p)
  have hT : ∀ z, V.guard.HaltsWithin z (c * max z.length 1 ^ k) := by
    intro z
    have hbound : 2 * z.length + 2 + p.eval z.length ≤ c * max z.length 1 ^ k := by
      have := hle z.length
      simpa using this
    by_cases hok : PS.run .tag z = .ok
    · obtain ⟨x, w, rfl⟩ := PS.run_eq_ok z hok
      have hxw : x.length + w.length ≤ (pair x w).length := by rw [pair_length]; omega
      refine V.guard.haltsWithin_mono (V.guard_valid hok (hV x w)).1 ?_
      have := eval_mono_nat p hxw
      omega
    · exact V.guard.haltsWithin_mono (V.guard_invalid hok) (by omega)
  have hdec : ∀ n C, (oneCell V.guard c k hT).dec n C = some (C 0) := fun _ _ => rfl
  have hc0 : ∀ z, (oneCell V.guard c k hT).cfg z 0 0 = (oneCell V.guard c k hT).enc z 0 := by
    intro z
    show (oneCell V.guard c k hT).init z 0 = _
    unfold UWCC.init
    rw [if_pos]
    exact Set.mem_singleton _
  have henc : ∀ z, (oneCell V.guard c k hT).enc z 0 = true ↔ V.guard.Accepts z :=
    fun z => @decide_eq_true_iff (V.guard.Accepts z) (Classical.propDecidable _)
  have hfd : ∀ z b, (oneCell V.guard c k hT).FirstDecision z b ↔ (b = true ↔ V.guard.Accepts z) := by
    intro z b
    constructor
    · rintro ⟨t, hn, hb⟩
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        rw [hdec, hc0] at hb
        rw [← Option.some.inj hb]
        exact henc z
      · have := hn 0 h0
        rw [hdec] at this
        cases this
    · intro hb
      refine ⟨0, fun s hs => absurd hs (Nat.not_lt_zero _), ?_⟩
      rw [hdec, hc0]
      congr 1
      exact Bool.eq_iff_iff.2 ((henc z).trans hb.symm)
  refine ⟨oneCell V.guard c k hT, 1, q, fun x y _ => ?_, fun x y => ⟨0, by simp,
    fun s hs => absurd hs (Nat.not_lt_zero _), by rw [hdec]; simp⟩, fun x => ?_⟩
  · show ({0} : Set (Fin 1 → ℤ)).ncard ≤ _
    simp
  · rw [hLV x]
    refine exists_congr fun y => and_congr_right fun _ => ?_
    rw [hfd, iff_true_left rfl]
    obtain ⟨B, hB⟩ : ∃ B, V.HaltsWithin (pair x y) B := ⟨_, hV x y⟩
    exact (V.guard_valid (PS.run_pair x y) hB).2.symm

/-- **`thm:np_equiv` for the uniform model: `NP^{disc}_{WCC} = NP_TM`.** -/
theorem NP_disc_eq_NP_TM : NP_disc = NP_TM :=
  Set.Subset.antisymm NP_disc_subset_NP_TM NP_TM_subset_NP_disc

end PVNP.PartIIUniform
