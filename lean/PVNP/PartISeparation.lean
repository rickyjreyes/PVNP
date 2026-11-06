import PVNP.PhysicalModelAudit
import PVNP.ComplexityEquivalence
import PVNP.WCCDSweepMain
import PVNP.PSubsetNP

/-!
# Part I: the separation argument, claim by claim

Literal translations of the separation statements of Part I
(*P vs NP in Curvature-Bounded Wave Computation*, revised 27 October 2026), with the
manuscript's own quantifiers.

**State-level statements.**
* `complexity_schema`: Proposition "Curvature-Confinement Complexity Schema".
* `conditional_symbolic_separation`: Theorem "Conditional Symbolic Separation" and the
  state-level part of Proposition "Model-Relative Separation in Ideal WCC".

**Language-level statements.**
* `win05`: Proposition WIN-05.
* `np_type_conditional`: Proposition "Conditional separation from a language-level barrier".
* `curv_bdd_sep`: Proposition "Conditional physical separation".
* `fixed_n_impossible`: the remark that follows it.
* `WCCDepth_iff_not_P_TM`, `WCCDDepth_iff_not_P_TM`: Conjecture `conj:wcc_depth` is
  *exactly* `L ∉ P_TM` (the manuscript: "precisely as difficult as showing P ≠ NP by proving
  3-SAT ∉ P").
* `internal_sep_conditional`: Proposition `prop:internal_sep_conditional`.
* `conditional_product_lower_bound`: Proposition `lem:lower`.
* `conditional_bridge_WCC` and `restricted_separation_schema_iff`: Proposition
  `cor:P-neq-NP-conditional`, both parts.

**Inference steps that do not hold as stated.**
* `state_separation_not_language_separation`: a verifiable, unreachable state in a model whose
  *language* classes coincide. "ψ* ∈ NP \ P" for a state does not give a separation of
  language classes.
* `accepted_language_not_in_NP_diff_P`: Conditional Turing Reduction Template, second
  conclusion. Under hypothesis (2) the accepted-target language is already in `P_TM`.
* `universal_scope_counterexample`: the "universal scope" inference. "Every machine misses some
  solution" holds for a language in `P_TM`.
* `PNP_SAT_physically_constant`: Section "Category error and physical barriers". If
  `P_TM = NP_TM`, SAT is decided in the frozen physical model at constant cost with a
  polynomial-time encoder. The claim that it "would require violating the curvature and energy
  constraints" therefore implies `P_TM ≠ NP_TM`.
* `high_K_not_poly_witness`: Conjecture "Dimensional-Lock Hypothesis". Its hypothesis (1),
  `K(ψ*) > poly`, forbids ψ* from being a polynomial-size witness.
* `trivial_partition_invariant`: Proposition `prop:collapse-grammar` (1), as literally stated.
-/

namespace PVNP.PartISeparation

open PVNP.Discrete

/-! ### Trivial machines and monotonicity of time bounds -/

/-- The machine that answers `b` at step `0`. -/
def constTM (b : Bool) : TM where
  Λ := Unit
  Γ := Bool
  blank := false
  inp := id
  start := ()
  δ := fun _ _ => none
  acc := fun _ => b
  rej := fun _ => !b

theorem constTM_out (b : Bool) (x : List Bool) (s : ℕ) : (constTM b).out x s = some b := by
  have hnext : (constTM b).next = id := by funext c; rfl
  have hrun : (constTM b).run ((constTM b).init x) s = (constTM b).init x := by
    simp only [TM.run, hnext, Function.iterate_id, id]
  simp only [TM.out, hrun, TM.ans, answerOf]
  cases b <;> rfl

theorem constTM_decides (b : Bool) (L : Set (List Bool)) (hL : ∀ x, x ∈ L ↔ b = true) :
    (constTM b).Decides L (fun _ => 0) := by
  intro x
  exact ⟨b, ⟨0, le_rfl, constTM_out b x 0, fun s hs => absurd hs (Nat.not_lt_zero _)⟩, (hL x).symm⟩

theorem univ_mem_P_TM : (Set.univ : Set (List Bool)) ∈ P_TM :=
  ⟨constTM true, 0, by simpa using constTM_decides true Set.univ (fun _ => by simp)⟩

theorem empty_mem_P_TM : (∅ : Set (List Bool)) ∈ P_TM :=
  ⟨constTM false, 0, by simpa using constTM_decides false ∅ (fun _ => by simp)⟩

theorem empty_mem_NP_TM : (∅ : Set (List Bool)) ∈ NP_TM :=
  P_TM_subset_NP_TM empty_mem_P_TM

theorem FirstAnswer.mono {out : ℕ → Option Bool} {T T' : ℕ} {b : Bool} (h : FirstAnswer out T b)
    (hT : T ≤ T') : FirstAnswer out T' b := by
  obtain ⟨s, hs, h1, h2⟩ := h
  exact ⟨s, hs.trans hT, h1, h2⟩

theorem DecidesAt.mono {out : ℕ → Option Bool} {T T' : ℕ} {x : List Bool} {L : Set (List Bool)}
    (h : DecidesAt out T x L) (hT : T ≤ T') : DecidesAt out T' x L := by
  obtain ⟨b, hb, hL⟩ := h
  exact ⟨b, FirstAnswer.mono hb hT, hL⟩

/-- A bound that is eventually below `p` is everywhere below `p + C`. -/
theorem eventually_poly_bound (T : ℕ → ℕ) (p : Polynomial ℕ) (N : ℕ)
    (h : ∀ n, N ≤ n → T n ≤ p.eval n) :
    ∀ n, T n ≤ (p + Polynomial.C ((Finset.range N).sup T)).eval n := by
  intro n
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  by_cases hn : N ≤ n
  · exact le_trans (h n hn) (Nat.le_add_right _ _)
  · exact le_trans (Finset.le_sup (Finset.mem_range.2 (by omega))) (Nat.le_add_left _ _)

/-! ### State-level schemata (Proposition "Complexity Schema", Theorem "Conditional Symbolic
Separation") -/

/-- A state-construction model: machines that produce states, a polynomial-time predicate on
machines, and a verification predicate on states. -/
structure ConstructionModel where
  State : Type
  Machine : Type
  polyTime : Machine → Prop
  produces : Machine → State → Prop
  verifiable : State → Prop

namespace ConstructionModel

variable (M : ConstructionModel)

/-- States constructible by a polynomial-time machine (`P_WCC^phys` at state level). -/
def Pst : Set M.State := {ψ | ∃ m, M.polyTime m ∧ M.produces m ψ}

/-- Verifiable states (`NP_WCC^phys` at state level). -/
def NPst : Set M.State := {ψ | M.verifiable ψ}

end ConstructionModel

/-- **Proposition "Curvature-Confinement Complexity Schema in Physical WCC" (Part I).**
(1) `C(ψ*)` exceeds the achievable bound of every polynomial-time machine;
(2) `ψ*` is verifiable.  Then `ψ* ∈ NP \ P` and the state classes differ. -/
theorem complexity_schema (M : ConstructionModel) (C : M.State → ℝ) (ψ : M.State)
    (h1 : ∀ m, M.polyTime m → ∃ T : ℝ, (∀ φ, M.produces m φ → C φ ≤ T) ∧ T < C ψ)
    (h2 : M.verifiable ψ) : ψ ∈ M.NPst \ M.Pst ∧ M.Pst ≠ M.NPst := by
  have hP : ψ ∉ M.Pst := by
    rintro ⟨m, hm, hprod⟩
    obtain ⟨T, hT, hlt⟩ := h1 m hm
    exact absurd (hT ψ hprod) (not_le.2 hlt)
  exact ⟨⟨h2, hP⟩, fun he => hP (he ▸ h2)⟩

/-- **Theorem "Conditional Symbolic Separation in Physical WCC" (Part I)** (and the state-level
part of Proposition "Model-Relative Separation in Ideal WCC").  If `ψ*` is verifiable and no
polynomial-time machine constructs it, then `ψ* ∈ NP \ P` and the state classes differ. -/
theorem conditional_symbolic_separation (M : ConstructionModel) (ψ : M.State)
    (h1 : M.verifiable ψ) (h2 : ∀ m, M.polyTime m → ¬ M.produces m ψ) :
    ψ ∈ M.NPst \ M.Pst ∧ M.Pst ≠ M.NPst := by
  have hP : ψ ∉ M.Pst := fun ⟨m, hm, hprod⟩ => h2 m hm hprod
  exact ⟨⟨h1, hP⟩, fun he => hP (he ▸ h1)⟩

/-! ### Language-level conditional separations -/

/-- A physical resource semantics, fixed once for deciders and verifiers: admissible deciders,
their resources (time, curvature, energy, …) per input, and physical NP membership. -/
structure PhysSemantics where
  Dec : Type
  decides : Dec → Set (List Bool) → Prop
  Res : Type
  cost : Dec → Res → List Bool → ℕ
  NPphys : Set (Set (List Bool))

namespace PhysSemantics

variable (S : PhysSemantics)

/-- `P^phys`: some admissible decider meets polynomial rails for every resource on every input. -/
def Pphys : Set (Set (List Bool)) :=
  {L | ∃ D, S.decides D L ∧ ∃ p : S.Res → Polynomial ℕ, ∀ r x, S.cost D r x ≤ (p r).eval x.length}

/-- Every admissible deterministic decider of `L` exceeds at least one polynomial resource rail
on arbitrarily large inputs. -/
def Hard (L : Set (List Bool)) : Prop :=
  ∀ D, S.decides D L → ∀ p : S.Res → Polynomial ℕ, ∀ N : ℕ,
    ∃ x : List Bool, N ≤ x.length ∧ ∃ r, (p r).eval x.length < S.cost D r x

theorem not_mem_Pphys_of_hard (L : Set (List Bool)) (h : S.Hard L) : L ∉ S.Pphys := by
  rintro ⟨D, hD, p, hp⟩
  obtain ⟨x, -, r, hr⟩ := h D hD p 0
  exact absurd (hp r x) (not_le.2 hr)

end PhysSemantics

/-- **Proposition WIN-05 (`thm:pwcc-neq-npwcc`, Part I).** -/
theorem win05 (S : PhysSemantics) (L : Set (List Bool)) (hv : L ∈ S.NPphys) (h : S.Hard L) :
    S.Pphys ≠ S.NPphys := fun he => S.not_mem_Pphys_of_hard L h (he ▸ hv)

/-- **Proposition "Conditional separation from a language-level barrier"
(`thm:np-type-conditional`, Part I).** -/
theorem np_type_conditional (S : PhysSemantics) (L : Set (List Bool)) (hv : L ∈ S.NPphys)
    (h : S.Hard L) : L ∈ S.NPphys \ S.Pphys := ⟨hv, S.not_mem_Pphys_of_hard L h⟩

/-- **Proposition "Conditional physical separation" (`thm:curv-bdd-sep`, Part I).**  Premise (1)
is physical NP membership; premise (2) is the asymptotic hardness against every decider and
every polynomial (the input threshold may depend on both). -/
theorem curv_bdd_sep (S : PhysSemantics) (L : Set (List Bool)) (h1 : L ∈ S.NPphys)
    (h2 : S.Hard L) : L ∈ S.NPphys \ S.Pphys := np_type_conditional S L h1 h2

/-- **Remark after `thm:curv-bdd-sep`.**  At one fixed input length, no finite cost exceeds every
polynomial bound. -/
theorem fixed_n_impossible (c n : ℕ) : ¬ ∀ p : Polynomial ℕ, p.eval n < c := by
  intro h
  have := h (Polynomial.C c)
  simp at this

/-! ### Conjecture `conj:wcc_depth` and the conditional internal separation -/

/-- **Conjecture `conj:wcc_depth`** for a language `L` in the uniform discrete (1-D) WCC model:
every machine deciding `L` exceeds every polynomial on infinitely many input lengths. -/
def WCCDepth (L : Set (List Bool)) : Prop :=
  ∀ (A : WCC) (T : ℕ → ℕ), A.Decides L T → ∀ p : Polynomial ℕ, ∀ N : ℕ, ∃ n, N ≤ n ∧ p.eval n < T n

theorem WCC.Decides.mono {A : WCC} {L : Set (List Bool)} {T T' : ℕ → ℕ} (h : A.Decides L T)
    (hT : ∀ n, T n ≤ T' n) : A.Decides L T' := fun x => DecidesAt.mono (h x) (hT _)

theorem WCCDepth_iff_not_P_WCC (L : Set (List Bool)) : WCCDepth L ↔ L ∉ P_WCC := by
  constructor
  · rintro h ⟨A, p, hA⟩
    obtain ⟨n, -, hn⟩ := h A _ hA p 0
    exact lt_irrefl _ hn
  · intro hL A T hA p N
    by_contra hc
    push_neg at hc
    exact hL ⟨A, _, WCC.Decides.mono hA (eventually_poly_bound T p N hc)⟩

/-- **`conj:wcc_depth` is exactly `L ∉ P_TM`** ("precisely as difficult as showing `P ≠ NP` by
proving that 3-SAT is not in `P`"). -/
theorem WCCDepth_iff_not_P_TM (L : Set (List Bool)) : WCCDepth L ↔ L ∉ P_TM := by
  rw [WCCDepth_iff_not_P_WCC, P_WCC_eq_P_TM]

/-- `conj:wcc_depth` on the lattice `ℤ^(1+d)` (radius-one Moore neighbourhood). -/
def WCCDDepth (d : ℕ) (L : Set (List Bool)) : Prop :=
  ∀ (A : WCCD d) (T : ℕ → ℕ), A.Decides L T → ∀ p : Polynomial ℕ, ∀ N : ℕ, ∃ n, N ≤ n ∧ p.eval n < T n

theorem WCCDDepth_iff_not_P_TM (d : ℕ) (L : Set (List Bool)) : WCCDDepth d L ↔ L ∉ P_TM := by
  rw [← P_WCCD_eq_P_TM d]
  constructor
  · rintro h ⟨A, p, hA⟩
    obtain ⟨n, -, hn⟩ := h A _ hA p 0
    exact lt_irrefl _ hn
  · intro hL A T hA p N
    by_contra hc
    push_neg at hc
    exact hL ⟨A, _, fun x => DecidesAt.mono (hA x) (eventually_poly_bound T p N hc _)⟩

/-- **Proposition `prop:internal_sep_conditional` (Part I).**  If Conjecture `conj:wcc_depth`
holds for a language `L ∈ NP_WCC`, then `L ∈ NP_WCC \ P_WCC`, `P_WCC ⊊ NP_WCC`, and (with the
kernel-checked equalities `P_WCC = P_TM`, `NP_WCC = NP_TM`) `P_TM ≠ NP_TM`. -/
theorem internal_sep_conditional (L : Set (List Bool)) (hL : L ∈ NP_WCC) (h : WCCDepth L) :
    L ∈ NP_WCC \ P_WCC ∧ P_WCC ⊂ NP_WCC ∧ P_TM ≠ NP_TM := by
  have hP : L ∉ P_WCC := (WCCDepth_iff_not_P_WCC L).1 h
  refine ⟨⟨hL, hP⟩, ⟨P_WCC_subset_NP_WCC, fun hsub => hP (hsub hL)⟩, fun he => hP ?_⟩
  rw [P_WCC_eq_P_TM, he, ← NP_WCC_eq_NP_TM]
  exact hL

/-- The instance used in Part I: SAT (dense CNF encoding), which lies in `NP_WCC`. -/
theorem internal_sep_SAT (h : WCCDepth SATV.SAT_dense) :
    SATV.SAT_dense ∈ NP_WCC \ P_WCC ∧ P_WCC ⊂ NP_WCC ∧ P_TM ≠ NP_TM :=
  internal_sep_conditional _ SATV.SAT_dense_mem_NP_WCC h

/-! ### Proposition `lem:lower`: conditional product of two lower bounds -/

open scoped ENNReal

/-- The data of Part I §"Semantic Curvature Complexity": admissible algorithms, their trajectories
and step counts, a nonnegative per-state functional `Φ`, and the separator measure of a state. -/
structure CurvModel where
  State : Type
  Alg : Type
  decides : Alg → Set (List Bool) → Prop
  steps : Alg → List Bool → ℕ
  traj : Alg → List Bool → ℕ → State
  Φ : State → ℝ≥0∞
  area : State → ℝ≥0∞

namespace CurvModel

variable (W : CurvModel)

/-- `Cost_Θ(M, x) = Σ_{t ≤ T_M(x)} Φ(ψ^t_{M,x})`. -/
noncomputable def Cost (M : W.Alg) (x : List Bool) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range (W.steps M x + 1), W.Φ (W.traj M x t)

/-- `C_{Θ,𝔚}(L, n) = inf_{M decides L} max_{|x| ≤ n} Cost_Θ(M, x)` (empty infimum `= +∞`). -/
noncomputable def Ccost (L : Set (List Bool)) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (M : W.Alg) (_ : W.decides M L), ⨆ (x : List Bool) (_ : x.length ≤ n), W.Cost M x

end CurvModel

/-- **Proposition `lem:lower` (Part I).**  Under the uniform interface price
`Φ ≥ κ₀ · area` (Hypothesis `lem:separator-price`) and the interface growth
`area ≥ c₀ 2^{γn}` incurred on at least one step of a worst-case input of every admissible decider
(Hypothesis `prop:locked-expander-full`), the semantic curvature cost is at least
`κ₀ c₀ 2^{γn}`. -/
theorem conditional_product_lower_bound (W : CurvModel) (L : Set (List Bool)) (n : ℕ)
    (κ₀ B : ℝ≥0∞)
    (hprice : ∀ M x t, W.decides M L → κ₀ * W.area (W.traj M x t) ≤ W.Φ (W.traj M x t))
    (hgrowth : ∀ M, W.decides M L → ∃ x : List Bool, x.length ≤ n ∧
      ∃ t ≤ W.steps M x, B ≤ W.area (W.traj M x t)) :
    κ₀ * B ≤ W.Ccost L n := by
  unfold CurvModel.Ccost
  refine le_iInf₂ fun M hM => ?_
  obtain ⟨x, hx, t, ht, hB⟩ := hgrowth M hM
  refine le_trans ?_ (le_iSup₂_of_le x hx le_rfl)
  calc κ₀ * B ≤ κ₀ * W.area (W.traj M x t) := mul_le_mul_left' hB _
    _ ≤ W.Φ (W.traj M x t) := hprice M x t hM
    _ ≤ W.Cost M x := by
      unfold CurvModel.Cost
      exact Finset.single_le_sum (f := fun t => W.Φ (W.traj M x t)) (fun _ _ => zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le ht))

/-! ### Proposition `cor:P-neq-NP-conditional` -/

/-- **Proposition `cor:P-neq-NP-conditional`, first part.**  For the same discrete classes, the
identifications (here kernel-checked) turn a separation into `P ≠ NP`. -/
theorem conditional_bridge_WCC (h : P_WCC ≠ NP_WCC) : P_TM ≠ NP_TM :=
  fun he => h (p_vs_np_discrete_transfer.2 he)

theorem conditional_bridge_WCCD (d : ℕ) (h : P_WCCD d ≠ NPOf (P_WCCD d)) : P_TM ≠ NP_TM := by
  intro he
  apply h
  rw [P_WCCD_eq_P_TM]
  exact he

/-- **Proposition `cor:P-neq-NP-conditional`, second part.**  The principle "a separation of
restricted subclasses of `P_TM`, `NP_TM` implies `P ≠ NP`" is *equivalent* to `P ≠ NP`: a
restricted separation always exists (`∅ ⊊ {∅}`), so the principle cannot be used without a
class-identification theorem. -/
theorem restricted_separation_schema_iff :
    (∀ Pp NPp : Set (Set (List Bool)), Pp ⊆ P_TM → NPp ⊆ NP_TM → Pp ≠ NPp → P_TM ≠ NP_TM) ↔
      P_TM ≠ NP_TM := by
  constructor
  · intro h
    refine h ∅ {∅} (Set.empty_subset _) ?_ ?_
    · intro L hL
      rw [Set.mem_singleton_iff] at hL
      rw [hL]
      exact empty_mem_NP_TM
    · exact (Set.singleton_nonempty _).ne_empty.symm
  · intro h _ _ _ _ _
    exact h

/-! ### Inference steps that do not hold as stated -/

theorem NPOf_univ : NPOf (Set.univ : Set (Set (List Bool))) = Set.univ := by
  ext L
  simp only [Set.mem_univ, iff_true]
  refine ⟨{y | ∃ x ∈ L, y = pair x []}, Set.mem_univ _, 0, fun x => ⟨fun hx => ⟨[], by simp, x, hx, rfl⟩, ?_⟩⟩
  rintro ⟨w, -, x', hx', he⟩
  rw [(pair_injective he).1]
  exact hx'

/-- **State-level separation does not give a language-level separation.**  In the frozen WCT
plane-wave model the state `ψ*` of amplitude `1` passes the local test `‖ψ*(0,0)‖ = 1` and is
never reached from the trivial state (amplitude is conserved), yet the language classes with
the same (unrestricted) encoding semantics coincide: `P^phys = NP^phys` (both are all
languages).  Hence "ψ* ∈ NP \ P" for a *state* (Theorem "Conditional Symbolic Separation",
Propositions "Model-Relative Separation in Ideal WCC" and "Formal Model-Theoretic Separation")
does not by itself separate language classes. -/
theorem state_separation_not_language_separation (κ β γ : ℝ) :
    (∃ ψstar : ℝ × ℝ → ℂ, ‖ψstar (0, 0)‖ = 1 ∧ ∀ t, PhysicalAudit.field κ β γ 0 t ≠ ψstar) ∧
      PhysicalAudit.PhysConst κ β γ Set.univ = NPOf (PhysicalAudit.PhysConst κ β γ Set.univ) := by
  refine ⟨⟨PhysicalAudit.field κ β γ 1 0, ?_, fun t h => ?_⟩, ?_⟩
  · have := PhysicalAudit.readout_eq κ β γ 1 0
    simpa [PhysicalAudit.readout] using this
  · have h0 := PhysicalAudit.readout_eq κ β γ 0 t
    have h1 := PhysicalAudit.readout_eq κ β γ 1 0
    simp only [PhysicalAudit.readout] at h0 h1
    rw [h] at h0
    rw [h0] at h1
    simp at h1
  · rw [PhysicalAudit.unrestricted_encoder_trivializes, NPOf_univ]

/-- **Conditional Turing Reduction Template, second conclusion.**  Hypothesis (2) makes the
acceptance predicate polynomial-time computable; the language of accepted target encodings is
then in `P_TM`, so it never lies in `NP_TM \ P_TM`. -/
theorem accepted_language_not_in_NP_diff_P (Acc : Set (List Bool)) (h2 : Acc ∈ P_TM) :
    Acc ∉ NP_TM \ P_TM := fun h => h.2 h2

/-- **"Universal scope" inference.**  For the accept-all verifier, every deterministic printer
misses some witness of some instance at every length, yet the language (all strings) is in
`P_TM`.  So "every polynomial-time machine fails to print some solution" does not imply that the
language is outside `P`. -/
theorem universal_scope_counterexample :
    (∀ out : ℕ → List Bool, ∀ n : ℕ, ∃ x : List Bool, x.length = n ∧
      ∃ w : List Bool, w.length ≤ 1 ∧ out n ≠ w) ∧
      {x : List Bool | ∃ w : List Bool, w.length ≤ 1} ∈ P_TM := by
  refine ⟨fun out n => ⟨List.replicate n false, by simp, ?_⟩, ?_⟩
  · by_cases h : out n = []
    · exact ⟨[true], by simp, by rw [h]; simp⟩
    · exact ⟨[], by simp, h⟩
  · have : {x : List Bool | ∃ w : List Bool, w.length ≤ 1} = Set.univ :=
      Set.eq_univ_of_forall fun _ => ⟨[], by simp⟩
    rw [this]
    exact univ_mem_P_TM

/-- **Section "Category error and physical barriers".**  If `P_TM = NP_TM`, SAT is decided in the
frozen physical model at constant mass, zero curvature energy and two final states, with a
polynomial-time (charged) indicator encoder. -/
theorem PNP_SAT_physically_constant (κ β γ : ℝ) (h : P_TM = NP_TM) :
    SATV.SAT_dense ∈ PhysicalAudit.PhysConst κ β γ PhysicalAudit.polyEnc := by
  rw [PhysicalAudit.PhysConst_polyEnc_eq_P_TM, h]
  exact SATV.SAT_dense_mem_NP_TM

/-- The claim "even if `P = NP`, any algorithm for SAT would violate the WCT rails", read in this
model, already implies `P_TM ≠ NP_TM`. -/
theorem category_error_claim_implies_classical (κ β γ : ℝ)
    (claim : P_TM = NP_TM → SATV.SAT_dense ∉ PhysicalAudit.PhysConst κ β γ PhysicalAudit.polyEnc) :
    P_TM ≠ NP_TM := fun h => claim h (PNP_SAT_physically_constant κ β γ h)

/-- Description-length complexity of `s` for a (partial) description method `D`. -/
noncomputable def Kc (D : List Bool → Option (List Bool)) (s : List Bool) : ℕ :=
  sInf {k | ∃ d : List Bool, d.length = k ∧ D d = some s}

theorem Kc_le (D : List Bool → Option (List Bool)) (c : ℕ)
    (hD : ∀ s, ∃ d, D d = some s ∧ d.length ≤ s.length + c) (s : List Bool) :
    Kc D s ≤ s.length + c := by
  obtain ⟨d, hd, hl⟩ := hD s
  exact le_trans (Nat.sInf_le ⟨d, rfl, hd⟩) hl

/-- **Conjecture "Dimensional-Lock Hypothesis (Physical Model)", hypothesis (1).**  For any
description method that contains the literal description (overhead `c`),
`K(ψ*) > q(n) + c` forces `|ψ*| > q(n)`: such a ψ* is not a polynomial-size witness. -/
theorem high_K_not_poly_witness (D : List Bool → Option (List Bool)) (c : ℕ)
    (hD : ∀ s, ∃ d, D d = some s ∧ d.length ≤ s.length + c) (q : Polynomial ℕ) (n : ℕ)
    (s : List Bool) (hK : q.eval n + c < Kc D s) : q.eval n < s.length := by
  have := Kc_le D c hD s
  omega

/-- **Proposition `prop:collapse-grammar`, item (1), as literally stated.**  For every evolution
there *is* a finite partition of the state space invariant under it (the one-block partition),
so (1) requires an unstated non-triviality condition on "metastable symbols". -/
theorem trivial_partition_invariant {X : Type*} (F : X → X) :
    ∃ (S : Type) (_ : Fintype S) (σ : X → S), ∀ x, σ (F x) = σ x :=
  ⟨Unit, inferInstance, fun _ => (), fun _ => rfl⟩

/-!
## I-10 (amended): conditional obstruction to nontrivial invariant symbols

A relation of *possible observed transitions* with a common one-step successor
for every pair of configurations cannot preserve a nonconstant symbolic readout.
No statement here deduces the common-successor property from high curvature,
asserts that trajectory languages are trivial, or proves rule unidentifiability.
The original one-block counterexample remains above.
-/

/-- The common-successor property of a possibly nondeterministic observable
transition relation. It is a substantive hypothesis, not implied by the
curvature threshold on a deterministic WCT flow. -/
def CommonSuccessor {X : Type*} (R : X → X → Prop) : Prop :=
  ∀ x y : X, ∃ z : X, R x z ∧ R y z

/-- A symbol preserved along every allowed transition must be constant if all
pairs of states share an allowed successor. -/
theorem invariant_constant_of_common_successor {X S : Type*}
    (R : X → X → Prop) (σ : X → S) (hCommon : CommonSuccessor R)
    (hInv : ∀ x y : X, R x y → σ x = σ y) :
    ∀ x y : X, σ x = σ y := by
  intro x y
  obtain ⟨z, hxz, hyz⟩ := hCommon x y
  exact (hInv x z hxz).trans (hInv y z hyz).symm

/-- **Corrected Part I proposition I-10.** No *nonconstant* partition is
pathwise invariant under a relation with the common-successor property.
The statement is stronger than finite alphabet because the target
type S is unrestricted. -/
theorem no_nontrivial_invariant_of_common_successor {X S : Type*}
    (R : X → X → Prop) (σ : X → S) (hCommon : CommonSuccessor R)
    (hNontrivial : ∃ x y : X, σ x ≠ σ y) :
    ¬ ∀ x y : X, R x y → σ x = σ y := by
  intro hInv
  obtain ⟨x, y, hneq⟩ := hNontrivial
  exact hneq (invariant_constant_of_common_successor R σ hCommon hInv x y)

end PVNP.PartISeparation
