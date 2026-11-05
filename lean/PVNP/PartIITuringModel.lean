import PVNP.PSubsetNP

/-!
# Part II, Definitions `def:tm`, `def:pturing`, `def:tm_verifier`, `def:npturing`

Literal translation of the manuscript's Turing-machine model and its comparison with the
repository model `PVNP.Discrete.TM`.

**The manuscript's machine (`def:tm`).**  `M = (Q, Γ, Σ, δ, q₀, q_acc, q_rej)` with finite `Q`
and `Γ`, a blank `␣ ∈ Γ`, an input alphabet `Σ ⊆ Γ \ {␣}`, a **total** transition function
`δ : Q × Γ → Q × Γ × {L, R}` (no stay move), and halting states `q_acc`, `q_rej`.  One step
applies `δ(q, γ(h))`.  The input `x₁…x_n` occupies cells `0, …, n−1` with the head on cell `0`
(the convention of `def:wm`).  `T_M(x)` is the first time a halting state is entered, and `M`
accepts `x` when that halting state is `q_acc`.  Here `Σ = {0,1}` (`MTM.inp` is injective and
avoids the blank), matching the binary languages of the repository.

**Finding: the literal `def:pturing` is degenerate.**  `def:pturing` requires `T_M(n) ≤ c nᵏ` with
`c, k ≥ 1` *for all* `n`.  At `n = 0` this forces `T_M(0) = 0`, so `q₀` is a halting state, and
then `M` halts at time `0` on every input.  Hence the literal class is `{∅, Σ*}`
(`P_Turing_lit_eq`).  Consequently, under the literal definitions, `P_Turing ≠ P_TM`
(`P_Turing_lit_ne_P_TM`) and `P_Turing ≠ NP_Turing` (`P_Turing_lit_ne_NP_Turing`).  The second
is an artefact of the `n = 0` case and has no bearing on the classical question.

**Corrected statement (clearly distinguished).**  `P_Turing` replaces `c nᵏ` by `c·max(n,1)ᵏ`,
changing only the `n = 0` case.  Then:
* `P_Turing_eq_P_TM`: `P_Turing = P_TM`.  Both simulations are explicit (`MTM.toTM`, `ofTM`).
  The second removes stay moves at a factor-2 time cost and replaces partial halting by the
  manuscript's two halting states.
* `NP_Turing_eq_NP_TM`: the verifier class of `def:tm_verifier`/`def:npturing` equals `NP_TM`.
  Here witnesses are binary, pairs use the repository's self-delimiting format `pair`, and
  the time bound `p(|x| + |y|)` is required only on well-formed pairs, as in the manuscript.
  A poly-time format check (`MTM.guard`) supplies a total decider.
  `def:tm_verifier` has no `n = 0` defect because its bound is an arbitrary polynomial.
-/

namespace PVNP.PartIITuring

open PVNP.Discrete

/-! ## The manuscript's machine model -/

/-- Head moves of `def:tm`: `{L, R}`. -/
inductive Mv
  | L
  | R
  deriving DecidableEq, Fintype

/-- Integer displacement of a move. -/
def Mv.shift : Mv → ℤ
  | .L => -1
  | .R => 1

/-- The repository direction with the same displacement. -/
def Mv.toDir : Mv → Dir
  | .L => .L
  | .R => .R

theorem Mv.toDir_shift (m : Mv) : m.toDir.shift = m.shift := by cases m <;> rfl

/-- **Definition `def:tm`** (with `Σ = {0,1}`). -/
structure MTM where
  Q : Type
  Γ : Type
  [finQ : Fintype Q]
  [finΓ : Fintype Γ]
  [decQ : DecidableEq Q]
  [decΓ : DecidableEq Γ]
  blank : Γ
  /-- The input alphabet `Σ = {0,1}` inside `Γ \ {␣}`. -/
  inp : Bool → Γ
  inp_inj : Function.Injective inp
  inp_ne_blank : ∀ b, inp b ≠ blank
  /-- Total transition function `δ : Q × Γ → Q × Γ × {L,R}`. -/
  δ : Q → Γ → Q × Γ × Mv
  q0 : Q
  qacc : Q
  qrej : Q

namespace MTM

attribute [instance] MTM.finQ MTM.finΓ MTM.decQ MTM.decΓ

variable (M : MTM)

/-- A configuration `(γ, h, q)`. -/
structure Cfg where
  tape : ℤ → M.Γ
  head : ℤ
  q : M.Q

/-- One transition step: apply `δ(q, γ(h))`. -/
def step (c : M.Cfg) : M.Cfg :=
  ⟨Function.update c.tape c.head (M.δ c.q (c.tape c.head)).2.1,
    c.head + (M.δ c.q (c.tape c.head)).2.2.shift, (M.δ c.q (c.tape c.head)).1⟩

/-- `t` transition steps. -/
def run (c : M.Cfg) (t : ℕ) : M.Cfg := M.step^[t] c

theorem run_zero (c : M.Cfg) : M.run c 0 = c := rfl

theorem run_succ (c : M.Cfg) (t : ℕ) : M.run c (t + 1) = M.step (M.run c t) := by
  simp [run, Function.iterate_succ_apply']

theorem run_add (c : M.Cfg) (a b : ℕ) : M.run c (a + b) = M.run (M.run c a) b := by
  simp only [run]
  rw [add_comm, Function.iterate_add_apply]

/-- The input `x₁ … x_n` on cells `0, …, n−1`, blank elsewhere. -/
def inputTape (x : List Bool) (i : ℤ) : M.Γ :=
  if 0 ≤ i ∧ i < x.length then M.inp (x.getD i.toNat false) else M.blank

/-- Initial configuration: head on cell `0` in state `q₀`. -/
def init (x : List Bool) : M.Cfg := ⟨M.inputTape x, 0, M.q0⟩

/-- The halting states `q_acc`, `q_rej`. -/
def Halting (q : M.Q) : Prop := q = M.qacc ∨ q = M.qrej

/-- `t = T_M(x)`: the run on `x` first enters a halting state at time `t`. -/
def FirstHalt (x : List Bool) (t : ℕ) : Prop :=
  M.Halting (M.run (M.init x) t).q ∧ ∀ s < t, ¬ M.Halting (M.run (M.init x) s).q

/-- `M` accepts `x`: the first halting state is `q_acc`. -/
def Accepts (x : List Bool) : Prop :=
  ∃ t, M.FirstHalt x t ∧ (M.run (M.init x) t).q = M.qacc

/-- `T_M(x) ≤ B`. -/
def HaltsWithin (x : List Bool) (B : ℕ) : Prop := ∃ t ≤ B, M.FirstHalt x t

theorem firstHalt_unique {x : List Bool} {t t' : ℕ} (h : M.FirstHalt x t)
    (h' : M.FirstHalt x t') : t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 t hlt)
  · exact heq
  · exact absurd h'.1 (h.2 t' hgt)

theorem accepts_iff_of_firstHalt {x : List Bool} {t : ℕ} (h : M.FirstHalt x t) :
    M.Accepts x ↔ (M.run (M.init x) t).q = M.qacc := by
  constructor
  · rintro ⟨t', ht', hq⟩
    rwa [M.firstHalt_unique h ht']
  · intro hq
    exact ⟨t, h, hq⟩

theorem haltsWithin_mono {x : List Bool} {B B' : ℕ} (h : M.HaltsWithin x B) (hB : B ≤ B') :
    M.HaltsWithin x B' := by
  obtain ⟨t, ht, hf⟩ := h
  exact ⟨t, ht.trans hB, hf⟩

end MTM

/-! ## The classes -/

/-- **Definition `def:pturing`, literal**: `T_M(n) ≤ c nᵏ` for all `n`, with `c, k ≥ 1`. -/
def P_Turing_lit : Set (Set (List Bool)) :=
  {L | ∃ (M : MTM) (c k : ℕ), 1 ≤ c ∧ 1 ≤ k ∧ (∀ x, M.HaltsWithin x (c * x.length ^ k)) ∧
    ∀ x, (M.Accepts x ↔ x ∈ L)}

/-- **Corrected `def:pturing`**: `T_M(n) ≤ c·max(n,1)ᵏ` (only the case `n = 0` changes). -/
def P_Turing : Set (Set (List Bool)) :=
  {L | ∃ (M : MTM) (c k : ℕ), 1 ≤ c ∧ 1 ≤ k ∧
    (∀ x, M.HaltsWithin x (c * max x.length 1 ^ k)) ∧ ∀ x, (M.Accepts x ↔ x ∈ L)}

/-- **Definitions `def:tm_verifier` and `def:npturing`** (binary witnesses, pairs encoded by
`pair`): the verifier halts within `p(|x| + |y|)` on every pair, and
`x ∈ L ⟺ ∃ y, |y| ≤ q(|x|) ∧ V accepts (x, y)`. -/
def NP_Turing : Set (Set (List Bool)) :=
  {L | ∃ (V : MTM) (p q : Polynomial ℕ),
    (∀ x w : List Bool, V.HaltsWithin (pair x w) (p.eval (x.length + w.length))) ∧
    ∀ x, (x ∈ L ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ V.Accepts (pair x w))}

/-! ## Polynomial bounds -/

/-- Every polynomial bound is dominated by some `c·max(n,1)ᵏ` with `c, k ≥ 1`. -/
theorem poly_le_cmax (p : Polynomial ℕ) :
    ∃ c k : ℕ, 1 ≤ c ∧ 1 ≤ k ∧ ∀ n, p.eval n ≤ c * max n 1 ^ k := by
  refine ⟨p.eval 1 + 1, p.natDegree + 1, by omega, by omega, fun n => ?_⟩
  set m := max n 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  have hnm : n ≤ m := le_max_left _ _
  rw [Polynomial.eval_eq_sum_range (x := n), Polynomial.eval_eq_sum_range (x := 1)]
  calc ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * m ^ (p.natDegree + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Nat.mul_le_mul_left
        calc n ^ i ≤ m ^ i := Nat.pow_le_pow_left hnm i
          _ ≤ m ^ (p.natDegree + 1) :=
            Nat.pow_le_pow_right hm1 (by simp at hi; omega)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * 1 ^ i) * m ^ (p.natDegree + 1) := by
        rw [Finset.sum_mul]; simp
    _ ≤ ((∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * 1 ^ i) + 1) *
          m ^ (p.natDegree + 1) := Nat.mul_le_mul_right _ (by omega)

/-- `c·max(n,1)ᵏ` is a polynomial bound. -/
theorem cmax_le_poly (c k n : ℕ) :
    c * max n 1 ^ k ≤ (Polynomial.C c * (Polynomial.X + 1) ^ k).eval n := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-! ## The literal class is `{∅, Σ*}` -/

/-- A machine that halts at time `0`: in `q_acc` if `b`, in `q_rej` otherwise. -/
def constMTM (b : Bool) : MTM where
  Q := Bool
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank := fun _ => Option.some_ne_none _
  δ q a := (q, a, .R)
  q0 := b
  qacc := true
  qrej := false

theorem constMTM_firstHalt (b : Bool) (x : List Bool) : (constMTM b).FirstHalt x 0 := by
  refine ⟨?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
  show b = true ∨ b = false
  cases b <;> simp

theorem constMTM_accepts (b : Bool) (x : List Bool) : (constMTM b).Accepts x ↔ b = true := by
  rw [(constMTM b).accepts_iff_of_firstHalt (constMTM_firstHalt b x)]
  rfl

/-- **The literal `def:pturing` is degenerate**: `P_Turing^{lit} = {∅, Σ*}`. -/
theorem P_Turing_lit_eq : P_Turing_lit = {∅, Set.univ} := by
  ext L
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨M, c, k, -, hk, hT, hL⟩
    -- `T_M(0) ≤ c·0ᵏ = 0`: the start state is halting.
    obtain ⟨t, ht, hf⟩ := hT []
    have ht0 : t = 0 := by
      have : c * ([] : List Bool).length ^ k = 0 := by simp [Nat.zero_pow hk]
      omega
    subst ht0
    have hq0 : M.Halting M.q0 := hf.1
    have hall : ∀ x, M.FirstHalt x 0 :=
      fun x => ⟨hq0, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
    by_cases hacc : M.q0 = M.qacc
    · right
      ext x
      simp only [Set.mem_univ, iff_true]
      exact (hL x).1 ((M.accepts_iff_of_firstHalt (hall x)).2 hacc)
    · left
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hacc ((M.accepts_iff_of_firstHalt (hall x)).1 ((hL x).2 hx))
  · rintro (rfl | rfl)
    · refine ⟨constMTM false, 1, 1, le_rfl, le_rfl, fun x => ⟨0, Nat.zero_le _,
        constMTM_firstHalt false x⟩, fun x => ?_⟩
      rw [constMTM_accepts]; simp
    · refine ⟨constMTM true, 1, 1, le_rfl, le_rfl, fun x => ⟨0, Nat.zero_le _,
        constMTM_firstHalt true x⟩, fun x => ?_⟩
      rw [constMTM_accepts]; simp

/-! ## From the manuscript model to the repository model -/

namespace MTM

variable (M : MTM)

/-- The repository machine running `M`: it stops (`δ = none`) exactly in the halting states and
displays the answer `q = q_acc`. -/
def toTM : TM where
  Λ := M.Q
  Γ := M.Γ
  blank := M.blank
  inp := M.inp
  start := M.q0
  δ q a := if q = M.qacc ∨ q = M.qrej then none
    else some ((M.δ q a).1, (M.δ q a).2.1, (M.δ q a).2.2.toDir)
  acc q := decide (q = M.qacc)
  rej q := decide (q = M.qrej)

/-- Configuration correspondence. -/
def liftCfg (c : M.Cfg) : M.toTM.Cfg := ⟨c.q, c.tape, c.head⟩

theorem toTM_next (c : M.Cfg) (hc : ¬ M.Halting c.q) :
    M.toTM.next (M.liftCfg c) = M.liftCfg (M.step c) := by
  have hc' : ¬ (c.q = M.qacc ∨ c.q = M.qrej) := hc
  simp only [TM.next, TM.step, liftCfg, toTM, if_neg hc', Option.map_some, Option.getD_some,
    step, Mv.toDir_shift]

theorem toTM_run (x : List Bool) :
    ∀ t, (∀ s < t, ¬ M.Halting (M.run (M.init x) s).q) →
      M.toTM.run (M.toTM.init x) t = M.liftCfg (M.run (M.init x) t)
  | 0, _ => rfl
  | t + 1, h => by
    rw [TM.run_succ, toTM_run x t (fun s hs => h s (by omega)), M.run_succ,
      M.toTM_next _ (h t (by omega))]

theorem toTM_ans (c : M.Cfg) :
    M.toTM.ans (M.liftCfg c) = answerOf (decide (c.q = M.qacc)) (decide (c.q = M.qrej)) := rfl

theorem answerOf_halting {q : M.Q} (h : M.Halting q) :
    answerOf (decide (q = M.qacc)) (decide (q = M.qrej)) = some (decide (q = M.qacc)) := by
  by_cases ha : q = M.qacc
  · rw [decide_eq_true ha]; rfl
  · rw [decide_eq_false ha, decide_eq_true (h.resolve_left ha)]; rfl

theorem answerOf_not_halting {q : M.Q} (h : ¬ M.Halting q) :
    answerOf (decide (q = M.qacc)) (decide (q = M.qrej)) = none := by
  rw [decide_eq_false fun e => h (Or.inl e), decide_eq_false fun e => h (Or.inr e)]; rfl

/-- If `M` halts within `B` on `x`, the repository machine gives its first answer `[q = q_acc]`
within `B`. -/
theorem toTM_decidesAt {x : List Bool} {B : ℕ} {L : Set (List Bool)} (hB : M.HaltsWithin x B)
    (hL : M.Accepts x ↔ x ∈ L) : DecidesAt (M.toTM.out x) B x L := by
  obtain ⟨t, htB, hf⟩ := hB
  have hrun := M.toTM_run x t hf.2
  refine ⟨decide ((M.run (M.init x) t).q = M.qacc), ⟨t, htB, ?_, fun s hs => ?_⟩, ?_⟩
  · show M.toTM.ans (M.toTM.run (M.toTM.init x) t) = _
    rw [hrun, toTM_ans, M.answerOf_halting hf.1]
  · show M.toTM.ans (M.toTM.run (M.toTM.init x) s) = none
    rw [M.toTM_run x s (fun s' hs' => hf.2 s' (by omega)), toTM_ans,
      M.answerOf_not_halting (hf.2 s hs)]
  · rw [decide_eq_true_iff, ← hL, M.accepts_iff_of_firstHalt hf]

end MTM

/-- `P_Turing ⊆ P_TM`. -/
theorem P_Turing_subset_P_TM : P_Turing ⊆ P_TM := by
  rintro L ⟨M, c, k, -, -, hT, hL⟩
  refine ⟨M.toTM, Polynomial.C c * (Polynomial.X + 1) ^ k, fun x => ?_⟩
  exact M.toTM_decidesAt (M.haltsWithin_mono (hT x) (cmax_le_poly c k x.length)) (hL x)


/-! ## From the repository model to the manuscript model -/

/-- Control states of the manuscript machine simulating a repository machine: `main q`
simulates state `q`; `back q` completes a stay move (one step right, one step back);
`acc`/`rej` are the halting states; `loop` follows a non-answering halt. -/
inductive OQ (Λ : Type) where
  | main (q : Λ)
  | back (q : Λ)
  | acc
  | rej
  | loop
  deriving DecidableEq, Fintype

namespace OfTM

variable (M : TM)

/-- Reading map: the fresh input symbol `inr b` is read as `M.inp b`. -/
def rd : M.Γ ⊕ Bool → M.Γ := Sum.elim id M.inp

/-- The manuscript state representing the repository state `q` (answers first, with the
repository's precedence of acceptance). -/
def E (q : M.Λ) : OQ M.Λ := if M.acc q then .acc else if M.rej q then .rej else .main q

/-- The total transition function. -/
def δ' : OQ M.Λ → M.Γ ⊕ Bool → OQ M.Λ × (M.Γ ⊕ Bool) × Mv
  | .main q, g =>
    match M.δ q (rd M g) with
    | none => (.loop, g, .R)
    | some (q', a', .L) => (E M q', .inl a', .L)
    | some (q', a', .R) => (E M q', .inl a', .R)
    | some (q', a', .S) => (.back q', .inl a', .R)
  | .back q, g => (E M q, g, .L)
  | .acc, g => (.acc, g, .R)
  | .rej, g => (.rej, g, .R)
  | .loop, g => (.loop, g, .R)

end OfTM

/-- **Repository machine → manuscript machine.**  Total `δ`, moves in `{L, R}`, halting states
`q_acc`, `q_rej`; the input alphabet `{inr 0, inr 1}` is fresh and avoids the blank. -/
def ofTM (M : TM) : MTM where
  Q := OQ M.Λ
  Γ := M.Γ ⊕ Bool
  blank := .inl M.blank
  inp := .inr
  inp_inj := Sum.inr_injective
  inp_ne_blank := fun _ h => Sum.inr_ne_inl h
  δ := OfTM.δ' M
  q0 := OfTM.E M M.start
  qacc := .acc
  qrej := .rej

namespace OfTM

variable (M : TM)

/-- Simulation relation. -/
def Rel (cN : (ofTM M).Cfg) (cM : M.Cfg) : Prop :=
  cN.q = E M cM.q ∧ cN.head = cM.head ∧ ∀ i, rd M (cN.tape i) = cM.tape i

theorem rel_init (x : List Bool) : Rel M ((ofTM M).init x) (M.init x) := by
  refine ⟨rfl, rfl, fun i => ?_⟩
  show rd M ((ofTM M).inputTape x i) = M.inputTape x i
  unfold MTM.inputTape TM.inputTape
  split_ifs <;> rfl

theorem E_of_ans_none {q : M.Λ} (h : answerOf (M.acc q) (M.rej q) = none) :
    E M q = .main q := by
  unfold E
  cases ha : M.acc q <;> cases hr : M.rej q <;> simp_all [answerOf]

theorem halting_main (q : M.Λ) : ¬ (ofTM M).Halting (.main q) := by
  rintro (h | h) <;> cases h

theorem halting_back (q : M.Λ) : ¬ (ofTM M).Halting (.back q) := by
  rintro (h | h) <;> cases h

theorem halting_E {q : M.Λ} {b : Bool} (h : answerOf (M.acc q) (M.rej q) = some b) :
    (ofTM M).Halting (E M q) ∧ (E M q = .acc ↔ b = true) := by
  unfold E
  cases ha : M.acc q <;> cases hr : M.rej q <;> simp_all [answerOf, MTM.Halting, ofTM]

theorem update_rel {T : ℤ → M.Γ ⊕ Bool} {U : ℤ → M.Γ} (hT : ∀ i, rd M (T i) = U i) (h : ℤ)
    (a : M.Γ) : ∀ i, rd M (Function.update T h (.inl a) i) = Function.update U h a i := by
  intro i
  by_cases hi : i = h
  · subst hi; simp [rd]
  · simp [Function.update_of_ne hi, hT i]

/-- One repository step is simulated by one manuscript step (moves `L`, `R`) or two (move `S`),
through non-halting states. -/
theorem sim_step {cN : (ofTM M).Cfg} {cM cM' : M.Cfg} (hR : Rel M cN cM)
    (hans : M.ans cM = none) (hstep : M.step cM = some cM') :
    ∃ k, 1 ≤ k ∧ k ≤ 2 ∧ Rel M ((ofTM M).run cN k) cM' ∧
      ∀ j < k, ¬ (ofTM M).Halting ((ofTM M).run cN j).q := by
  obtain ⟨hq, hh, ht⟩ := hR
  have hE : E M cM.q = .main cM.q := E_of_ans_none M hans
  have hread : rd M (cN.tape cN.head) = cM.tape cM.head := by rw [hh, ht]
  obtain ⟨q', a', d, hδ⟩ : ∃ q' a' d, M.δ cM.q (cM.tape cM.head) = some (q', a', d) := by
    cases hδ : M.δ cM.q (cM.tape cM.head) with
    | none => simp [TM.step, hδ] at hstep
    | some t => exact ⟨t.1, t.2.1, t.2.2, rfl⟩
  have hM' : cM' = ⟨q', Function.update cM.tape cM.head a', cM.head + d.shift⟩ := by
    simp [TM.step, hδ] at hstep; exact hstep.symm
  subst hM'
  have hδN : ∀ d0 : Dir, d = d0 →
      OfTM.δ' M cN.q (cN.tape cN.head) =
        match d0 with
        | .L => (E M q', .inl a', .L)
        | .R => (E M q', .inl a', .R)
        | .S => (.back q', .inl a', .R) := by
    intro d0 hd
    subst hd
    rw [hq, hE]
    show (match M.δ cM.q (rd M (cN.tape cN.head)) with
      | none => _ | some (q', a', .L) => _ | some (q', a', .R) => _
      | some (q', a', .S) => _) = _
    rw [hread, hδ]
    cases d <;> rfl
  have hnot0 : ¬ (ofTM M).Halting ((ofTM M).run cN 0).q := by
    show ¬ (ofTM M).Halting cN.q
    rw [hq, hE]; exact halting_main M _
  cases d with
  | L =>
    refine ⟨1, le_rfl, by omega, ?_, fun j hj => ?_⟩
    · show Rel M ((ofTM M).step cN) _
      have h1 := hδN .L rfl
      refine ⟨?_, ?_, ?_⟩
      · show (OfTM.δ' M cN.q (cN.tape cN.head)).1 = _
        rw [h1]
      · show cN.head + (OfTM.δ' M cN.q (cN.tape cN.head)).2.2.shift = _
        rw [h1, hh]; rfl
      · show ∀ i, rd M (Function.update cN.tape cN.head
          (OfTM.δ' M cN.q (cN.tape cN.head)).2.1 i) = _
        rw [h1, hh]
        exact update_rel M ht cM.head a'
    · interval_cases j; exact hnot0
  | R =>
    refine ⟨1, le_rfl, by omega, ?_, fun j hj => ?_⟩
    · show Rel M ((ofTM M).step cN) _
      have h1 := hδN .R rfl
      refine ⟨?_, ?_, ?_⟩
      · show (OfTM.δ' M cN.q (cN.tape cN.head)).1 = _
        rw [h1]
      · show cN.head + (OfTM.δ' M cN.q (cN.tape cN.head)).2.2.shift = _
        rw [h1, hh]; rfl
      · show ∀ i, rd M (Function.update cN.tape cN.head
          (OfTM.δ' M cN.q (cN.tape cN.head)).2.1 i) = _
        rw [h1, hh]
        exact update_rel M ht cM.head a'
    · interval_cases j; exact hnot0
  | S =>
    have h1 := hδN .S rfl
    have hs1 : (ofTM M).run cN 1 =
        ⟨Function.update cN.tape cN.head (.inl a'), cN.head + 1, .back q'⟩ := by
      show (ofTM M).step cN = _
      simp only [MTM.step]
      show (⟨Function.update cN.tape cN.head (OfTM.δ' M cN.q (cN.tape cN.head)).2.1,
        cN.head + (OfTM.δ' M cN.q (cN.tape cN.head)).2.2.shift,
        (OfTM.δ' M cN.q (cN.tape cN.head)).1⟩ : (ofTM M).Cfg) = _
      rw [h1]; rfl
    refine ⟨2, by omega, le_rfl, ?_, fun j hj => ?_⟩
    · rw [show (2 : ℕ) = 1 + 1 from rfl, MTM.run_add, hs1]
      show Rel M ((ofTM M).step _) _
      simp only [MTM.step]
      show Rel M ⟨Function.update (Function.update cN.tape cN.head (.inl a')) (cN.head + 1)
          (OfTM.δ' M (.back q') (Function.update cN.tape cN.head (.inl a')
            (cN.head + 1))).2.1,
        cN.head + 1 + (OfTM.δ' M (.back q') (Function.update cN.tape cN.head (.inl a')
            (cN.head + 1))).2.2.shift,
        (OfTM.δ' M (.back q') (Function.update cN.tape cN.head (.inl a')
            (cN.head + 1))).1⟩ _
      simp only [OfTM.δ', Function.update_eq_self]
      refine ⟨rfl, ?_, ?_⟩
      · show cN.head + 1 + -1 = cM.head + Dir.S.shift
        rw [hh]; simp [Dir.shift]
      · show ∀ i, rd M (Function.update cN.tape cN.head (.inl a') i) =
          Function.update cM.tape cM.head a' i
        rw [hh]
        exact update_rel M ht cM.head a'
    · interval_cases j
      · exact hnot0
      · rw [hs1]; exact halting_back M q'

/-- If the repository machine gives its first answer at time `T`, no transition before `T` is
undefined. -/
theorem step_ne_none {x : List Bool} {T : ℕ} {b : Bool} (hT : M.out x T = some b)
    (hbefore : ∀ s < T, M.out x s = none) :
    ∀ s < T, M.step (M.run (M.init x) s) ≠ none := by
  intro s hs hnone
  have hfix : ∀ j, M.run (M.init x) (s + j) = M.run (M.init x) s := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← Nat.add_assoc, TM.run_succ, ih]
      simp [TM.next, hnone]
  have h := hfix (T - s)
  rw [Nat.add_sub_cancel' hs.le] at h
  have hb : M.out x T = M.out x s := by
    show M.ans (M.run (M.init x) T) = M.ans (M.run (M.init x) s)
    rw [h]
  rw [hT, hbefore s hs] at hb
  cases hb

/-- **Simulation invariant**: up to the first answer, every repository configuration at time
`s` is represented at some manuscript time `τ ≤ 2s`, with no halting state before. -/
theorem sim_run {x : List Bool} {T : ℕ} {b : Bool} (hT : M.out x T = some b)
    (hbefore : ∀ s < T, M.out x s = none) :
    ∀ s ≤ T, ∃ τ ≤ 2 * s, Rel M ((ofTM M).run ((ofTM M).init x) τ) (M.run (M.init x) s) ∧
      ∀ τ' < τ, ¬ (ofTM M).Halting ((ofTM M).run ((ofTM M).init x) τ').q := by
  intro s
  induction s with
  | zero =>
    intro _
    exact ⟨0, le_rfl, rel_init M x, fun τ' h => absurd h (Nat.not_lt_zero _)⟩
  | succ s ih =>
    intro hs
    obtain ⟨τ, hτ, hR, hnh⟩ := ih (by omega)
    have hans : M.ans (M.run (M.init x) s) = none := hbefore s (by omega)
    obtain ⟨cM', hcM'⟩ : ∃ c', M.step (M.run (M.init x) s) = some c' :=
      Option.ne_none_iff_exists'.1 (step_ne_none M hT hbefore s (by omega))
    have hnext : M.run (M.init x) (s + 1) = cM' := by
      rw [TM.run_succ]; simp [TM.next, hcM']
    obtain ⟨k, hk1, hk2, hRk, hnhk⟩ := sim_step M hR hans hcM'
    refine ⟨τ + k, by omega, ?_, fun τ' hτ' => ?_⟩
    · rw [hnext, MTM.run_add]; exact hRk
    · by_cases hlt : τ' < τ
      · exact hnh τ' hlt
      · obtain ⟨j, rfl⟩ : ∃ j, τ' = τ + j := ⟨τ' - τ, by omega⟩
        rw [MTM.run_add]
        exact hnhk j (by omega)

/-- The manuscript machine decides what the repository machine decides, with first halting
time at most twice the first answer time. -/
theorem ofTM_decides {x : List Bool} {B : ℕ} {L : Set (List Bool)}
    (h : DecidesAt (M.out x) B x L) :
    (ofTM M).HaltsWithin x (2 * B) ∧ ((ofTM M).Accepts x ↔ x ∈ L) := by
  obtain ⟨b, ⟨T, hTB, hT, hbefore⟩, hbL⟩ := h
  obtain ⟨τ, hτ, ⟨hq, -, -⟩, hnh⟩ := sim_run M hT hbefore T le_rfl
  have hans : answerOf (M.acc (M.run (M.init x) T).q) (M.rej (M.run (M.init x) T).q) = some b :=
    hT
  obtain ⟨hhalt, hacc⟩ := halting_E M hans
  have hfirst : (ofTM M).FirstHalt x τ := ⟨by rw [hq]; exact hhalt, hnh⟩
  refine ⟨⟨τ, by omega, hfirst⟩, ?_⟩
  rw [(ofTM M).accepts_iff_of_firstHalt hfirst, hq, ← hbL]
  exact hacc

end OfTM

/-- `P_TM ⊆ P_Turing`. -/
theorem P_TM_subset_P_Turing : P_TM ⊆ P_Turing := by
  rintro L ⟨M, p, hM⟩
  obtain ⟨c, k, hc, hk, hle⟩ := poly_le_cmax (2 * p)
  refine ⟨ofTM M, c, k, hc, hk, fun x => ?_, fun x => (OfTM.ofTM_decides M (hM x)).2⟩
  refine (ofTM M).haltsWithin_mono (OfTM.ofTM_decides M (hM x)).1 ?_
  have := hle x.length
  simpa [Polynomial.eval_mul] using this

/-- **Corrected `def:pturing` agrees with the repository class**: `P_Turing = P_TM`. -/
theorem P_Turing_eq_P_TM : P_Turing = P_TM :=
  Set.Subset.antisymm P_Turing_subset_P_TM P_TM_subset_P_Turing


/-! ## Well-formed pairs and the format guard -/

/-- States of the pair-format automaton: expecting a tag bit, expecting a data bit, or past the
separator. -/
inductive PS where
  | tag
  | dat
  | ok
  deriving DecidableEq, Fintype

/-- One automaton transition. -/
def PS.next : PS → Bool → PS
  | .tag, true => .dat
  | .tag, false => .ok
  | .dat, _ => .tag
  | .ok, _ => .ok

/-- The automaton run on a word. -/
def PS.run : PS → List Bool → PS
  | s, [] => s
  | s, b :: z => PS.run (s.next b) z

theorem PS.run_append : ∀ (s : PS) (z z' : List Bool), PS.run s (z ++ z') = PS.run (PS.run s z) z'
  | _, [], _ => rfl
  | s, b :: z, z' => PS.run_append (s.next b) z z'

theorem PS.run_ok : ∀ z : List Bool, PS.run .ok z = .ok
  | [] => rfl
  | _ :: z => PS.run_ok z

theorem PS.run_pair (x w : List Bool) : PS.run .tag (pair x w) = .ok := by
  induction x with
  | nil => exact PS.run_ok w
  | cons b x ih =>
    simp only [pair, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    exact ih

/-- The automaton accepts exactly the well-formed pairs. -/
theorem PS.run_eq_ok : ∀ z : List Bool, PS.run .tag z = .ok → ∃ x w, z = pair x w
  | [], h => by cases h
  | false :: w, _ => ⟨[], w, rfl⟩
  | [true], h => by cases h
  | true :: b :: z, h => by
    obtain ⟨x, w, rfl⟩ := PS.run_eq_ok z h
    exact ⟨b :: x, w, by simp [pair]⟩

/-- Control states of the guarded verifier: format check, return to cell `0`, then `V`. -/
inductive GQ (Q : Type) where
  | chk (s : PS)
  | back
  | run (q : Q)
  deriving DecidableEq, Fintype

namespace MTM

variable (V : MTM)

/-- Transition function of the guarded verifier. -/
def guardδ : GQ V.Q → V.Γ → GQ V.Q × V.Γ × Mv
  | .chk s, a =>
    if a = V.blank then (if s = .ok then (.back, a, .L) else (.run V.qrej, a, .R))
    else (.chk (s.next (decide (a = V.inp true))), a, .R)
  | .back, a => if a = V.blank then (.run V.q0, a, .R) else (.back, a, .L)
  | .run q, a => (.run (V.δ q a).1, (V.δ q a).2.1, (V.δ q a).2.2)

/-- **The guarded verifier**: it scans the input with the pair-format automaton, rejects a
malformed input at the first blank, and otherwise returns to cell `0` and runs `V`. -/
def guard : MTM where
  Q := GQ V.Q
  Γ := V.Γ
  blank := V.blank
  inp := V.inp
  inp_inj := V.inp_inj
  inp_ne_blank := V.inp_ne_blank
  δ := V.guardδ
  q0 := .chk .tag
  qacc := .run V.qacc
  qrej := .run V.qrej

theorem guard_step (c : V.guard.Cfg) :
    V.guard.step c = ⟨Function.update c.tape c.head (V.guardδ c.q (c.tape c.head)).2.1,
      c.head + (V.guardδ c.q (c.tape c.head)).2.2.shift, (V.guardδ c.q (c.tape c.head)).1⟩ :=
  rfl

theorem guard_inputTape (z : List Bool) : V.guard.inputTape z = V.inputTape z := rfl

theorem inputTape_ne_blank {z : List Bool} {i : ℤ} (h0 : 0 ≤ i) (hi : i < z.length) :
    V.inputTape z i = V.inp (z.getD i.toNat false) := by
  simp [inputTape, h0, hi]

theorem inputTape_blank {z : List Bool} {i : ℤ} (h : i < 0 ∨ z.length ≤ i) :
    V.inputTape z i = V.blank := by
  unfold inputTape
  rw [if_neg]
  omega

/-- Format-check phase. -/
theorem guard_scan (z : List Bool) :
    ∀ i ≤ z.length, V.guard.run (V.guard.init z) i =
      ⟨V.inputTape z, i, .chk (PS.run .tag (z.take i))⟩
  | 0, _ => rfl
  | i + 1, hi => by
    rw [MTM.run_succ, guard_scan z i (by omega), guard_step]
    have hc : V.inputTape z (i : ℤ) = V.inp (z.getD i false) :=
      V.inputTape_ne_blank (by omega) (by omega)
    have hne : V.inputTape z (i : ℤ) ≠ V.blank := by rw [hc]; exact V.inp_ne_blank _
    have hdec : decide (V.inp (z.getD i false) = V.inp true) = z.getD i false := by
      cases z.getD i false
      · exact decide_eq_false fun h => Bool.false_ne_true (V.inp_inj h)
      · exact decide_eq_true rfl
    have hstate : (PS.run .tag (z.take i)).next (z.getD i false) =
        PS.run .tag (z.take (i + 1)) := by
      rw [← List.take_append_getElem (by omega : i < z.length), PS.run_append]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < z.length),
        Option.getD_some]
      rfl
    simp only [guardδ, if_neg hne, Function.update_eq_self]
    simp only [hc, hdec, hstate, Mv.shift, Nat.cast_succ]

/-- Return phase: after the format check succeeds, the head walks back to cell `-1`. -/
theorem guard_back (z : List Bool) (hok : PS.run .tag z = .ok) :
    ∀ j ≤ z.length, V.guard.run (V.guard.init z) (z.length + 1 + j) =
      ⟨V.inputTape z, (z.length : ℤ) - 1 - j, .back⟩
  | 0, _ => by
    rw [Nat.add_zero, MTM.run_succ, V.guard_scan z z.length le_rfl, guard_step]
    have hb : V.inputTape z (z.length : ℤ) = V.blank := V.inputTape_blank (by omega)
    have hu : Function.update (V.inputTape z) (z.length : ℤ) V.blank = V.inputTape z := by
      rw [← hb]; exact Function.update_eq_self _ _
    simp only [List.take_length, hok, guardδ, hb, if_true, hu]
    simp only [show (z.length : ℤ) + Mv.L.shift = (z.length : ℤ) - 1 - ((0 : ℕ) : ℤ) by
      simp [Mv.shift]; ring]
  | j + 1, hj => by
    rw [show z.length + 1 + (j + 1) = (z.length + 1 + j) + 1 by omega, MTM.run_succ,
      guard_back z hok j (by omega), guard_step]
    have hne : V.inputTape z ((z.length : ℤ) - 1 - j) ≠ V.blank := by
      rw [V.inputTape_ne_blank (by omega) (by omega)]; exact V.inp_ne_blank _
    simp only [guardδ, if_neg hne, Function.update_eq_self]
    simp only [show (z.length : ℤ) - 1 - (j : ℤ) + Mv.L.shift =
        (z.length : ℤ) - 1 - ((j + 1 : ℕ) : ℤ) by simp [Mv.shift]; ring]

/-- The run phase starts at `V`'s initial configuration at time `2|z| + 2`. -/
theorem guard_start (z : List Bool) (hok : PS.run .tag z = .ok) :
    V.guard.run (V.guard.init z) (2 * z.length + 2) = ⟨V.inputTape z, 0, .run V.q0⟩ := by
  rw [show 2 * z.length + 2 = (z.length + 1 + z.length) + 1 by omega, MTM.run_succ,
    V.guard_back z hok z.length le_rfl, guard_step]
  have hb : V.inputTape z ((z.length : ℤ) - 1 - (z.length : ℤ)) = V.blank :=
    V.inputTape_blank (by omega)
  have hu : Function.update (V.inputTape z) ((z.length : ℤ) - 1 - (z.length : ℤ)) V.blank =
      V.inputTape z := by
    rw [← hb]; exact Function.update_eq_self _ _
  simp only [guardδ, hb, if_true, hu]
  simp only [show (z.length : ℤ) - 1 - (z.length : ℤ) + Mv.R.shift = 0 by simp [Mv.shift]]

/-- Lift of a configuration of `V` to the run phase of the guarded verifier. -/
def liftG (c : V.Cfg) : V.guard.Cfg := ⟨c.tape, c.head, .run c.q⟩

theorem guard_run_lift (c : V.Cfg) : ∀ t, V.guard.run (V.liftG c) t = V.liftG (V.run c t)
  | 0 => rfl
  | t + 1 => by
    rw [MTM.run_succ, guard_run_lift c t, MTM.run_succ, guard_step]
    rfl

theorem guard_halting_run (q : V.Q) : V.guard.Halting (.run q) ↔ V.Halting q := by
  constructor
  · rintro (h | h)
    · exact Or.inl (GQ.run.inj h)
    · exact Or.inr (GQ.run.inj h)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)

theorem guard_not_halting_chk (s : PS) : ¬ V.guard.Halting (.chk s) := by
  rintro (h | h) <;> cases h

theorem guard_not_halting_back : ¬ V.guard.Halting .back := by
  rintro (h | h) <;> cases h

/-- On a well-formed input the guarded verifier halts `2|z| + 2` steps after `V` would, with the
same verdict. -/
theorem guard_valid {z : List Bool} (hok : PS.run .tag z = .ok) {B : ℕ}
    (hB : V.HaltsWithin z B) :
    V.guard.HaltsWithin z (2 * z.length + 2 + B) ∧ (V.guard.Accepts z ↔ V.Accepts z) := by
  obtain ⟨t, htB, hf⟩ := hB
  have hrun : ∀ s, V.guard.run (V.guard.init z) (2 * z.length + 2 + s) =
      V.liftG (V.run (V.init z) s) := by
    intro s
    rw [MTM.run_add, V.guard_start z hok]
    exact V.guard_run_lift (V.init z) s
  have hpre : ∀ s < 2 * z.length + 2, ¬ V.guard.Halting (V.guard.run (V.guard.init z) s).q := by
    intro s hs
    by_cases h1 : s ≤ z.length
    · rw [V.guard_scan z s h1]; exact V.guard_not_halting_chk _
    · obtain ⟨j, rfl⟩ : ∃ j, s = z.length + 1 + j := ⟨s - (z.length + 1), by omega⟩
      rw [V.guard_back z hok j (by omega)]; exact V.guard_not_halting_back
  have hfirst : V.guard.FirstHalt z (2 * z.length + 2 + t) := by
    refine ⟨?_, fun s hs => ?_⟩
    · rw [hrun]; exact (V.guard_halting_run _).2 hf.1
    · by_cases h : s < 2 * z.length + 2
      · exact hpre s h
      · obtain ⟨j, rfl⟩ : ∃ j, s = 2 * z.length + 2 + j := ⟨s - (2 * z.length + 2), by omega⟩
        rw [hrun]
        exact fun h' => hf.2 j (by omega) ((V.guard_halting_run _).1 h')
  refine ⟨⟨_, by omega, hfirst⟩, ?_⟩
  rw [V.guard.accepts_iff_of_firstHalt hfirst, V.accepts_iff_of_firstHalt hf, hrun]
  exact ⟨fun h => GQ.run.inj h, fun h => by rw [liftG, h]; rfl⟩

/-- On a malformed input the guarded verifier halts at time `|z| + 1`. -/
theorem guard_invalid {z : List Bool} (hbad : PS.run .tag z ≠ .ok) :
    V.guard.HaltsWithin z (z.length + 1) := by
  refine ⟨z.length + 1, le_rfl, ?_, fun s hs => ?_⟩
  · rw [MTM.run_succ, V.guard_scan z z.length le_rfl, guard_step]
    have hb : V.inputTape z (z.length : ℤ) = V.blank := V.inputTape_blank (by omega)
    simp only [List.take_length, guardδ, hb, if_true, if_neg hbad]
    exact Or.inr rfl
  · rw [V.guard_scan z s (by omega)]; exact V.guard_not_halting_chk _

end MTM

/-! ## The verifier classes -/

/-- `NP_Turing ⊆ NP_TM`. -/
theorem NP_Turing_subset_NP_TM : NP_Turing ⊆ NP_TM := by
  rintro L ⟨V, p, q, hV, hL⟩
  obtain ⟨c, k, hc, hk, hle⟩ := poly_le_cmax (2 * Polynomial.X + 2 + p)
  have hP : {z | V.guard.Accepts z} ∈ P_Turing := by
    refine ⟨V.guard, c, k, hc, hk, fun z => ?_, fun z => Iff.rfl⟩
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
  refine ⟨{z | V.guard.Accepts z}, P_Turing_subset_P_TM hP, q, fun x => ?_⟩
  rw [hL x]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  obtain ⟨B, hB⟩ : ∃ B, V.HaltsWithin (pair x w) B := ⟨_, hV x w⟩
  exact (V.guard_valid (PS.run_pair x w) hB).2.symm

/-- `NP_TM ⊆ NP_Turing`. -/
theorem NP_TM_subset_NP_Turing : NP_TM ⊆ NP_Turing := by
  rintro L ⟨V', hV', q, hL⟩
  obtain ⟨V, c, k, -, -, hT, hA⟩ := P_TM_subset_P_Turing hV'
  refine ⟨V, Polynomial.C c * (2 * Polynomial.X + 1) ^ k, q, fun x w => ?_, fun x => ?_⟩
  · refine V.haltsWithin_mono (hT (pair x w)) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    rw [pair_length]
    omega
  · rw [hL x]
    exact exists_congr fun w => and_congr_right fun _ => (hA (pair x w)).symm

/-- **`def:npturing` agrees with the repository class**: `NP_Turing = NP_TM`. -/
theorem NP_Turing_eq_NP_TM : NP_Turing = NP_TM :=
  Set.Subset.antisymm NP_Turing_subset_NP_TM NP_TM_subset_NP_Turing

/-! ## Consequences of the literal `def:pturing` -/

/-- A one-step decider of `{x | x starts with 1}`. -/
def headMTM : MTM where
  Q := Option Bool
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank := fun _ => Option.some_ne_none _
  δ q a := match q with
    | none => (some (decide (a = some true)), a, .R)
    | some b => (some b, a, .R)
  q0 := none
  qacc := some true
  qrej := some false

/-- The language of words starting with `1`. -/
def startsWithOne : Set (List Bool) := {x | x.head? = some true}

theorem startsWithOne_mem_P_Turing : startsWithOne ∈ P_Turing := by
  have hrun1 : ∀ x : List Bool, (headMTM.run (headMTM.init x) 1).q =
      some (decide (headMTM.inputTape x 0 = some true)) := fun x => rfl
  have hfirst : ∀ x, headMTM.FirstHalt x 1 := by
    intro x
    refine ⟨?_, fun s hs => ?_⟩
    · rw [hrun1]
      cases decide (headMTM.inputTape x 0 = some true)
      · exact Or.inr rfl
      · exact Or.inl rfl
    · interval_cases s
      rintro (h | h) <;> cases h
  refine ⟨headMTM, 1, 1, le_rfl, le_rfl, fun x => ⟨1, ?_, hfirst x⟩, fun x => ?_⟩
  · simp
  · rw [headMTM.accepts_iff_of_firstHalt (hfirst x), hrun1]
    show some (decide (headMTM.inputTape x 0 = some true)) = some true ↔ x.head? = some true
    cases x with
    | nil => simp [MTM.inputTape, headMTM]
    | cons b x => cases b <;> simp [MTM.inputTape, headMTM]

theorem startsWithOne_ne_empty : startsWithOne ≠ ∅ := by
  intro h
  have : [true] ∈ startsWithOne := rfl
  rw [h] at this
  exact this

theorem startsWithOne_ne_univ : startsWithOne ≠ Set.univ := by
  intro h
  have : ([] : List Bool) ∈ startsWithOne := by rw [h]; trivial
  cases this

/-- Under the literal `def:pturing`, `P_Turing ≠ P_TM`. -/
theorem P_Turing_lit_ne_P_TM : P_Turing_lit ≠ P_TM := by
  intro h
  have hmem : startsWithOne ∈ P_Turing_lit := by
    rw [h, ← P_Turing_eq_P_TM]; exact startsWithOne_mem_P_Turing
  rw [P_Turing_lit_eq] at hmem
  rcases hmem with h1 | h1
  · exact startsWithOne_ne_empty h1
  · exact startsWithOne_ne_univ h1

/-- Under the literal definitions `def:pturing` and `def:npturing`, `P_Turing ≠ NP_Turing`.  This
"separation" is an artefact of the `n = 0` case of the literal time bound and says nothing about
the classical question. -/
theorem P_Turing_lit_ne_NP_Turing : P_Turing_lit ≠ NP_Turing := by
  intro h
  have hmem : startsWithOne ∈ P_Turing_lit := by
    rw [h, NP_Turing_eq_NP_TM]
    exact P_TM_subset_NP_TM (P_Turing_subset_P_TM startsWithOne_mem_P_Turing)
  rw [P_Turing_lit_eq] at hmem
  rcases hmem with h1 | h1
  · exact startsWithOne_ne_empty h1
  · exact startsWithOne_ne_univ h1

end PVNP.PartIITuring
