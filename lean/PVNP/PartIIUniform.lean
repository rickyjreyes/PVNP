import PVNP.PartIITwoPhase

/-!
# Part II, Definition `def:wcc_machine`: the uniform discrete WCC model

A uniform discrete WCC machine `W = ({Λ_n}, S, r, U, enc, dec)` has:
* a dimension `d ≥ 1` and a radius `r ≥ 0`;
* finite cell sets `Λ_n ⊂ ℤ^d` produced by a poly-time lattice algorithm;
* a fixed finite alphabet `S` with background symbol `s_∂`;
* one local rule `U : S^{{−r..r}^d} → S`;
* a poly-time encoder `enc`;
* a poly-time decoder `dec_n : S^{Λ_n} → {run, 0, 1}` that reads the canonical configuration
  encoding.

**Poly-time computable functions** (`FP`) are those computed by the manuscript's machine `MTM`
(`def:tm`) in polynomial time.  The output convention: the output `y` occupies cells
`0, …, |y|−1` as input symbols and cell `|y|` is blank (`MTM.Shows`).

**Representation conventions** (the manuscript fixes none):
* The lattice description is `1^R 0` followed by the membership bitmap of the box `[−R, R]^d`,
  listed by flattened index with axis `0` fastest (`latCode`).  The box contains `Λ_n` together
  with its radius-`r` neighbourhoods (`UWCC.margin`), so it "constructs and enumerates `Λ_n` and
  its fixed-radius neighbourhoods".
* The canonical configuration encoding lists the states of the cells of `Λ_n` in the same order,
  `w` bits each (`cfgCode`).
* The decoder reads `1^n 0` followed by the configuration code, and outputs `[]` for `run` and
  `[b]` for the bit `b`.
* The lattice algorithm reads any word of length `n` (unary `n`).

**Results.**
* `P_TM_subset_P_disc`: `P_TM ⊆ P^{disc}_{WCC}`.  This is the remark in Part II's formal-status
  paragraph that the encoder may compute the decision bit (`rem:verified-scope`).  The
  answer-writing machine `MTM.answerWriter` is explicit: it simulates the decider, tracks on which
  side of cell `0` the head is, walks back, and writes the answer.
* The converse inclusion `P^{disc}_{WCC} ⊆ P_TM` is **not** trivial.  It needs a Turing-machine
  simulation of the local rule on canonical codes, composed with the encoder and decoder; this is
  `PVNP.PartIIUniform.P_disc_subset_P_TM` in `PVNP.PartIIUniformEquiv` (the simulator is the
  sweep program of `PVNP.UniformSim`).  So the manuscript's sentence that the uniform equality
  "also holds for this trivial reason" is right only for the inclusion `P_Turing ⊆ P^{disc}_{WCC}`.
-/

/-! ## Poly-time computable functions -/

namespace PVNP.PartIITuring.MTM

variable (M : MTM)

/-- Output convention: `y` on cells `0, …, |y|−1`, cell `|y|` blank. -/
def Shows (c : M.Cfg) (y : List Bool) : Prop :=
  (∀ i : ℕ, i < y.length → c.tape i = M.inp (y.getD i false)) ∧ c.tape y.length = M.blank

/-- On input `z`, `M` halts within `B` steps with output `y`. -/
def Outputs (z : List Bool) (y : List Bool) (B : ℕ) : Prop :=
  ∃ t ≤ B, M.FirstHalt z t ∧ M.Shows (M.run (M.init z) t) y

/-- `M` computes `f` within the polynomial time bound `p`. -/
def ComputesIn (f : List Bool → List Bool) (p : Polynomial ℕ) : Prop :=
  ∀ x, M.Outputs x (f x) (p.eval x.length)

end PVNP.PartIITuring.MTM

namespace PVNP.PartIIUniform

open PVNP.Discrete PVNP.PartIITuring

/-- **Poly-time computable functions** on a standard deterministic Turing machine. -/
def FP (f : List Bool → List Bool) : Prop := ∃ (M : MTM) (p : Polynomial ℕ), M.ComputesIn f p

/-! ## Boxes, lattice descriptions and configuration codes -/

/-- Side length `2R + 1` of the box `[−R, R]^d`. -/
def side (R : ℕ) : ℕ := 2 * R + 1

/-- The site with flattened index `idx` (axis `0` varies fastest). -/
def site (d R idx : ℕ) : Fin d → ℤ :=
  fun k => (((idx / side R ^ (k : ℕ)) % side R : ℕ) : ℤ) - R

/-- Flattened indices of the box. -/
def boxIdx (d R : ℕ) : List ℕ := List.range (side R ^ d)

/-- Lattice description: `1^R 0` and the membership bitmap of `[−R, R]^d`. -/
def latCode (d R : ℕ) (Λ : Set (Fin d → ℤ)) [DecidablePred (· ∈ Λ)] : List Bool :=
  List.replicate R true ++ false :: (boxIdx d R).map fun idx => decide (site d R idx ∈ Λ)

/-- Canonical configuration encoding: the states of the cells of `Λ` in flattened order. -/
def cfgCode {S : Type} (bits : S → List Bool) (d R : ℕ) (Λ : Set (Fin d → ℤ))
    [DecidablePred (· ∈ Λ)] (C : (Fin d → ℤ) → S) : List Bool :=
  ((boxIdx d R).filter fun idx => decide (site d R idx ∈ Λ)).flatMap fun idx =>
    bits (C (site d R idx))

/-- Decoder output: `run ↦ []`, `b ↦ [b]`. -/
def decOut : Option Bool → List Bool
  | none => []
  | some b => [b]

/-! ## The uniform machine -/

/-- **Definition `def:wcc_machine`.** -/
structure UWCC where
  d : ℕ
  d_pos : 1 ≤ d
  r : ℕ
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  /-- background symbol `s_∂` -/
  sbd : S
  /-- the local rule on the neighbourhood `{−r, …, r}^d` -/
  U : ((Fin d → Fin (2 * r + 1)) → S) → S
  /-- fixed-width state codes -/
  w : ℕ
  bits : S → List Bool
  bits_len : ∀ s, (bits s).length = w
  bits_inj : Function.Injective bits
  /-- bounding-box radius and cell sets -/
  R : ℕ → ℕ
  Λ : ℕ → Set (Fin d → ℤ)
  [decΛ : ∀ n, DecidablePred (· ∈ Λ n)]
  /-- the box contains `Λ_n` and its radius-`r` neighbourhoods -/
  margin : ∀ n i, i ∈ Λ n → ∀ k, |i k| + r ≤ R n
  enc : List Bool → (Fin d → ℤ) → S
  dec : ℕ → ((Fin d → ℤ) → S) → Option Bool
  /-- uniform poly-time lattice algorithm (input: any word of length `n`) -/
  lat_fp : FP fun y => latCode d (R y.length) (Λ y.length)
  /-- uniform poly-time encoder -/
  enc_fp : FP fun x => cfgCode bits d (R x.length) (Λ x.length) (enc x)
  /-- uniform poly-time decoder on the canonical configuration encoding, in time `poly(n)` -/
  dec_fp : ∃ (D : MTM) (p : Polynomial ℕ), ∀ (n : ℕ) (C : (Fin d → ℤ) → S),
    D.Outputs (List.replicate n true ++ false :: cfgCode bits d (R n) (Λ n) C)
      (decOut (dec n C)) (p.eval n)

namespace UWCC

attribute [instance] UWCC.finS UWCC.decS UWCC.decΛ

variable (W : UWCC)

/-- Neighbourhood offset `v − r`. -/
def offset (v : Fin W.d → Fin (2 * W.r + 1)) : Fin W.d → ℤ := fun k => (v k : ℤ) - W.r

/-- Synchronous update on `Λ_n` with background `s_∂` outside. -/
def step (n : ℕ) (C : (Fin W.d → ℤ) → W.S) : (Fin W.d → ℤ) → W.S :=
  fun i => if i ∈ W.Λ n then W.U (fun v => C (i + W.offset v)) else W.sbd

/-- `C_0 = enc(x)` on `Λ_{|x|}`, background elsewhere. -/
def init (x : List Bool) : (Fin W.d → ℤ) → W.S :=
  fun i => if i ∈ W.Λ x.length then W.enc x i else W.sbd

/-- `C_t`. -/
def cfg (x : List Bool) (t : ℕ) : (Fin W.d → ℤ) → W.S := (W.step x.length)^[t] (W.init x)

end UWCC

/-- **Definition `def:pwcc`**: the first halting output appears within `p(|x|)` updates and
equals `1_L(x)`. -/
def P_disc : Set (Set (List Bool)) :=
  {L | ∃ (W : UWCC) (p : Polynomial ℕ), ∀ x, ∃ t ≤ p.eval x.length,
    (∀ s < t, W.dec x.length (W.cfg x s) = none) ∧
      ∃ b, W.dec x.length (W.cfg x t) = some b ∧ (b = true ↔ x ∈ L)}

end PVNP.PartIIUniform

/-! ## Explicit machines -/

namespace PVNP.PartIITuring

/-- Control states of the answer writer. -/
inductive AQ (Q : Type) where
  | mark
  | sim (q : Q) (left : Bool)
  | walkR (b : Bool)
  | walkL (b : Bool)
  | blk
  | done
  deriving DecidableEq, Fintype

namespace MTM

variable (M : MTM)

/-- Transition function of the answer writer. -/
def awδ : AQ M.Q → M.Γ × Bool → AQ M.Q × (M.Γ × Bool) × Mv
  | .mark, (a, _) =>
    if M.q0 = M.qacc ∨ M.q0 = M.qrej then
      (.blk, (M.inp (decide (M.q0 = M.qacc)), false), .R)
    else ((.sim (M.δ M.q0 a).1 (decide ((M.δ M.q0 a).2.2 = .L))),
      ((M.δ M.q0 a).2.1, true), (M.δ M.q0 a).2.2)
  | .sim q s, (a, m) =>
    if q = M.qacc ∨ q = M.qrej then
      (if m then (.blk, (M.inp (decide (q = M.qacc)), false), .R)
       else if s then (.walkR (decide (q = M.qacc)), (a, m), .R)
       else (.walkL (decide (q = M.qacc)), (a, m), .L))
    else (.sim (M.δ q a).1 (if m then decide ((M.δ q a).2.2 = .L) else s),
      ((M.δ q a).2.1, m), (M.δ q a).2.2)
  | .walkR b, (a, m) => if m then (.blk, (M.inp b, false), .R) else (.walkR b, (a, m), .R)
  | .walkL b, (a, m) => if m then (.blk, (M.inp b, false), .R) else (.walkL b, (a, m), .L)
  | .blk, _ => (.done, (M.blank, false), .R)
  | .done, g => (.done, g, .R)

/-- **The answer writer**: computes `x ↦ [M accepts x]` from a decider `M`. -/
def answerWriter : MTM where
  Q := AQ M.Q
  Γ := M.Γ × Bool
  blank := (M.blank, false)
  inp b := (M.inp b, false)
  inp_inj := fun _ _ h => M.inp_inj (Prod.ext_iff.1 h).1
  inp_ne_blank := fun b h => M.inp_ne_blank b (Prod.ext_iff.1 h).1
  δ := M.awδ
  q0 := .mark
  qacc := .done
  qrej := .done

theorem aw_step (c : M.answerWriter.Cfg) :
    M.answerWriter.step c = ⟨Function.update c.tape c.head (M.awδ c.q (c.tape c.head)).2.1,
      c.head + (M.awδ c.q (c.tape c.head)).2.2.shift, (M.awδ c.q (c.tape c.head)).1⟩ := rfl

/-- The marked encoding of a configuration of `M`. -/
def awTape (T : ℤ → M.Γ) (i : ℤ) : M.Γ × Bool := (T i, decide (i = 0))

theorem aw_init_tape (x : List Bool) (i : ℤ) :
    M.answerWriter.inputTape x i = (M.inputTape x i, false) := by
  unfold MTM.inputTape
  split_ifs <;> rfl

/-- Simulation phase: for `1 ≤ t ≤ T`, the writer is in `sim q_t s` on the marked tape. -/
theorem aw_sim (x : List Bool) {T : ℕ} (hT : M.FirstHalt x T) (hT0 : 0 < T) :
    ∀ t, 1 ≤ t → t ≤ T → ∃ s : Bool,
      M.answerWriter.run (M.answerWriter.init x) t =
        ⟨M.awTape (M.run (M.init x) t).tape, (M.run (M.init x) t).head,
          .sim (M.run (M.init x) t).q s⟩ ∧
      ((M.run (M.init x) t).head ≠ 0 → s = decide ((M.run (M.init x) t).head < 0))
  | 0, h1, _ => absurd h1 (by omega)
  | 1, _, _ => by
    have hq0 : ¬ (M.q0 = M.qacc ∨ M.q0 = M.qrej) := hT.2 0 hT0
    refine ⟨decide ((M.δ M.q0 (M.inputTape x 0)).2.2 = .L), ?_, ?_⟩
    · show M.answerWriter.step (M.answerWriter.init x) = _
      rw [aw_step]
      show (⟨Function.update (M.answerWriter.inputTape x) 0
          (M.awδ .mark (M.answerWriter.inputTape x 0)).2.1,
        0 + (M.awδ .mark (M.answerWriter.inputTape x 0)).2.2.shift,
        (M.awδ .mark (M.answerWriter.inputTape x 0)).1⟩ : M.answerWriter.Cfg) = _
      rw [aw_init_tape]
      simp only [awδ, if_neg hq0]
      have h1 : M.run (M.init x) 1 = M.step (M.init x) := rfl
      rw [h1]
      simp only [MTM.step, MTM.init, zero_add]
      congr 1
      funext i
      by_cases hi : i = 0
      · subst hi; simp [awTape]
      · simp [awTape, hi, aw_init_tape]
    · intro hne
      have h1 : M.run (M.init x) 1 = M.step (M.init x) := rfl
      rw [h1] at hne ⊢
      simp only [MTM.step, MTM.init, zero_add] at hne ⊢
      cases (M.δ M.q0 (M.inputTape x 0)).2.2 <;> simp [Mv.shift]
  | t + 2, _, ht => by
    obtain ⟨s, hrun, hs⟩ := aw_sim x hT hT0 (t + 1) (by omega) (by omega)
    have hnh : ¬ ((M.run (M.init x) (t + 1)).q = M.qacc ∨
        (M.run (M.init x) (t + 1)).q = M.qrej) := hT.2 (t + 1) (by omega)
    have hsucc : M.run (M.init x) (t + 2) = M.step (M.run (M.init x) (t + 1)) := M.run_succ _ _
    rw [hsucc]
    generalize M.run (M.init x) (t + 1) = c at hrun hs hnh ⊢
    have hδ : M.awδ (.sim c.q s) (M.awTape c.tape c.head) =
        (.sim (M.δ c.q (c.tape c.head)).1
          (if decide (c.head = 0) then decide ((M.δ c.q (c.tape c.head)).2.2 = .L) else s),
          ((M.δ c.q (c.tape c.head)).2.1, decide (c.head = 0)), (M.δ c.q (c.tape c.head)).2.2) := by
      simp only [awδ, awTape, if_neg hnh]
    refine ⟨if c.head = 0 then decide ((M.δ c.q (c.tape c.head)).2.2 = .L) else s, ?_, ?_⟩
    · rw [MTM.run_succ, hrun, aw_step]
      show (⟨Function.update (M.awTape c.tape) c.head (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).2.1,
        c.head + (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).2.2.shift,
        (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).1⟩ : M.answerWriter.Cfg) = _
      rw [hδ]
      simp only [MTM.step]
      congr 1
      · funext i
        by_cases hi : i = c.head
        · subst hi; simp [awTape]
        · simp [Function.update_of_ne hi, awTape]
      · by_cases h0 : c.head = 0 <;> simp [h0]
    · intro hne
      simp only [MTM.step] at hne ⊢
      by_cases h0 : c.head = 0
      · rw [if_pos h0]
        have key : ∀ m : Mv, decide (m = Mv.L) = decide (c.head + m.shift < 0) := by
          intro m; cases m <;> simp [Mv.shift, h0]
        exact key _
      · rw [if_neg h0, hs h0]
        have hst : ∀ m : Mv, c.head + m.shift ≠ 0 →
            decide (c.head < 0) = decide (c.head + m.shift < 0) := by
          intro m hm'
          cases m <;> simp [Mv.shift] at hm' ⊢ <;> omega
        exact hst _ hne

theorem aw_halting_iff (q : AQ M.Q) : M.answerWriter.Halting q ↔ q = .done := by
  show q = AQ.done ∨ q = AQ.done ↔ _
  exact or_self_iff

/-- Walking right over unmarked cells. -/
theorem aw_walkR (b : Bool) (T : ℤ → M.Γ × Bool) :
    ∀ (k : ℕ) (p : ℤ), (∀ j : ℕ, j < k → (T (p + j)).2 = false) →
      M.answerWriter.run ⟨T, p, .walkR b⟩ k = ⟨T, p + k, .walkR b⟩
  | 0, p, _ => by simp [MTM.run]
  | k + 1, p, h => by
    rw [MTM.run_succ, aw_walkR b T k p (fun j hj => h j (by omega)), aw_step]
    have hm : (T (p + k)).2 = false := h k (by omega)
    rcases hT : T (p + k) with ⟨a, m⟩
    rw [hT] at hm
    simp only at hm
    subst hm
    simp only [awδ, hT, Bool.false_eq_true, if_false]
    rw [← hT, Function.update_eq_self]
    simp [Mv.shift]; ring

/-- Walking left over unmarked cells. -/
theorem aw_walkL (b : Bool) (T : ℤ → M.Γ × Bool) :
    ∀ (k : ℕ) (p : ℤ), (∀ j : ℕ, j < k → (T (p - j)).2 = false) →
      M.answerWriter.run ⟨T, p, .walkL b⟩ k = ⟨T, p - k, .walkL b⟩
  | 0, p, _ => by simp [MTM.run]
  | k + 1, p, h => by
    rw [MTM.run_succ, aw_walkL b T k p (fun j hj => h j (by omega)), aw_step]
    have hm : (T (p - k)).2 = false := h k (by omega)
    rcases hT : T (p - k) with ⟨a, m⟩
    rw [hT] at hm
    simp only at hm
    subst hm
    simp only [awδ, hT, Bool.false_eq_true, if_false]
    rw [← hT, Function.update_eq_self]
    simp [Mv.shift]; ring

theorem aw_walkR_states (b : Bool) (T : ℤ → M.Γ × Bool) (k : ℕ) (p : ℤ)
    (h : ∀ j : ℕ, j < k → (T (p + j)).2 = false) :
    ∀ j ≤ k, (M.answerWriter.run ⟨T, p, .walkR b⟩ j).q = .walkR b := by
  intro j hj
  rw [M.aw_walkR b T j p (fun i hi => h i (by omega))]

theorem aw_walkL_states (b : Bool) (T : ℤ → M.Γ × Bool) (k : ℕ) (p : ℤ)
    (h : ∀ j : ℕ, j < k → (T (p - j)).2 = false) :
    ∀ j ≤ k, (M.answerWriter.run ⟨T, p, .walkL b⟩ j).q = .walkL b := by
  intro j hj
  rw [M.aw_walkL b T j p (fun i hi => h i (by omega))]

/-- The final two steps: at the marked cell `0`, write the answer, then blank cell `1`. -/
theorem aw_finish (T : ℤ → M.Γ × Bool) (b : Bool) (q : AQ M.Q)
    (hq : (M.awδ q (T 0)) = (.blk, (M.inp b, false), .R)) :
    M.answerWriter.run ⟨T, 0, q⟩ 2 =
        ⟨Function.update (Function.update T 0 (M.inp b, false)) 1 (M.blank, false), 2, .done⟩ ∧
      (M.answerWriter.run ⟨T, 0, q⟩ 1).q = .blk := by
  have h1 : M.answerWriter.run ⟨T, 0, q⟩ 1 = ⟨Function.update T 0 (M.inp b, false), 1, .blk⟩ := by
    show M.answerWriter.step _ = _
    rw [aw_step]
    show (⟨Function.update T 0 (M.awδ q (T 0)).2.1, 0 + (M.awδ q (T 0)).2.2.shift,
      (M.awδ q (T 0)).1⟩ : M.answerWriter.Cfg) = _
    rw [hq]; simp [Mv.shift]
  refine ⟨?_, by rw [h1]⟩
  rw [show (2 : ℕ) = 1 + 1 from rfl, MTM.run_succ, h1, aw_step]
  simp [awδ, Mv.shift]

theorem awTape_mark (T : ℤ → M.Γ) (i : ℤ) : (M.awTape T i).2 = decide (i = 0) := rfl

/-- **The answer writer outputs the verdict of `M`** within `2T + 2` steps, where `T` is the first
halting time of `M`. -/
theorem answerWriter_outputs (x : List Bool) {T : ℕ} (hT : M.FirstHalt x T) :
    M.answerWriter.Outputs x [decide ((M.run (M.init x) T).q = M.qacc)] (2 * T + 2) := by
  set b := decide ((M.run (M.init x) T).q = M.qacc) with hb
  -- the output shape after the final two steps
  have hshow : ∀ (Tp : ℤ → M.Γ × Bool), M.answerWriter.Shows
      ⟨Function.update (Function.update Tp 0 (M.inp b, false)) 1 (M.blank, false), 2, .done⟩
      [b] := by
    intro Tp
    refine ⟨fun i hi => ?_, ?_⟩
    · have : i = 0 := by simp at hi; omega
      subst this
      simp
      rfl
    · simp; rfl
  rcases Nat.eq_zero_or_pos T with hT0 | hT0
  · -- `q₀` halts: the mark step writes the answer at once
    subst hT0
    have hq0 : M.q0 = M.qacc ∨ M.q0 = M.qrej := hT.1
    have hfin := M.aw_finish (M.answerWriter.inputTape x) b .mark (by
      show M.awδ .mark (M.answerWriter.inputTape x 0) = _
      rw [aw_init_tape]
      simp only [awδ, if_pos hq0]
      rfl)
    refine ⟨2, by omega, ⟨?_, fun s hs => ?_⟩, ?_⟩
    · rw [(M.aw_halting_iff _)]
      show (M.answerWriter.run ⟨M.answerWriter.inputTape x, 0, .mark⟩ 2).q = _
      rw [hfin.1]
    · rw [M.aw_halting_iff]
      interval_cases s
      · show AQ.mark ≠ AQ.done
        exact AQ.noConfusion
      · show (M.answerWriter.run ⟨M.answerWriter.inputTape x, 0, .mark⟩ 1).q ≠ _
        rw [hfin.2]; exact AQ.noConfusion
    · show M.answerWriter.Shows (M.answerWriter.run ⟨M.answerWriter.inputTape x, 0, .mark⟩ 2) [b]
      rw [hfin.1]; exact hshow _
  · obtain ⟨s, hrun, hs⟩ := M.aw_sim x hT hT0 T hT0 le_rfl
    set c := M.run (M.init x) T with hc
    have hq : c.q = M.qacc ∨ c.q = M.qrej := hT.1
    have hhb := PVNP.PartIITwoPhase.head_bound M x T
    rw [← hc] at hhb
    obtain ⟨hhl, hhr⟩ := abs_le.1 hhb
    have hsimstates : ∀ u ≤ T, ¬ M.answerWriter.Halting (M.answerWriter.run (M.answerWriter.init x) u).q := by
      intro u hu
      rw [M.aw_halting_iff]
      rcases Nat.eq_zero_or_pos u with hu0 | hu0
      · subst hu0; exact AQ.noConfusion
      · obtain ⟨s', hr', -⟩ := M.aw_sim x hT hT0 u hu0 hu
        rw [hr']; exact AQ.noConfusion
    rcases lt_trichotomy c.head 0 with hneg | hzero | hpos
    · -- walk right
      have hsT : s = true := by rw [hs hneg.ne]; simp [hneg]
      have hstep1 : M.answerWriter.run (M.answerWriter.init x) (T + 1) =
          ⟨M.awTape c.tape, c.head + 1, .walkR b⟩ := by
        rw [MTM.run_succ, hrun, aw_step]
        have hδ : M.awδ (.sim c.q s) (M.awTape c.tape c.head) =
            (.walkR b, M.awTape c.tape c.head, .R) := by
          simp [awδ, awTape, hq, hsT, hb, hneg.ne]
        show (⟨Function.update (M.awTape c.tape) c.head
            (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).2.1,
          c.head + (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).2.2.shift,
          (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).1⟩ : M.answerWriter.Cfg) = _
        rw [hδ, Function.update_eq_self]; rfl
      set k := (-c.head - 1).toNat with hk
      have hkk : (k : ℤ) = -c.head - 1 := by rw [hk]; omega
      have hunm : ∀ j : ℕ, j < k → (M.awTape c.tape (c.head + 1 + j)).2 = false := by
        intro j hj; rw [awTape_mark]; simp; omega
      have hwalk := M.aw_walkR b (M.awTape c.tape) k (c.head + 1) hunm
      have hpos0 : c.head + 1 + (k : ℤ) = 0 := by omega
      rw [hpos0] at hwalk
      have hfin := M.aw_finish (M.awTape c.tape) b (.walkR b) (by
        simp [awδ, awTape_mark])
      have htot : M.answerWriter.run (M.answerWriter.init x) (T + 1 + k + 2) =
          ⟨Function.update (Function.update (M.awTape c.tape) 0 (M.inp b, false)) 1
            (M.blank, false), 2, .done⟩ := by
        rw [MTM.run_add, MTM.run_add, hstep1, hwalk, hfin.1]
      refine ⟨T + 1 + k + 2, by omega, ⟨?_, fun u hu => ?_⟩, ?_⟩
      · rw [htot, M.aw_halting_iff]
      · by_cases hu1 : u ≤ T
        · exact hsimstates u hu1
        · rw [M.aw_halting_iff]
          by_cases hu2 : u ≤ T + 1 + k
          · obtain ⟨j, rfl⟩ : ∃ j, u = T + 1 + j := ⟨u - (T + 1), by omega⟩
            rw [MTM.run_add, hstep1,
              M.aw_walkR_states b (M.awTape c.tape) k (c.head + 1) hunm j (by omega)]
            exact AQ.noConfusion
          · have : u = T + 1 + k + 1 := by omega
            subst this
            rw [MTM.run_add, MTM.run_add, hstep1, hwalk, hfin.2]
            exact AQ.noConfusion
      · rw [htot]; exact hshow _
    · -- already at cell `0`
      have hfin := M.aw_finish (M.awTape c.tape) b (.sim c.q s) (by
        simp [awδ, awTape_mark, if_pos hq, hb])
      have htot : M.answerWriter.run (M.answerWriter.init x) (T + 2) =
          ⟨Function.update (Function.update (M.awTape c.tape) 0 (M.inp b, false)) 1
            (M.blank, false), 2, .done⟩ := by
        rw [MTM.run_add, hrun, hzero, hfin.1]
      refine ⟨T + 2, by omega, ⟨?_, fun u hu => ?_⟩, ?_⟩
      · rw [htot, M.aw_halting_iff]
      · by_cases hu1 : u ≤ T
        · exact hsimstates u hu1
        · have : u = T + 1 := by omega
          subst this
          rw [M.aw_halting_iff, MTM.run_add, hrun, hzero, hfin.2]
          exact AQ.noConfusion
      · rw [htot]; exact hshow _
    · -- walk left
      have hsF : s = false := by rw [hs hpos.ne']; simp; omega
      have hstep1 : M.answerWriter.run (M.answerWriter.init x) (T + 1) =
          ⟨M.awTape c.tape, c.head - 1, .walkL b⟩ := by
        rw [MTM.run_succ, hrun, aw_step]
        have hδ : M.awδ (.sim c.q s) (M.awTape c.tape c.head) =
            (.walkL b, M.awTape c.tape c.head, .L) := by
          simp [awδ, awTape, hq, hsF, hb, hpos.ne']
        show (⟨Function.update (M.awTape c.tape) c.head
            (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).2.1,
          c.head + (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).2.2.shift,
          (M.awδ (.sim c.q s) (M.awTape c.tape c.head)).1⟩ : M.answerWriter.Cfg) = _
        rw [hδ, Function.update_eq_self]
        simp only [Mv.shift]; congr 1
      set k := (c.head - 1).toNat with hk
      have hkk : (k : ℤ) = c.head - 1 := by rw [hk]; omega
      have hunm : ∀ j : ℕ, j < k → (M.awTape c.tape (c.head - 1 - j)).2 = false := by
        intro j hj; rw [awTape_mark]; simp; omega
      have hwalk := M.aw_walkL b (M.awTape c.tape) k (c.head - 1) hunm
      have hpos0 : c.head - 1 - (k : ℤ) = 0 := by omega
      rw [hpos0] at hwalk
      have hfin := M.aw_finish (M.awTape c.tape) b (.walkL b) (by
        simp [awδ, awTape_mark])
      have htot : M.answerWriter.run (M.answerWriter.init x) (T + 1 + k + 2) =
          ⟨Function.update (Function.update (M.awTape c.tape) 0 (M.inp b, false)) 1
            (M.blank, false), 2, .done⟩ := by
        rw [MTM.run_add, MTM.run_add, hstep1, hwalk, hfin.1]
      refine ⟨T + 1 + k + 2, by omega, ⟨?_, fun u hu => ?_⟩, ?_⟩
      · rw [htot, M.aw_halting_iff]
      · by_cases hu1 : u ≤ T
        · exact hsimstates u hu1
        · rw [M.aw_halting_iff]
          by_cases hu2 : u ≤ T + 1 + k
          · obtain ⟨j, rfl⟩ : ∃ j, u = T + 1 + j := ⟨u - (T + 1), by omega⟩
            rw [MTM.run_add, hstep1,
              M.aw_walkL_states b (M.awTape c.tape) k (c.head - 1) hunm j (by omega)]
            exact AQ.noConfusion
          · have : u = T + 1 + k + 1 := by omega
            subst this
            rw [MTM.run_add, MTM.run_add, hstep1, hwalk, hfin.2]
            exact AQ.noConfusion
      · rw [htot]; exact hshow _

end MTM

end PVNP.PartIITuring

/-! ## Two fixed machines -/

namespace PVNP.PartIIUniform

open PVNP.Discrete PVNP.PartIITuring

/-- A machine writing `[0, 1]` on cells `0, 1` and a blank on cell `2`. -/
def latMTM : MTM where
  Q := Fin 4
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank := fun _ => Option.some_ne_none _
  δ q a := match q with
    | 0 => (1, some false, .R)
    | 1 => (2, some true, .R)
    | 2 => (3, none, .R)
    | _ => (3, a, .R)
  q0 := 0
  qacc := 3
  qrej := 3

theorem latMTM_outputs (y : List Bool) : latMTM.Outputs y [false, true] 3 := by
  refine ⟨3, le_rfl, ⟨Or.inl rfl, fun s hs => ?_⟩, ?_, ?_⟩
  · interval_cases s
    · show ¬ ((0 : Fin 4) = 3 ∨ (0 : Fin 4) = 3); decide
    · show ¬ ((1 : Fin 4) = 3 ∨ (1 : Fin 4) = 3); decide
    · show ¬ ((2 : Fin 4) = 3 ∨ (2 : Fin 4) = 3); decide
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi' with rfl | rfl <;> rfl
  · rfl

/-- States of the decoder of the one-cell machine. -/
inductive DQ where
  | scan
  | get
  | back (b : Bool)
  | put (b : Bool)
  | blk
  | done
  deriving DecidableEq, Fintype

/-- Transition function of the decoder. -/
def decδ : DQ → Option Bool → DQ × Option Bool × Mv
  | .scan, a => if a = some true then (.scan, a, .R) else (.get, a, .R)
  | .get, a => (.back (decide (a = some true)), a, .L)
  | .back b, a => if a = none then (.put b, a, .R) else (.back b, a, .L)
  | .put b, _ => (.blk, some b, .R)
  | .blk, _ => (.done, none, .R)
  | .done, a => (.done, a, .R)

/-- The decoder of the one-cell machine: reads `1^n 0 b` and outputs `[b]`. -/
def decMTM : MTM where
  Q := DQ
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank := fun _ => Option.some_ne_none _
  δ := decδ
  q0 := .scan
  qacc := .done
  qrej := .done

theorem decMTM_step (c : decMTM.Cfg) :
    decMTM.step c = ⟨Function.update c.tape c.head (decδ c.q (c.tape c.head)).2.1,
      c.head + (decδ c.q (c.tape c.head)).2.2.shift, (decδ c.q (c.tape c.head)).1⟩ := rfl

theorem decMTM_halting (q : DQ) : decMTM.Halting q ↔ q = .done := or_self_iff

section DecRun

variable (n : ℕ) (b : Bool)

/-- The decoder's input `1^n 0 b`. -/
abbrev decIn : List Bool := List.replicate n true ++ false :: [b]

theorem decIn_length : (decIn n b).length = n + 2 := by simp

theorem t_lt (j : ℕ) (hj : j < n) : decMTM.inputTape (decIn n b) j = some true := by
  unfold MTM.inputTape
  rw [if_pos ⟨by omega, by rw [decIn_length]; push_cast; omega⟩]
  simp only [Int.toNat_natCast, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
  simp [hj]; rfl

theorem t_n : decMTM.inputTape (decIn n b) n = some false := by
  unfold MTM.inputTape
  rw [if_pos ⟨by omega, by rw [decIn_length]; push_cast; omega⟩]
  simp only [Int.toNat_natCast, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self]
  rfl

theorem t_n1 : decMTM.inputTape (decIn n b) ((n : ℤ) + 1) = some b := by
  unfold MTM.inputTape
  rw [if_pos ⟨by omega, by rw [decIn_length]; push_cast; omega⟩]
  rw [show ((n : ℤ) + 1).toNat = n + 1 by omega]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), List.length_replicate,
    show n + 1 - n = 1 by omega]
  rfl

theorem t_neg : decMTM.inputTape (decIn n b) (-1) = none := by
  unfold MTM.inputTape
  rw [if_neg (by omega)]
  rfl

theorem t_ne_none (j : ℕ) (hj : j ≤ n) : decMTM.inputTape (decIn n b) j ≠ none := by
  rcases Nat.lt_or_eq_of_le hj with h | rfl
  · rw [t_lt n b j h]; exact Option.some_ne_none _
  · rw [t_n]; exact Option.some_ne_none _

theorem dec_scan : ∀ j ≤ n, decMTM.run (decMTM.init (decIn n b)) j =
    ⟨decMTM.inputTape (decIn n b), j, .scan⟩
  | 0, _ => rfl
  | j + 1, hj => by
    rw [MTM.run_succ, dec_scan j (by omega), decMTM_step]
    have ht := t_lt n b j (by omega)
    simp only [decδ, ht, if_true]
    rw [Function.update_eq_self_iff.2 ht.symm]
    simp [Mv.shift]

theorem dec_get : decMTM.run (decMTM.init (decIn n b)) (n + 1) =
    ⟨decMTM.inputTape (decIn n b), (n : ℤ) + 1, .get⟩ := by
  rw [MTM.run_succ, dec_scan n b n le_rfl, decMTM_step]
  have hn := t_n n b
  simp only [decδ, hn, Option.some.injEq, Bool.false_eq_true, if_false]
  rw [Function.update_eq_self_iff.2 hn.symm]
  simp [Mv.shift]

theorem dec_back : ∀ j ≤ n + 1, decMTM.run (decMTM.init (decIn n b)) (n + 2 + j) =
    ⟨decMTM.inputTape (decIn n b), (n : ℤ) - j, .back b⟩
  | 0, _ => by
    rw [show n + 2 + 0 = (n + 1) + 1 by omega, MTM.run_succ, dec_get, decMTM_step]
    have hn1 := t_n1 n b
    simp only [decδ, hn1]
    rw [Function.update_eq_self_iff.2 hn1.symm]
    cases b <;> simp [Mv.shift]
  | j + 1, hj => by
    rw [show n + 2 + (j + 1) = (n + 2 + j) + 1 by omega, MTM.run_succ, dec_back j (by omega),
      decMTM_step]
    have hne : decMTM.inputTape (decIn n b) ((n : ℤ) - j) ≠ none := by
      have := t_ne_none n b (n - j) (by omega)
      rwa [show ((n - j : ℕ) : ℤ) = (n : ℤ) - j by omega] at this
    simp only [decδ, if_neg hne, Function.update_eq_self]
    simp [Mv.shift]; ring

theorem decMTM_outputs : decMTM.Outputs (decIn n b) [b] (2 * n + 6) := by
  have hback := dec_back n b (n + 1) le_rfl
  have hm1 := t_neg n b
  set T0 := decMTM.inputTape (decIn n b) with hT0
  have h1 : decMTM.run (decMTM.init (decIn n b)) (2 * n + 4) = ⟨T0, 0, .put b⟩ := by
    rw [show 2 * n + 4 = (n + 2 + (n + 1)) + 1 by omega, MTM.run_succ, hback, decMTM_step]
    have : ((n : ℤ) - ((n + 1 : ℕ) : ℤ)) = -1 := by push_cast; ring
    simp only [this, decδ, hm1, if_true]
    rw [(Function.update_eq_self_iff (f := T0) (a := (-1 : ℤ)) (b := (none : Option Bool))).2
      hm1.symm]
    simp [Mv.shift]
  have h2 : decMTM.run (decMTM.init (decIn n b)) (2 * n + 5) =
      ⟨Function.update T0 0 (some b), 1, .blk⟩ := by
    rw [MTM.run_succ, h1, decMTM_step]; simp [decδ, Mv.shift]
  have h3 : decMTM.run (decMTM.init (decIn n b)) (2 * n + 6) =
      ⟨Function.update (Function.update T0 0 (some b)) 1 none, 2, .done⟩ := by
    rw [MTM.run_succ, h2, decMTM_step]; simp [decδ, Mv.shift]
  refine ⟨2 * n + 6, le_rfl, ⟨?_, fun s hs => ?_⟩, ?_⟩
  · rw [h3, decMTM_halting]
  · rw [decMTM_halting]
    by_cases hs1 : s ≤ n
    · rw [dec_scan n b s hs1]; exact DQ.noConfusion
    · by_cases hs2 : s = n + 1
      · subst hs2; rw [dec_get]; exact DQ.noConfusion
      · by_cases hs3 : s ≤ 2 * n + 3
        · obtain ⟨j, rfl⟩ : ∃ j, s = n + 2 + j := ⟨s - (n + 2), by omega⟩
          rw [dec_back n b j (by omega)]; exact DQ.noConfusion
        · by_cases hs4 : s = 2 * n + 4
          · subst hs4; rw [h1]; exact DQ.noConfusion
          · have : s = 2 * n + 5 := by omega
            subst this; rw [h2]; exact DQ.noConfusion
  · rw [h3]
    refine ⟨fun i hi => ?_, ?_⟩
    · have : i = 0 := by simp at hi; omega
      subst this; simp; rfl
    · simp; rfl

end DecRun

end PVNP.PartIIUniform

/-! ## `P_TM ⊆ P^{disc}_{WCC}`: the encoder computes the decision bit -/

namespace PVNP.PartIIUniform

open PVNP.Discrete PVNP.PartIITuring Classical

theorem MTM.outputs_mono {M : MTM} {z y : List Bool} {B B' : ℕ} (h : M.Outputs z y B)
    (hB : B ≤ B') : M.Outputs z y B' := by
  obtain ⟨t, ht, h1, h2⟩ := h
  exact ⟨t, ht.trans hB, h1, h2⟩

theorem site_one_zero : site 1 0 0 = 0 := by
  funext k; simp [site, side]

theorem boxIdx_one_zero : boxIdx 1 0 = [0] := by simp [boxIdx, side]

theorem latCode_one (Λ : Set (Fin 1 → ℤ)) [DecidablePred (· ∈ Λ)]
    (h0 : (0 : Fin 1 → ℤ) ∈ Λ) : latCode 1 0 Λ = [false, true] := by
  simp [latCode, boxIdx_one_zero, site_one_zero, h0]

theorem cfgCode_one {S : Type} (bits : S → List Bool) (Λ : Set (Fin 1 → ℤ))
    [DecidablePred (· ∈ Λ)] (h0 : (0 : Fin 1 → ℤ) ∈ Λ) (C : (Fin 1 → ℤ) → S) :
    cfgCode bits 1 0 Λ C = bits (C 0) := by
  simp [cfgCode, boxIdx_one_zero, site_one_zero, h0]

/-- **The one-cell uniform machine** of a decider `M`: one cell, radius `0`, the identity rule.
The encoder writes the decision bit computed by `M` (`MTM.answerWriter`), and the decoder reads
that cell. -/
noncomputable def oneCell (M : MTM) (c k : ℕ)
    (hT : ∀ x, M.HaltsWithin x (c * max x.length 1 ^ k)) : UWCC where
  d := 1
  d_pos := le_rfl
  r := 0
  S := Bool
  sbd := false
  U := fun nb => nb (fun _ => ⟨0, by norm_num⟩)
  w := 1
  bits b := [b]
  bits_len _ := rfl
  bits_inj := fun _ _ h => by simpa using h
  R := fun _ => 0
  Λ := fun _ => {0}
  decΛ := fun _ i => decidable_of_iff (i = 0) Set.mem_singleton_iff.symm
  margin := by
    intro n i hi k
    rw [Set.mem_singleton_iff] at hi
    subst hi; simp
  enc x _ := decide (M.Accepts x)
  dec _ C := some (C 0)
  lat_fp := ⟨latMTM, Polynomial.C 3, fun y => by
    simp only [latCode, boxIdx_one_zero, site_one_zero, List.replicate_zero, List.nil_append,
      List.map_cons, List.map_nil, Set.mem_singleton_iff, decide_true, Polynomial.eval_C]
    exact latMTM_outputs y⟩
  enc_fp := ⟨M.answerWriter, 2 * (Polynomial.C c * (Polynomial.X + 1) ^ k) + 2, fun x => by
    simp only [cfgCode, boxIdx_one_zero, site_one_zero, Set.mem_singleton_iff, decide_true,
      List.filter_cons_of_pos, List.filter_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    obtain ⟨T, hTc, hf⟩ := hT x
    have hacc : decide (M.Accepts x) = decide ((M.run (M.init x) T).q = M.qacc) := by
      rw [Bool.decide_congr (M.accepts_iff_of_firstHalt hf)]
    rw [hacc]
    refine MTM.outputs_mono (M.answerWriter_outputs x hf) ?_
    have := cmax_le_poly c k x.length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at this ⊢
    omega⟩
  dec_fp := ⟨decMTM, 2 * Polynomial.X + 6, fun n C => by
    simp only [cfgCode, boxIdx_one_zero, site_one_zero, Set.mem_singleton_iff, decide_true,
      List.filter_cons_of_pos, List.filter_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    simpa [decOut] using decMTM_outputs n (C 0)⟩

/-- **`P_Turing ⊆ P^{disc}_{WCC}`** for the uniform model of `def:wcc_machine`: the poly-time
encoder may compute the decision bit (Part II, `rem:verified-scope` and formal-status
paragraph). -/
theorem P_Turing_subset_P_disc : P_Turing ⊆ P_disc := by
  rintro L ⟨M, c, k, -, -, hT, hL⟩
  refine ⟨oneCell M c k hT, 0, fun x =>
    ⟨0, Nat.zero_le _, fun s hs => absurd hs (Nat.not_lt_zero _), decide (M.Accepts x), ?_, ?_⟩⟩
  · show some ((oneCell M c k hT).init x 0) = _
    simp [UWCC.init, oneCell]
  · rw [decide_eq_true_iff, hL x]

/-- **`P_TM ⊆ P^{disc}_{WCC}`.** -/
theorem P_TM_subset_P_disc : P_TM ⊆ P_disc :=
  fun _ h => P_Turing_subset_P_disc (P_TM_subset_P_Turing h)

end PVNP.PartIIUniform
