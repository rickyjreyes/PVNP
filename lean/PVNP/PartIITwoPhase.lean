import PVNP.PartIITuringModel

/-!
# Part II: the two-phase simulation `W_M` of a Turing machine

Literal formalization of the construction in Part II §"Simulation of polynomial-time Turing
machines by WCC":
* the alphabet of `def:local_state`;
* the phase-0 and phase-1 rules, with the phase-1 cases in the manuscript's order;
* the window `Λ_n = {−L(n), …, L(n)}` with background symbol (`def:wcc_machine`, item 2);
* `enc_M` and `dec_M` of `def:wm`.

**Alphabet.**  `S = Γ × (Q' ∪ {⊥}) × {0,1}` with `Q' = Q ∪ {(q,L)} ∪ {(q,R)}`.  In Lean the head
component is `Option (Q ⊕ Q × {L,R})`, and the phase bit `0`/`1` is `false`/`true`.  The
background symbol is `s_∂ = (␣, ⊥, 0)`; the manuscript does not name it for `W_M`.  The rule on
states the manuscript leaves unspecified (a directional mark in phase 0) keeps the mark.  These
states are never reached.

**Results.**
* `two_steps`: **Proposition `prop:local-tm`**.  Two applications of the radius-one rule realize
  one transition of `M`.
* `one_step`: **Lemma `lem:one_step`**.  `C_{2t}` encodes the Turing configuration after `t`
  steps for every `t` up to the time the head first leaves `Λ_n`, in particular for all
  `t ≤ L(n) + 1`, hence for all `t ≤ T_M(n)`.
* `invariant_even`, `invariant_odd`: **Lemma `lem:invariant`**, on the same range.
* `runtime`, `tm_to_wcc_decides`: **Lemma `lem:runtime`** and the decision part of
  **Theorem `thm:tm_to_wcc`**.  The first output of `dec_M` appears at time exactly `2·T_M(x)`
  and is `1` iff `M` accepts.  `card_window` gives `|Λ_n| = 2L(n) + 1`.

**Literal quantifier.**  `lem:invariant` and `lem:one_step` are stated "for all `t ≥ 0`".  This
fails once the head leaves `Λ_n`.  `rightMTM` accepts at time `0` and then moves right forever;
it decides `Σ*` with `T_M = 0`, and with the manuscript's own choice `L(n) = T_M(n) + n` its
head leaves `Λ_0 = {0}` after one step.  `one_step_literal_fails` and
`invariant_literal_fails` record this.  The intended range `t ≤ T_M(n)` is covered above.

**Not formalized here.**  The poly-time uniformity of `enc_M`, `dec_M` and `Λ_n` on a Turing
machine (`def:wcc_machine`, items 1, 4, 5).  It needs a theory of poly-time computable
functions on the repository's machine model.  So the class inclusion
`P_Turing ⊆ P_WCC^{disc}` for the uniform class is not concluded here.
-/

namespace PVNP.PartIITwoPhase

open PVNP.Discrete PVNP.PartIITuring

variable (M : MTM)

/-- Head component `Q' ∪ {⊥}`: `none` is `⊥`, `some (inl q)` a head in state `q`,
`some (inr (q, d))` the directional mark `(q, d)`. -/
abbrev Hd := Option (M.Q ⊕ M.Q × Mv)

/-- The local alphabet `S = Γ × (Q' ∪ {⊥}) × {0,1}` of `def:local_state`. -/
abbrev S := M.Γ × Hd M × Bool

/-- `S` is a fixed finite alphabet. -/
example : Fintype (S M) := inferInstance

/-- Background symbol `s_∂ = (␣, ⊥, 0)`. -/
def sbd : S M := (M.blank, none, false)

/-- `U_phase0`: at a head `(γ, q, 0)` apply `δ(q, γ) = (q', γ', d)` and write `(γ', (q', d), 1)`;
otherwise flip the phase. -/
def U0 (c : S M) : S M :=
  match c.2.1 with
  | some (.inl q) => ((M.δ q c.1).2.1, some (.inr ((M.δ q c.1).1, (M.δ q c.1).2.2)), true)
  | h => (c.1, h, true)

/-- `U_phase1` on the centre symbol `γ` and the head components of centre, left and right
neighbours, with the five cases in the manuscript's order. -/
def U1h (γ : M.Γ) : Hd M → Hd M → Hd M → S M
  | some (.inr (_, .R)), _, _ => (γ, none, false)
  | none, some (.inr (q', .R)), _ => (γ, some (.inl q'), false)
  | some (.inr (_, .L)), _, _ => (γ, none, false)
  | none, _, some (.inr (q', .L)) => (γ, some (.inl q'), false)
  | h, _, _ => (γ, h, false)

/-- The radius-one rule `U : S^{−1,0,1} → S`; the centre's phase bit selects the branch. -/
def U (l c r : S M) : S M := if c.2.2 then U1h M c.1 c.2.1 l.2.1 r.2.1 else U0 M c

/-- Membership in the window `Λ_n = {−L, …, L}`. -/
def InWin (L : ℕ) (i : ℤ) : Prop := -(L : ℤ) ≤ i ∧ i ≤ L

instance (L : ℕ) (i : ℤ) : Decidable (InWin L i) := inferInstanceAs (Decidable (_ ∧ _))

/-- `|Λ_n| = 2L + 1`. -/
theorem card_window (L : ℕ) : (Finset.Icc (-(L : ℤ)) L).card = 2 * L + 1 := by
  simp only [Int.card_Icc]; omega

/-- One synchronous update on `Λ_n`; cells outside hold the background symbol. -/
def stepW (L : ℕ) (C : ℤ → S M) (i : ℤ) : S M :=
  if InWin L i then U M (C (i - 1)) (C i) (C (i + 1)) else sbd M

/-- `t` synchronous updates. -/
def runW (L : ℕ) (C : ℤ → S M) (t : ℕ) : ℤ → S M := (stepW M L)^[t] C

theorem runW_succ (L : ℕ) (C : ℤ → S M) (t : ℕ) :
    runW M L C (t + 1) = stepW M L (runW M L C t) := by
  simp [runW, Function.iterate_succ_apply']

/-- Phase-0 encoding of a Turing configuration `(γ, h, q)` on `Λ_n`. -/
def encCfg (L : ℕ) (c : M.Cfg) (i : ℤ) : S M :=
  if InWin L i then (c.tape i, (if i = c.head then some (Sum.inl c.q) else none : Hd M), false)
  else sbd M

/-- The configuration after the phase-0 update (odd times). -/
def encMid (L : ℕ) (c : M.Cfg) (i : ℤ) : S M :=
  if InWin L i then
    if i = c.head then
      ((M.δ c.q (c.tape c.head)).2.1,
        some (.inr ((M.δ c.q (c.tape c.head)).1, (M.δ c.q (c.tape c.head)).2.2)), true)
    else (c.tape i, none, true)
  else sbd M

/-- `enc_M(x)` exactly as in `def:wm`: `(x₁, q₀, 0)` on cell `0`, `(x_{i+1}, ⊥, 0)` on cells
`1 ≤ i ≤ n−1`, `(␣, ⊥, 0)` elsewhere on `Λ_n`.  For `n = 0` cell `0` carries the blank. -/
def encM (L : ℕ) (x : List Bool) (i : ℤ) : S M :=
  if InWin L i then
    if i = 0 then (M.inputTape x 0, some (.inl M.q0), false)
    else if 1 ≤ i ∧ i ≤ (x.length : ℤ) - 1 then (M.inp (x.getD i.toNat false), none, false)
    else (M.blank, none, false)
  else sbd M

theorem encM_eq (L : ℕ) (x : List Bool) : encM M L x = encCfg M L (M.init x) := by
  funext i
  unfold encM encCfg
  by_cases hw : InWin L i
  · rw [if_pos hw, if_pos hw]
    show _ = (M.inputTape x i, (if i = 0 then some (Sum.inl M.q0) else none : Hd M), false)
    by_cases h0 : i = 0
    · subst h0; simp
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : 1 ≤ i ∧ i ≤ (x.length : ℤ) - 1
      · rw [if_pos h1, M.inputTape_ne_blank (by omega) (by omega)]
      · rw [if_neg h1, M.inputTape_blank (by omega)]
  · rw [if_neg hw, if_neg hw]

/-! ## Phase 0 and phase 1 -/

theorem step_encCfg (L : ℕ) (c : M.Cfg) : stepW M L (encCfg M L c) = encMid M L c := by
  funext i
  unfold stepW encMid
  by_cases hw : InWin L i
  · rw [if_pos hw, if_pos hw]
    have hci : encCfg M L c i =
        (c.tape i, (if i = c.head then some (Sum.inl c.q) else none : Hd M), false) := by
      simp [encCfg, hw]
    rw [U, hci]
    by_cases hh : i = c.head
    · subst hh; simp [U0]
    · simp [U0, hh]
  · rw [if_neg hw, if_neg hw]

/-- Head component of the odd-time configuration. -/
theorem encMid_hd (L : ℕ) (c : M.Cfg) (i : ℤ) :
    (encMid M L c i).2.1 = if InWin L i ∧ i = c.head then
      some (.inr ((M.δ c.q (c.tape c.head)).1, (M.δ c.q (c.tape c.head)).2.2)) else none := by
  unfold encMid
  by_cases hw : InWin L i
  · by_cases hh : i = c.head
    · subst hh; simp [hw]
    · simp [hw, hh]
  · simp [hw, sbd]

theorem step_encMid (L : ℕ) (c : M.Cfg) (hc : InWin L c.head) :
    stepW M L (encMid M L c) = encCfg M L (M.step c) := by
  rcases hδ : M.δ c.q (c.tape c.head) with ⟨q', γ', d⟩
  have hstep : M.step c = ⟨Function.update c.tape c.head γ', c.head + d.shift, q'⟩ := by
    simp [MTM.step, hδ]
  rw [hstep]
  funext i
  unfold stepW encCfg
  by_cases hw : InWin L i
  · rw [if_pos hw, if_pos hw]
    have hcen : encMid M L c i = (if i = c.head then γ' else c.tape i,
        if i = c.head then some (.inr (q', d)) else none, true) := by
      unfold encMid
      rw [if_pos hw]
      by_cases hh : i = c.head
      · subst hh; simp [hδ]
      · simp [hh]
    have hl := encMid_hd M L c (i - 1)
    have hr := encMid_hd M L c (i + 1)
    rw [hδ] at hl hr
    rw [U, hcen]
    simp only [if_true]
    rw [hl, hr]
    by_cases hh : i = c.head
    · -- the head leaves the cell
      subst hh
      cases d <;> simp [U1h, Mv.shift]
    · rw [if_neg hh, if_neg hh, Function.update_of_ne hh]
      by_cases hL1 : i - 1 = c.head
      · -- left neighbour carries the mark
        have hR1 : ¬ (InWin L (i + 1) ∧ i + 1 = c.head) := by omega
        rw [if_pos ⟨by rw [hL1]; exact hc, hL1⟩, if_neg hR1]
        cases d with
        | R => simp [U1h, Mv.shift]; omega
        | L => simp [U1h, Mv.shift]; omega
      · by_cases hR1 : i + 1 = c.head
        · rw [if_neg (fun h => hL1 h.2), if_pos ⟨by rw [hR1]; exact hc, hR1⟩]
          cases d with
          | R => simp [U1h, Mv.shift]; omega
          | L => simp [U1h, Mv.shift]; omega
        · rw [if_neg (fun h => hL1 h.2), if_neg (fun h => hR1 h.2)]
          have hne : i ≠ c.head + d.shift := by cases d <;> simp [Mv.shift] <;> omega
          simp [U1h, hne]
  · rw [if_neg hw, if_neg hw]

/-- **Proposition `prop:local-tm`.**  Under the two-phase encoding, two applications of the
radius-one rule `U` realize one transition of `M` (whenever the head lies in `Λ_n`). -/
theorem two_steps (L : ℕ) (c : M.Cfg) (hc : InWin L c.head) :
    stepW M L (stepW M L (encCfg M L c)) = encCfg M L (M.step c) := by
  rw [step_encCfg, step_encMid M L c hc]

/-! ## Lemmas `lem:one_step` and `lem:invariant` -/

/-- **Lemma `lem:one_step`.**  As long as the head has stayed in `Λ_n`, `C_{2t}` is the phase-0
encoding of the Turing configuration after `t` steps. -/
theorem one_step_of_inWin (L : ℕ) (x : List Bool) :
    ∀ t, (∀ s < t, InWin L (M.run (M.init x) s).head) →
      runW M L (encM M L x) (2 * t) = encCfg M L (M.run (M.init x) t)
  | 0, _ => by rw [encM_eq]; rfl
  | t + 1, h => by
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, runW_succ, runW_succ,
      one_step_of_inWin L x t (fun s hs => h s (by omega)), two_steps M L _ (h t (by omega)),
      ← M.run_succ]

/-- The head moves one cell per step. -/
theorem head_bound (x : List Bool) : ∀ t, |(M.run (M.init x) t).head| ≤ t
  | 0 => by simp [MTM.run, MTM.init]
  | t + 1 => by
    rw [MTM.run_succ]
    have := head_bound x t
    have hs : ∀ m : Mv, |m.shift| ≤ 1 := by intro m; cases m <;> simp [Mv.shift]
    simp only [MTM.step]
    calc |(M.run (M.init x) t).head + _| ≤ |(M.run (M.init x) t).head| + |_| := abs_add_le _ _
      _ ≤ t + 1 := by have := hs (M.δ (M.run (M.init x) t).q
            ((M.run (M.init x) t).tape (M.run (M.init x) t).head)).2.2; linarith

/-- **Lemma `lem:one_step`** for all `t ≤ L(n) + 1`, in particular for every `t ≤ T_M(n)` when
`L(n) ≥ T_M(n)`. -/
theorem one_step (L : ℕ) (x : List Bool) (t : ℕ) (ht : t ≤ L + 1) :
    runW M L (encM M L x) (2 * t) = encCfg M L (M.run (M.init x) t) := by
  refine one_step_of_inWin M L x t fun s hs => ?_
  have := head_bound M x s
  rw [abs_le] at this
  exact ⟨by omega, by omega⟩

/-- The odd-time configuration `C_{2t+1}`. -/
theorem odd_step (L : ℕ) (x : List Bool) (t : ℕ) (ht : t ≤ L + 1) :
    runW M L (encM M L x) (2 * t + 1) = encMid M L (M.run (M.init x) t) := by
  rw [runW_succ, one_step M L x t ht, step_encCfg]

/-- **Lemma `lem:invariant`, even times** (`t ≤ L(n)`): every cell of `Λ_n` has phase `0`; the
head cell `h_t ∈ Λ_n` carries `(γ_t(h_t), q_t, 0)`; every other cell carries `⊥`. -/
theorem invariant_even (L : ℕ) (x : List Bool) (t : ℕ) (ht : t ≤ L) :
    (∀ i, InWin L i → (runW M L (encM M L x) (2 * t) i).2.2 = false) ∧
      InWin L (M.run (M.init x) t).head ∧
      runW M L (encM M L x) (2 * t) (M.run (M.init x) t).head =
        ((M.run (M.init x) t).tape (M.run (M.init x) t).head,
          some (Sum.inl (M.run (M.init x) t).q), false) ∧
      ∀ i, InWin L i → i ≠ (M.run (M.init x) t).head →
        (runW M L (encM M L x) (2 * t) i).2.1 = none := by
  have hC := one_step M L x t (by omega)
  have hh : InWin L (M.run (M.init x) t).head := by
    have := head_bound M x t; rw [abs_le] at this; exact ⟨by omega, by omega⟩
  refine ⟨fun i hi => ?_, hh, ?_, fun i hi hne => ?_⟩
  · rw [hC]; simp [encCfg, hi]
  · rw [hC]; simp [encCfg, hh]
  · rw [hC]; simp [encCfg, hi, hne]

/-- **Lemma `lem:invariant`, odd times** (`t ≤ L(n)`): every cell of `Λ_n` has phase `1`; the
cell `j_t = h_t` carries a directional mark `(q', d)`; no other cell carries a mark. -/
theorem invariant_odd (L : ℕ) (x : List Bool) (t : ℕ) (ht : t ≤ L) :
    (∀ i, InWin L i → (runW M L (encM M L x) (2 * t + 1) i).2.2 = true) ∧
      InWin L (M.run (M.init x) t).head ∧
      (∃ (γ : M.Γ) (q' : M.Q) (d : Mv),
        runW M L (encM M L x) (2 * t + 1) (M.run (M.init x) t).head =
          (γ, some (Sum.inr (q', d)), true)) ∧
      ∀ i, InWin L i → i ≠ (M.run (M.init x) t).head →
        (runW M L (encM M L x) (2 * t + 1) i).2.1 = none := by
  have hC := odd_step M L x t (by omega)
  have hh : InWin L (M.run (M.init x) t).head := by
    have := head_bound M x t; rw [abs_le] at this; exact ⟨by omega, by omega⟩
  set c := M.run (M.init x) t with hc
  refine ⟨fun i hi => ?_, hh, ⟨(M.δ c.q (c.tape c.head)).2.1, (M.δ c.q (c.tape c.head)).1,
    (M.δ c.q (c.tape c.head)).2.2, ?_⟩, fun i hi hne => ?_⟩
  · rw [hC]; unfold encMid
    by_cases h : i = c.head
    · rw [h] at hi ⊢; simp [hi]
    · simp [hi, h]
  · rw [hC]; simp [encMid, hh]
  · rw [hC]; simp [encMid, hi, hne]

/-! ## Decoder, runtime and acceptance -/

/-- `dec_M`: `1` if the simulated head (a non-directional head component) is in `q_acc`, `0` if
it is in `q_rej`, and `run` (`none`) otherwise. -/
def decM (L : ℕ) (C : ℤ → S M) : Option Bool :=
  if ∃ i ∈ Finset.Icc (-(L : ℤ)) L, (C i).2.1 = some (.inl M.qacc) then some true
  else if ∃ i ∈ Finset.Icc (-(L : ℤ)) L, (C i).2.1 = some (.inl M.qrej) then some false
  else none

/-- The output stream of `W_M` on input `x`. -/
def outW (L : ℕ) (x : List Bool) (t : ℕ) : Option Bool := decM M L (runW M L (encM M L x) t)

theorem decM_encCfg (L : ℕ) (c : M.Cfg) (hc : InWin L c.head) :
    decM M L (encCfg M L c) =
      if c.q = M.qacc then some true else if c.q = M.qrej then some false else none := by
  have key : ∀ q : M.Q, (∃ i ∈ Finset.Icc (-(L : ℤ)) L, (encCfg M L c i).2.1 = some (.inl q)) ↔
      c.q = q := by
    intro q
    constructor
    · rintro ⟨i, -, hi⟩
      unfold encCfg at hi
      split_ifs at hi with h1 h2 <;> simp_all [sbd]
    · intro hq
      refine ⟨c.head, Finset.mem_Icc.2 hc, ?_⟩
      simp [encCfg, hc, hq]
  unfold decM
  by_cases ha : c.q = M.qacc
  · rw [if_pos ((key _).2 ha), if_pos ha]
  · rw [if_neg (fun h => ha ((key _).1 h)), if_neg ha]
    by_cases hr : c.q = M.qrej
    · rw [if_pos ((key _).2 hr), if_pos hr]
    · rw [if_neg (fun h => hr ((key _).1 h)), if_neg hr]

theorem decM_encMid (L : ℕ) (c : M.Cfg) : decM M L (encMid M L c) = none := by
  have key : ∀ q : M.Q, ¬ ∃ i ∈ Finset.Icc (-(L : ℤ)) L, (encMid M L c i).2.1 = some (.inl q) := by
    rintro q ⟨i, -, hi⟩
    rw [encMid_hd] at hi
    split_ifs at hi
    simp at hi
  unfold decM
  rw [if_neg (key _), if_neg (key _)]

/-- **Lemma `lem:runtime`** and the decision part of **Theorem `thm:tm_to_wcc`.**  If `M` first
halts at time `T ≤ L(n)` on `x`, the first non-`run` output of `W_M` appears at time exactly `2T`,
and it is `1` iff the halting state is `q_acc`. -/
theorem runtime (L : ℕ) {x : List Bool} {T : ℕ} (hT : M.FirstHalt x T) (hTL : T ≤ L) :
    outW M L x (2 * T) = some (decide ((M.run (M.init x) T).q = M.qacc)) ∧
      ∀ s < 2 * T, outW M L x s = none := by
  have hin : ∀ t ≤ L, InWin L (M.run (M.init x) t).head := by
    intro t ht
    have := head_bound M x t; rw [abs_le] at this; constructor <;> omega
  refine ⟨?_, fun s hs => ?_⟩
  · unfold outW
    rw [one_step M L x T (by omega), decM_encCfg M L _ (hin T hTL)]
    by_cases ha : (M.run (M.init x) T).q = M.qacc
    · rw [if_pos ha]; simp [ha]
    · rw [if_neg ha, if_pos (hT.1.resolve_left ha)]; simp [ha]
  · unfold outW
    obtain ⟨u, rfl | rfl⟩ : ∃ u, s = 2 * u ∨ s = 2 * u + 1 := ⟨s / 2, by omega⟩
    · rw [one_step M L x u (by omega), decM_encCfg M L _ (hin u (by omega))]
      have hnh := hT.2 u (by omega)
      have h1 : ¬ (M.run (M.init x) u).q = M.qacc := fun h => hnh (Or.inl h)
      have h2 : ¬ (M.run (M.init x) u).q = M.qrej := fun h => hnh (Or.inr h)
      simp [h1, h2]
    · rw [odd_step M L x u (by omega), decM_encMid]

/-- Acceptance part of `lem:runtime`: the first output of `W_M` is `1` iff `M` accepts `x`. -/
theorem runtime_accepts (L : ℕ) {x : List Bool} {T : ℕ} (hT : M.FirstHalt x T) (hTL : T ≤ L) :
    outW M L x (2 * T) = some true ↔ M.Accepts x := by
  rw [(runtime M L hT hTL).1, M.accepts_iff_of_firstHalt hT]
  simp

/-- **Theorem `thm:tm_to_wcc`, decision part.**  If `M` decides `L` with `T_M(x) ≤ c·max(|x|,1)ᵏ`,
then with `L(n) = c·max(n,1)ᵏ + n` the machine `W_M` decides `L` with first-output time exactly
`2T_M(x) ≤ 2c·max(|x|,1)ᵏ`. -/
theorem tm_to_wcc_decides {Lang : Set (List Bool)} {c k : ℕ}
    (hT : ∀ x, M.HaltsWithin x (c * max x.length 1 ^ k)) (hL : ∀ x, M.Accepts x ↔ x ∈ Lang)
    (x : List Bool) :
    DecidesAt (outW M (c * max x.length 1 ^ k + x.length) x) (2 * (c * max x.length 1 ^ k))
      x Lang := by
  obtain ⟨T, hTc, hf⟩ := hT x
  obtain ⟨h1, h2⟩ := runtime M (c * max x.length 1 ^ k + x.length) hf (by omega)
  refine ⟨_, ⟨2 * T, by omega, h1, h2⟩, ?_⟩
  rw [decide_eq_true_iff, ← hL x, M.accepts_iff_of_firstHalt hf]

/-! ## The literal quantifier "for all `t ≥ 0`" -/

/-- A machine that accepts at time `0` and then moves right forever.  It decides `Σ*` with
`T_M(n) = 0`. -/
def rightMTM : MTM where
  Q := Bool
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank := fun _ => Option.some_ne_none _
  δ q a := (q, a, .R)
  q0 := true
  qacc := true
  qrej := false

theorem rightMTM_head (x : List Bool) : ∀ t, (rightMTM.run (rightMTM.init x) t).head = t
  | 0 => rfl
  | t + 1 => by
    rw [MTM.run_succ]
    show (rightMTM.run (rightMTM.init x) t).head + Mv.R.shift = _
    rw [rightMTM_head x t]; simp [Mv.shift]

theorem rightMTM_decides : ∀ x, rightMTM.FirstHalt x 0 ∧ rightMTM.Accepts x := by
  intro x
  have hf : rightMTM.FirstHalt x 0 := ⟨Or.inl rfl, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
  exact ⟨hf, ⟨0, hf, rfl⟩⟩

/-- **The literal `lem:one_step` fails.**  For `rightMTM` the head at time `L + 1` is outside
`Λ_n = {−L, …, L}`, so no cell of `Λ_n` can be "the unique `i = h_t`". -/
theorem one_step_literal_fails (L : ℕ) :
    ¬ InWin L (rightMTM.run (rightMTM.init []) (L + 1)).head := by
  rw [rightMTM_head]; unfold InWin; push_cast; omega

/-- **The literal `lem:invariant` fails.**  For `rightMTM` on the empty input with
`Λ = {−L, …, L}`, the configuration at the even time `2(L+1)` has no head cell at all.  With the
manuscript's choice `L(n) = T_M(n) + n` this happens already at time `2` (`L(0) = 0`). -/
theorem invariant_literal_fails (L : ℕ) :
    ∀ i, InWin L i → (runW rightMTM L (encM rightMTM L []) (2 * (L + 1)) i).2.1 = none := by
  intro i hi
  rw [one_step_of_inWin rightMTM L [] (L + 1) fun s hs => by
    rw [rightMTM_head]; unfold InWin; constructor <;> omega]
  have hne : i ≠ (rightMTM.run (rightMTM.init []) (L + 1)).head := by
    rw [rightMTM_head]; unfold InWin at hi; push_cast; omega
  simp [encCfg, hi, hne]

end PVNP.PartIITwoPhase
