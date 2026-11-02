import PVNP.WitnessSizeUniformity

/-!
# `P ⊆ NP` for ordinary Turing machines and discrete WCCs (Part III `thm:p-in-np`)

For every ordinary TM `M` we construct an explicit ordinary TM `M.unpairTM`
deciding the verifier language `{pair x w | x ∈ L(M)}`:

1. **parse** the self-delimiting pair `t x₀ t x₁ … t x_{n-1} f w`, rejecting
   every string that is not of this form (`epass_ok`, `epass_bad`);
2. **erase** the witness and the terminator (`wpass`);
3. **return** to the left end (`backpass`, `go_steps`);
4. **simulate** `M` on the odd cells: virtual cell `i` is physical cell
   `2i+1`, one `M` step costs at most two steps (`sim_step`, `sim_run`).

`unpair_decides`: if `M` decides `L` within `p`, then `M.unpairTM` decides
the verifier language within `2N + 3 + 2 p(N)` steps on inputs of length `N`.

Consequences, with no hypothesis about the classes:
`P_TM_subset_NP_TM`, `P_WCC_subset_NP_WCC`.  This makes Part III Theorem
`thm:p-in-np` unconditional for the discrete classes (the physical version
remains conditional on its stated closure premise).
-/

namespace PVNP.Discrete

/-- Control states of the unpairing verifier. -/
inductive UPhase (Λ : Type) where
  | E
  | Skip
  | W
  | Back
  | Go
  | sim (q : Λ)
  | midR (q : Λ)
  | midL (q : Λ)
  | rejHalt
  deriving DecidableEq, Fintype

namespace TM

variable (M : TM)

theorem next_some {c : M.Cfg} {q' : M.Λ} {a : M.Γ} {d : Dir}
    (h : M.δ c.q (c.tape c.head) = some (q', a, d)) :
    M.next c = ⟨q', Function.update c.tape c.head a, c.head + d.shift⟩ := by
  simp [next, step, h]

theorem next_none {c : M.Cfg} (h : M.δ c.q (c.tape c.head) = none) : M.next c = c := by
  simp [next, step, h]

/-- Interpretation of the verifier's tape symbols as symbols of `M`. -/
def uval : M.Γ ⊕ Option Bool → M.Γ
  | .inl g => g
  | .inr (some b) => M.inp b
  | .inr none => M.blank

/-- Simulation transition after an `M` transition. -/
def simOut (t : M.Λ × M.Γ × Dir) : UPhase M.Λ × (M.Γ ⊕ Option Bool) × Dir :=
  match t.2.2 with
  | .S => (.sim t.1, .inl t.2.1, .S)
  | .R => (.midR t.1, .inl t.2.1, .R)
  | .L => (.midL t.1, .inl t.2.1, .L)

/-- Transition function of the unpairing verifier. -/
def uδ : UPhase M.Λ → (M.Γ ⊕ Option Bool) → Option (UPhase M.Λ × (M.Γ ⊕ Option Bool) × Dir)
  | .E, .inl g => some (.rejHalt, .inl g, .S)
  | .E, .inr none => some (.rejHalt, .inr none, .S)
  | .E, .inr (some true) => some (.Skip, .inr (some true), .R)
  | .E, .inr (some false) => some (.W, .inr none, .R)
  | .Skip, .inl g => some (.rejHalt, .inl g, .S)
  | .Skip, .inr none => some (.rejHalt, .inr none, .S)
  | .Skip, .inr (some b) => some (.E, .inr (some b), .R)
  | .W, .inl g => some (.Back, .inl g, .L)
  | .W, .inr none => some (.Back, .inr none, .L)
  | .W, .inr (some _) => some (.W, .inr none, .R)
  | .Back, .inr o => some (.Back, .inr o, .L)
  | .Back, .inl g => some (.Go, .inl g, .R)
  | .Go, z => some (.sim M.start, z, .R)
  | .sim q, z => (M.δ q (M.uval z)).map M.simOut
  | .midR q, z => some (.sim q, z, .R)
  | .midL q, z => some (.sim q, z, .L)
  | .rejHalt, _ => none

def uacc : UPhase M.Λ → Bool
  | .sim q => M.acc q
  | _ => false

def urej : UPhase M.Λ → Bool
  | .sim q => M.rej q
  | .rejHalt => true
  | _ => false

/-- The verifier for `{pair x w | x ∈ L(M)}`. -/
abbrev unpairTM : TM where
  Λ := UPhase M.Λ
  Γ := M.Γ ⊕ Option Bool
  blank := .inl M.blank
  inp b := .inr (some b)
  start := .E
  δ := M.uδ
  acc := M.uacc
  rej := M.urej

/-- The tape agrees with the list `ys` starting at position `p`. -/
def Matches (T : ℤ → M.Γ ⊕ Option Bool) (p : ℤ) (ys : List Bool) : Prop :=
  ∀ i : ℕ, i < ys.length → T (p + i) = .inr (some (ys.getD i false))

theorem ans_pre (T : ℤ → M.Γ ⊕ Option Bool) (h : ℤ) (s : UPhase M.Λ)
    (hs : s = .E ∨ s = .Skip ∨ s = .W ∨ s = .Back ∨ s = .Go ∨ (∃ q, s = .midR q) ∨
      (∃ q, s = .midL q)) :
    M.unpairTM.ans ⟨s, T, h⟩ = none := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | ⟨q, rfl⟩ | ⟨q, rfl⟩ <;>
    simp [ans, answerOf, uacc, urej]

/-! ### Parsing pass -/

theorem epass_ok (x w : List Bool) (T : ℤ → M.Γ ⊕ Option Bool) (p : ℤ)
    (hT : M.Matches T p (pair x w)) :
    M.unpairTM.run ⟨.E, T, p⟩ (2 * x.length + 1) =
      ⟨.W, Function.update T (p + 2 * x.length) (.inr none), p + 2 * x.length + 1⟩ ∧
    ∀ m < 2 * x.length + 1, M.unpairTM.ans (M.unpairTM.run ⟨.E, T, p⟩ m) = none := by
  induction x generalizing p with
  | nil =>
    have h0 : T p = .inr (some false) := by
      have := hT 0 (by simp [pair]); simpa [pair] using this
    refine ⟨?_, ?_⟩
    · show M.unpairTM.run _ (0 + 1) = _
      rw [run_succ]
      simp only [run, Function.iterate_zero, id]
      rw [M.unpairTM.next_some (q' := .W) (a := .inr none) (d := .R) (by simp [uδ, h0])]
      simp [Dir.shift]
    · intro m hm
      obtain rfl : m = 0 := by simpa using hm
      exact M.ans_pre _ _ _ (Or.inl rfl)
  | cons b x ih =>
    have h0 : T p = .inr (some true) := by
      have := hT 0 (by simp [pair]); simpa [pair] using this
    have h1 : T (p + 1) = .inr (some b) := by
      have := hT 1 (by simp [pair]); simpa [pair] using this
    have hT' : M.Matches T (p + 2) (pair x w) := by
      intro i hi
      have := hT (i + 2) (by simp [pair] at hi ⊢; omega)
      rw [show p + ((i + 2 : ℕ) : ℤ) = p + 2 + i by push_cast; ring] at this
      simpa [pair] using this
    have one : M.unpairTM.run ⟨.E, T, p⟩ 1 = ⟨.Skip, T, p + 1⟩ := by
      show M.unpairTM.run _ (0 + 1) = _
      rw [run_succ]; simp only [run, Function.iterate_zero, id]
      rw [M.unpairTM.next_some (q' := .Skip) (a := .inr (some true)) (d := .R)
        (by simp [uδ, h0])]
      have hu : Function.update T p (.inr (some true)) = T := by
        rw [← h0]; exact Function.update_eq_self p T
      simp [hu, Dir.shift]
    have two : M.unpairTM.run ⟨.E, T, p⟩ 2 = ⟨.E, T, p + 2⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, one]
      rw [M.unpairTM.next_some (q' := .E) (a := .inr (some b)) (d := .R)
        (by simp [uδ, h1])]
      have hu : Function.update T (p + 1) (.inr (some b)) = T := by
        rw [← h1]; exact Function.update_eq_self _ T
      simp only [hu, Dir.shift]; ring_nf
    obtain ⟨ih1, ih2⟩ := ih (p + 2) hT'
    refine ⟨?_, ?_⟩
    · rw [show 2 * (b :: x).length + 1 = 2 + (2 * x.length + 1) by simp; ring, run_add, two, ih1]
      simp only [List.length_cons]; push_cast; ring_nf
    · intro m hm
      by_cases hm2 : m < 2
      · interval_cases m
        · exact M.ans_pre _ _ _ (Or.inl rfl)
        · rw [one]; exact M.ans_pre _ _ _ (Or.inr (Or.inl rfl))
      · obtain ⟨m', rfl⟩ : ∃ m', m = 2 + m' := ⟨m - 2, by omega⟩
        rw [run_add, two]
        exact ih2 m' (by simp at hm; omega)

theorem epass_bad : ∀ (ys : List Bool) (T : ℤ → M.Γ ⊕ Option Bool) (p : ℤ),
    M.Matches T p ys → T (p + ys.length) = .inl M.blank → (∀ x w, ys ≠ pair x w) →
    ∃ m ≤ ys.length + 1, (M.unpairTM.run ⟨.E, T, p⟩ m).q = .rejHalt ∧
      ∀ m' < m, M.unpairTM.ans (M.unpairTM.run ⟨.E, T, p⟩ m') = none
  | [], T, p, _, hb, _ => by
    refine ⟨1, le_refl _, ?_, ?_⟩
    · show (M.unpairTM.run _ (0 + 1)).q = _
      rw [run_succ]; simp only [run, Function.iterate_zero, id]
      simp only [List.length_nil, CharP.cast_eq_zero, add_zero] at hb
      rw [M.unpairTM.next_some (q' := .rejHalt) (a := .inl M.blank) (d := .S)
        (by simp [uδ, hb])]
    · intro m' hm'
      obtain rfl : m' = 0 := by omega
      exact M.ans_pre _ _ _ (Or.inl rfl)
  | false :: w, _, _, _, _, hbad => absurd (show false :: w = pair [] w by simp [pair]) (hbad [] w)
  | [true], T, p, hT, hb, _ => by
    have h0 : T p = .inr (some true) := by simpa using hT 0 (by simp)
    have h1 : T (p + 1) = .inl M.blank := by simpa using hb
    have one : M.unpairTM.run ⟨.E, T, p⟩ 1 = ⟨.Skip, T, p + 1⟩ := by
      show M.unpairTM.run _ (0 + 1) = _
      rw [run_succ]; simp only [run, Function.iterate_zero, id]
      rw [M.unpairTM.next_some (q' := .Skip) (a := .inr (some true)) (d := .R)
        (by simp [uδ, h0])]
      have hu : Function.update T p (.inr (some true)) = T := by
        rw [← h0]; exact Function.update_eq_self p T
      simp [hu, Dir.shift]
    refine ⟨2, by simp, ?_, ?_⟩
    · rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, one]
      rw [M.unpairTM.next_some (q' := .rejHalt) (a := .inl M.blank) (d := .S)
        (by simp [uδ, h1])]
    · intro m' hm'
      interval_cases m'
      · exact M.ans_pre _ _ _ (Or.inl rfl)
      · rw [one]; exact M.ans_pre _ _ _ (Or.inr (Or.inl rfl))
  | true :: b :: rest, T, p, hT, hb, hbad => by
    have h0 : T p = .inr (some true) := by simpa using hT 0 (by simp)
    have h1 : T (p + 1) = .inr (some b) := by simpa using hT 1 (by simp)
    have hT' : M.Matches T (p + 2) rest := by
      intro i hi
      have := hT (i + 2) (by simp; omega)
      rw [show p + ((i + 2 : ℕ) : ℤ) = p + 2 + i by push_cast; ring] at this
      simpa using this
    have hb' : T (p + 2 + rest.length) = .inl M.blank := by
      rw [← hb]; congr 1; simp; ring
    have hbad' : ∀ x w, rest ≠ pair x w := by
      intro x w h
      exact hbad (b :: x) w (by simp [pair, h])
    obtain ⟨m, hm, hq, hans⟩ := epass_bad rest T (p + 2) hT' hb' hbad'
    have one : M.unpairTM.run ⟨.E, T, p⟩ 1 = ⟨.Skip, T, p + 1⟩ := by
      show M.unpairTM.run _ (0 + 1) = _
      rw [run_succ]; simp only [run, Function.iterate_zero, id]
      rw [M.unpairTM.next_some (q' := .Skip) (a := .inr (some true)) (d := .R)
        (by simp [uδ, h0])]
      have hu : Function.update T p (.inr (some true)) = T := by
        rw [← h0]; exact Function.update_eq_self p T
      simp [hu, Dir.shift]
    have two : M.unpairTM.run ⟨.E, T, p⟩ 2 = ⟨.E, T, p + 2⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, one]
      rw [M.unpairTM.next_some (q' := .E) (a := .inr (some b)) (d := .R)
        (by simp [uδ, h1])]
      have hu : Function.update T (p + 1) (.inr (some b)) = T := by
        rw [← h1]; exact Function.update_eq_self _ T
      simp only [hu, Dir.shift]; ring_nf
    refine ⟨2 + m, by simp; omega, by rw [run_add, two]; exact hq, ?_⟩
    intro m' hm'
    by_cases h2 : m' < 2
    · interval_cases m'
      · exact M.ans_pre _ _ _ (Or.inl rfl)
      · rw [one]; exact M.ans_pre _ _ _ (Or.inr (Or.inl rfl))
    · obtain ⟨k, rfl⟩ : ∃ k, m' = 2 + k := ⟨m' - 2, by omega⟩
      rw [run_add, two]; exact hans k (by omega)

/-! ### Erasing the witness and returning -/

theorem wpass (w : List Bool) (T : ℤ → M.Γ ⊕ Option Bool) (p : ℤ) (hT : M.Matches T p w)
    (hb : T (p + w.length) = .inl M.blank) :
    M.unpairTM.run ⟨.W, T, p⟩ (w.length + 1) =
      ⟨.Back, fun i => if p ≤ i ∧ i < p + w.length then .inr none else T i, p + w.length - 1⟩ ∧
    ∀ m < w.length + 1, M.unpairTM.ans (M.unpairTM.run ⟨.W, T, p⟩ m) = none := by
  induction w generalizing T p with
  | nil =>
    simp only [List.length_nil, CharP.cast_eq_zero, add_zero] at hb ⊢
    refine ⟨?_, ?_⟩
    · show M.unpairTM.run _ (0 + 1) = _
      rw [run_succ]; simp only [run, Function.iterate_zero, id]
      rw [M.unpairTM.next_some (q' := .Back) (a := .inl M.blank) (d := .L) (by simp [uδ, hb])]
      have hu : Function.update T p (.inl M.blank) = T := by
        rw [← hb]; exact Function.update_eq_self p T
      have hf : (fun i => if p ≤ i ∧ i < p then (.inr none : M.Γ ⊕ Option Bool) else T i) = T :=
        funext fun i => by rw [if_neg (by omega)]
      simp [hu, hf, Dir.shift]; ring
    · intro m hm
      obtain rfl : m = 0 := by omega
      exact M.ans_pre _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
  | cons b w ih =>
    have h0 : T p = .inr (some b) := by simpa using hT 0 (by simp)
    set T1 := Function.update T p (.inr none : M.Γ ⊕ Option Bool) with hT1
    have one : M.unpairTM.run ⟨.W, T, p⟩ 1 = ⟨.W, T1, p + 1⟩ := by
      show M.unpairTM.run _ (0 + 1) = _
      rw [run_succ]; simp only [run, Function.iterate_zero, id]
      rw [M.unpairTM.next_some (q' := .W) (a := .inr none) (d := .R) (by simp [uδ, h0])]
      simp [Dir.shift, hT1]
    have hT1' : M.Matches T1 (p + 1) w := by
      intro i hi
      have := hT (i + 1) (by simp; omega)
      rw [show p + ((i + 1 : ℕ) : ℤ) = p + 1 + i by push_cast; ring] at this
      rw [hT1, Function.update_of_ne (by omega)]
      simpa using this
    have hb1 : T1 (p + 1 + w.length) = .inl M.blank := by
      rw [hT1, Function.update_of_ne (by omega), ← hb]; congr 1; simp; ring
    obtain ⟨ih1, ih2⟩ := ih T1 (p + 1) hT1' hb1
    refine ⟨?_, ?_⟩
    · rw [show (b :: w).length + 1 = 1 + (w.length + 1) by simp; ring, run_add, one, ih1]
      congr 1
      · funext i
        simp only [List.length_cons, hT1]
        push_cast
        by_cases hi : i = p
        · subst hi; simp
        · rw [Function.update_of_ne hi]
          by_cases h3 : p + 1 ≤ i ∧ i < p + 1 + w.length
          · rw [if_pos h3, if_pos ⟨by omega, by omega⟩]
          · rw [if_neg h3, if_neg (by omega)]
      · simp; ring
    · intro m hm
      by_cases h1 : m < 1
      · obtain rfl : m = 0 := by omega
        exact M.ans_pre _ _ _ (Or.inr (Or.inr (Or.inl rfl)))
      · obtain ⟨k, rfl⟩ : ∃ k, m = 1 + k := ⟨m - 1, by omega⟩
        rw [run_add, one]; exact ih2 k (by simp at hm; omega)

theorem backpass (k : ℕ) (T : ℤ → M.Γ ⊕ Option Bool) (p : ℤ)
    (hT : ∀ j : ℕ, j ≤ k → ∃ o, T (p - j) = .inr o) :
    M.unpairTM.run ⟨.Back, T, p⟩ (k + 1) = ⟨.Back, T, p - k - 1⟩ ∧
    ∀ m < k + 1, M.unpairTM.ans (M.unpairTM.run ⟨.Back, T, p⟩ m) = none := by
  have one : ∀ p, (∃ o, T p = .inr o) → M.unpairTM.run ⟨.Back, T, p⟩ 1 = ⟨.Back, T, p - 1⟩ := by
    intro p ⟨o, ho⟩
    show M.unpairTM.run _ (0 + 1) = _
    rw [run_succ]; simp only [run, Function.iterate_zero, id]
    rw [M.unpairTM.next_some (q' := .Back) (a := .inr o) (d := .L) (by simp [uδ, ho])]
    have hu : Function.update T p (.inr o) = T := by rw [← ho]; exact Function.update_eq_self p T
    simp [hu, Dir.shift]; ring
  induction k generalizing p with
  | zero =>
    refine ⟨by simpa using one p (by simpa using hT 0 le_rfl), ?_⟩
    intro m hm
    obtain rfl : m = 0 := by omega
    exact M.ans_pre _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | succ k ih =>
    have h1 := one p (by simpa using hT 0 (by omega))
    obtain ⟨ih1, ih2⟩ := ih (p - 1) (fun j hj => by
      obtain ⟨o, ho⟩ := hT (j + 1) (by omega)
      exact ⟨o, by rw [← ho]; congr 1; push_cast; ring⟩)
    refine ⟨?_, ?_⟩
    · rw [show k + 1 + 1 = 1 + (k + 1) by ring, run_add, h1, ih1]; congr 1; push_cast; ring
    · intro m hm
      by_cases h0 : m < 1
      · obtain rfl : m = 0 := by omega
        exact M.ans_pre _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · obtain ⟨j, rfl⟩ : ∃ j, m = 1 + j := ⟨m - 1, by omega⟩
        rw [run_add, h1]; exact ih2 j (by omega)

theorem go_steps (T : ℤ → M.Γ ⊕ Option Bool) (p : ℤ) (g : M.Γ) (hT : T p = .inl g) :
    M.unpairTM.run ⟨.Back, T, p⟩ 2 = ⟨.sim M.start, T, p + 2⟩ ∧
    ∀ m < 2, M.unpairTM.ans (M.unpairTM.run ⟨.Back, T, p⟩ m) = none := by
  have one : M.unpairTM.run ⟨.Back, T, p⟩ 1 = ⟨.Go, T, p + 1⟩ := by
    show M.unpairTM.run _ (0 + 1) = _
    rw [run_succ]; simp only [run, Function.iterate_zero, id]
    rw [M.unpairTM.next_some (q' := .Go) (a := .inl g) (d := .R) (by simp [uδ, hT])]
    have hu : Function.update T p (.inl g) = T := by rw [← hT]; exact Function.update_eq_self p T
    simp [hu, Dir.shift]
  refine ⟨?_, ?_⟩
  · rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, one]
    rw [M.unpairTM.next_some (q' := .sim M.start) (a := T (p + 1)) (d := .R) (by simp [uδ])]
    simp [Dir.shift]; ring
  · intro m hm
    interval_cases m
    · exact M.ans_pre _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · rw [one]; exact M.ans_pre _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

/-! ### Odd-cell simulation -/

/-- `c'` represents `c`: same control state, head on the odd cell `2h+1`, and
odd cells carry the simulated tape. -/
def Rep (c : M.Cfg) (c' : M.unpairTM.Cfg) : Prop :=
  c'.q = .sim c.q ∧ c'.head = 2 * c.head + 1 ∧ ∀ i, M.uval (c'.tape (2 * i + 1)) = c.tape i

/-- Number of verifier steps per simulated step. -/
def cost (c : M.Cfg) : ℕ :=
  match M.δ c.q (c.tape c.head) with
  | none => 0
  | some (_, _, .S) => 1
  | some (_, _, .L) => 2
  | some (_, _, .R) => 2

theorem ans_rep {c : M.Cfg} {c' : M.unpairTM.Cfg} (h : M.Rep c c') :
    M.unpairTM.ans c' = M.ans c := by
  simp [ans, h.1, uacc, urej]

theorem rep_tape_update {c : M.Cfg} {c' : M.unpairTM.Cfg} (h : M.Rep c c') (a : M.Γ) :
    ∀ i, M.uval (Function.update c'.tape c'.head (.inl a) (2 * i + 1)) =
      Function.update c.tape c.head a i := by
  intro i
  rw [h.2.1]
  by_cases hi : i = c.head
  · subst hi; simp [uval]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne hi, h.2.2]

theorem sim_step {c : M.Cfg} {c' : M.unpairTM.Cfg} (h : M.Rep c c') :
    M.Rep (M.next c) (M.unpairTM.run c' (M.cost c)) ∧
    (∀ m, 0 < m → m < M.cost c → M.unpairTM.ans (M.unpairTM.run c' m) = none) ∧
    M.cost c ≤ 2 := by
  obtain ⟨hq, hh, ht⟩ := h
  have hread : M.uval (c'.tape c'.head) = c.tape c.head := by rw [hh, ht]
  rcases hδ : M.δ c.q (c.tape c.head) with _ | ⟨q', a, d⟩
  · have hc : M.cost c = 0 := by simp [cost, hδ]
    rw [hc, M.next_none hδ]
    exact ⟨⟨hq, hh, ht⟩, fun m h1 h2 => by omega, by omega⟩
  · have hδ' : M.unpairTM.δ c'.q (c'.tape c'.head) = some (M.simOut (q', a, d)) := by
      simp [hq, uδ, hread, hδ]
    rw [M.next_some hδ]
    have htape := M.rep_tape_update ⟨hq, hh, ht⟩ a
    cases d with
    | S =>
      have hc : M.cost c = 1 := by simp [cost, hδ]
      rw [hc]
      refine ⟨?_, fun m h1 h2 => by omega, by omega⟩
      show M.Rep _ (M.unpairTM.run c' (0 + 1))
      rw [run_succ]; simp only [run, Function.iterate_zero, id]
      rw [M.unpairTM.next_some hδ']
      refine ⟨rfl, ?_, htape⟩
      simp [Dir.shift, hh]
    | R =>
      have hc : M.cost c = 2 := by simp [cost, hδ]
      rw [hc]
      have one : M.unpairTM.run c' 1 =
          ⟨.midR q', Function.update c'.tape c'.head (.inl a), c'.head + 1⟩ := by
        show M.unpairTM.run c' (0 + 1) = _
        rw [run_succ]; simp only [run, Function.iterate_zero, id]
        rw [M.unpairTM.next_some hδ']; simp [simOut, Dir.shift]
      refine ⟨?_, fun m h1 h2 => ?_, by omega⟩
      · rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, one]
        rw [M.unpairTM.next_some (q' := .sim q') (d := .R)
          (a := Function.update c'.tape c'.head (.inl a) (c'.head + 1)) (by simp [uδ])]
        refine ⟨rfl, ?_, ?_⟩
        · simp [Dir.shift, hh]; ring
        · intro i
          simp only [Function.update_eq_self]
          exact htape i
      · obtain rfl : m = 1 := by omega
        rw [one]; exact M.ans_pre _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q', rfl⟩))))))
    | L =>
      have hc : M.cost c = 2 := by simp [cost, hδ]
      rw [hc]
      have one : M.unpairTM.run c' 1 =
          ⟨.midL q', Function.update c'.tape c'.head (.inl a), c'.head - 1⟩ := by
        show M.unpairTM.run c' (0 + 1) = _
        rw [run_succ]; simp only [run, Function.iterate_zero, id]
        rw [M.unpairTM.next_some hδ']; simp [simOut, Dir.shift]; ring
      refine ⟨?_, fun m h1 h2 => ?_, by omega⟩
      · rw [show (2 : ℕ) = 1 + 1 from rfl, run_succ, one]
        rw [M.unpairTM.next_some (q' := .sim q') (d := .L)
          (a := Function.update c'.tape c'.head (.inl a) (c'.head - 1)) (by simp [uδ])]
        refine ⟨rfl, ?_, ?_⟩
        · simp [Dir.shift, hh]; ring
        · intro i
          simp only [Function.update_eq_self]
          exact htape i
      · obtain rfl : m = 1 := by omega
        rw [one]; exact M.ans_pre _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q', rfl⟩))))))

theorem sim_run (c : M.Cfg) (c' : M.unpairTM.Cfg) (h : M.Rep c c') :
    ∀ j, (∀ j' < j, M.ans (M.run c j') = none) →
      ∃ σ ≤ 2 * j, M.Rep (M.run c j) (M.unpairTM.run c' σ) ∧
        ∀ m < σ, M.unpairTM.ans (M.unpairTM.run c' m) = none := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨0, le_refl _, h, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj
    obtain ⟨σ, hσ, hrep, hans⟩ := ih (fun j' hj' => hj j' (by omega))
    obtain ⟨hrep', hmid, hcost⟩ := M.sim_step hrep
    refine ⟨σ + M.cost (M.run c j), by omega, ?_, ?_⟩
    · rw [run_succ, run_add]; exact hrep'
    · intro m hm
      by_cases h1 : m < σ
      · exact hans m h1
      · obtain ⟨k, rfl⟩ : ∃ k, m = σ + k := ⟨m - σ, by omega⟩
        rw [run_add]
        by_cases hk : k = 0
        · subst hk
          rw [show M.unpairTM.run (M.unpairTM.run c' σ) 0 = M.unpairTM.run c' σ from rfl,
            M.ans_rep hrep]
          exact hj j (by omega)
        · exact hmid k (by omega) (by omega)

/-! ### Assembly -/

theorem getD_pair_odd (x w : List Bool) (i : ℕ) (hi : i < x.length) :
    (pair x w).getD (2 * i + 1) false = x.getD i false := by
  induction x generalizing i with
  | nil => simp at hi
  | cons b x ih =>
    cases i with
    | zero => simp [pair]
    | succ i =>
      have := ih i (by simp at hi; omega)
      simp only [pair, List.flatMap_cons, List.cons_append, List.nil_append] at this ⊢
      rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 1 + 1 by ring]
      simpa using this

theorem getD_pair_even (x w : List Bool) (i : ℕ) (hi : i < x.length) :
    (pair x w).getD (2 * i) false = true := by
  induction x generalizing i with
  | nil => simp at hi
  | cons b x ih =>
    cases i with
    | zero => simp [pair]
    | succ i =>
      have := ih i (by simp at hi; omega)
      simp only [pair, List.flatMap_cons, List.cons_append, List.nil_append] at this ⊢
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
      simpa using this

theorem getD_pair_witness (x w : List Bool) (j : ℕ) :
    (pair x w).getD (2 * x.length + 1 + j) false = w.getD j false := by
  induction x with
  | nil =>
    simp only [pair, List.flatMap_nil, List.nil_append, List.length_nil]
    rw [show 2 * 0 + 1 + j = j + 1 by ring]; simp
  | cons b x ih =>
    simp only [pair, List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons] at ih ⊢
    rw [show 2 * (x.length + 1) + 1 + j = (2 * x.length + 1 + j) + 1 + 1 by ring]
    simpa using ih

/-- Tape after preprocessing a well-formed input `pair x w`. -/
def preTape (x w : List Bool) : ℤ → M.Γ ⊕ Option Bool :=
  fun i => if 2 * (x.length : ℤ) + 1 ≤ i ∧ i < 2 * x.length + 1 + w.length then .inr none
    else Function.update (M.unpairTM.inputTape (pair x w)) (2 * x.length) (.inr none) i

theorem matches_input (y : List Bool) : M.Matches (M.unpairTM.inputTape y) 0 y := by
  intro i hi
  simp only [inputTape, zero_add]
  rw [if_pos ⟨by omega, by exact_mod_cast hi⟩]
  simp

theorem preprocess (x w : List Bool) :
    M.unpairTM.run (M.unpairTM.init (pair x w)) (4 * x.length + 2 * w.length + 5) =
      ⟨.sim M.start, M.preTape x w, 1⟩ ∧
    ∀ m < 4 * x.length + 2 * w.length + 5,
      M.unpairTM.ans (M.unpairTM.run (M.unpairTM.init (pair x w)) m) = none := by
  set n := x.length
  set y := pair x w
  have hy : y.length = 2 * n + 1 + w.length := pair_length x w
  set T0 := M.unpairTM.inputTape y
  have hinit : M.unpairTM.init y = ⟨.E, T0, 0⟩ := rfl
  obtain ⟨e1, e2⟩ := M.epass_ok x w T0 0 (M.matches_input y)
  simp only [zero_add] at e1
  set T1 := Function.update T0 (2 * (n : ℤ)) (.inr none : M.Γ ⊕ Option Bool)
  have hT0_in : ∀ i : ℕ, i < y.length → T0 i = .inr (some (y.getD i false)) := by
    intro i hi; simpa using M.matches_input y i hi
  have hT0_out : ∀ i : ℤ, (i < 0 ∨ (y.length : ℤ) ≤ i) → T0 i = .inl M.blank := by
    intro i hi
    simp only [T0, inputTape]
    rw [if_neg (by omega)]
  have hW : M.Matches T1 (2 * n + 1) w := by
    intro j hj
    have hlt : 2 * n + 1 + j < y.length := by omega
    have := hT0_in (2 * n + 1 + j) hlt
    rw [getD_pair_witness] at this
    simp only [T1]
    rw [Function.update_of_ne (by omega)]
    rw [← this]; congr 1
  have hWb : T1 (2 * n + 1 + w.length) = .inl M.blank := by
    simp only [T1]
    rw [Function.update_of_ne (by omega)]
    exact hT0_out _ (Or.inr (by omega))
  obtain ⟨w1, w2⟩ := M.wpass w T1 (2 * n + 1) hW hWb
  set T2 : ℤ → M.Γ ⊕ Option Bool :=
    fun i => if 2 * (n : ℤ) + 1 ≤ i ∧ i < 2 * n + 1 + w.length then .inr none else T1 i
  have hT2 : T2 = M.preTape x w := rfl
  have hback : ∀ j : ℕ, j ≤ 2 * n + w.length → ∃ o, T2 ((2 * n + 1 + w.length - 1 : ℤ) - j) = .inr o := by
    intro j hj
    set i : ℤ := (2 * n + 1 + w.length - 1 : ℤ) - j
    simp only [T2]
    by_cases h1 : 2 * (n : ℤ) + 1 ≤ i ∧ i < 2 * n + 1 + w.length
    · exact ⟨none, by rw [if_pos h1]⟩
    · rw [if_neg h1]
      by_cases h2 : i = 2 * n
      · exact ⟨none, by simp only [T1]; rw [h2, Function.update_self]⟩
      · simp only [T1]
        rw [Function.update_of_ne h2]
        have hi0 : 0 ≤ i := by omega
        have := hT0_in i.toNat (by omega)
        rw [show ((i.toNat : ℕ) : ℤ) = i by omega] at this
        exact ⟨_, this⟩
  obtain ⟨b1, b2⟩ := M.backpass (2 * n + w.length) T2 (2 * n + 1 + w.length - 1) hback
  have hneg : T2 (2 * n + 1 + w.length - 1 - ((2 * n + w.length : ℕ) : ℤ) - 1) = .inl M.blank := by
    simp only [T2, T1]
    rw [if_neg (by push_cast; omega), Function.update_of_ne (by push_cast; omega)]
    exact hT0_out _ (Or.inl (by push_cast; omega))
  obtain ⟨g1, g2⟩ := M.go_steps T2 _ M.blank hneg
  have htot : 4 * n + 2 * w.length + 5 =
      (2 * n + 1) + ((w.length + 1) + ((2 * n + w.length + 1) + 2)) := by ring
  refine ⟨?_, ?_⟩
  · rw [htot, hinit, run_add, e1, run_add, w1, run_add, b1, g1, hT2]
    congr 1; push_cast; ring
  · intro m hm
    rw [hinit]
    by_cases h1 : m < 2 * n + 1
    · exact e2 m h1
    · obtain ⟨m1, rfl⟩ : ∃ m1, m = (2 * n + 1) + m1 := ⟨m - (2 * n + 1), by omega⟩
      rw [run_add, e1]
      by_cases h2 : m1 < w.length + 1
      · exact w2 m1 h2
      · obtain ⟨m2, rfl⟩ : ∃ m2, m1 = (w.length + 1) + m2 := ⟨m1 - (w.length + 1), by omega⟩
        rw [run_add, w1]
        by_cases h3 : m2 < 2 * n + w.length + 1
        · exact b2 m2 h3
        · obtain ⟨m3, rfl⟩ : ∃ m3, m2 = (2 * n + w.length + 1) + m3 :=
            ⟨m2 - (2 * n + w.length + 1), by omega⟩
          rw [run_add, b1]
          exact g2 m3 (by omega)

theorem rep_init (x w : List Bool) : M.Rep (M.init x) ⟨.sim M.start, M.preTape x w, 1⟩ := by
  refine ⟨rfl, by simp [init], ?_⟩
  intro i
  simp only [preTape, init, inputTape]
  by_cases h1 : 2 * (x.length : ℤ) + 1 ≤ 2 * i + 1 ∧ 2 * i + 1 < 2 * x.length + 1 + w.length
  · rw [if_pos h1, if_neg (by omega)]; rfl
  · rw [if_neg h1, Function.update_of_ne (by omega)]
    simp only [inputTape]
    have hy := pair_length x w
    by_cases h2 : 0 ≤ 2 * i + 1 ∧ 2 * i + 1 < ((pair x w).length : ℤ)
    · rw [if_pos h2]
      have hi : 0 ≤ i ∧ i < x.length := by omega
      rw [if_pos hi]
      have hodd := getD_pair_odd x w i.toNat (by omega)
      rw [show (2 * i + 1).toNat = 2 * i.toNat + 1 by omega, hodd]
      rfl
    · rw [if_neg h2, if_neg (by omega)]; rfl

/-- **Unpairing verifier theorem.** -/
theorem unpair_decides {L : Set (List Bool)} {p : Polynomial ℕ}
    (h : M.Decides L (fun n => p.eval n)) :
    M.unpairTM.Decides {y | ∃ x w, y = pair x w ∧ x ∈ L}
      (fun N => 2 * N + 3 + 2 * p.eval N) := by
  intro y
  by_cases hy : ∃ x w, y = pair x w
  · obtain ⟨x, w, rfl⟩ := hy
    obtain ⟨b, ⟨s, hs, hout, hfirst⟩, hb⟩ := h x
    obtain ⟨pre1, pre2⟩ := M.preprocess x w
    obtain ⟨σ, hσ, hrep, hans⟩ := M.sim_run (M.init x) _ (M.rep_init x w) s
      (fun j' hj' => hfirst j' hj')
    have hlen := pair_length x w
    refine ⟨b, ⟨(4 * x.length + 2 * w.length + 5) + σ, ?_, ?_, ?_⟩, ?_⟩
    · have hp := eval_mono_nat p (show x.length ≤ (pair x w).length by omega)
      simp only at hs
      show _ ≤ 2 * (pair x w).length + 3 + 2 * p.eval (pair x w).length
      omega
    · simp only [out]
      rw [run_add, pre1, M.ans_rep hrep]; exact hout
    · intro m hm
      simp only [out]
      by_cases h1 : m < 4 * x.length + 2 * w.length + 5
      · exact pre2 m h1
      · obtain ⟨k, rfl⟩ : ∃ k, m = (4 * x.length + 2 * w.length + 5) + k :=
          ⟨m - (4 * x.length + 2 * w.length + 5), by omega⟩
        rw [run_add, pre1]; exact hans k (by omega)
    · rw [hb]
      constructor
      · intro hx; exact ⟨x, w, rfl, hx⟩
      · rintro ⟨x', w', heq, hx'⟩
        rw [(pair_injective heq).1]; exact hx'
  · have hbad : ∀ x w, y ≠ pair x w := fun x w h => hy ⟨x, w, h⟩
    obtain ⟨m, hm, hq, hans⟩ := M.epass_bad y (M.unpairTM.inputTape y) 0 (M.matches_input y)
      (by simp only [inputTape, zero_add]; rw [if_neg (by omega)]) hbad
    refine ⟨false, ⟨m, by show m ≤ 2 * y.length + 3 + 2 * p.eval y.length; omega, ?_, hans⟩, ?_⟩
    · simp only [out]
      show M.unpairTM.ans (M.unpairTM.run ⟨.E, _, 0⟩ m) = _
      simp [ans, hq, answerOf, uacc, urej]
    · simp only [Bool.false_eq_true, false_iff, Set.mem_setOf_eq, not_exists, not_and]
      intro x w h; exact absurd h (hbad x w)

end TM

/-- **`P_TM ⊆ NP_TM`**, unconditionally. -/
theorem P_TM_subset_NP_TM : P_TM ⊆ NP_TM := by
  apply P_subset_NPOf
  rintro L ⟨M, p, h⟩
  refine ⟨M.unpairTM, 2 * Polynomial.X + 3 + 2 * p, ?_⟩
  have heq : (fun n : ℕ => (2 * Polynomial.X + 3 + 2 * p).eval n) =
      (fun n => 2 * n + 3 + 2 * p.eval n) := by funext n; simp
  rw [heq]; exact M.unpair_decides h

/-- **`P_WCC ⊆ NP_WCC`**, unconditionally. -/
theorem P_WCC_subset_NP_WCC : P_WCC ⊆ NP_WCC := by
  rw [P_WCC_eq_P_TM, NP_WCC_eq_NP_TM]; exact P_TM_subset_NP_TM

end PVNP.Discrete
