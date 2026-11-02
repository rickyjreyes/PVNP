import PVNP.WCCRadius

/-!
# Generality of the Part II equivalence: lattices `ℤ^(1+d)`, encoders, advice

* **Multidimensional lattices.** `WCCD d` is a finite-alphabet quiescent
  cellular automaton on `ℤ^(1+d)` with the Moore neighbourhood of radius one,
  the input written on the first coordinate axis, and the shared first-answer
  semantics.  `WCC.toD` embeds every radius-one WCC with an *identical* run on
  the axis and blank cells off it (`toD_run`), hence
  `P_TM ⊆ P_WCCD d` for every `d` (`P_TM_subset_P_WCCD`).
  The converse inclusion `P_WCCD d ⊆ P_TM` (`d ≥ 1`) is the classical
  polynomial simulation of a `(1+d)`-dimensional automaton by a one-tape TM; it
  is **not** formalized here and is recorded as an explicit obligation in
  `pvnp/proofs/remaining-obstructions.md`.  No manuscript claim may rely on it.
* **Encoders.** `P_WCC_enc E` lets an encoder from `E` rewrite the input
  before the WCC runs.  With unrestricted encoders every language — including
  undecidable ones — is decided in time `0` by a fixed one-cell reader
  (`unrestricted_encoder_trivializes_WCC`).  The frozen model uses the identity
  encoder (`P_WCC_enc_id`).
* **Advice.** Prepending a single length-indexed advice bit already decides
  every length-determined language (`advice_bit_trivializes`), so
  non-uniform advice must be excluded explicitly.
-/

namespace PVNP.Discrete

/-! ## `(1 + d)`-dimensional WCCs -/

/-- A discrete WCC on `ℤ × ℤ^d` (Moore neighbourhood of radius one). -/
structure WCCD (d : ℕ) where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  blank : S
  rule : (Fin 3 × (Fin d → Fin 3) → S) → S
  quiescent : rule (fun _ => blank) = blank
  inp : Bool → S
  origin : Option Bool → S
  acc : S → Bool
  rej : S → Bool

namespace WCCD

attribute [instance] WCCD.finS WCCD.decS

/-- Lattice sites of `ℤ^(1+d)`. -/
abbrev Site (d : ℕ) := ℤ × (Fin d → ℤ)

/-- Offset `-1, 0, 1` of a neighbourhood index. -/
def off (u : Fin 3) : ℤ := (u : ℤ) - 1

theorem off_zero : off 0 = -1 := by decide
theorem off_one : off 1 = 0 := by decide
theorem off_two : off 2 = 1 := by decide

variable {d : ℕ} (A : WCCD d)

/-- Synchronous global update. -/
def step (c : Site d → A.S) : Site d → A.S :=
  fun p => A.rule fun u => c (p.1 + off u.1, fun i => p.2 i + off (u.2 i))

def run (c : Site d → A.S) (t : ℕ) : Site d → A.S := (A.step)^[t] c

/-- Input on the first coordinate axis, exactly as in the one-dimensional model. -/
def init (x : List Bool) (p : Site d) : A.S :=
  if p.2 = 0 then
    (if p.1 = 0 then A.origin x.head?
     else if 0 < p.1 ∧ p.1 < x.length then A.inp (x.getD p.1.toNat false) else A.blank)
  else A.blank

open Classical in
noncomputable def outCfg (c : Site d → A.S) : Option Bool :=
  answerOf (decide (∃ p, A.acc (c p) = true)) (decide (∃ p, A.rej (c p) = true))

noncomputable def out (x : List Bool) (s : ℕ) : Option Bool := A.outCfg (A.run (A.init x) s)

def Decides (L : Set (List Bool)) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, DecidesAt (A.out x) (T x.length) x L

theorem run_succ (c : Site d → A.S) (t : ℕ) : A.run c (t + 1) = A.step (A.run c t) := by
  simp [run, Function.iterate_succ_apply']

end WCCD

/-- Languages decided in polynomial time by a `(1+d)`-dimensional WCC. -/
def P_WCCD (d : ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (A : WCCD d) (p : Polynomial ℕ), A.Decides L (fun n => p.eval n)}

namespace WCC

variable (B : WCC)

/-- Light cone: cells left of `-t` are blank at time `t`. -/
theorem run_blank_left (x : List Bool) (t : ℕ) (j : ℤ) (hj : j < -(t : ℤ)) :
    B.run (B.init x) t j = B.blank := by
  induction t generalizing j with
  | zero =>
    show B.init x j = B.blank
    simp only [WCC.init]
    rw [if_neg (by omega), if_neg (by omega)]
  | succ t ih =>
    rw [WCC.run_succ]
    show B.rule (B.run (B.init x) t (j - 1)) (B.run (B.init x) t j)
      (B.run (B.init x) t (j + 1)) = B.blank
    push_cast at hj
    rw [ih (j - 1) (by omega), ih j (by omega), ih (j + 1) (by omega), B.quiescent]

/-- A radius-one WCC on `ℤ`, embedded in `ℤ^(1+d)`: the rule reads only the
two first-axis neighbours and the centre. -/
def toD (d : ℕ) : WCCD d where
  S := B.S
  blank := B.blank
  rule w := B.rule (w (0, fun _ => 1)) (w (1, fun _ => 1)) (w (2, fun _ => 1))
  quiescent := B.quiescent
  inp := B.inp
  origin := B.origin
  acc := B.acc
  rej := B.rej

variable {d : ℕ}

theorem toD_step (c : WCCD.Site d → B.S) (j : ℤ) (q : Fin d → ℤ) :
    (B.toD d).step c (j, q) = B.rule (c (j - 1, q)) (c (j, q)) (c (j + 1, q)) := by
  show B.rule (c (j + WCCD.off 0, fun i => q i + WCCD.off 1))
      (c (j + WCCD.off 1, fun i => q i + WCCD.off 1))
      (c (j + WCCD.off 2, fun i => q i + WCCD.off 1)) = _
  rw [WCCD.off_zero, WCCD.off_one, WCCD.off_two]
  simp only [add_zero, ← sub_eq_add_neg]

/-- **Exact embedding of the run**: on the first axis the `(1+d)`-dimensional
run is the one-dimensional run; every other cell stays blank. -/
theorem toD_run (x : List Bool) (t : ℕ) (j : ℤ) (q : Fin d → ℤ) :
    (B.toD d).run ((B.toD d).init x) t (j, q) =
      if q = 0 then B.run (B.init x) t j else B.blank := by
  induction t generalizing j q with
  | zero => rfl
  | succ t ih =>
    rw [WCCD.run_succ, B.toD_step, ih, ih, ih, WCC.run_succ]
    by_cases hq : q = 0
    · simp only [hq, if_true]; rfl
    · simp only [hq, if_false]; exact B.quiescent

theorem toD_exists (x : List Bool) (s : ℕ) (P : B.S → Bool) :
    (∃ p, P ((B.toD d).run ((B.toD d).init x) s p) = true) ↔
      ∃ j, P (B.run (B.init x) s j) = true := by
  constructor
  · rintro ⟨⟨j, q⟩, h⟩
    rw [B.toD_run] at h
    by_cases hq : q = 0
    · rw [if_pos hq] at h; exact ⟨j, h⟩
    · rw [if_neg hq] at h
      exact ⟨-(s : ℤ) - 1, by rw [B.run_blank_left x s _ (by omega)]; exact h⟩
  · rintro ⟨j, h⟩
    exact ⟨(j, 0), by rw [B.toD_run, if_pos rfl]; exact h⟩

theorem toD_out (x : List Bool) (s : ℕ) : (B.toD d).out x s = B.out x s := by
  unfold WCCD.out WCC.out WCCD.outCfg WCC.outCfg
  congr 1
  · exact decide_eq_decide.2 (B.toD_exists x s B.acc)
  · exact decide_eq_decide.2 (B.toD_exists x s B.rej)

theorem toD_decides {L : Set (List Bool)} {T : ℕ → ℕ} (h : B.Decides L T) :
    (B.toD d).Decides L T := by
  intro x
  rw [show (B.toD d).out x = B.out x from funext (B.toD_out x)]
  exact h x

end WCC

theorem P_WCC_subset_P_WCCD (d : ℕ) : P_WCC ⊆ P_WCCD d := by
  rintro L ⟨B, p, h⟩
  exact ⟨B.toD d, p, B.toD_decides h⟩

/-- **Every polynomial-time TM language is decided in polynomial time on every
lattice `ℤ^(1+d)`** (same polynomial as the one-dimensional real-time
simulation). -/
theorem P_TM_subset_P_WCCD (d : ℕ) : P_TM ⊆ P_WCCD d :=
  P_TM_subset_P_WCC.trans (P_WCC_subset_P_WCCD d)

theorem NP_TM_subset_NP_WCCD (d : ℕ) : NP_TM ⊆ NPOf (P_WCCD d) := by
  rintro L ⟨V, hV, q, hq⟩
  exact ⟨V, P_TM_subset_P_WCCD d hV, q, hq⟩

/-! ## Encoders and advice -/

/-- Languages decided by a WCC after rewriting the input with an encoder from
`E` (the time bound is charged in the original input length). -/
def P_WCC_enc (E : Set (List Bool → List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ (A : WCC) (p : Polynomial ℕ) (e : List Bool → List Bool), e ∈ E ∧
      ∀ x, DecidesAt (A.out (e x)) (p.eval x.length) x L}

/-- The frozen model is the identity encoder. -/
theorem P_WCC_enc_id : P_WCC_enc {id} = P_WCC := by
  ext L
  constructor
  · rintro ⟨A, p, e, he, h⟩
    rw [Set.mem_singleton_iff] at he
    subst he
    exact ⟨A, p, h⟩
  · rintro ⟨A, p, h⟩
    exact ⟨A, p, id, rfl, h⟩

/-- A one-cell reader: accepts iff the first encoded bit is `true`. -/
def bitReader : WCC where
  S := Fin 3
  blank := 0
  rule _ b _ := b
  quiescent := rfl
  inp _ := 0
  origin o := if o = some true then 1 else 2
  acc s := decide (s = 1)
  rej s := decide (s = 2)

theorem bitReader_run (c : ℤ → bitReader.S) (t : ℕ) : bitReader.run c t = c :=
  Function.iterate_fixed (f := bitReader.step) (x := c) (funext fun _ => rfl) t

theorem bitReader_out (b : Bool) (xs : List Bool) (s : ℕ) :
    bitReader.out (b :: xs) s = some b := by
  classical
  unfold WCC.out WCC.outCfg
  rw [bitReader_run]
  have h0 : bitReader.init (b :: xs) 0 = (if b then 1 else 2 : Fin 3) := by
    cases b <;> rfl
  have hne : ∀ i : ℤ, i ≠ 0 → bitReader.init (b :: xs) i = (0 : Fin 3) := by
    intro i hi
    simp only [WCC.init, if_neg hi]
    split_ifs <;> rfl
  have hacc : (∃ i, bitReader.acc (bitReader.init (b :: xs) i) = true) ↔ b = true := by
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i = 0
      · subst h; rw [h0] at hi; cases b
        · exact absurd hi (by decide)
        · rfl
      · rw [hne i h] at hi; exact absurd hi (by decide)
    · intro hb; exact ⟨0, by rw [h0, hb]; decide⟩
  have hrej : (∃ i, bitReader.rej (bitReader.init (b :: xs) i) = true) ↔ b = false := by
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i = 0
      · subst h; rw [h0] at hi; cases b
        · rfl
        · exact absurd hi (by decide)
      · rw [hne i h] at hi; exact absurd hi (by decide)
    · intro hb; exact ⟨0, by rw [h0, hb]; decide⟩
  cases b
  · have ha : ¬ ∃ i, bitReader.acc (bitReader.init (false :: xs) i) = true := by
      rw [hacc]; decide
    have hr : ∃ i, bitReader.rej (bitReader.init (false :: xs) i) = true := hrej.2 rfl
    simp only [answerOf, decide_eq_false ha, decide_eq_true hr]
    rfl
  · have ha : ∃ i, bitReader.acc (bitReader.init (true :: xs) i) = true := hacc.2 rfl
    simp only [answerOf, decide_eq_true ha]
    rfl

theorem bitReader_decides (L : Set (List Bool)) (x : List Bool) (b : Bool) (xs : List Bool)
    (hb : b = true ↔ x ∈ L) : DecidesAt (bitReader.out (b :: xs)) 0 x L :=
  ⟨b, ⟨0, le_rfl, bitReader_out b xs 0, fun _ h => absurd h (Nat.not_lt_zero _)⟩, hb⟩

/-- **Unrestricted encoders trivialize the discrete model**: every language
(decidable or not) is decided in time `0` by the fixed reader `bitReader`. -/
theorem unrestricted_encoder_trivializes_WCC : P_WCC_enc Set.univ = Set.univ := by
  classical
  ext L
  simp only [Set.mem_univ, iff_true]
  refine ⟨bitReader, 0, fun x => [decide (x ∈ L)], Set.mem_univ _, fun x => ?_⟩
  simpa using bitReader_decides L x (decide (x ∈ L)) [] (by simp)

/-- Encoders that prepend one advice bit depending only on the input length. -/
def adviceBitEnc : Set (List Bool → List Bool) :=
  {e | ∃ a : ℕ → Bool, e = fun x => a x.length :: x}

/-- **One bit of length advice trivializes every length-determined language**
(for instance `{x | the |x|-th TM halts}`), so non-uniform advice must be
excluded from any admissible encoder class. -/
theorem advice_bit_trivializes (a : ℕ → Bool) :
    {x : List Bool | a x.length = true} ∈ P_WCC_enc adviceBitEnc :=
  ⟨bitReader, 0, fun x => a x.length :: x, ⟨a, rfl⟩, fun x => by
    simpa using bitReader_decides {x : List Bool | a x.length = true} x (a x.length) x
      (by simp)⟩

end PVNP.Discrete
