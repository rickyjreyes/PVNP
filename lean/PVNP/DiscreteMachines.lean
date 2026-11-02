import Mathlib

/-!
# Discrete machine models for the Part II equivalence theorem (issue #11)

This file freezes the two *discrete* models compared in Part II.

* `TM`: an ordinary deterministic single-tape Turing machine with a
  **finite** control set `Λ`, a **finite** tape alphabet `Γ`, a bi-infinite
  tape `ℤ → Γ`, and a partial transition function that in one step writes a
  symbol and moves the head left, right, or not at all.
* `WCC`: a discrete wave-constrained computer in the Part II sense: a
  synchronous radius-one cellular automaton on `ℤ` with a **finite** cell
  alphabet, a quiescent blank (`rule blank blank blank = blank`), and a fixed
  local input convention (the origin cell carries a distinguished symbol).

Both models are *finite objects*: finiteness of every alphabet is part of the
structure, so no infinite-alphabet local function is treated as a machine
(compare `PVNP.OracleObstruction`).

Decision semantics are identical in both models: the run produces an output
stream `out : ℕ → Option Bool`, and a machine decides `L` within time bound
`T` when the *first* non-`none` output appears at a step `s ≤ T |x|` and equals
the membership bit of `x`.

The complexity classes `P_TM`, `P_WCC`, `NP_TM`, `NP_WCC` are defined
explicitly with polynomial time bounds `Polynomial ℕ`, and (for NP) explicit
witness-length polynomials and a fixed self-delimiting pairing of input and
witness.  Nothing about the relationship between the classes is assumed here.
-/

namespace PVNP.Discrete

/-! ## Shared decision semantics -/

/-- `FirstAnswer out T b`: the first non-`none` entry of `out` occurs at some
step `s ≤ T`, and that entry is `some b`. -/
def FirstAnswer (out : ℕ → Option Bool) (T : ℕ) (b : Bool) : Prop :=
  ∃ s ≤ T, out s = some b ∧ ∀ s' < s, out s' = none

/-- `out` decides the membership of `x` in `L` within `T` steps. -/
def DecidesAt (out : ℕ → Option Bool) (T : ℕ) (x : List Bool)
    (L : Set (List Bool)) : Prop :=
  ∃ b : Bool, FirstAnswer out T b ∧ (b = true ↔ x ∈ L)

/-- Output convention shared by both models: acceptance takes precedence. -/
def answerOf (a r : Bool) : Option Bool :=
  if a then some true else if r then some false else none

/-! ## Ordinary Turing machines -/

/-- Head movement of an ordinary Turing machine. -/
inductive Dir
  | L
  | S
  | R
  deriving DecidableEq, Fintype

/-- Integer displacement of a head movement. -/
def Dir.shift : Dir → ℤ
  | .L => -1
  | .S => 0
  | .R => 1

/-- An ordinary deterministic single-tape Turing machine with finite control
and finite tape alphabet.  `δ q a = none` means the machine halts. -/
structure TM where
  Λ : Type
  Γ : Type
  [finΛ : Fintype Λ]
  [finΓ : Fintype Γ]
  [decΛ : DecidableEq Λ]
  [decΓ : DecidableEq Γ]
  blank : Γ
  inp : Bool → Γ
  start : Λ
  δ : Λ → Γ → Option (Λ × Γ × Dir)
  acc : Λ → Bool
  rej : Λ → Bool

namespace TM

attribute [instance] TM.finΛ TM.finΓ TM.decΛ TM.decΓ

/-- A full Turing-machine configuration: control state, tape, head position. -/
structure Cfg (M : TM) where
  q : M.Λ
  tape : ℤ → M.Γ
  head : ℤ

variable (M : TM)

/-- One transition, or `none` if the machine has halted. -/
def step (c : M.Cfg) : Option M.Cfg :=
  (M.δ c.q (c.tape c.head)).map fun t =>
    ⟨t.1, Function.update c.tape c.head t.2.1, c.head + t.2.2.shift⟩

/-- Total successor: a halted configuration is a fixed point. -/
def next (c : M.Cfg) : M.Cfg := (M.step c).getD c

/-- `t` steps of execution. -/
def run (c : M.Cfg) (t : ℕ) : M.Cfg := (M.next)^[t] c

/-- Input tape: `x` written on cells `0, …, |x|-1`, blank elsewhere. -/
def inputTape (x : List Bool) (i : ℤ) : M.Γ :=
  if 0 ≤ i ∧ i < x.length then M.inp (x.getD i.toNat false) else M.blank

/-- Initial configuration on input `x`: start state, head on cell `0`. -/
def init (x : List Bool) : M.Cfg := ⟨M.start, M.inputTape x, 0⟩

/-- The answer currently displayed by the control state. -/
def ans (c : M.Cfg) : Option Bool := answerOf (M.acc c.q) (M.rej c.q)

/-- Output stream of the run on input `x`. -/
def out (x : List Bool) (s : ℕ) : Option Bool := M.ans (M.run (M.init x) s)

/-- `M` decides `L` with time bound `T` (as a function of input length). -/
def Decides (L : Set (List Bool)) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, DecidesAt (M.out x) (T x.length) x L

theorem run_succ (c : M.Cfg) (t : ℕ) : M.run c (t + 1) = M.next (M.run c t) := by
  simp [run, Function.iterate_succ_apply']

theorem run_add (c : M.Cfg) (a b : ℕ) : M.run c (a + b) = M.run (M.run c a) b := by
  simp only [run]
  rw [add_comm, Function.iterate_add_apply]

end TM

/-! ## Discrete wave-constrained computers (radius-one finite CA) -/

/-- A discrete WCC: finite alphabet, radius-one synchronous rule on `ℤ`,
quiescent blank, origin-marked input convention. -/
structure WCC where
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  blank : S
  rule : S → S → S → S
  quiescent : rule blank blank blank = blank
  inp : Bool → S
  origin : Option Bool → S
  acc : S → Bool
  rej : S → Bool

namespace WCC

attribute [instance] WCC.finS WCC.decS

variable (A : WCC)

/-- Synchronous global update. -/
def step (c : ℤ → A.S) : ℤ → A.S := fun i => A.rule (c (i - 1)) (c i) (c (i + 1))

/-- `t` synchronous updates. -/
def run (c : ℤ → A.S) (t : ℕ) : ℤ → A.S := (A.step)^[t] c

/-- Initial configuration: cell `0` carries `origin (head of x)`, cells
`1, …, |x|-1` carry the input bits, every other cell is blank. -/
def init (x : List Bool) (i : ℤ) : A.S :=
  if i = 0 then A.origin x.head?
  else if 0 < i ∧ i < x.length then A.inp (x.getD i.toNat false) else A.blank

open Classical in
/-- Global output: accept if some cell is accepting, otherwise reject if
some cell is rejecting. -/
noncomputable def outCfg (c : ℤ → A.S) : Option Bool :=
  answerOf (decide (∃ i, A.acc (c i) = true)) (decide (∃ i, A.rej (c i) = true))

/-- Output stream of the run on input `x`. -/
noncomputable def out (x : List Bool) (s : ℕ) : Option Bool := A.outCfg (A.run (A.init x) s)

/-- `A` decides `L` with time bound `T`. -/
def Decides (L : Set (List Bool)) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, DecidesAt (A.out x) (T x.length) x L

theorem run_succ (c : ℤ → A.S) (t : ℕ) : A.run c (t + 1) = A.step (A.run c t) := by
  simp [run, Function.iterate_succ_apply']

end WCC

/-! ## Complexity classes -/

/-- Languages decided by an ordinary TM in polynomial time. -/
def P_TM : Set (Set (List Bool)) :=
  {L | ∃ (M : TM) (p : Polynomial ℕ), M.Decides L (fun n => p.eval n)}

/-- Languages decided by a discrete WCC in polynomial time. -/
def P_WCC : Set (Set (List Bool)) :=
  {L | ∃ (A : WCC) (p : Polynomial ℕ), A.Decides L (fun n => p.eval n)}

/-- Self-delimiting pairing of an input and a witness: every input bit `b`
becomes `true, b`, followed by the terminator `false`, then the witness. -/
def pair (x w : List Bool) : List Bool :=
  x.flatMap (fun b => [true, b]) ++ false :: w

/-- Verifier-based NP over an arbitrary base class of polynomial-time
languages, with an explicit witness-length polynomial. -/
def NPOf (C : Set (Set (List Bool))) : Set (Set (List Bool)) :=
  {L | ∃ V ∈ C, ∃ q : Polynomial ℕ, ∀ x : List Bool,
      x ∈ L ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ pair x w ∈ V}

/-- NP for ordinary Turing machines (polynomial-time TM verifiers). -/
def NP_TM : Set (Set (List Bool)) := NPOf P_TM

/-- NP for discrete WCCs (polynomial-time WCC verifiers). -/
def NP_WCC : Set (Set (List Bool)) := NPOf P_WCC

theorem pair_injective {x x' w w' : List Bool} (h : pair x w = pair x' w') :
    x = x' ∧ w = w' := by
  induction x generalizing x' with
  | nil =>
    cases x' with
    | nil => simpa [pair] using h
    | cons b x' => simp [pair] at h
  | cons b x ih =>
    cases x' with
    | nil => simp [pair] at h
    | cons b' x' =>
      simp only [pair, List.flatMap_cons, List.cons_append, List.nil_append,
        List.cons.injEq, true_and] at h
      obtain ⟨hb, h⟩ := h
      have := ih (by simpa [pair] using h)
      exact ⟨by rw [hb, this.1], this.2⟩

end PVNP.Discrete
