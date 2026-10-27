import PVNP.PartII

/-!
# Part II — a uniform radius-one discrete WCC machine

A fixed blank state and fixed local rule operate on a finite one-dimensional
lattice. Exact wave/symbol simulation holds under a COMMUTING local rule.
This does not formalize the complexity-theoretic polynomial-overhead theorem.
-/

namespace PVNP.PartII

variable {State Target : Type}

abbrev Configuration (n : Nat) (State : Type) := Fin n → State

structure RadiusOneMachine (State : Type) where
  blank : State
  localRule : State → State → State → State

def sample (M : RadiusOneMachine State) {n : Nat}
    (c : Configuration n State) (j : Nat) : State :=
  if h : j < n then c ⟨j, h⟩ else M.blank

def left (M : RadiusOneMachine State) {n : Nat}
    (c : Configuration n State) (i : Fin n) : State :=
  if i.val = 0 then M.blank else sample M c (i.val - 1)

def right (M : RadiusOneMachine State) {n : Nat}
    (c : Configuration n State) (i : Fin n) : State :=
  sample M c (i.val + 1)

def step (M : RadiusOneMachine State) {n : Nat}
    (c : Configuration n State) : Configuration n State :=
  fun i => M.localRule (left M c i) (c i) (right M c i)

/-- Each updated cell depends only on its bounded three-cell stencil. -/
theorem local_update_only
    (M : RadiusOneMachine State) {n : Nat}
    (c d : Configuration n State) (i : Fin n)
    (hl : left M c i = left M d i)
    (hc : c i = d i)
    (hr : right M c i = right M d i) :
    step M c i = step M d i := by
  simp [step, hl, hc, hr]

/-- Quantization preserves fallback readings if blank states agree. -/
theorem sample_compatible
    (A : RadiusOneMachine State) (B : RadiusOneMachine Target)
    (Q : State → Target) (hblank : Q A.blank = B.blank)
    {n : Nat} (c : Configuration n State) (j : Nat) :
    Q (sample A c j) = sample B (fun i => Q (c i)) j := by
  unfold sample
  split_ifs <;> simp [hblank]

theorem left_compatible
    (A : RadiusOneMachine State) (B : RadiusOneMachine Target)
    (Q : State → Target) (hblank : Q A.blank = B.blank)
    {n : Nat} (c : Configuration n State) (i : Fin n) :
    Q (left A c i) = left B (fun i => Q (c i)) i := by
  unfold left
  split_ifs
  · exact hblank
  · exact sample_compatible A B Q hblank c _

theorem right_compatible
    (A : RadiusOneMachine State) (B : RadiusOneMachine Target)
    (Q : State → Target) (hblank : Q A.blank = B.blank)
    {n : Nat} (c : Configuration n State) (i : Fin n) :
    Q (right A c i) = right B (fun i => Q (c i)) i := by
  exact sample_compatible A B Q hblank c _

/-- A commuting local transition and compatible blank yield a commuting
global update, with no appeal to unproved physical realizability. -/
theorem step_compatible
    (A : RadiusOneMachine State) (B : RadiusOneMachine Target)
    (Q : State → Target) (hblank : Q A.blank = B.blank)
    (hrule : ∀ a b c, Q (A.localRule a b c) =
      B.localRule (Q a) (Q b) (Q c))
    {n : Nat} (c : Configuration n State) :
    (fun i => Q (step A c i)) = step B (fun i => Q (c i)) := by
  funext i
  simp only [step]
  rw [hrule]
  rw [left_compatible A B Q hblank c i]
  rw [right_compatible A B Q hblank c i]

/-- Semiconjugacy of a bounded-local WCC machine is preserved under
arbitrarily many deterministic discrete updates. -/
theorem trajectory_compatible
    (A : RadiusOneMachine State) (B : RadiusOneMachine Target)
    (Q : State → Target) (hblank : Q A.blank = B.blank)
    (hrule : ∀ a b c, Q (A.localRule a b c) =
      B.localRule (Q a) (Q b) (Q c))
    {n : Nat} (c : Configuration n State) (t : Nat) :
    (fun i => Q ((iterate (step A) t c) i)) =
      iterate (step B) t (fun i => Q (c i)) := by
  exact encode_iterate (step A) (step B) (fun conf i => Q (conf i))
    (fun conf => step_compatible A B Q hblank hrule conf) t c

end PVNP.PartII
