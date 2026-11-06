import Mathlib

/-! Finite Boolean circuits with an explicit bounded-fan-in basis. A layer may read
each preceding wire any number of times. Series composition counts the producer
once. Arbitrary acyclic straight-line circuits can retain their earlier wires and
append one binary gate at a time. No bound on depth or uniformity is imposed. -/
namespace PVNP.BooleanNetwork

inductive Expr (I : Type) where
  | var (i : I)
  | lit (b : Bool)
  | neg (a : Expr I)
  | conj (a b : Expr I)
  | disj (a b : Expr I)

namespace Expr

def eval (x : I → Bool) : Expr I → Bool
  | .var i => x i
  | .lit b => b
  | .neg a => !(eval x a)
  | .conj a b => eval x a && eval x b
  | .disj a b => eval x a || eval x b

-- This upper bound also charges the leaves of each gate expression.
def size : Expr I → ℕ
  | .var _ | .lit _ => 1
  | .neg a => a.size + 1
  | .conj a b | .disj a b => a.size + b.size + 1

def any (xs : List A) (f : A → Expr I) : Expr I :=
  xs.foldr (fun a r => .disj (f a) r) (.lit false)

theorem eval_any (xs : List A) (f : A → Expr I) (x : I → Bool) :
    (any xs f).eval x = true ↔ ∃ a ∈ xs, (f a).eval x = true := by
  induction xs with
  | nil => simp [any, eval]
  | cons a xs ih => simp [any, eval] at ih ⊢; exact or_congr_right ih

theorem size_any (xs : List A) (f : A → Expr I) {k : ℕ} (h : ∀ a, (f a).size ≤ k) :
    (any xs f).size ≤ 1 + (k+1)*xs.length := by
  induction xs with
  | nil => simp [any, size]
  | cons a xs ih =>
    change (f a).size + (any xs f).size + 1 ≤ _
    simp only [List.length_cons, Nat.mul_succ]
    have := h a
    omega

noncomputable def elems (A : Type) [Fintype A] : List A := (Finset.univ : Finset A).toList

@[simp] theorem mem_elems [Fintype A] (a : A) : a ∈ elems A := by simp [elems]
@[simp] theorem length_elems (A : Type) [Fintype A] : (elems A).length = Fintype.card A := by simp [elems]

def bitMap (i : I) : Bool → Bool → Expr I
  | false, false => .lit false
  | false, true => .var i
  | true, false => .neg (.var i)
  | true, true => .lit true

theorem bitMap_eval (i : I) (a b : Bool) (x : I → Bool) :
    (bitMap i a b).eval x = if x i then b else a := by
  cases a <;> cases b <;> cases h : x i <;> simp [bitMap, eval, h]

theorem bitMap_size (i : I) (a b : Bool) : (bitMap i a b).size ≤ 2 := by
  cases a <;> cases b <;> simp [bitMap, size]

end Expr

inductive Net : Type → Type → Type 1 where
  | wires {I O} (port : O → I) : Net I O
  | layer {I O} [fin : Fintype O] (gates : O → Expr I) : Net I O
  | seq {I A O} (first : Net I A) (second : Net A O) : Net I O
  | par {I A B} (left : Net I A) (right : Net I B) : Net I (A ⊕ B)

namespace Net

def eval : Net I O → (I → Bool) → (O → Bool)
  | .wires f, x => x ∘ f
  | @Net.layer _ _ _ f, x => fun o => (f o).eval x
  | .seq a b, x => b.eval (a.eval x)
  | .par a b, x => Sum.elim (a.eval x) (b.eval x)

def size : Net I O → ℕ
  | .wires _ => 0
  | @Net.layer _ _ _ f => ∑ i, (f i).size
  | .seq a b | .par a b => a.size + b.size

end Net

/-- A non-uniform family, one exact circuit for each input length, one
polynomial bounding the sizes of all members of the family. -/
def PPoly : Set (Set (List Bool)) :=
  {L | ∃ p : Polynomial ℕ, ∀ n, ∃ C : Net (Fin n) Unit,
    C.size ≤ p.eval n ∧ ∀ x : Fin n → Bool, C.eval x () = true ↔ List.ofFn x ∈ L}

end PVNP.BooleanNetwork
