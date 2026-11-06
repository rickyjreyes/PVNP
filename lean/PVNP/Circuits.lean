import PVNP.SATTarget

/-!
# Phase X: Boolean circuits and the class `Ppoly`

A Boolean circuit is a finite directed acyclic graph of fan-in at most two gates (`const`, `inp`,
`not`, `and`, `or`) with one output. It is represented here by

* a gate for every register name (`gate : α → Gate α`);
* a rank function decreasing along every wire (`wf`), so that the gate graph is acyclic;
* the finite list `regs` of registers that carry gates. Every other register is the constant
  `false` (`triv`), so no computation can hide outside `regs`;
* an output register `out`.

The **size** of a circuit is `regs.length`, an upper bound on the number of gates. Evaluation is
by fuel (`valN`); the value function `val` satisfies the gate equations (`val_eq`).

`Ppoly` is the class of languages decided, at every input length `n`, by a circuit of size at most
`p(n)` for one polynomial `p`. This is non-uniform polynomial size, the standard `P/poly`.
-/

namespace PVNP.Circuits

/-- A gate of a Boolean circuit with register names in `α`. -/
inductive Gate (α : Type) where
  | const (b : Bool)
  | inp (i : ℕ)
  | not (a : α)
  | and (a b : α)
  | or (a b : α)

namespace Gate

variable {α : Type}

/-- The registers a gate reads. -/
def args : Gate α → List α
  | const _ => []
  | inp _ => []
  | not a => [a]
  | and a b => [a, b]
  | or a b => [a, b]

/-- The value of a gate, given values `v` of the registers and the input bits `x`. -/
def eval (v : α → Bool) (x : ℕ → Bool) : Gate α → Bool
  | const b => b
  | inp i => x i
  | not a => !(v a)
  | and a b => v a && v b
  | or a b => v a || v b

theorem eval_congr {v w : α → Bool} (x : ℕ → Bool) (g : Gate α) (h : ∀ a ∈ g.args, v a = w a) :
    g.eval v x = g.eval w x := by
  cases g <;> simp_all [args, eval]

end Gate

/-- A Boolean circuit: an acyclic gate graph on registers `α`, with the finite list `regs` of
non-trivial registers and an output register. -/
structure Circuit (α : Type) where
  gate : α → Gate α
  rank : α → ℕ
  wf : ∀ a, ∀ b ∈ (gate a).args, rank b < rank a
  regs : List α
  triv : ∀ a, a ∉ regs → gate a = Gate.const false
  out : α

namespace Circuit

variable {α : Type} (C : Circuit α)

/-- Evaluation with fuel `k`. -/
def valN (x : ℕ → Bool) : ℕ → α → Bool
  | 0, _ => false
  | k + 1, a => (C.gate a).eval (valN x k) x

theorem valN_stable (x : ℕ → Bool) :
    ∀ (r : ℕ) (a : α), C.rank a = r → ∀ k k', r < k → r < k' → C.valN x k a = C.valN x k' a := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro a ha k k' hk hk'
    obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by omega⟩
    simp only [valN]
    apply Gate.eval_congr
    intro b hb
    have hrb := C.wf a b hb
    exact ih (C.rank b) (by omega) b rfl k k' (by omega) (by omega)

/-- The value of a register. -/
def val (x : ℕ → Bool) (a : α) : Bool := C.valN x (C.rank a + 1) a

/-- **Gate equations.** Every register's value is its gate applied to the values of its
arguments. -/
theorem val_eq (x : ℕ → Bool) (a : α) : C.val x a = (C.gate a).eval (C.val x) x := by
  show C.valN x (C.rank a + 1) a = _
  rw [valN]
  apply Gate.eval_congr
  intro b hb
  have hrb := C.wf a b hb
  show C.valN x (C.rank a) b = C.valN x (C.rank b + 1) b
  exact C.valN_stable x (C.rank b) b rfl _ _ (by omega) (by omega)

/-- The output of the circuit on the input bits `x`. -/
def eval (x : ℕ → Bool) : Bool := C.val x C.out

/-- The size of the circuit: the number of listed registers. -/
def size : ℕ := C.regs.length

theorem val_const (x : ℕ → Bool) {a : α} {b : Bool} (h : C.gate a = Gate.const b) :
    C.val x a = b := by rw [val_eq, h]; rfl

theorem val_inp (x : ℕ → Bool) {a : α} {i : ℕ} (h : C.gate a = Gate.inp i) :
    C.val x a = x i := by rw [val_eq, h]; rfl

theorem val_not (x : ℕ → Bool) {a b : α} (h : C.gate a = Gate.not b) :
    C.val x a = !(C.val x b) := by rw [val_eq, h]; rfl

theorem val_and (x : ℕ → Bool) {a b c : α} (h : C.gate a = Gate.and b c) :
    C.val x a = (C.val x b && C.val x c) := by rw [val_eq, h]; rfl

theorem val_or (x : ℕ → Bool) {a b c : α} (h : C.gate a = Gate.or b c) :
    C.val x a = (C.val x b || C.val x c) := by rw [val_eq, h]; rfl

end Circuit

/-! ### Renaming registers -/

namespace Gate

variable {α β : Type}

/-- Renaming the registers of a gate. -/
def map (f : α → β) : Gate α → Gate β
  | .const b => .const b
  | .inp i => .inp i
  | .not a => .not (f a)
  | .and a b => .and (f a) (f b)
  | .or a b => .or (f a) (f b)

theorem eval_map (f : α → β) (v : β → Bool) (x : ℕ → Bool) (g : Gate α) :
    (g.map f).eval v x = g.eval (v ∘ f) x := by
  cases g <;> rfl

theorem args_map (f : α → β) (g : Gate α) : (g.map f).args = g.args.map f := by
  cases g <;> rfl

end Gate

namespace Circuit

variable {α β : Type}

/-- **Embedding**: a register whose gate is the renamed gate of another circuit has the same
value. -/
theorem val_embed (C : Circuit α) (C' : Circuit β) (f : α → β)
    (hg : ∀ a, C'.gate (f a) = (C.gate a).map f) (x : ℕ → Bool) :
    ∀ a, C'.val x (f a) = C.val x a := by
  intro a
  induction h : C.rank a using Nat.strong_induction_on generalizing a with
  | _ r ih =>
    rw [C'.val_eq, hg, Gate.eval_map, C.val_eq]
    apply Gate.eval_congr
    intro b hb
    exact ih (C.rank b) (h ▸ C.wf a b hb) b rfl

end Circuit

/-- A circuit decides the length-`n` slice of `L`. -/
def DecidesLen {α : Type} (C : Circuit α) (L : Set (List Bool)) (n : ℕ) : Prop :=
  ∀ x : List Bool, x.length = n → (C.eval (fun i => x.getD i false) = true ↔ x ∈ L)

/-- **`P/poly`**: languages decided at every input length `n` by a circuit of size at most
`p(n)`, for one polynomial `p`. -/
def Ppoly : Set (Set (List Bool)) :=
  {L | ∃ p : Polynomial ℕ, ∀ n : ℕ, ∃ (α : Type) (C : Circuit α), C.size ≤ p.eval n ∧ DecidesLen C L n}

/-- Natural-coefficient polynomials are monotone. -/
theorem poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self _), Polynomial.eval_eq_sum_range' (Nat.lt_succ_self _)]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

end PVNP.Circuits
