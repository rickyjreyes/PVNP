import PVNP.PartIIExtended

/-!
# Executable radius-one compiler for a finite Turing transition table

This module compiles *an arbitrary fixed deterministic transition function*
into a finite-alphabet radius-one WCC local rule. The machine has a
single-tape head-marker alphabet, with stationary, left and right moves.
The local logic handles the moving head and the overwritten symbol. The
global inductive simulation invariant (exactly one head, no falloff,
correct decode over arbitrary runs) and a uniform binary machine-description
compiler are still independent formal obligations.
-/

namespace PVNP.TMCellCompiler

open PVNP.PartII

inductive Move where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

structure Instruction (Q Gamma : Type) where
  next : Q
  write : Gamma
  move : Move

structure TapeCell (Q Gamma : Type) where
  symbol : Gamma
  head : Option Q

/-- Structural extensionality for marked tape cells. -/
theorem TapeCell.ext {Q Gamma : Type} {a b : TapeCell Q Gamma}
    (hsymbol : a.symbol = b.symbol) (hhead : a.head = b.head) :
    a = b := by
  cases a with
  | mk sa ha =>
      cases b with
      | mk sb hb =>
          dsimp at hsymbol hhead
          cases hsymbol
          cases hhead
          rfl

structure TMTable (Q Gamma : Type) where
  blankSymbol : Gamma
  transition : Q → Gamma → Instruction Q Gamma

/-- If there is a head in the center, update its symbol. Otherwise move
    a head into the center only when the neighbor's transition points here. -/
def compiledRule {Q Gamma : Type} (T : TMTable Q Gamma)
    (l c r : TapeCell Q Gamma) : TapeCell Q Gamma :=
  match c.head with
  | some q =>
      let ins := T.transition q c.symbol
      { symbol := ins.write
        head := if ins.move = Move.stay then some ins.next else none }
  | none =>
      let leftArrives : Option Q :=
        match l.head with
        | none => none
        | some q =>
            let ins := T.transition q l.symbol
            if ins.move = Move.right then some ins.next else none
      let rightArrives : Option Q :=
        match r.head with
        | none => none
        | some q =>
            let ins := T.transition q r.symbol
            if ins.move = Move.left then some ins.next else none
      { symbol := c.symbol
        head := leftArrives.orElse (fun _ => rightArrives) }

/-- Finite blank symbol and one fixed finite radius-one local rule. -/
def compile {Q Gamma : Type} (T : TMTable Q Gamma) :
    RadiusOneMachine (TapeCell Q Gamma) where
  blank := { symbol := T.blankSymbol, head := none }
  localRule := compiledRule T

/-- Any head-bearing cell writes the symbol prescribed by its transition
    table, regardless of neighbor values. -/
theorem on_head_writes {Q Gamma : Type} (T : TMTable Q Gamma)
    (q : Q) (l c r : TapeCell Q Gamma) :
    (compiledRule T l { c with head := some q } r).symbol =
      (T.transition q c.symbol).write := by
  rfl

/-- The center marker remains iff the transition stays. -/
theorem on_head_stay {Q Gamma : Type} (T : TMTable Q Gamma)
    (q : Q) (l c r : TapeCell Q Gamma)
    (h : (T.transition q c.symbol).move = Move.stay) :
    (compiledRule T l { c with head := some q } r).head =
      some (T.transition q c.symbol).next := by
  simp [compiledRule, h]

theorem on_head_move {Q Gamma : Type} (T : TMTable Q Gamma)
    (q : Q) (l c r : TapeCell Q Gamma)
    (h : (T.transition q c.symbol).move ≠ Move.stay) :
    (compiledRule T l { c with head := some q } r).head =
      none := by
  simp [compiledRule, h]

/-- A headless center cell never changes its tape symbol. -/
theorem headless_preserves_symbol {Q Gamma : Type} (T : TMTable Q Gamma)
    (l c r : TapeCell Q Gamma) (h : c.head = none) :
    (compiledRule T l c r).symbol = c.symbol := by
  simp [compiledRule, h]

/-- A right-moving left neighbor deposits its new control at an unmarked
    center, provided no other head is already there. -/
theorem right_move_arrives {Q Gamma : Type} (T : TMTable Q Gamma)
    (q : Q) (l c r : TapeCell Q Gamma)
    (hc : c.head = none) (hl : l.head = some q)
    (h : (T.transition q l.symbol).move = Move.right) :
    (compiledRule T l c r).head =
      some (T.transition q l.symbol).next := by
  simp [compiledRule, hc, hl, h]


/-- The symmetric left-arrival clause. Only the right neighbor may carry
    the head; a competing left neighbor would be a malformed TM encoding. -/
theorem left_move_arrives {Q Gamma : Type} (T : TMTable Q Gamma)
    (q : Q) (l c r : TapeCell Q Gamma)
    (hc : c.head = none) (hl : l.head = none)
    (hr : r.head = some q)
    (h : (T.transition q r.symbol).move = Move.left) :
    (compiledRule T l c r).head =
      some (T.transition q r.symbol).next := by
  simp [compiledRule, hc, hl, hr, h]

/-- A headless center with headless neighbors remains headless for ANY
    finite transition table. -/
theorem no_head_appears_from_empty_stencil {Q Gamma : Type}
    (T : TMTable Q Gamma) (l c r : TapeCell Q Gamma)
    (hl : l.head = none) (hc : c.head = none)
    (hr : r.head = none) :
    (compiledRule T l c r).head = none := by
  simp [compiledRule, hc, hl, hr]

end PVNP.TMCellCompiler
