import PVNP.TwoPhaseWindowWord
import PVNP.CookLevinGen

/-! Concrete finite-control single-tape programs for the original polynomial
radius. Addresses and state-code words are fixed at machine construction. A
control never holds the input length, a tape index, or an unbounded counter.
The register and serialization invariants needed to conclude MTM.Outputs for
these programs are recorded in the companion proof note. -/
namespace PVNP.TwoPhasePolynomialWriter

open PartIITuring PartIIUniform PartIITwoPhase TwoPhaseDecoder

inductive Mark | acc | dest | outer | inner deriving DecidableEq, Fintype
inductive Source | input | zero | mark (key : Mark) deriving DecidableEq, Fintype

structure Cell where
  inp : Option Bool
  flags : Mark → Bool
  out : Option Bool
  deriving DecidableEq, Fintype

private def emptyCell : Cell := ⟨none, fun _ => false, none⟩

inductive Sym | blank | leftEnd | raw (b : Bool) | work (c : Cell)
  deriving DecidableEq, Fintype

inductive Inst
  | finish
  | copy (src : Source) (dst : Mark) (next : ℕ)
  | take (key : Mark) (yes no : ℕ)
  | nextInput (ifBlank ifFalse ifTrue exhausted : ℕ)
  | headInput (ifBlank ifFalse ifTrue : ℕ)
  | inc (next : ℕ)
  | emit (b : Bool) (next : ℕ)
  deriving Inhabited

inductive State (size : ℕ)
  | start | mark | normalize | done
  | ret (pc : Fin (size+1)) | scan (pc : Fin (size+1)) | neighbor (pc : Fin (size+1))
  deriving DecidableEq, Fintype

private def asCell : Sym → Cell | .work c => c | _ => emptyCell
private def readBit (s : Sym) (b z o : ℕ) :=
  match (asCell s).inp with | none => b | some false => z | some true => o

private def lookup (p : Array Inst) (i : ℕ) : Inst := p[i]?.getD .finish
private def addr (p : Array Inst) (i : ℕ) : Fin (p.size+1) := ⟨min i p.size, by omega⟩

private def takeMark (c : Cell) (k : Mark) : Sym :=
  .work {c with flags := Function.update c.flags k false}

/-! ### Normalization phase: local operational proof obligations

These lemmas are about the *actual* finite-control transducer's tape
symbols and transition rule, not an abstract polynomial-output function.
They isolate the induction step needed for its still-unproved full
`MTM.Outputs` correctness theorem. -/

/-- During normalization, positions before k contain work symbols retaining
their exact input bits; the remaining positions are still raw input bits.
The fixed left-end sentinel sits at -1. -/
def partiallyNormalizedTape (x : List Bool) (k : ℕ) (i : ℤ) : Sym :=
  if i = -1 then .leftEnd
  else if 0 ≤ i ∧ i < (k : ℤ) then
    .work {emptyCell with inp := some (x.getD i.toNat false)}
  else if 0 ≤ i ∧ i < (x.length : ℤ) then
    .raw (x.getD i.toNat false)
  else .blank

/-- The next input cell remains unchanged until its normalization step. -/
theorem partially_normalized_current_input (x : List Bool) (k : ℕ)
    (hk : k < x.length) :
    partiallyNormalizedTape x k (k : ℤ) = .raw (x.getD k false) := by
  simp [partiallyNormalizedTape, hk, show (k : ℤ) ≠ -1 by omega]

/-- Replacing the current raw symbol with the marked work symbol extends
the correctly normalized prefix by exactly one cell, with all other
tape positions unchanged. -/
theorem partially_normalized_extend (x : List Bool) (k : ℕ) :
    Function.update (partiallyNormalizedTape x k) (k : ℤ)
      (.work {emptyCell with inp := some (x.getD k false)}) =
    partiallyNormalizedTape x (k + 1) := by
  funext i
  by_cases hi : i = (k : ℤ)
  · subst i
    simp [partiallyNormalizedTape]
  · rw [Function.update_of_ne hi]
    unfold partiallyNormalizedTape
    split_ifs <;> first | rfl | omega



private def step (p : Array Inst) (entry : ℕ) :
    State p.size → Sym → State p.size × Sym × Mv
  | .start, s => (.mark, s, .L)
  | .mark, _ => (.normalize, .leftEnd, .R)
  | .normalize, .raw b => (.normalize, .work {emptyCell with inp := some b}, .R)
  | .normalize, s => (.ret (addr p entry), s, .L)
  | .ret pc, .leftEnd => (.scan pc, .leftEnd, .R)
  | .ret pc, s => (.ret pc, s, .L)
  | .neighbor pc, s =>
    match lookup p pc with
    | .nextInput b z o _ => (.ret (addr p (readBit s b z o)), s, .L)
    | _ => (.done, s, .R)
  | .scan pc, s =>
    let c := asCell s
    match lookup p pc with
    | .finish =>
      match c.out with
      | none => (.done, .blank, .R)
      | some bit => (.scan pc, .raw bit, .R)
    | .headInput b z o => (.ret (addr p (readBit s b z o)), s, .L)
    | .copy src dst next =>
      match s with
      | .work old =>
        let b := match src with | .input => old.inp.isSome | .zero => false | .mark k => old.flags k
        (.scan pc, .work {old with flags := Function.update old.flags dst b}, .R)
      | _ => (.ret (addr p next), s, .L)
    | .take k yes no =>
      match s with
      | .work old => if old.flags k then (.ret (addr p yes), takeMark old k, .L)
                     else (.scan pc, s, .R)
      | _ => (.ret (addr p no), s, .L)
    | .nextInput _ _ _ ex =>
      match s with
      | .work old => if old.flags .outer then (.neighbor pc, takeMark old .outer, .R)
                     else (.scan pc, s, .R)
      | _ => (.ret (addr p ex), s, .L)
    | .inc next => if c.flags .dest then (.scan pc, s, .R)
                   else (.ret (addr p next), .work {c with flags := Function.update c.flags .dest true}, .L)
    | .emit b next => if c.out.isSome then (.scan pc, s, .R)
                      else (.ret (addr p next), .work {c with out := some b}, .L)
  | .done, s => (.done, s, .R)

private abbrev Asm := StateM (Array Inst)
private def putI (i : Inst) : Asm ℕ := do
  let p ← get
  set (p.push i)
  return p.size

private def setI (i : ℕ) (v : Inst) : Asm Unit := modify fun p => p.setIfInBounds i v

private def word (bits : List Bool) (next : ℕ) : Asm ℕ :=
  bits.foldrM (fun bit j => putI (.emit bit j)) next

private def repeated (bits : List Bool) (next : ℕ) : Asm ℕ := do
  let loop ← putI .finish
  let yes ← word bits loop
  setI loop (.take .outer yes next)
  putI (.copy (.mark .acc) .outer loop)

private def horner (next c : ℕ) : Asm ℕ := do
  let endStage ← putI (.copy (.mark .dest) .acc next)
  let addC ← (List.range c).foldlM (fun j _ => putI (.inc j)) endStage
  let outer ← putI .finish
  let inner ← putI .finish
  let inc ← putI (.inc inner)
  setI inner (.take .inner inc outer)
  let enter ← putI (.copy .input .inner inner)
  setI outer (.take .outer enter addC)
  let clear ← putI (.copy .zero .dest outer)
  putI (.copy (.mark .acc) .outer clear)

private def assemble (cs : List ℕ) (body : Asm ℕ) : ℕ × Array Inst :=
  (do let start ← body; cs.foldlM horner start).run #[]

private def coeffs (p : Polynomial ℕ) : List ℕ :=
  (List.range (p.natDegree+1)).map p.coeff

/-- The coefficient sequence assembled by the *actual polynomial writer* is
low-degree-first and is executed in reverse by its nested Horner control.
Its numeric clock value exactly equals the original polynomial radius.
This settles coefficient ordering only. It does not prove that the
finite-control tape-machine execution implements that Horner value. -/
theorem writer_clock_eq_polynomial (p : Polynomial ℕ) (n : ℕ) :
    CookLevin.Gen.horner ((coeffs p).reverse) n = p.eval n := by
  have h : (coeffs p).reverse = CookLevin.Gen.hcoeffs p := by
    simp [coeffs, CookLevin.Gen.hcoeffs, List.reverse_map]
  rw [h]
  exact CookLevin.Gen.horner_hcoeffs p n

/-- The assembled machine has a fixed finite coefficient program depending
only on p; its list length does not depend on the runtime input length. -/
theorem writer_coeffs_length (p : Polynomial ℕ) :
    (coeffs p).length = p.natDegree + 1 := by
  simp [coeffs]

/-- The *numeric radius clock* of the original finite-control assembler
has a classical polynomial upper bound for every natural input length.
This uses the already kernel-checked polynomial domination theorem.
This is NOT a statement about the MTM execution time. -/
theorem writer_clock_poly_bound (p : Polynomial ℕ) :
    ∃ c k : ℕ, 1 ≤ c ∧ 1 ≤ k ∧
      ∀ n : ℕ, CookLevin.Gen.horner ((coeffs p).reverse) n ≤
        c * (max n 1) ^ k := by
  obtain ⟨c, k, hc, hk, hb⟩ := PartIITuring.poly_le_cmax p
  exact ⟨c, k, hc, hk, fun n => by
    rw [writer_clock_eq_polynomial]
    exact hb n⟩

/-- The canonical output word has exactly the length prescribed by the
original writer's numeric Horner clock. No statement about actual
tape writes or their first-halting time is inferred. -/
theorem expected_window_length_from_writer_clock
    (p : Polynomial ℕ) (x : List Bool) :
    (TwoPhaseUniform.originalWindowCode p x).length =
      3 * CookLevin.Gen.horner ((coeffs p).reverse) x.length + 5 := by
  rw [TwoPhaseWindowWord.originalWindowCode_length_from_word,
    writer_clock_eq_polynomial]



private def windowBody : Asm ℕ := do
  let endWord ← putI .finish
  let tail ← word [true,false] endWord
  let middle ← repeated [true,true] tail
  let header ← word [true,false,false] middle
  repeated [true] header

private noncomputable def inputBody (M : MTM) : Asm ℕ := do
  let block := fun (sym : M.Γ) (head : Bool) =>
    stateBits M (sym, if head then some (.inl M.q0) else none, false)
  let endWord ← putI .finish
  let loop ← putI .finish
  let b ← word (block M.blank false) loop
  let z ← word (block (M.inp false) false) loop
  let o ← word (block (M.inp true) false) loop
  setI loop (.nextInput b z o endWord)
  let right ← putI (.copy (.mark .acc) .outer loop)
  let hb ← word (block M.blank true) right
  let hz ← word (block (M.inp false) true) right
  let ho ← word (block (M.inp true) true) right
  let center ← putI (.headInput hb hz ho)
  repeated (block M.blank false) center

private def build (program : ℕ × Array Inst) : MTM where
  Q := State program.2.size
  Γ := Sym
  blank := .blank
  inp := .raw
  inp_inj := by intro a b h; cases h; rfl
  inp_ne_blank := by intro b; exact Sym.noConfusion
  δ := step program.2 program.1
  q0 := .start
  qacc := .done
  qrej := .done

/-- The actual MTM normalization transition preserves the input bit
and turns the raw symbol into a marked work symbol. This is the exact
single-step rule needed by the prefix-normalization induction. -/
theorem normalize_raw_rule (program : ℕ × Array Inst) (b : Bool) :
    (build program).δ (.normalize) (.raw b) =
      (.normalize, .work {emptyCell with inp := some b}, .R) := by
  rfl

/-- A full *actual machine-configuration* normalization step preserves
the entire tape invariant and advances the head exactly one position.
This is the inductive successor obligation for the polynomial writer's
normalization phase. The initial sentinel state and the later Horner
and output phases remain separate proof obligations. -/
theorem normalization_cfg_step (program : ℕ × Array Inst)
    (x : List Bool) (k : ℕ) (hk : k < x.length) :
    (build program).step
      ⟨partiallyNormalizedTape x k, (k : ℤ), .normalize⟩ =
      (⟨partiallyNormalizedTape x (k + 1), ((k + 1 : ℕ) : ℤ), .normalize⟩ :
        (build program).Cfg) := by
  change
    (⟨Function.update (partiallyNormalizedTape x k) (k : ℤ)
        ((build program).δ (.normalize)
          (partiallyNormalizedTape x k (k : ℤ))).2.1,
       (k : ℤ) +
        ((build program).δ (.normalize)
          (partiallyNormalizedTape x k (k : ℤ))).2.2.shift,
       ((build program).δ (.normalize)
          (partiallyNormalizedTape x k (k : ℤ))).1⟩ :
        (build program).Cfg) = _
  rw [partially_normalized_current_input x k hk, normalize_raw_rule]
  simp only [Mv.shift, partially_normalized_extend, Nat.cast_add, Nat.cast_one]

/-- The initial input tape with the left-end marker installed is the
zero-length normalized prefix. -/
theorem initialized_sentinel_tape (program : ℕ × Array Inst)
    (x : List Bool) :
    Function.update ((build program).inputTape x) (-1 : ℤ) .leftEnd =
      partiallyNormalizedTape x 0 := by
  funext i
  by_cases hi : i = (-1 : ℤ)
  · subst i
    simp [partiallyNormalizedTape]
  · have hnot : ¬ (0 ≤ i ∧ i < (0 : ℤ)) := by omega
    rw [Function.update_of_ne hi]
    simp only [partiallyNormalizedTape, if_neg hi, if_neg hnot]
    rfl

/-- The machine's first transition moves left to install the sentinel.
The input tape remains unchanged. -/
theorem start_to_mark (program : ℕ × Array Inst) (x : List Bool) :
    (build program).step ((build program).init x) =
      (⟨(build program).inputTape x, (-1 : ℤ), .mark⟩ :
        (build program).Cfg) := by
  simp [MTM.step, MTM.init, build, step, Mv.shift, Function.update_eq_self]

/-- The second transition installs the left-end marker and returns
the head to cell zero in the normalization control state. -/
theorem mark_to_normalize (program : ℕ × Array Inst) (x : List Bool) :
    (build program).step
      (⟨(build program).inputTape x, (-1 : ℤ), .mark⟩ :
        (build program).Cfg) =
      (⟨partiallyNormalizedTape x 0, (0 : ℤ), .normalize⟩ :
        (build program).Cfg) := by
  change
    (⟨Function.update ((build program).inputTape x) (-1 : ℤ) .leftEnd,
       (-1 : ℤ) + 1, .normalize⟩ : (build program).Cfg) = _
  rw [initialized_sentinel_tape program x]
  rfl

/-- Complete inductive *prefix-normalization execution* of the actual
single-head MTM for arbitrary input length. At time k+2, with k input
cells processed, the head is at k and the complete tape is exactly
the one defined by `partiallyNormalizedTape`.

This completes only the initialization/normalization phase. The
return scans, Horner counters, and output writer remain unproved. -/
theorem run_normalizes_input (program : ℕ × Array Inst) (x : List Bool) :
    ∀ k : ℕ, k ≤ x.length →
      (build program).run ((build program).init x) (k + 2) =
        (⟨partiallyNormalizedTape x k, (k : ℤ), .normalize⟩ :
          (build program).Cfg) := by
  intro k
  induction k with
  | zero =>
      intro _
      change (build program).run ((build program).init x) (1 + 1) = _
      rw [MTM.run_succ]
      change (build program).step
        ((build program).run ((build program).init x) (0 + 1)) = _
      rw [MTM.run_succ, MTM.run_zero, start_to_mark, mark_to_normalize]
  | succ k ih =>
      intro hk
      rw [show (k + 1) + 2 = (k + 2) + 1 by omega,
        MTM.run_succ, ih (by omega)]
      exact normalization_cfg_step program x k (by omega)



noncomputable def windowMTM (p : Polynomial ℕ) : MTM :=
  build (assemble (coeffs p) windowBody)

noncomputable def inputMTM (M : MTM) (p : Polynomial ℕ) : MTM :=
  build (assemble (coeffs p) (inputBody M))

/-- The actual original polynomial *window writer* completes the
normalization phase with the exact preserved input prefix, regardless
of the polynomial's coefficients. The output phase is still open. -/
theorem windowMTM_normalization (p : Polynomial ℕ)
    (x : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    (windowMTM p).run ((windowMTM p).init x) (k + 2) =
      (⟨partiallyNormalizedTape x k, (k : ℤ), .normalize⟩ :
        (windowMTM p).Cfg) := by
  exact run_normalizes_input (assemble (coeffs p) windowBody) x k hk

/-- The actual original polynomial *input-code writer* has the identical
verified normalization prefix. This does not assume the correctness
of its later Horner-counter or serialization phases. -/
theorem inputMTM_normalization (M : MTM) (p : Polynomial ℕ)
    (x : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    (inputMTM M p).run ((inputMTM M p).init x) (k + 2) =
      (⟨partiallyNormalizedTape x k, (k : ℤ), .normalize⟩ :
        (inputMTM M p).Cfg) := by
  exact run_normalizes_input
    (assemble (coeffs p) (inputBody M)) x k hk


/-- A common polynomial bound from the sweep accounting. The remaining
low-level proof concerns these two fixed MTMs and this output convention. -/
noncomputable def timePoly (cs : List ℕ) (w : ℕ) : Polynomial ℕ :=
  let R := Polynomial.C (1+cs.sum)*(Polynomial.X+1)^cs.length
  let S := Polynomial.X + R + Polynomial.C (w+3)*(2*R+3)+8
  let Q := Polynomial.C ((cs.length+4)*(12+8*w))*(R+1)+Polynomial.C (1+cs.sum)+10
  (Q+4)*(2*S+6)

/-- Exact numeric form of the specified polynomial transition budget.
It matches the fixed-control writer's Python `step_bound` formula.
The statement verifies the budget *expression*, not that every
execution actually halts within that budget. -/
theorem timePoly_eval (cs : List ℕ) (w n : ℕ) :
    (timePoly cs w).eval n =
      let R := (1 + cs.sum) * (n + 1) ^ cs.length
      let S := n + R + (w + 3) * (2 * R + 3) + 8
      let Q := (cs.length + 4) * (12 + 8 * w) * (R + 1) + (1 + cs.sum) + 10
      (Q + 4) * (2 * S + 6) := by
  simp [timePoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]

end PVNP.TwoPhasePolynomialWriter
