import PVNP.TwoPhaseWindowWord

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

noncomputable def windowMTM (p : Polynomial ℕ) : MTM :=
  build (assemble (coeffs p) windowBody)

noncomputable def inputMTM (M : MTM) (p : Polynomial ℕ) : MTM :=
  build (assemble (coeffs p) (inputBody M))

/-- A common polynomial bound from the sweep accounting. The remaining
low-level proof concerns these two fixed MTMs and this output convention. -/
noncomputable def timePoly (cs : List ℕ) (w : ℕ) : Polynomial ℕ :=
  let R := Polynomial.C (1+cs.sum)*(Polynomial.X+1)^cs.length
  let S := Polynomial.X + R + Polynomial.C (w+3)*(2*R+3)+8
  let Q := Polynomial.C ((cs.length+4)*(12+8*w))*(R+1)+Polynomial.C (1+cs.sum)+10
  (Q+4)*(2*S+6)

end PVNP.TwoPhasePolynomialWriter
