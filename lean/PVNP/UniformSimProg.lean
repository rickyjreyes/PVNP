import PVNP.UniformSimLib

/-!
# Milestone 5, part 2: the simulating sweep program

For a uniform machine `W : UWCC` and Turing machines `ML` (lattice), `ME` (encoder) and `MD`
(decoder), we define one round-trip sweep program `prog σ`.  It is compiled to an ordinary
single-tape machine by `Prog.toTM`.

**Tracks** of a data cell:
* the input: `inp`, `fst`;
* the three folded machine tapes: `lat`, `enc`, `dec`;
* lattice flags from the lattice description `1^R 0 bitmap`: `pre`, `box`, `mem`, `rfst`;
* a ruler of `B = 2R+1` cells, `rul`;
* pointers and flags: `pp`, `gp`, `rp`, `ld`, `tgt`, `sp`, `pk`, `lab`;
* counters for nested rotations: `cnt`;
* the configuration: `cur`, `tmp`, and the window `win`.

**Phases.**
1. `init` (with the optional pair-format guard).
2. Run the lattice and encoder machines: `simL`, `simE`.
3. Parse the lattice description: `parse`.
4. Build the ruler (`rulStep`) and make room (`growA`, `growB`).
5. Load the encoded configuration onto the box: `load0`, `load`.
6. Rounds:
   * pack the canonical code onto the decoder tape: `dprep`, `pack`;
   * run the decoder: `simD`;
   * read its output: `dread`;
   * gather the windows for every offset by cyclic rotations by `±B^k`, nested over the
     ruler: `wcopy`, `rotU`, `rotI`, `rotA`, `wsave`;
   * apply the local rule: `apply`.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

/-- The data of a simulation: a uniform machine and the machines witnessing its uniformity. -/
structure Spec where
  W : UWCC
  ML : MTM
  ME : MTM
  MD : MTM
  /-- check the self-delimiting pair format of the input first -/
  guard : Bool

namespace Spec

variable (σ : Spec)

/-- Number of neighbourhood offsets. -/
abbrev K : ℕ := (2 * σ.W.r + 1) ^ σ.W.d

/-- Bound on the number of rotation tasks of one offset, plus one. -/
abbrev NT : ℕ := σ.W.d * σ.W.r + 1

/-- Neighbourhood offsets `{0, …, 2r}^d` (offset `v − r`). -/
abbrev Off : Type := Fin σ.W.d → Fin (2 * σ.W.r + 1)

/-- Enumeration of the offsets. -/
def offs (i : Fin σ.K) : σ.Off := finFunctionFinEquiv.symm i

theorem K_pos : 0 < σ.K := by positivity

/-- Rotation tasks of offset `v`: `|v_a − r|` unit tasks along axis `a`, leftwards iff `v_a > r`. -/
def tasks (v : σ.Off) : List (Fin σ.W.d × Bool) :=
  (List.finRange σ.W.d).flatMap fun a =>
    List.replicate ((v a : ℤ) - σ.W.r).natAbs (a, decide (σ.W.r < (v a : ℕ)))

theorem tasks_length_le (v : σ.Off) : (σ.tasks v).length ≤ σ.W.d * σ.W.r := by
  unfold tasks
  rw [List.length_flatMap]
  calc (List.map (fun a => (List.replicate ((v a : ℤ) - σ.W.r).natAbs
          (a, decide (σ.W.r < (v a : ℕ)))).length) (List.finRange σ.W.d)).sum
      ≤ (List.map (fun _ => σ.W.r) (List.finRange σ.W.d)).sum := by
        apply List.sum_le_sum
        intro a _
        simp only [List.length_replicate]
        have := (v a).isLt
        omega
    _ = σ.W.d * σ.W.r := by simp

def axis0 : Fin σ.W.d := ⟨0, σ.W.d_pos⟩

/-- Task `t` of offset `i`. -/
def task (i : Fin σ.K) (t : ℕ) : Fin σ.W.d × Bool := (σ.tasks (σ.offs i)).getD t (σ.axis0, false)

/-- Decode a fixed-width bit block into a state (the background if it is no code). -/
def decodeBits (bs : Fin σ.W.w → Bool) : σ.W.S :=
  if h : ∃ s, σ.W.bits s = List.ofFn bs then
    Fintype.choose (fun s => σ.W.bits s = List.ofFn bs)
      (let ⟨s, hs⟩ := h; ⟨s, hs, fun _ ht => σ.W.bits_inj (ht.trans hs.symm)⟩)
  else σ.W.sbd

theorem decodeBits_bits (s : σ.W.S) (bs : Fin σ.W.w → Bool) (h : List.ofFn bs = σ.W.bits s) :
    σ.decodeBits bs = s := by
  unfold decodeBits
  rw [dif_pos ⟨s, h.symm⟩]
  exact σ.W.bits_inj ((Fintype.choose_spec (fun s => σ.W.bits s = List.ofFn bs) _).trans h)

/-- The `k`-th bit of the code of a state. -/
def bitOf (s : σ.W.S) (k : Fin σ.W.w) : Bool :=
  (σ.W.bits s).getD k false

end Spec

/-- A data cell of the simulator. -/
structure Cell (σ : Spec) where
  inp : Option Bool
  fst : Bool
  lat : FCell σ.ML.Γ
  enc : FCell σ.ME.Γ
  dec : FCell σ.MD.Γ
  pre : Bool
  box : Bool
  mem : Bool
  rfst : Bool
  rul : Bool
  pp : Bool
  gp : Bool
  rp : Bool
  ld : Bool
  tgt : Bool
  sp : Bool
  pk : Bool
  lab : Option (Fin σ.W.w)
  cnt : Fin σ.W.d → Bool
  cur : σ.W.S
  tmp : σ.W.S
  win : σ.Off → σ.W.S
  deriving DecidableEq

namespace Cell

variable {σ : Spec}

/-- `Cell` as a product type. -/
def equiv : Cell σ ≃
    Option Bool × Bool × FCell σ.ML.Γ × FCell σ.ME.Γ × FCell σ.MD.Γ × Bool × Bool × Bool × Bool ×
      Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Option (Fin σ.W.w) ×
      (Fin σ.W.d → Bool) × σ.W.S × σ.W.S × (σ.Off → σ.W.S) where
  toFun c := (c.inp, c.fst, c.lat, c.enc, c.dec, c.pre, c.box, c.mem, c.rfst, c.rul, c.pp, c.gp,
    c.rp, c.ld, c.tgt, c.sp, c.pk, c.lab, c.cnt, c.cur, c.tmp, c.win)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Cell σ) := Fintype.ofEquiv _ equiv.symm

end Cell

/-- Buffer of the simulator's transducers. -/
structure Buf (σ : Spec) where
  sL : SimBuf σ.ML.Q
  sE : SimBuf σ.ME.Q
  sD : SimBuf σ.MD.Q
  g : PS
  ph : Fin 3
  f1 : Bool
  f2 : Bool
  f3 : Bool
  cS : Option σ.W.S
  rc : Fin (σ.W.w + 1)
  bits : Fin σ.W.w → Bool
  dout : Option σ.MD.Γ
  deriving DecidableEq

namespace Buf

variable {σ : Spec}

/-- `Buf` as a product type. -/
def equiv : Buf σ ≃
    SimBuf σ.ML.Q × SimBuf σ.ME.Q × SimBuf σ.MD.Q × PS × Fin 3 × Bool × Bool × Bool ×
      Option σ.W.S × Fin (σ.W.w + 1) × (Fin σ.W.w → Bool) × Option σ.MD.Γ where
  toFun b := (b.sL, b.sE, b.sD, b.g, b.ph, b.f1, b.f2, b.f3, b.cS, b.rc, b.bits, b.dout)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Buf σ) := Fintype.ofEquiv _ equiv.symm

end Buf

/-- Instructions of the simulator. -/
inductive Ins (σ : Spec) where
  | init
  | simL (q : σ.ML.Q)
  | simE (q : σ.ME.Q)
  | parse
  | rulStep
  | growA
  | growB (k : Fin (σ.W.w + 2))
  | load0
  | load
  | dprep
  | pack
  | simD (q : σ.MD.Q)
  | dread
  | wcopy (i : Fin σ.K)
  | rotU (i : Fin σ.K) (t : Fin σ.NT)
  | rotI (i : Fin σ.K) (t : Fin σ.NT) (k : Fin σ.W.d)
  | rotA (i : Fin σ.K) (t : Fin σ.NT) (k : Fin σ.W.d)
  | wsave (i : Fin σ.K)
  | apply
  deriving DecidableEq, Fintype

namespace Spec

variable (σ : Spec)

/-! ### Default cell and buffer, lenses -/

/-- A fresh cell. -/
def dflt : Cell σ where
  inp := none
  fst := false
  lat := ⟨σ.ML.blank, σ.ML.blank, none, none⟩
  enc := ⟨σ.ME.blank, σ.ME.blank, none, none⟩
  dec := ⟨σ.MD.blank, σ.MD.blank, none, none⟩
  pre := false
  box := false
  mem := false
  rfst := false
  rul := false
  pp := false
  gp := false
  rp := false
  ld := false
  tgt := false
  sp := false
  pk := false
  lab := none
  cnt := fun _ => false
  cur := σ.W.sbd
  tmp := σ.W.sbd
  win := fun _ => σ.W.sbd

/-- The initial buffer of every instruction. -/
def buf0 : Buf σ where
  sL := SimBuf.start _
  sE := SimBuf.start _
  sD := SimBuf.start _
  g := .tag
  ph := 0
  f1 := false
  f2 := false
  f3 := false
  cS := none
  rc := 0
  bits := fun _ => false
  dout := none

def latL : Lens (Cell σ) (FCell σ.ML.Γ) :=
  ⟨Cell.lat, fun t c => {c with lat := t}, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
def encL : Lens (Cell σ) (FCell σ.ME.Γ) :=
  ⟨Cell.enc, fun t c => {c with enc := t}, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
def decL : Lens (Cell σ) (FCell σ.MD.Γ) :=
  ⟨Cell.dec, fun t c => {c with dec := t}, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
def sLL : Lens (Buf σ) (SimBuf σ.ML.Q) :=
  ⟨Buf.sL, fun t b => {b with sL := t}, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
def sEL : Lens (Buf σ) (SimBuf σ.ME.Q) :=
  ⟨Buf.sE, fun t b => {b with sE := t}, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
def sDL : Lens (Buf σ) (SimBuf σ.MD.Q) :=
  ⟨Buf.sD, fun t b => {b with sD := t}, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-! ### Control flow -/

def haltingQ (M : MTM) (q : M.Q) : Bool := decide (q = M.qacc ∨ q = M.qrej)

/-- After the encoder: parse the lattice description. -/
def encEntry : Ins σ := if haltingQ σ.ME σ.ME.q0 then .parse else .simE σ.ME.q0

/-- After the lattice machine: run the encoder. -/
def latExit : Ins σ := σ.encEntry

/-- Start of the lattice machine. -/
def latEntry : Ins σ := if haltingQ σ.ML σ.ML.q0 then σ.latExit else .simL σ.ML.q0

/-- Start of the decoder. -/
def decEntry : Ins σ := if haltingQ σ.MD σ.MD.q0 then .dread else .simD σ.MD.q0

/-- Start a rotation by `B^k` in context `(i, t)`. -/
def startRot (i : Fin σ.K) (t : Fin σ.NT) (k : Fin σ.W.d) : Ins σ :=
  if k.val = 0 then .rotU i t else .rotI i t k

/-- Enter task `t` of offset `i`. -/
def taskEntry (i : Fin σ.K) (t : ℕ) : Ins σ :=
  if h : t < (σ.tasks (σ.offs i)).length then
    σ.startRot i ⟨t, by have := σ.tasks_length_le (σ.offs i); show t < σ.W.d * σ.W.r + 1; omega⟩
      (σ.task i t).1
  else .wsave i

/-- Return from a rotation of level `k` in context `(i, t)`. -/
def retRot (i : Fin σ.K) (t : Fin σ.NT) (k : Fin σ.W.d) : Ins σ :=
  if k = (σ.task i t).1 then σ.taskEntry i (t.val + 1)
  else if h : k.val + 1 < σ.W.d then .rotA i t ⟨k.val + 1, h⟩ else σ.taskEntry i (t.val + 1)

/-! ### Transducers -/

/-- The input symbol of a machine for an optional input bit. -/
def inSym (M : MTM) : Option Bool → M.Γ
  | some b => M.inp b
  | none => M.blank

/-- Bit read from a tape symbol. -/
def symBit (M : MTM) (g : M.Γ) : Bool := decide (g = M.inp true)

/-- Guard automaton step on an optional input bit. -/
def gStep (g : PS) : Option Bool → PS
  | some x => g.next x
  | none => g

/-- Decoder-input symbol written by `dprep`. -/
def dprepSym (ph : Fin 3) : Option Bool → σ.MD.Γ
  | some _ => σ.MD.inp true
  | none => if ph = 0 then σ.MD.inp false else σ.MD.blank

/-- Phase update of `dprep`. -/
def dprepPh (ph : Fin 3) : Option Bool → Fin 3
  | some _ => ph
  | none => if ph = 0 then 1 else 2

/-- One step of a slot walk over `w` cells starting at the pointer cell: the new phase, counter
and pointer flag, and the label of this cell. -/
def walk (w : ℕ) (ph : Fin 3) (rc : Fin (w + 1)) (ptr : Bool) :
    Fin 3 × Fin (w + 1) × Bool × Option (Fin w) :=
  match ph with
  | 0 =>
    if ptr then
      if h : 0 < w then (1, ⟨1, by omega⟩, false, some ⟨0, h⟩) else (2, rc, ptr, none)
    else (0, rc, ptr, none)
  | 1 => if h : rc.val < w then (1, ⟨rc.val + 1, by omega⟩, ptr, some ⟨rc.val, h⟩)
    else (2, rc, true, none)
  | _ => (2, rc, ptr, none)

/-- Record the bit of a labelled cell. -/
def readBit {w : ℕ} : Option (Fin w) → (Fin w → Bool) → Bool → (Fin w → Bool)
  | some k, bs, v => Function.update bs k v
  | none, bs, _ => bs

/-- Load: mark the first member not yet loaded. -/
def ldMark (b : Buf σ) (a : Cell σ) : Cell σ × Buf σ :=
  if a.box && a.mem && !a.ld && !b.f1 then ({a with tgt := true}, {b with f1 := true}) else (a, b)

/-- Pack: mark the first member not yet packed and capture its state. -/
def pkMark (b : Buf σ) (a : Cell σ) : Cell σ × Buf σ :=
  if a.box && a.mem && !a.pk && !b.f1 then
    ({a with pk := true}, {b with f1 := true, cS := some a.cur})
  else (a, b)

/-- Forward transducers. -/
def fwd : Ins σ → Buf σ → Cell σ → Cell σ × Buf σ
  | .init, b, a =>
    ({a with
        fst := !b.f1
        lat := ⟨inSym σ.ML a.inp, σ.ML.blank, if b.f1 then none else some true, none⟩
        enc := ⟨inSym σ.ME a.inp, σ.ME.blank, if b.f1 then none else some true, none⟩},
      {b with f1 := true, g := gStep b.g a.inp})
  | .simL q, b, a => gF σ.ML σ.latL σ.sLL q b a
  | .simE q, b, a => gF σ.ME σ.encL σ.sEL q b a
  | .parse, b, a =>
    match b.ph with
    | 0 =>
      if a.lat.r = σ.ML.inp true then
        ({a with
            pre := true, box := false, mem := false, rfst := false, rul := false
            pp := !b.f1, gp := false}, {b with f1 := true})
      else
        ({a with
            pre := false, box := false, mem := false, rfst := false, rul := false
            pp := false, gp := false}, {b with ph := 1, f1 := true})
    | 1 =>
      if a.lat.r = σ.ML.blank then
        ({a with
            pre := false, box := false, mem := false, rfst := false, rul := false
            pp := false, gp := false}, {b with ph := 2})
      else
        ({a with
            pre := false, box := true, mem := symBit σ.ML a.lat.r, rfst := !b.f2
            rul := !b.f2, pp := false, gp := !b.f2}, {b with f2 := true})
    | _ =>
      ({a with
          pre := false, box := false, mem := false, rfst := false, rul := false
          pp := false, gp := false}, b)
  | .rulStep, b, a =>
    -- move `pp` right (carry in `f1`), record in `f2` whether it was on a prefix cell, and
    -- (if so) mark the two cells following the ruler (state in `ph`, `f3` = previous was ruler)
    ({a with
        pp := b.f1
        rul := a.rul || (b.f2 || (a.pp && a.pre)) &&
          ((b.ph = 0 && b.f3 && !a.rul) || b.ph = 1)},
      {b with
        f1 := a.pp
        f2 := b.f2 || (a.pp && a.pre)
        f3 := a.rul
        ph := if (b.f2 || (a.pp && a.pre)) && b.ph = 0 && b.f3 && !a.rul then 1
          else if b.ph = 1 then 2 else b.ph})
  | .growA, b, a => ({a with gp := b.f1}, {b with f1 := a.gp, f2 := b.f2 || (a.gp && a.box)})
  | .growB _, b, a => (a, b)
  | .load0, b, a => ({a with cur := σ.W.sbd, ld := false, tgt := false, rp := a.fst}, b)
  | .load, b, a =>
    ({(σ.ldMark b a).1 with
        rp := (walk σ.W.w (σ.ldMark b a).2.ph (σ.ldMark b a).2.rc (σ.ldMark b a).1.rp).2.2.1},
      {(σ.ldMark b a).2 with
        ph := (walk σ.W.w (σ.ldMark b a).2.ph (σ.ldMark b a).2.rc (σ.ldMark b a).1.rp).1
        rc := (walk σ.W.w (σ.ldMark b a).2.ph (σ.ldMark b a).2.rc (σ.ldMark b a).1.rp).2.1
        bits := readBit (walk σ.W.w (σ.ldMark b a).2.ph (σ.ldMark b a).2.rc
          (σ.ldMark b a).1.rp).2.2.2 (σ.ldMark b a).2.bits (symBit σ.ME a.enc.r)})
  | .dprep, b, a =>
    ({a with
        dec := ⟨σ.dprepSym b.ph a.inp, σ.MD.blank, if a.fst then some true else none, none⟩
        sp := b.ph = 1 && a.inp.isNone
        pk := false
        lab := none},
      {b with ph := dprepPh b.ph a.inp})
  | .pack, b, a =>
    ({(σ.pkMark b a).1 with
        sp := (walk σ.W.w (σ.pkMark b a).2.ph (σ.pkMark b a).2.rc (σ.pkMark b a).1.sp).2.2.1
        lab := (walk σ.W.w (σ.pkMark b a).2.ph (σ.pkMark b a).2.rc (σ.pkMark b a).1.sp).2.2.2},
      {(σ.pkMark b a).2 with
        ph := (walk σ.W.w (σ.pkMark b a).2.ph (σ.pkMark b a).2.rc (σ.pkMark b a).1.sp).1
        rc := (walk σ.W.w (σ.pkMark b a).2.ph (σ.pkMark b a).2.rc (σ.pkMark b a).1.sp).2.1})
  | .simD q, b, a => gF σ.MD σ.decL σ.sDL q b a
  | .dread, b, a => (a, if a.fst then {b with dout := some a.dec.r} else b)
  | .wcopy _, b, a => ({a with tmp := a.cur}, b)
  | .rotU i t, b, a =>
    if (σ.task i t).2 then
      -- left: capture the first value
      (a, if a.fst then {b with cS := some a.tmp} else b)
    else
      -- right: shift right by one, carrying the previous value
      ({a with tmp := b.cS.getD a.tmp}, {b with cS := some a.tmp})
  | .rotI _ _ k, b, a => ({a with cnt := Function.update a.cnt k a.rfst}, b)
  | .rotA _ _ k, b, a =>
    ({a with cnt := Function.update a.cnt k b.f1},
      {b with f1 := a.cnt k, f2 := b.f2 || (b.f1 && a.rul)})
  | .wsave i, b, a => ({a with win := Function.update a.win (σ.offs i) a.tmp}, b)
  | .apply, b, a =>
    ({a with cur := if a.box then (if a.mem then σ.W.U a.win else σ.W.sbd) else a.cur}, b)

/-- Right-end extensions. -/
def ext : Ins σ → Buf σ → Option (Cell σ)
  | .init, b =>
    if b.f1 then none
    else some {σ.dflt with
      fst := true
      lat := ⟨σ.ML.blank, σ.ML.blank, some true, none⟩
      enc := ⟨σ.ME.blank, σ.ME.blank, some true, none⟩}
  | .simL _, b => gE σ.ML σ.latL σ.sLL σ.dflt b
  | .simE _, b => gE σ.ME σ.encL σ.sEL σ.dflt b
  | .simD _, b => gE σ.MD σ.decL σ.sDL σ.dflt b
  | .growB _, _ => some σ.dflt
  | _, _ => none

/-- Backward transducers. -/
def bwd : Ins σ → Buf σ → Cell σ → Cell σ × Buf σ
  | .simL _, b, a => gB σ.ML σ.latL σ.sLL b a
  | .simE _, b, a => gB σ.ME σ.encL σ.sEL b a
  | .simD _, b, a => gB σ.MD σ.decL σ.sDL b a
  | .load, b, a =>
    if a.tgt then ({a with cur := σ.decodeBits b.bits, ld := true, tgt := false}, b) else (a, b)
  | .pack, b, a =>
    match a.lab, b.cS with
    | some k, some s =>
      ({a with dec := ⟨σ.MD.inp (σ.bitOf s k), a.dec.l, a.dec.hd, a.dec.pl⟩, lab := none}, b)
    | some _, none => ({a with lab := none}, b)
    | none, _ => (a, b)
  | .rotU i t, b, a =>
    if (σ.task i t).2 then
      ({a with tmp := b.cS.getD a.tmp}, {b with cS := some a.tmp})
    else
      (if a.fst then {a with tmp := b.cS.getD a.tmp} else a, b)
  | _, b, a => (a, b)

/-- Control flow. -/
def next : Ins σ → Buf σ → Ins σ ⊕ Bool
  | .init, b => if σ.guard && b.g != .ok then .inr false else .inl σ.latEntry
  | .simL _, b =>
    match b.sL.nq with
    | some q => if haltingQ σ.ML q then .inl σ.latExit else .inl (.simL q)
    | none => .inl σ.latExit
  | .simE _, b =>
    match b.sE.nq with
    | some q => if haltingQ σ.ME q then .inl .parse else .inl (.simE q)
    | none => .inl .parse
  | .parse, _ => .inl .rulStep
  | .rulStep, b => if b.f2 then .inl .rulStep else .inl .growA
  | .growA, b => if b.f2 then .inl (.growB 0) else .inl .load0
  | .growB k, _ =>
    if h : k.val + 1 < σ.W.w + 2 then .inl (.growB ⟨k.val + 1, h⟩) else .inl .growA
  | .load0, _ => .inl .load
  | .load, b => if b.f1 then .inl .load else .inl .dprep
  | .dprep, _ => .inl .pack
  | .pack, b => if b.f1 then .inl .pack else .inl σ.decEntry
  | .simD _, b =>
    match b.sD.nq with
    | some q => if haltingQ σ.MD q then .inl .dread else .inl (.simD q)
    | none => .inl .dread
  | .dread, b =>
    match b.dout with
    | some g =>
      if g = σ.MD.inp true then .inr true
      else if g = σ.MD.inp false then .inr false else .inl (.wcopy ⟨0, σ.K_pos⟩)
    | none => .inl (.wcopy ⟨0, σ.K_pos⟩)
  | .wcopy i, _ => .inl (σ.taskEntry i 0)
  | .rotU i t, _ => .inl (σ.retRot i t ⟨0, σ.W.d_pos⟩)
  | .rotI i t k, _ =>
    .inl (σ.startRot i t ⟨k.val - 1, by omega⟩)
  | .rotA i t k, b =>
    if b.f2 then .inl (σ.startRot i t ⟨k.val - 1, by omega⟩) else .inl (σ.retRot i t k)
  | .wsave i, _ =>
    if h : i.val + 1 < σ.K then .inl (.wcopy ⟨i.val + 1, h⟩) else .inl .apply
  | .apply, _ => .inl .dprep

/-- The lift of an input bit. -/
def lift (x : Bool) : Cell σ := {σ.dflt with inp := some x}

/-- **The simulating sweep program.** -/
abbrev prog : Prog where
  D := Cell σ
  I := Ins σ
  B := Buf σ
  lift := σ.lift
  start := .init
  init := fun _ => σ.buf0
  fwd := σ.fwd
  ext := σ.ext
  bwd := σ.bwd
  next := σ.next

end Spec

end PVNP.UniformSim
