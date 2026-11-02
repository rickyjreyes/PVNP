import PVNP.DiscreteMachines

/-!
# Flat binary serialization of arbitrary finite Turing machines (issue #11 B)

This module upgrades the bit-grid encodings of `MachineCode` /
`MachineTableDecoder` to a genuine **flat** `List Bool` serialization with a
strict prefix parser.

* `Codec α`: an encoder `α → List Bool` together with a prefix decoder
  `List Bool → Option (α × List Bool)` satisfying the two laws
  `dec_enc` (round trip, for every continuation) and `enc_dec` (soundness:
  every accepted parse is literally a canonical encoding followed by the
  remainder).  Malformed or noncanonical input is therefore always rejected.
* Combinators: `bool`, `unary`, `fin`, `dir`, `prod`, `sigma`, `option`, `vec`,
  `map`, `filter`, all proved to satisfy both laws, with length bounds.
* `Table`: a finite TM transition table over `Fin k` states and `Fin m`
  symbols, serialized as `1^k 0 1^m 0 · data`.
* `encodeTable_decodeTable`, `decodeTable_sound`, `encodeTable_injective`,
  `encodeTable_length_le`: round trip, rejection of malformed descriptions,
  injectivity, and the polynomial size bound
  `|code| ≤ 4 + 6k + 4m + k·m·(k + m + 4)`.
* `TM.normalize_decides`: **every** `TM` (with arbitrary finite types `Λ`, `Γ`)
  decides exactly the same languages in exactly the same time as the
  serializable table machine `ofTable (M.toTable)`.

Scope note: the decoder is a total Lean function (structurally recursive,
one pass).  A universal TM that *executes* serialized descriptions, and a
formal TM-step bound for parsing, are **not** constructed here; they are not
needed for `P_WCC = P_TM` because the classes quantify over machines directly.
-/

namespace PVNP.Discrete

/-- A prefix code with verified round-trip and soundness laws. -/
structure Codec (α : Type) where
  enc : α → List Bool
  dec : List Bool → Option (α × List Bool)
  dec_enc : ∀ a rest, dec (enc a ++ rest) = some (a, rest)
  enc_dec : ∀ s a rest, dec s = some (a, rest) → s = enc a ++ rest

namespace Codec

variable {α β : Type}

/-- Whole-string decoding: the parse must consume the entire input. -/
def decodeAll (c : Codec α) (s : List Bool) : Option α :=
  match c.dec s with
  | some (a, []) => some a
  | _ => none

theorem decodeAll_enc (c : Codec α) (a : α) : c.decodeAll (c.enc a) = some a := by
  have := c.dec_enc a []
  simp only [List.append_nil] at this
  simp [decodeAll, this]

theorem decodeAll_sound (c : Codec α) {s : List Bool} {a : α}
    (h : c.decodeAll s = some a) : c.enc a = s := by
  unfold decodeAll at h
  split at h
  · rename_i a' heq
    cases h
    have := c.enc_dec _ _ _ heq
    simpa using this.symm
  · cases h

theorem enc_injective (c : Codec α) : Function.Injective c.enc := by
  intro a b h
  have h1 := c.decodeAll_enc a
  rw [h, c.decodeAll_enc b] at h1
  exact (Option.some.inj h1).symm

/-- Bounded encodings. -/
def Bounded (c : Codec α) (B : ℕ) : Prop := ∀ a, (c.enc a).length ≤ B

/-! ### Basic codecs -/

def unit : Codec Unit where
  enc _ := []
  dec s := some ((), s)
  dec_enc _ _ := rfl
  enc_dec s a rest h := by cases h; rfl

def bool : Codec Bool where
  enc b := [b]
  dec
    | [] => none
    | b :: r => some (b, r)
  dec_enc _ _ := rfl
  enc_dec s a rest h := by
    cases s with
    | nil => cases h
    | cons b r => cases h; rfl

/-- Unary prefix decoder for natural numbers. -/
def unaryDec : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: r => some (0, r)
  | true :: r => (unaryDec r).map fun p => (p.1 + 1, p.2)

def unaryEnc (n : ℕ) : List Bool := List.replicate n true ++ [false]

theorem unaryDec_enc (n : ℕ) (rest : List Bool) :
    unaryDec (unaryEnc n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unaryEnc, List.replicate_succ, List.cons_append, List.append_assoc,
      List.nil_append] at ih ⊢
    simp [unaryDec, ih]

theorem unaryDec_sound : ∀ (s : List Bool) (n : ℕ) (rest : List Bool),
    unaryDec s = some (n, rest) → s = unaryEnc n ++ rest
  | [], _, _, h => by cases h
  | false :: r, n, rest, h => by
    simp only [unaryDec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | true :: r, n, rest, h => by
    simp only [unaryDec, Option.map_eq_some_iff] at h
    obtain ⟨⟨n', r'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [unaryDec_sound r n' r' h1]
    simp [unaryEnc, List.replicate_succ]

def unary : Codec ℕ where
  enc := unaryEnc
  dec := unaryDec
  dec_enc := unaryDec_enc
  enc_dec := unaryDec_sound

theorem unary_length (n : ℕ) : (unary.enc n).length = n + 1 := by
  simp [unary, unaryEnc]

/-! ### Combinators -/

def map (c : Codec α) (e : α ≃ β) : Codec β where
  enc b := c.enc (e.symm b)
  dec s := (c.dec s).map fun p => (e p.1, p.2)
  dec_enc b rest := by simp [c.dec_enc]
  enc_dec s b rest h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨a, r⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simpa using c.enc_dec _ _ _ h1

def filter (c : Codec α) (P : α → Prop) [DecidablePred P] : Codec {a // P a} where
  enc a := c.enc a.1
  dec s :=
    match c.dec s with
    | some (a, r) => if h : P a then some (⟨a, h⟩, r) else none
    | none => none
  dec_enc a rest := by simp [c.dec_enc, a.2]
  enc_dec s a rest h := by
    split at h
    · rename_i a' r heq
      split_ifs at h with hp
      cases h
      exact c.enc_dec _ _ _ heq
    · cases h

def prod (ca : Codec α) (cb : Codec β) : Codec (α × β) where
  enc p := ca.enc p.1 ++ cb.enc p.2
  dec s := (ca.dec s).bind fun p => (cb.dec p.2).map fun q => ((p.1, q.1), q.2)
  dec_enc p rest := by simp [List.append_assoc, ca.dec_enc, cb.dec_enc]
  enc_dec s p rest h := by
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, r⟩, h1, ⟨b, r'⟩, h2, h3⟩ := h
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    simp only at h2 ⊢
    rw [ca.enc_dec _ _ _ h1, cb.enc_dec _ _ _ h2, List.append_assoc]

def sigma {β : α → Type} (ca : Codec α) (cb : (a : α) → Codec (β a)) :
    Codec (Σ a, β a) where
  enc p := ca.enc p.1 ++ (cb p.1).enc p.2
  dec s := (ca.dec s).bind fun p => ((cb p.1).dec p.2).map fun q => (⟨p.1, q.1⟩, q.2)
  dec_enc p rest := by simp [List.append_assoc, ca.dec_enc, (cb p.1).dec_enc]
  enc_dec s p rest h := by
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, r⟩, h1, ⟨b, r'⟩, h2, h3⟩ := h
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    simp only at h2 b ⊢
    rw [ca.enc_dec _ _ _ h1, (cb a).enc_dec _ _ _ h2, List.append_assoc]

def option (c : Codec α) : Codec (Option α) where
  enc
    | none => [false]
    | some a => true :: c.enc a
  dec
    | [] => none
    | false :: r => some (none, r)
    | true :: r => (c.dec r).map fun p => (some p.1, p.2)
  dec_enc a rest := by cases a <;> simp [c.dec_enc]
  enc_dec s a rest h := by
    match s, h with
    | false :: r, h =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
    | true :: r, h =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨a', r'⟩, h1, h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp [c.enc_dec _ _ _ h1]

/-- Equivalence `(Fin 0 → α) ≃ Unit`. -/
def fin0Equiv (α : Type) : (Fin 0 → α) ≃ Unit where
  toFun _ := ()
  invFun _ := Fin.elim0
  left_inv f := funext fun i => i.elim0
  right_inv _ := rfl

/-- Fixed-length sequences. -/
def vec (c : Codec α) : (n : ℕ) → Codec (Fin n → α)
  | 0 => unit.map (fin0Equiv α).symm
  | n + 1 => (prod c (vec c n)).map (Fin.consEquiv fun _ => α)

/-- `Fin n`, written in unary and range-checked. -/
def fin (n : ℕ) : Codec (Fin n) := (unary.filter (· < n)).map (Fin.equivSubtype).symm

/-- Equivalence between head movements and `Fin 3`. -/
def dirEquiv : Dir ≃ Fin 3 where
  toFun | .L => 0 | .S => 1 | .R => 2
  invFun i := if i = 0 then .L else if i = 1 then .S else .R
  left_inv d := by cases d <;> rfl
  right_inv i := by fin_cases i <;> rfl

def dir : Codec Dir := (fin 3).map dirEquiv.symm

/-! ### Length bounds -/

theorem map_bounded {c : Codec α} {B : ℕ} (h : c.Bounded B) (e : α ≃ β) :
    (c.map e).Bounded B := fun b => h _

theorem filter_bounded {c : Codec α} {B : ℕ} (h : c.Bounded B) (P : α → Prop)
    [DecidablePred P] : (c.filter P).Bounded B := fun a => h _

theorem prod_bounded {ca : Codec α} {cb : Codec β} {A B : ℕ} (ha : ca.Bounded A)
    (hb : cb.Bounded B) : (prod ca cb).Bounded (A + B) := fun p => by
  simp only [prod, List.length_append]; exact Nat.add_le_add (ha _) (hb _)

theorem option_bounded {c : Codec α} {B : ℕ} (h : c.Bounded B) :
    (option c).Bounded (B + 1) := fun a => by
  cases a with
  | none => simp [option]
  | some a => simp only [option, List.length_cons]; exact Nat.succ_le_succ (h a)

theorem vec_bounded {c : Codec α} {B : ℕ} (h : c.Bounded B) :
    ∀ n, (vec c n).Bounded (n * B)
  | 0 => fun _ => by simp [vec, map, unit]
  | n + 1 => by
    have := map_bounded (prod_bounded h (vec_bounded h n)) (Fin.consEquiv fun _ => α)
    intro f; have := this f; simp only [vec] at *; nlinarith

theorem fin_bounded (n : ℕ) : (fin n).Bounded n := fun i => by
  simp only [fin, map, filter, Equiv.symm_symm]
  have := unary_length (Fin.equivSubtype i).1
  simp only [Fin.equivSubtype_apply] at this
  have hi := i.2
  simp [unary] at this ⊢; omega

theorem bool_bounded : bool.Bounded 1 := fun _ => le_refl _

theorem dir_bounded : dir.Bounded 3 := map_bounded (fin_bounded 3) _

end Codec

/-! ## Finite transition tables -/

/-- Payload of a table machine with `k` states and `m` symbols:
blank, input symbols for `false`/`true`, start state, transition table,
accept and reject flags. -/
abbrev TableData (k m : ℕ) : Type :=
  Fin m × Fin m × Fin m × Fin k × (Fin k → Fin m → Option (Fin k × Fin m × Dir)) ×
    (Fin k → Bool) × (Fin k → Bool)

/-- A finite Turing machine table with explicit sizes. -/
abbrev Table : Type := Σ k : ℕ, Σ m : ℕ, TableData k m

open Codec in
/-- Codec for the payload. -/
def dataCodec (k m : ℕ) : Codec (TableData k m) :=
  prod (fin m) <| prod (fin m) <| prod (fin m) <| prod (fin k) <|
    prod (vec (vec (option (prod (fin k) (prod (fin m) dir))) m) k) <|
    prod (vec bool k) (vec bool k)

open Codec in
/-- Codec for a whole table: `1^k 0 1^m 0` followed by the payload. -/
def tableCodec : Codec Table := sigma unary fun k => sigma unary fun m => dataCodec k m

/-- Serialization of a finite machine table. -/
def encodeTable (t : Table) : List Bool := tableCodec.enc t

/-- Strict parser: returns a table only on a complete canonical encoding. -/
def decodeTable (s : List Bool) : Option Table := tableCodec.decodeAll s

theorem encodeTable_decodeTable (t : Table) : decodeTable (encodeTable t) = some t :=
  tableCodec.decodeAll_enc t

/-- Every accepted bit string is the canonical encoding of what it decodes to;
in particular malformed or noncanonical strings are rejected. -/
theorem decodeTable_sound {s : List Bool} {t : Table} (h : decodeTable s = some t) :
    encodeTable t = s :=
  tableCodec.decodeAll_sound h

theorem decodeTable_rejects {s : List Bool} (h : ∀ t, encodeTable t ≠ s) :
    decodeTable s = none := by
  cases hd : decodeTable s with
  | none => rfl
  | some t => exact absurd (decodeTable_sound hd) (h t)

theorem encodeTable_injective : Function.Injective encodeTable :=
  tableCodec.enc_injective

theorem dataCodec_bounded (k m : ℕ) :
    (dataCodec k m).Bounded (m + (m + (m + (k + (k * (m * (k + (m + 3) + 1)) + (k + k)))))) := by
  open Codec in
  exact prod_bounded (fin_bounded m) <| prod_bounded (fin_bounded m) <|
    prod_bounded (fin_bounded m) <| prod_bounded (fin_bounded k) <|
    prod_bounded (by
      have := vec_bounded (vec_bounded (option_bounded
        (prod_bounded (fin_bounded k) (prod_bounded (fin_bounded m) dir_bounded))) m) k
      simpa [Nat.mul_one] using this) <|
    prod_bounded (by simpa using vec_bounded bool_bounded k)
      (by simpa using vec_bounded bool_bounded k)

/-- **Polynomial description size.** -/
theorem encodeTable_length_le (t : Table) :
    (encodeTable t).length ≤ 4 + 6 * t.1 + 4 * t.2.1 + t.1 * t.2.1 * (t.1 + t.2.1 + 4) := by
  obtain ⟨k, m, d⟩ := t
  have h := dataCodec_bounded k m d
  simp only [encodeTable, tableCodec, Codec.sigma, List.length_append, Codec.unary_length]
  have : k * (m * (k + (m + 3) + 1)) = k * m * (k + m + 4) := by ring
  omega

/-! ## Table machines and normalization -/

/-- The ordinary TM described by a table. -/
def TM.ofTable (t : Table) : TM where
  Λ := Fin t.1
  Γ := Fin t.2.1
  blank := t.2.2.1
  inp b := if b then t.2.2.2.2.1 else t.2.2.2.1
  start := t.2.2.2.2.2.1
  δ := t.2.2.2.2.2.2.1
  acc := t.2.2.2.2.2.2.2.1
  rej := t.2.2.2.2.2.2.2.2

namespace TM

variable (M : TM)

/-- Relabel a machine's states and symbols by `Fin` via `Fintype.equivFin`. -/
noncomputable def toTable : Table :=
  let e := Fintype.equivFin M.Λ
  let f := Fintype.equivFin M.Γ
  ⟨Fintype.card M.Λ, Fintype.card M.Γ,
    f M.blank, f (M.inp false), f (M.inp true), e M.start,
    (fun q a => (M.δ (e.symm q) (f.symm a)).map fun t => (e t.1, f t.2.1, t.2.2)),
    (fun q => M.acc (e.symm q)), (fun q => M.rej (e.symm q))⟩

/-- Relabelled configuration. -/
noncomputable def relabel (c : M.Cfg) : (ofTable M.toTable).Cfg :=
  ⟨Fintype.equivFin M.Λ c.q, (Fintype.equivFin M.Γ) ∘ c.tape, c.head⟩

theorem relabel_next (c : M.Cfg) :
    (ofTable M.toTable).next (M.relabel c) = M.relabel (M.next c) := by
  simp only [next, step, relabel]
  rcases hδ : M.δ c.q (c.tape c.head) with _ | ⟨q', a, d⟩
  · simp [ofTable, toTable, hδ]
  · simp only [Option.map_some, Option.getD_some]
    have : (ofTable M.toTable).δ (Fintype.equivFin M.Λ c.q)
        (((Fintype.equivFin M.Γ) ∘ c.tape) c.head) =
        some (Fintype.equivFin M.Λ q', Fintype.equivFin M.Γ a, d) := by
      simp [ofTable, toTable, hδ]
    rw [this]
    simp [Function.comp_update]

theorem relabel_run (c : M.Cfg) (t : ℕ) :
    (ofTable M.toTable).run (M.relabel c) t = M.relabel (M.run c t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, relabel_next, run_succ]

theorem relabel_init (x : List Bool) :
    (ofTable M.toTable).init x = M.relabel (M.init x) := by
  simp only [init, relabel]
  congr 1
  funext i
  simp only [inputTape, Function.comp]
  split_ifs
  · cases x.getD i.toNat false <;> simp [ofTable, toTable]
  · simp [ofTable, toTable]

theorem relabel_ans (c : M.Cfg) : (ofTable M.toTable).ans (M.relabel c) = M.ans c := by
  simp [ans, relabel, ofTable, toTable]

/-- **Normalization.** Every ordinary TM has a serializable table machine
with identical output stream on every input. -/
theorem normalize_out (x : List Bool) : (ofTable M.toTable).out x = M.out x := by
  funext s
  simp [out, relabel_init, relabel_run, relabel_ans]

theorem normalize_decides (L : Set (List Bool)) (T : ℕ → ℕ) :
    (ofTable M.toTable).Decides L T ↔ M.Decides L T := by
  simp only [Decides, normalize_out]

end TM

/-- `P_TM` is exactly the class of languages decided in polynomial time by a
machine with a flat binary description. -/
theorem P_TM_eq_tables :
    P_TM = {L | ∃ (t : Table) (p : Polynomial ℕ), (TM.ofTable t).Decides L (fun n => p.eval n)} := by
  ext L
  constructor
  · rintro ⟨M, p, h⟩
    exact ⟨M.toTable, p, (M.normalize_decides L _).2 h⟩
  · rintro ⟨t, p, h⟩
    exact ⟨TM.ofTable t, p, h⟩

end PVNP.Discrete
