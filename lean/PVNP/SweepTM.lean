import PVNP.TMScan

/-!
# D-1 tape compiler: round-trip sweep programs → ordinary single-tape TMs

A *sweep program* is a finite-control program whose only tape operation is a
**round trip** over the used tape segment: a left-to-right Mealy transduction
of every data cell, an optional one-cell extension at the right end, and a
right-to-left Mealy transduction back to a left end-marker.  The next
instruction (or a final answer) is chosen from the finite buffer left by the
backward pass.  Each transduction uses a *finite* buffer, so the program has
no unbounded registers, no random access and no uncharged lookups.

`Prog.toTM` compiles a sweep program to an ordinary `PVNP.Discrete.TM`
(finite control `St I B`, finite tape alphabet `Sym D`, one head).  The
compiled machine charges every head move:

* `trip_run_pre`, `trip_run`: one round trip on a data segment of length `ℓ`
  costs exactly `2ℓ + 2 + e` transitions (`e ∈ {0,1}` the extension).
* `reach_run`, `halts_run`: whole program runs, by induction.
* `toTM_firstAnswer`: if the program halts with answer `a` after total cost
  `C`, the TM's first answer is `a`, given at exactly time `C + 2`
  (two initialization transitions place the left end-marker).

No property of any particular program is assumed here.
-/

namespace PVNP.Discrete.Sweep

/-- Tape symbols of a compiled sweep machine. -/
inductive Sym (D : Type) where
  | blank
  | mark
  | raw (b : Bool)
  | dat (a : D)
  deriving DecidableEq, Fintype

/-- Control states of a compiled sweep machine. -/
inductive St (I B : Type) where
  | init0
  | init1
  | fwd (i : I) (b : B)
  | bwd (i : I) (b : B)
  | halt (ans : Bool)
  deriving DecidableEq, Fintype

/-- Left-to-right Mealy transduction. -/
def fscan {D B : Type} (f : B → D → D × B) : B → List D → List D × B
  | b, [] => ([], b)
  | b, a :: l => ((f b a).1 :: (fscan f (f b a).2 l).1, (fscan f (f b a).2 l).2)

/-- Right-to-left Mealy transduction (the last cell is processed first). -/
def bscan {D B : Type} (f : B → D → D × B) : B → List D → List D × B
  | b, [] => ([], b)
  | b, a :: l => ((f (bscan f b l).2 a).1 :: (bscan f b l).1, (f (bscan f b l).2 a).2)

theorem fscan_length {D B : Type} (f : B → D → D × B) :
    ∀ (b : B) (l : List D), (fscan f b l).1.length = l.length
  | _, [] => rfl
  | b, a :: l => by simp [fscan, fscan_length f _ l]

theorem bscan_length {D B : Type} (f : B → D → D × B) :
    ∀ (b : B) (l : List D), (bscan f b l).1.length = l.length
  | _, [] => rfl
  | b, a :: l => by simp [bscan, bscan_length f b l]

/-- A sweep program: finite data alphabet `D`, finite instructions `I`,
finite buffers `B`. -/
structure Prog where
  D : Type
  I : Type
  B : Type
  [finD : Fintype D]
  [decD : DecidableEq D]
  [finI : Fintype I]
  [decI : DecidableEq I]
  [finB : Fintype B]
  [decB : DecidableEq B]
  /-- how a raw input bit is read as data -/
  lift : Bool → D
  start : I
  /-- initial forward buffer of an instruction -/
  init : I → B
  fwd : I → B → D → D × B
  /-- optional one-cell extension at the right end -/
  ext : I → B → Option D
  /-- backward transducer; it starts from the final forward buffer -/
  bwd : I → B → D → D × B
  /-- continuation chosen from the final backward buffer -/
  next : I → B → I ⊕ Bool

namespace Prog

attribute [instance] Prog.finD Prog.decD Prog.finI Prog.decI Prog.finB Prog.decB

variable (P : Prog)

/-! ### Abstract semantics -/

/-- Forward pass of instruction `i`. -/
def fpass (i : P.I) (l : List P.D) : List P.D × P.B := fscan (P.fwd i) (P.init i) l

/-- Data after the forward pass and the extension. -/
def mid (i : P.I) (l : List P.D) : List P.D :=
  (P.fpass i l).1 ++ (P.ext i (P.fpass i l).2).toList

/-- One round trip: new data list and final backward buffer. -/
def trip (i : P.I) (l : List P.D) : List P.D × P.B :=
  bscan (P.bwd i) (P.fpass i l).2 (P.mid i l)

/-- Exact number of TM transitions of one round trip. -/
def tripCost (i : P.I) (l : List P.D) : ℕ :=
  2 * l.length + 2 + (P.ext i (P.fpass i l).2).toList.length

/-- One program step. -/
def stepP (s : P.I × List P.D) : (P.I × List P.D) ⊕ (Bool × List P.D) :=
  match P.next s.1 (P.trip s.1 s.2).2 with
  | .inl i' => .inl (i', (P.trip s.1 s.2).1)
  | .inr a => .inr (a, (P.trip s.1 s.2).1)

/-- `Reach s s' c`: from `s` the program reaches the running state `s'`
after round trips of total cost `c`. -/
inductive Reach : P.I × List P.D → P.I × List P.D → ℕ → Prop
  | refl (s : P.I × List P.D) : Reach s s 0
  | step {s s' s'' : P.I × List P.D} {c : ℕ} :
      P.stepP s = .inl s' → Reach s' s'' c → Reach s s'' (P.tripCost s.1 s.2 + c)

/-- `Halts s a c`: from `s` the program halts with answer `a`, total cost `c`. -/
inductive Halts : P.I × List P.D → Bool → ℕ → Prop
  | last {s : P.I × List P.D} {a : Bool} {l : List P.D} :
      P.stepP s = .inr (a, l) → Halts s a (P.tripCost s.1 s.2)
  | step {s s' : P.I × List P.D} {a : Bool} {c : ℕ} :
      P.stepP s = .inl s' → Halts s' a c → Halts s a (P.tripCost s.1 s.2 + c)

theorem Reach.trans {s s' s'' : P.I × List P.D} {c c' : ℕ}
    (h : P.Reach s s' c) (h' : P.Reach s' s'' c') : P.Reach s s'' (c + c') := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => rw [add_assoc]; exact .step hs (ih h')

theorem Reach.halts {s s' : P.I × List P.D} {a : Bool} {c c' : ℕ}
    (h : P.Reach s s' c) (h' : P.Halts s' a c') : P.Halts s a (c + c') := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => rw [add_assoc]; exact .step hs (ih h')

theorem Reach.single {s s' : P.I × List P.D} (h : P.stepP s = .inl s') :
    P.Reach s s' (P.tripCost s.1 s.2) := by
  simpa using Reach.step h (Reach.refl s')

theorem tripCost_pos (i : P.I) (l : List P.D) : 0 < P.tripCost i l := by
  unfold tripCost; omega

theorem Halts.pos {s : P.I × List P.D} {a : Bool} {c : ℕ} (h : P.Halts s a c) : 0 < c := by
  cases h with
  | last _ => exact P.tripCost_pos _ _
  | step _ _ => have := P.tripCost_pos s.1 s.2; omega

/-! ### The compiled machine -/

/-- Read a data value from a cell (raw input bits are lifted). -/
def dec : Sym P.D → Option P.D
  | .dat a => some a
  | .raw x => some (P.lift x)
  | _ => none

def delta : St P.I P.B → Sym P.D → Option (St P.I P.B × Sym P.D × Dir)
  | .init0, a => some (.init1, a, .L)
  | .init1, _ => some (.fwd P.start (P.init P.start), .mark, .R)
  | .fwd i b, .dat a => some (.fwd i (P.fwd i b a).2, .dat (P.fwd i b a).1, .R)
  | .fwd i b, .raw x =>
      some (.fwd i (P.fwd i b (P.lift x)).2, .dat (P.fwd i b (P.lift x)).1, .R)
  | .fwd i b, .blank =>
      match P.ext i b with
      | some e => some (.bwd i b, .dat e, .S)
      | none => some (.bwd i b, .blank, .L)
  | .fwd _ _, .mark => none
  | .bwd i b, .dat a => some (.bwd i (P.bwd i b a).2, .dat (P.bwd i b a).1, .L)
  | .bwd i b, .raw x =>
      some (.bwd i (P.bwd i b (P.lift x)).2, .dat (P.bwd i b (P.lift x)).1, .L)
  | .bwd i b, .mark =>
      match P.next i b with
      | .inl i' => some (.fwd i' (P.init i'), .mark, .R)
      | .inr a => some (.halt a, .mark, .S)
  | .bwd _ _, .blank => none
  | .halt _, _ => none

/-- The compiled ordinary single-tape Turing machine. -/
def toTM : TM where
  Λ := St P.I P.B
  Γ := Sym P.D
  blank := .blank
  inp := .raw
  start := .init0
  δ := P.delta
  acc q := decide (q = .halt true)
  rej q := decide (q = .halt false)

/-! ### Tape bookkeeping -/

/-- Overwrite the cells `p, p+1, …` with the data list `out`. -/
def writeRange (T : ℤ → Sym P.D) (p : ℤ) (out : List P.D) (j : ℤ) : Sym P.D :=
  if p ≤ j then
    (match out[(j - p).toNat]? with
     | some a => .dat a
     | none => T j)
  else T j

theorem writeRange_nil (T : ℤ → Sym P.D) (p : ℤ) : P.writeRange T p [] = T := by
  funext j; unfold writeRange; split_ifs <;> simp

theorem writeRange_cons (T : ℤ → Sym P.D) (p : ℤ) (a : P.D) (out : List P.D) :
    P.writeRange (Function.update T p (.dat a)) (p + 1) out = P.writeRange T p (a :: out) := by
  funext j
  unfold writeRange
  by_cases hj : j = p
  · subst hj
    simp
  · by_cases h1 : p + 1 ≤ j
    · have h2 : p ≤ j := by omega
      rw [if_pos h1, if_pos h2]
      have e : (j - p).toNat = (j - (p + 1)).toNat + 1 := by omega
      rw [e, List.getElem?_cons_succ]
      cases out[(j - (p + 1)).toNat]? with
      | some b => rfl
      | none => simp [Function.update, hj]
    · have h2 : ¬ p ≤ j := by omega
      rw [if_neg h1, if_neg h2]
      simp [Function.update, hj]

theorem writeRange_cons' (T : ℤ → Sym P.D) (p : ℤ) (a : P.D) (out : List P.D) :
    Function.update (P.writeRange T (p + 1) out) p (.dat a) = P.writeRange T p (a :: out) := by
  funext j
  by_cases hj : j = p
  · subst hj
    simp [writeRange]
  · rw [Function.update_of_ne hj]
    unfold writeRange
    by_cases h1 : p + 1 ≤ j
    · have h2 : p ≤ j := by omega
      rw [if_pos h1, if_pos h2]
      have e : (j - p).toNat = (j - (p + 1)).toNat + 1 := by omega
      rw [e, List.getElem?_cons_succ]
    · have h2 : ¬ p ≤ j := by omega
      rw [if_neg h1, if_neg h2]

theorem writeRange_get (T : ℤ → Sym P.D) (out : List P.D) (k : ℕ) (hk : k < out.length) :
    P.writeRange T 0 out (0 + k) = .dat out[k] := by
  unfold writeRange
  rw [if_pos (by omega), show ((0 : ℤ) + (k : ℤ) - 0).toNat = k by omega,
    List.getElem?_eq_getElem hk]

theorem writeRange_append_one (T : ℤ → Sym P.D) (p : ℤ) (out : List P.D) (e : P.D) :
    Function.update (P.writeRange T p out) (p + out.length) (.dat e) =
      P.writeRange T p (out ++ [e]) := by
  funext j
  unfold writeRange
  by_cases hj : j = p + out.length
  · subst hj
    simp
  · simp only [Function.update, hj, dite_false]
    by_cases h : p ≤ j
    · rw [if_pos h, if_pos h]
      by_cases hk : (j - p).toNat < out.length
      · rw [List.getElem?_append_left hk]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    · rw [if_neg h, if_neg h]

theorem writeRange_writeRange (T : ℤ → Sym P.D) (p : ℤ) (out out' : List P.D)
    (h : out.length = out'.length) :
    P.writeRange (P.writeRange T p out) p out' = P.writeRange T p out' := by
  funext j
  by_cases hp : p ≤ j
  · simp only [writeRange, if_pos hp]
    cases h' : out'[(j - p).toNat]? with
    | some a => rfl
    | none =>
      have : out[(j - p).toNat]? = none := by
        rw [List.getElem?_eq_none_iff] at h' ⊢; omega
      simp [this]
  · simp only [writeRange, if_neg hp]

theorem writeRange_of_lt (T : ℤ → Sym P.D) (p : ℤ) (out : List P.D) (j : ℤ) (hj : j < p) :
    P.writeRange T p out j = T j := by
  unfold writeRange; rw [if_neg (by omega)]

theorem writeRange_of_ge (T : ℤ → Sym P.D) (p : ℤ) (out : List P.D) (j : ℤ)
    (hj : p + out.length ≤ j) : P.writeRange T p out j = T j := by
  unfold writeRange
  rw [if_pos (by omega), List.getElem?_eq_none (by omega)]

theorem writeRange_at (T : ℤ → Sym P.D) (p : ℤ) (out : List P.D) (k : ℕ) :
    P.writeRange T p out (p + k) = match out[k]? with | some a => .dat a | none => T (p + k) := by
  unfold writeRange
  rw [if_pos (by omega), show (p + (k : ℤ) - p).toNat = k by omega]

/-- `T` represents the data list `l`: end-marker at `-1`, data on `[0, |l|)`,
blank elsewhere. -/
structure Repr (T : ℤ → Sym P.D) (l : List P.D) : Prop where
  mark : T (-1) = .mark
  left : ∀ j : ℤ, j < -1 → T j = .blank
  cells : ∀ k : ℕ, k < l.length → P.dec (T k) = l[k]?
  right : ∀ j : ℤ, (l.length : ℤ) ≤ j → T j = .blank

theorem repr_writeRange {T : ℤ → Sym P.D} {l : List P.D} (hT : P.Repr T l)
    (l' : List P.D) (hl : l.length ≤ l'.length) : P.Repr (P.writeRange T 0 l') l' where
  mark := by rw [P.writeRange_of_lt _ _ _ _ (by norm_num)]; exact hT.mark
  left j hj := by rw [P.writeRange_of_lt _ _ _ _ (by omega)]; exact hT.left j hj
  cells k hk := by
    have := P.writeRange_at T 0 l' k
    simp only [zero_add] at this
    rw [this, List.getElem?_eq_getElem hk]
    rfl
  right j hj := by
    rw [P.writeRange_of_ge _ _ _ _ (by omega)]; exact hT.right j (by omega)

/-! ### Execution lemmas -/

theorem delta_fwd_dec {i : P.I} {b : P.B} {s : Sym P.D} {a : P.D} (h : P.dec s = some a) :
    P.delta (.fwd i b) s = some (.fwd i (P.fwd i b a).2, .dat (P.fwd i b a).1, .R) := by
  cases s with
  | dat a' => simp [dec] at h; subst h; rfl
  | raw x => simp [dec] at h; subst h; rfl
  | blank => simp [dec] at h
  | mark => simp [dec] at h

theorem run_one_step {q q' : St P.I P.B} {T : ℤ → Sym P.D} {p : ℤ} {a : Sym P.D} {d : Dir}
    (h : P.delta q (T p) = some (q', a, d)) :
    P.toTM.run ⟨q, T, p⟩ 1 = ⟨q', Function.update T p a, p + d.shift⟩ :=
  TM.run_step P.toTM (c := ⟨q, T, p⟩) h

/-- The forward pass over a represented segment. -/
theorem fwd_run (i : P.I) : ∀ (r : List P.D) (T : ℤ → Sym P.D) (p : ℤ) (b : P.B),
    (∀ k : ℕ, k < r.length → P.dec (T (p + k)) = r[k]?) →
    P.toTM.run ⟨.fwd i b, T, p⟩ r.length =
      ⟨.fwd i (fscan (P.fwd i) b r).2, P.writeRange T p (fscan (P.fwd i) b r).1, p + r.length⟩
  | [], T, p, b, _ => by
    simp [TM.run, fscan, P.writeRange_nil]
  | a :: r, T, p, b, h => by
    have h0 : P.dec (T p) = some a := by simpa using h 0 (by simp)
    have hstep := P.run_one_step (P.delta_fwd_dec (i := i) (b := b) h0)
    have hrest : ∀ k : ℕ, k < r.length →
        P.dec (Function.update T p (.dat (P.fwd i b a).1) (p + 1 + k)) = r[k]? := by
      intro k hk
      rw [Function.update_of_ne (by omega)]
      have := h (k + 1) (by simp; omega)
      rw [show p + 1 + (k : ℤ) = p + ((k + 1 : ℕ) : ℤ) by push_cast; ring]
      simpa using this
    rw [show (a :: r).length = 1 + r.length by simp; ring, TM.run_add, hstep]
    simp only [Dir.shift]
    rw [fwd_run i r _ (p + 1) _ hrest, P.writeRange_cons]
    simp only [fscan, List.length_cons]
    congr 1
    push_cast; ring

/-- The backward pass over a segment of data cells. -/
theorem bwd_run (i : P.I) : ∀ (u : List P.D) (T : ℤ → Sym P.D) (p : ℤ) (b : P.B),
    (∀ (k : ℕ) (hk : k < u.length), T (p + k) = .dat u[k]) →
    P.toTM.run ⟨.bwd i b, T, p + u.length - 1⟩ u.length =
      ⟨.bwd i (bscan (P.bwd i) b u).2, P.writeRange T p (bscan (P.bwd i) b u).1, p - 1⟩
  | [], T, p, b, _ => by
    simp [TM.run, bscan, P.writeRange_nil]
  | a :: l, T, p, b, h => by
    have hl : ∀ (k : ℕ) (hk : k < l.length), T (p + 1 + k) = .dat l[k] := by
      intro k hk
      have := h (k + 1) (by simp; omega)
      rw [show p + 1 + (k : ℤ) = p + ((k + 1 : ℕ) : ℤ) by push_cast; ring]
      simpa using this
    have ih := bwd_run i l T (p + 1) b hl
    have e1 : p + ((a :: l).length : ℤ) - 1 = p + 1 + l.length - 1 := by simp; ring
    rw [e1, show (a :: l).length = l.length + 1 by simp, TM.run_add, ih]
    have hTp : P.writeRange T (p + 1) (bscan (P.bwd i) b l).1 p = .dat a := by
      rw [P.writeRange_of_lt _ _ _ _ (by omega)]
      simpa using h 0 (by simp)
    have hδ : P.delta (.bwd i (bscan (P.bwd i) b l).2)
        (P.writeRange T (p + 1) (bscan (P.bwd i) b l).1 (p + 1 - 1)) =
        some (.bwd i (P.bwd i (bscan (P.bwd i) b l).2 a).2,
          .dat (P.bwd i (bscan (P.bwd i) b l).2 a).1, .L) := by
      rw [show p + 1 - 1 = p by ring, hTp]; rfl
    rw [P.run_one_step hδ]
    simp only [Dir.shift, show p + 1 - 1 = p by ring]
    rw [P.writeRange_cons']
    simp only [bscan, sub_eq_add_neg]

/-- One full round trip, stopping just before the end-marker transition. -/
theorem trip_run_pre (i : P.I) (l : List P.D) (T : ℤ → Sym P.D) (hT : P.Repr T l) :
    P.toTM.run ⟨.fwd i (P.init i), T, 0⟩ (P.tripCost i l - 1) =
      ⟨.bwd i (P.trip i l).2, P.writeRange T 0 (P.trip i l).1, -1⟩ := by
  have hlen : (P.fpass i l).1.length = l.length := fscan_length _ _ _
  have hfwd : P.toTM.run ⟨.fwd i (P.init i), T, 0⟩ l.length =
      ⟨.fwd i (P.fpass i l).2, P.writeRange T 0 (P.fpass i l).1, (l.length : ℤ)⟩ := by
    have h := P.fwd_run i l T 0 (P.init i) (by intro k hk; simpa using hT.cells k hk)
    simp only [zero_add] at h
    exact h
  have hblank : P.writeRange T 0 (P.fpass i l).1 (l.length : ℤ) = .blank := by
    rw [P.writeRange_of_ge _ _ _ _ (by simp [hlen])]
    exact hT.right _ le_rfl
  cases he : P.ext i (P.fpass i l).2 with
  | some e =>
    have hm : P.mid i l = (P.fpass i l).1 ++ [e] := by simp [mid, he]
    have hmlen : (P.mid i l).length = l.length + 1 := by simp [hm, hlen]
    have hcost : P.tripCost i l - 1 = l.length + 1 + (P.mid i l).length := by
      simp only [tripCost, he, Option.toList_some, List.length_singleton]; omega
    have hδ : P.delta (.fwd i (P.fpass i l).2) (P.writeRange T 0 (P.fpass i l).1 (l.length : ℤ)) =
        some (.bwd i (P.fpass i l).2, .dat e, .S) := by
      rw [hblank]; simp [delta, he]
    have hupd : Function.update (P.writeRange T 0 (P.fpass i l).1) (l.length : ℤ) (.dat e) =
        P.writeRange T 0 (P.mid i l) := by
      rw [hm, ← P.writeRange_append_one]; simp [hlen]
    have hbwd := P.bwd_run i (P.mid i l) (P.writeRange T 0 (P.mid i l)) 0 (P.fpass i l).2
      (fun k hk => P.writeRange_get T _ k hk)
    rw [hcost, TM.run_add, TM.run_add, hfwd, P.run_one_step hδ, hupd]
    simp only [Dir.shift, add_zero]
    rw [show (l.length : ℤ) = 0 + ((P.mid i l).length : ℤ) - 1 by rw [hmlen]; push_cast; ring,
      hbwd, P.writeRange_writeRange _ _ _ _ (by rw [bscan_length])]
    simp only [zero_sub]
    rfl
  | none =>
    have hm : P.mid i l = (P.fpass i l).1 := by simp [mid, he]
    have hmlen : (P.mid i l).length = l.length := by simp [hm, hlen]
    have hcost : P.tripCost i l - 1 = l.length + 1 + (P.mid i l).length := by
      simp only [tripCost, he, Option.toList_none, List.length_nil]; omega
    have hδ : P.delta (.fwd i (P.fpass i l).2) (P.writeRange T 0 (P.fpass i l).1 (l.length : ℤ)) =
        some (.bwd i (P.fpass i l).2, .blank, .L) := by
      rw [hblank]; simp [delta, he]
    have hupd : Function.update (P.writeRange T 0 (P.fpass i l).1) (l.length : ℤ) .blank =
        P.writeRange T 0 (P.mid i l) := by
      rw [← hblank, Function.update_eq_self, hm]
    have hbwd := P.bwd_run i (P.mid i l) (P.writeRange T 0 (P.mid i l)) 0 (P.fpass i l).2
      (fun k hk => P.writeRange_get T _ k hk)
    rw [hcost, TM.run_add, TM.run_add, hfwd, P.run_one_step hδ, hupd]
    simp only [Dir.shift]
    rw [show (l.length : ℤ) + -1 = 0 + ((P.mid i l).length : ℤ) - 1 by rw [hmlen]; ring,
      hbwd, P.writeRange_writeRange _ _ _ _ (by rw [bscan_length])]
    simp only [zero_sub]
    rfl

theorem trip_length (i : P.I) (l : List P.D) : l.length ≤ (P.trip i l).1.length := by
  simp [trip, mid, bscan_length, fpass, fscan_length]

theorem tripCost_eq (i : P.I) (l : List P.D) :
    P.tripCost i l = P.tripCost i l - 1 + 1 := by
  have := P.tripCost_pos i l; omega

/-- A continuing round trip returns to cell `0` in the next instruction. -/
theorem trip_run_cont {i i' : P.I} {l : List P.D} {T : ℤ → Sym P.D} (hT : P.Repr T l)
    (h : P.next i (P.trip i l).2 = .inl i') :
    P.toTM.run ⟨.fwd i (P.init i), T, 0⟩ (P.tripCost i l) =
      ⟨.fwd i' (P.init i'), P.writeRange T 0 (P.trip i l).1, 0⟩ := by
  rw [P.tripCost_eq i l, TM.run_add, P.trip_run_pre i l T hT]
  have hm : P.writeRange T 0 (P.trip i l).1 (-1) = .mark := by
    rw [P.writeRange_of_lt _ _ _ _ (by norm_num)]; exact hT.mark
  have hδ : P.delta (.bwd i (P.trip i l).2) (P.writeRange T 0 (P.trip i l).1 (-1)) =
      some (.fwd i' (P.init i'), .mark, .R) := by
    rw [hm]; simp [delta, h]
  rw [P.run_one_step hδ]
  simp only [Dir.shift]
  rw [show (-1 : ℤ) + 1 = 0 by norm_num, ← hm, Function.update_eq_self]

/-- A halting round trip ends in the answer state on the end-marker. -/
theorem trip_run_halt {i : P.I} {a : Bool} {l : List P.D} {T : ℤ → Sym P.D} (hT : P.Repr T l)
    (h : P.next i (P.trip i l).2 = .inr a) :
    P.toTM.run ⟨.fwd i (P.init i), T, 0⟩ (P.tripCost i l) =
      ⟨.halt a, P.writeRange T 0 (P.trip i l).1, -1⟩ := by
  rw [P.tripCost_eq i l, TM.run_add, P.trip_run_pre i l T hT]
  have hm : P.writeRange T 0 (P.trip i l).1 (-1) = .mark := by
    rw [P.writeRange_of_lt _ _ _ _ (by norm_num)]; exact hT.mark
  have hδ : P.delta (.bwd i (P.trip i l).2) (P.writeRange T 0 (P.trip i l).1 (-1)) =
      some (.halt a, .mark, .S) := by
    rw [hm]; simp [delta, h]
  rw [P.run_one_step hδ]
  simp only [Dir.shift, add_zero]
  rw [← hm, Function.update_eq_self]

/-- Whole-program execution between running states. -/
theorem reach_run {s s' : P.I × List P.D} {c : ℕ} (h : P.Reach s s' c) :
    ∀ T : ℤ → Sym P.D, P.Repr T s.2 →
      ∃ T', P.Repr T' s'.2 ∧
        P.toTM.run ⟨.fwd s.1 (P.init s.1), T, 0⟩ c = ⟨.fwd s'.1 (P.init s'.1), T', 0⟩ := by
  induction h with
  | refl s => intro T hT; exact ⟨T, hT, rfl⟩
  | @step s s₁ s₂ c hs _ ih =>
    intro T hT
    obtain ⟨i, l⟩ := s
    have hn : P.next i (P.trip i l).2 = .inl s₁.1 ∧ (P.trip i l).1 = s₁.2 := by
      simp only [stepP] at hs
      split at hs
      · rename_i i' heq
        simp only [Sum.inl.injEq] at hs
        subst hs
        exact ⟨heq, rfl⟩
      · simp at hs
    have hT' : P.Repr (P.writeRange T 0 (P.trip i l).1) s₁.2 := by
      rw [← hn.2]; exact P.repr_writeRange hT _ (P.trip_length i l)
    obtain ⟨T', hT'', hrun⟩ := ih _ hT'
    refine ⟨T', hT'', ?_⟩
    rw [TM.run_add]
    simp only at hrun ⊢
    rw [P.trip_run_cont hT hn.1, hrun]

/-- Whole-program execution up to the answer. -/
theorem halts_run {s : P.I × List P.D} {a : Bool} {c : ℕ} (h : P.Halts s a c) :
    ∀ T : ℤ → Sym P.D, P.Repr T s.2 →
      (∃ i b T', P.toTM.run ⟨.fwd s.1 (P.init s.1), T, 0⟩ (c - 1) = ⟨.bwd i b, T', -1⟩) ∧
      (∃ T', P.toTM.run ⟨.fwd s.1 (P.init s.1), T, 0⟩ c = ⟨.halt a, T', -1⟩) := by
  induction h with
  | @last s a l' hs =>
    intro T hT
    obtain ⟨i, l⟩ := s
    have hn : P.next i (P.trip i l).2 = .inr a := by
      simp only [stepP] at hs
      split at hs
      · simp at hs
      · rename_i a' heq
        simp only [Sum.inr.injEq, Prod.mk.injEq] at hs
        rw [heq, hs.1]
    exact ⟨⟨i, _, _, P.trip_run_pre i l T hT⟩, ⟨_, P.trip_run_halt hT hn⟩⟩
  | @step s s₁ a c hs hh ih =>
    intro T hT
    obtain ⟨i, l⟩ := s
    have hn : P.next i (P.trip i l).2 = .inl s₁.1 ∧ (P.trip i l).1 = s₁.2 := by
      simp only [stepP] at hs
      split at hs
      · rename_i i' heq
        simp only [Sum.inl.injEq] at hs
        subst hs
        exact ⟨heq, rfl⟩
      · simp at hs
    have hT' : P.Repr (P.writeRange T 0 (P.trip i l).1) s₁.2 := by
      rw [← hn.2]; exact P.repr_writeRange hT _ (P.trip_length i l)
    obtain ⟨⟨i', b', T₁, h₁⟩, ⟨T₂, h₂⟩⟩ := ih _ hT'
    have hpos := hh.pos
    refine ⟨⟨i', b', T₁, ?_⟩, ⟨T₂, ?_⟩⟩
    · rw [show P.tripCost i l + c - 1 = P.tripCost i l + (c - 1) by omega, TM.run_add]
      simp only at h₁ ⊢
      rw [P.trip_run_cont hT hn.1, h₁]
    · rw [TM.run_add]
      simp only at h₂ ⊢
      rw [P.trip_run_cont hT hn.1, h₂]

/-- Answering states of the compiled machine halt. -/
theorem answering_halts (c : P.toTM.Cfg) (h : P.toTM.ans c ≠ none) : P.toTM.step c = none := by
  obtain ⟨q, T, p⟩ := c
  cases q with
  | halt a => simp [TM.step, toTM, delta]
  | init0 => simp [TM.ans, toTM, answerOf] at h
  | init1 => simp [TM.ans, toTM, answerOf] at h
  | fwd i b => simp [TM.ans, toTM, answerOf] at h
  | bwd i b => simp [TM.ans, toTM, answerOf] at h

/-- The two initialization transitions place the end-marker. -/
theorem init_run (x : List Bool) :
    ∃ T, P.Repr T (x.map P.lift) ∧
      P.toTM.run (P.toTM.init x) 2 = ⟨.fwd P.start (P.init P.start), T, 0⟩ := by
  have h0 : P.delta .init0 (P.toTM.inputTape x 0) =
      some (.init1, P.toTM.inputTape x 0, .L) := rfl
  have h1 := P.run_one_step (q := .init0) (T := P.toTM.inputTape x) (p := 0) h0
  rw [Function.update_eq_self] at h1
  have h2 : P.delta .init1 (P.toTM.inputTape x (0 + Dir.L.shift)) =
      some (.fwd P.start (P.init P.start), .mark, .R) := rfl
  have h3 := P.run_one_step (q := .init1) (T := P.toTM.inputTape x) (p := 0 + Dir.L.shift) h2
  refine ⟨Function.update (P.toTM.inputTape x) (0 + Dir.L.shift) .mark, ?_, ?_⟩
  · simp only [Dir.shift, zero_add]
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      simp [TM.inputTape, toTM, show ¬ (0 ≤ j) by omega]
    · intro k hk
      rw [Function.update_of_ne (by omega)]
      simp only [List.length_map] at hk
      simp only [TM.inputTape, toTM, show (0 : ℤ) ≤ k by omega,
        show (k : ℤ) < x.length by omega, and_self, if_true, dec, List.getElem?_map,
        List.getElem?_eq_getElem hk, Int.toNat_natCast, Option.map_some]
      rw [List.getD_eq_getElem _ _ hk]
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      simp only [List.length_map] at hj
      simp [TM.inputTape, toTM, show ¬ (j < x.length) by omega]
  · rw [show (2 : ℕ) = 1 + 1 from rfl, TM.run_add]
    change P.toTM.run (P.toTM.run ⟨.init0, P.toTM.inputTape x, 0⟩ 1) 1 = _
    rw [h1, h3]
    simp [Dir.shift]

/-- **Compiler correctness.**  If the sweep program halts with answer `a`
after total round-trip cost `C` on input `x`, then the compiled single-tape TM
gives its first answer `a` at exactly time `C + 2`. -/
theorem toTM_firstAnswer (x : List Bool) {a : Bool} {C : ℕ}
    (h : P.Halts (P.start, x.map P.lift) a C) :
    FirstAnswer (P.toTM.out x) (C + 2) a := by
  obtain ⟨T, hT, hinit⟩ := P.init_run x
  obtain ⟨⟨i, b, T₁, hpre⟩, ⟨T₂, hfin⟩⟩ := P.halts_run h T hT
  have hpos := h.pos
  refine ⟨C + 2, le_rfl, ?_, ?_⟩
  · simp only [TM.out]
    rw [show C + 2 = 2 + C by ring, TM.run_add, hinit]
    simp only at hfin
    rw [hfin]
    cases a <;> simp [TM.ans, toTM, answerOf]
  · have hprev : 0 < C + 2 → P.toTM.ans (P.toTM.run (P.toTM.init x) (C + 2 - 1)) = none := by
      intro _
      rw [show C + 2 - 1 = 2 + (C - 1) by omega, TM.run_add, hinit]
      simp only at hpre
      rw [hpre]
      simp [TM.ans, toTM, answerOf]
    intro m hm
    exact TM.none_before P.toTM P.answering_halts _ hprev m hm

end Prog

end PVNP.Discrete.Sweep
