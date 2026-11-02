import PVNP.PSubsetNP
import PVNP.TMScan
import PVNP.DiscreteCurvatureRail
import PVNP.PartIExtended

/-!
# CNF-SAT is in `NP_TM`: an explicit, verified verifier machine (O2; Part III `prop:assignment-P`)

**Instance encoding (dense CNF).** A formula over `n ≥ 1` variables with `m`
clauses is the bit string listing, clause by clause, the `n` slots
`(p, q, e)` of each clause: `p` = "`xⱼ` occurs", `q` = "`¬xⱼ` occurs",
`e` = "this is the clause's last slot".  The witness is the assignment
`a₀ … a_{n-1}`.

**Verifier.** `satTM` reads `pair x w`, validates the pair format, then, slot
by slot, travels to the first unmarked witness bit, marks it and ORs the
literal value into a clause flag kept in the finite control; at a clause end
it checks that the witness was used exactly once per slot and that the flag
is set, then unmarks the witness.

* `satTM_decides`: `satTM` decides
  `V_SAT = {pair x w | chkFrom w x 0 false true}` in time `2(N+3)²`.
* `encDense_mem_SAT_iff`: for every Part I formula `F` whose variables are
  `< n` (`n ≥ 1`), `encDense n F ∈ SAT_dense ↔ PVNP.PartI.satisfiable F`.
* `SAT_dense_mem_NP_TM`, `SAT_dense_mem_NP_WCC`, `V_SAT_mem_P_TM`.
-/

namespace PVNP.Discrete.SATV

open TM

/-! ### The machine -/

/-- Tape alphabet: blank, raw input bit, processed tag, marked witness bit. -/
inductive Sym where
  | blank
  | raw (b : Bool)
  | done
  | wm (b : Bool)
  deriving DecidableEq, Fintype

/-- Control states. -/
inductive St where
  | P0
  | P1
  | back (fl atB : Bool)
  | seek (fl atB : Bool)
  | skipD (fl atB : Bool)
  | rdP (fl : Bool)
  | t2 (fl p : Bool)
  | rdQ (fl p : Bool)
  | t3 (fl p q : Bool)
  | rdE (fl p q : Bool)
  | toW (fl p q e : Bool)
  | toWD (fl p q e : Bool)
  | inW (fl p q e : Bool)
  | chkEnd (fl : Bool)
  | unmark
  | yes
  | no
  deriving DecidableEq, Fintype

/-- Truth value of slot `(p, q)` under `a`. -/
def lit (p q a : Bool) : Bool := (p && a) || (q && !a)

/-- Transition table (fully enumerated). -/
def δ : St → Sym → Option (St × Sym × Dir)
  | .P0, .blank => some (.no, .blank, .S)
  | .P0, .raw true => some (.P1, .raw true, .R)
  | .P0, .raw false => some (.back false true, .raw false, .L)
  | .P0, .done => some (.no, .done, .S)
  | .P0, .wm b => some (.no, .wm b, .S)
  | .P1, .raw b => some (.P0, .raw b, .R)
  | .P1, .blank => some (.no, .blank, .S)
  | .P1, .done => some (.no, .done, .S)
  | .P1, .wm b => some (.no, .wm b, .S)
  | .back fl atB, .blank => some (.seek fl atB, .blank, .R)
  | .back fl atB, .raw b => some (.back fl atB, .raw b, .L)
  | .back fl atB, .done => some (.back fl atB, .done, .L)
  | .back fl atB, .wm b => some (.back fl atB, .wm b, .L)
  | .seek _ _, .blank => some (.no, .blank, .S)
  | .seek fl _, .raw true => some (.rdP fl, .done, .R)
  | .seek _ atB, .raw false => some (if atB then .yes else .no, .raw false, .S)
  | .seek fl atB, .done => some (.skipD fl atB, .done, .R)
  | .seek _ _, .wm b => some (.no, .wm b, .S)
  | .skipD fl atB, s => some (.seek fl atB, s, .R)
  | .rdP fl, .raw p => some (.t2 fl p, .raw p, .R)
  | .rdP _, .blank => some (.no, .blank, .S)
  | .rdP _, .done => some (.no, .done, .S)
  | .rdP _, .wm b => some (.no, .wm b, .S)
  | .t2 fl p, .raw true => some (.rdQ fl p, .done, .R)
  | .t2 _ _, .raw false => some (.no, .raw false, .S)
  | .t2 _ _, .blank => some (.no, .blank, .S)
  | .t2 _ _, .done => some (.no, .done, .S)
  | .t2 _ _, .wm b => some (.no, .wm b, .S)
  | .rdQ fl p, .raw q => some (.t3 fl p q, .raw q, .R)
  | .rdQ _ _, .blank => some (.no, .blank, .S)
  | .rdQ _ _, .done => some (.no, .done, .S)
  | .rdQ _ _, .wm b => some (.no, .wm b, .S)
  | .t3 fl p q, .raw true => some (.rdE fl p q, .done, .R)
  | .t3 _ _ _, .raw false => some (.no, .raw false, .S)
  | .t3 _ _ _, .blank => some (.no, .blank, .S)
  | .t3 _ _ _, .done => some (.no, .done, .S)
  | .t3 _ _ _, .wm b => some (.no, .wm b, .S)
  | .rdE fl p q, .raw e => some (.toW fl p q e, .raw e, .R)
  | .rdE _ _ _, .blank => some (.no, .blank, .S)
  | .rdE _ _ _, .done => some (.no, .done, .S)
  | .rdE _ _ _, .wm b => some (.no, .wm b, .S)
  | .toW fl p q e, .raw true => some (.toWD fl p q e, .raw true, .R)
  | .toW fl p q e, .raw false => some (.inW fl p q e, .raw false, .R)
  | .toW _ _ _ _, .blank => some (.no, .blank, .S)
  | .toW _ _ _ _, .done => some (.no, .done, .S)
  | .toW _ _ _ _, .wm b => some (.no, .wm b, .S)
  | .toWD fl p q e, s => some (.toW fl p q e, s, .R)
  | .inW fl p q e, .wm b => some (.inW fl p q e, .wm b, .R)
  | .inW fl p q e, .raw a =>
    if e then some (.chkEnd (fl || lit p q a), .wm a, .R)
    else some (.back (fl || lit p q a) false, .wm a, .L)
  | .inW _ _ _ _, .blank => some (.no, .blank, .S)
  | .inW _ _ _ _, .done => some (.no, .done, .S)
  | .chkEnd fl, .blank => if fl then some (.unmark, .blank, .L) else some (.no, .blank, .S)
  | .chkEnd _, .raw b => some (.no, .raw b, .S)
  | .chkEnd _, .done => some (.no, .done, .S)
  | .chkEnd _, .wm b => some (.no, .wm b, .S)
  | .unmark, .wm b => some (.unmark, .raw b, .L)
  | .unmark, .raw b => some (.back false true, .raw b, .L)
  | .unmark, .blank => some (.no, .blank, .S)
  | .unmark, .done => some (.no, .done, .S)
  | .yes, _ => none
  | .no, _ => none

/-- The SAT verifier machine. -/
abbrev satTM : TM where
  Λ := St
  Γ := Sym
  blank := .blank
  inp b := .raw b
  start := .P0
  δ := δ
  acc s := decide (s = .yes)
  rej s := decide (s = .no)

theorem halting : ∀ c : satTM.Cfg, satTM.ans c ≠ none → satTM.step c = none := by
  intro c hc
  rcases c with ⟨q, T, h⟩
  cases q <;> simp_all [TM.ans, answerOf, TM.step, δ]

/-! ### Specification -/

/-- Recursive checker mirroring the machine (`j` used witness bits in the
current clause, `fl` clause flag, `atB` "at a clause boundary"). -/
def chkFrom (w : List Bool) : List Bool → ℕ → Bool → Bool → Bool
  | [], _, _, atB => atB
  | [_], _, _, _ => false
  | [_, _], _, _, _ => false
  | p :: q :: e :: rest, j, fl, _ =>
    if j < w.length then
      if e then
        (decide (j + 1 = w.length) && (fl || lit p q (w.getD j false))) &&
          chkFrom w rest 0 false true
      else chkFrom w rest (j + 1) (fl || lit p q (w.getD j false)) false
    else false

/-- The verification language (Part III `L_check`, in pair form). -/
def V_SAT : Set (List Bool) := {y | ∃ x w, y = pair x w ∧ chkFrom w x 0 false true = true}

/-- Dense CNF-SAT. -/
def SAT_dense : Set (List Bool) :=
  {x | ∃ w : List Bool, w.length ≤ x.length ∧ chkFrom w x 0 false true = true}

/-! ### Tape facts for `pair x w` -/

theorem getD_pair_term (x w : List Bool) : (pair x w).getD (2 * x.length) false = false := by
  induction x with
  | nil => simp [pair]
  | cons b x ih =>
    simp only [pair, List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons] at ih ⊢
    rw [show 2 * (x.length + 1) = 2 * x.length + 1 + 1 by ring]
    simpa using ih

section Facts

variable (x w : List Bool)

theorem tape_tag (i : ℕ) (hi : i < x.length) :
    satTM.inputTape (pair x w) (2 * (i : ℤ)) = .raw true := by
  have hl := pair_length x w
  simp only [inputTape]
  rw [if_pos ⟨by omega, by omega⟩, show (2 * (i : ℤ)).toNat = 2 * i by omega,
    TM.getD_pair_even x w i hi]

theorem tape_data (i : ℕ) (hi : i < x.length) :
    satTM.inputTape (pair x w) (2 * (i : ℤ) + 1) = .raw (x.getD i false) := by
  have hl := pair_length x w
  simp only [inputTape]
  rw [if_pos ⟨by omega, by omega⟩, show (2 * (i : ℤ) + 1).toNat = 2 * i + 1 by omega,
    TM.getD_pair_odd x w i hi]

theorem tape_term : satTM.inputTape (pair x w) (2 * (x.length : ℤ)) = .raw false := by
  have hl := pair_length x w
  simp only [inputTape]
  rw [if_pos ⟨by omega, by omega⟩, show (2 * (x.length : ℤ)).toNat = 2 * x.length by omega,
    getD_pair_term]

theorem tape_wit (j : ℕ) (hj : j < w.length) :
    satTM.inputTape (pair x w) (2 * (x.length : ℤ) + 1 + j) = .raw (w.getD j false) := by
  have hl := pair_length x w
  simp only [inputTape]
  rw [if_pos ⟨by omega, by omega⟩,
    show (2 * (x.length : ℤ) + 1 + j).toNat = 2 * x.length + 1 + j by omega,
    TM.getD_pair_witness x w j]

theorem tape_out (i : ℤ) (hi : i < 0 ∨ 2 * (x.length : ℤ) + 1 + w.length ≤ i) :
    satTM.inputTape (pair x w) i = .blank := by
  have hl := pair_length x w
  simp only [inputTape]
  rw [if_neg (by omega)]

end Facts

/-! ### Tape at the start of a round -/

section Rounds

variable (x w : List Bool)

/-- Tape at the start of round `k` (slots `0..k-1` processed, their tags
marked `done`) with `j` marked witness bits. -/
def tapeAt (k j : ℕ) : ℤ → Sym := fun i =>
  if 0 ≤ i ∧ i < 6 * (k : ℤ) ∧ i % 2 = 0 then .done
  else if 2 * (x.length : ℤ) + 1 ≤ i ∧ i < 2 * (x.length : ℤ) + 1 + j then
    .wm (w.getD (i - 2 * x.length - 1).toNat false)
  else satTM.inputTape (pair x w) i

variable {x w}

theorem tapeAt_done {k j : ℕ} (i : ℕ) (hi : i < 3 * k) : tapeAt x w k j (2 * (i : ℤ)) = .done := by
  simp only [tapeAt]; rw [if_pos ⟨by omega, by omega, by omega⟩]

theorem tapeAt_tag {k j : ℕ} (i : ℕ) (h1 : 3 * k ≤ i) (h2 : i < x.length) :
    tapeAt x w k j (2 * (i : ℤ)) = .raw true := by
  simp only [tapeAt]; rw [if_neg (by omega), if_neg (by omega)]; exact tape_tag x w i h2

theorem tapeAt_data {k j : ℕ} (i : ℕ) (hi : i < x.length) :
    tapeAt x w k j (2 * (i : ℤ) + 1) = .raw (x.getD i false) := by
  simp only [tapeAt]; rw [if_neg (by omega), if_neg (by omega)]; exact tape_data x w i hi

theorem tapeAt_term {k j : ℕ} (hk : 3 * k ≤ x.length) :
    tapeAt x w k j (2 * (x.length : ℤ)) = .raw false := by
  simp only [tapeAt]; rw [if_neg (by omega), if_neg (by omega)]; exact tape_term x w

theorem tapeAt_wm {k j : ℕ} (hk : 3 * k ≤ x.length) (i : ℕ) (hi : i < j) :
    tapeAt x w k j (2 * (x.length : ℤ) + 1 + i) = .wm (w.getD i false) := by
  simp only [tapeAt]
  rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  congr 2; omega

theorem tapeAt_wit {k j : ℕ} (hk : 3 * k ≤ x.length) (i : ℕ) (h1 : j ≤ i) (h2 : i < w.length) :
    tapeAt x w k j (2 * (x.length : ℤ) + 1 + i) = .raw (w.getD i false) := by
  simp only [tapeAt]; rw [if_neg (by omega), if_neg (by omega)]; exact tape_wit x w i h2

theorem tapeAt_end {k j : ℕ} (hk : 3 * k ≤ x.length) (hj : j ≤ w.length) :
    tapeAt x w k j (2 * (x.length : ℤ) + 1 + w.length) = .blank := by
  simp only [tapeAt]; rw [if_neg (by omega), if_neg (by omega)]
  exact tape_out x w _ (Or.inr le_rfl)

theorem tapeAt_neg {k j : ℕ} : tapeAt x w k j (-1) = .blank := by
  simp only [tapeAt]; rw [if_neg (by omega), if_neg (by omega)]
  exact tape_out x w _ (Or.inl (by omega))

theorem tapeAt_nonblank {k j : ℕ} (hk : 3 * k ≤ x.length) (hj : j ≤ w.length) (i : ℤ)
    (h0 : 0 ≤ i) (h1 : i ≤ 2 * (x.length : ℤ) + w.length) : tapeAt x w k j i ≠ .blank := by
  have hl := pair_length x w
  simp only [tapeAt]
  split_ifs
  · simp
  · simp
  · simp only [inputTape]
    rw [if_pos ⟨h0, by omega⟩]; simp

theorem tapeAt_zero : tapeAt x w 0 0 = satTM.inputTape (pair x w) := by
  funext i; simp only [tapeAt]; rw [if_neg (by omega), if_neg (by omega)]

theorem tapeAt_next_slot {k j : ℕ} :
    Function.update (Function.update (Function.update (tapeAt x w k j) (6 * (k : ℤ)) .done)
      (6 * (k : ℤ) + 2) .done) (6 * (k : ℤ) + 4) .done = tapeAt x w (k + 1) j := by
  funext i
  simp only [Function.update]
  by_cases h4 : i = 6 * (k : ℤ) + 4
  · subst h4; simp only [dite_true, tapeAt]; push_cast; rw [if_pos ⟨by omega, by omega, by omega⟩]
  · rw [dif_neg h4]
    by_cases h2 : i = 6 * (k : ℤ) + 2
    · subst h2; simp only [dite_true, tapeAt]; push_cast; rw [if_pos ⟨by omega, by omega, by omega⟩]
    · rw [dif_neg h2]
      by_cases h0 : i = 6 * (k : ℤ)
      · subst h0; simp only [dite_true, tapeAt]; push_cast; rw [if_pos ⟨by omega, by omega, by omega⟩]
      · rw [dif_neg h0]
        simp only [tapeAt]; push_cast
        by_cases hd : 0 ≤ i ∧ i < 6 * (k : ℤ) ∧ i % 2 = 0
        · rw [if_pos hd, if_pos ⟨hd.1, by omega, hd.2.2⟩]
        · rw [if_neg hd]
          by_cases hd' : 0 ≤ i ∧ i < 6 * ((k : ℤ) + 1) ∧ i % 2 = 0
          · exfalso; omega
          · rw [if_neg hd']

theorem tapeAt_mark {k j : ℕ} (hk : 3 * k ≤ x.length) (hj : j < w.length) :
    Function.update (tapeAt x w k j) (2 * (x.length : ℤ) + 1 + j) (.wm (w.getD j false)) =
      tapeAt x w k (j + 1) := by
  funext i
  simp only [Function.update]
  by_cases h : i = 2 * (x.length : ℤ) + 1 + j
  · subst h; simp only [dite_true]; rw [tapeAt_wm hk j (by omega)]
  · rw [dif_neg h]
    simp only [tapeAt]
    by_cases hd : 0 ≤ i ∧ i < 6 * (k : ℤ) ∧ i % 2 = 0
    · rw [if_pos hd, if_pos hd]
    · rw [if_neg hd, if_neg hd]
      by_cases hw : 2 * (x.length : ℤ) + 1 ≤ i ∧ i < 2 * (x.length : ℤ) + 1 + j
      · rw [if_pos hw, if_pos ⟨hw.1, by push_cast; omega⟩]
      · rw [if_neg hw, if_neg (by push_cast; omega)]

theorem tapeAt_unmark {k c : ℕ} (hk : 3 * k ≤ x.length) (hc : c < w.length) :
    Function.update (tapeAt x w k (c + 1)) (2 * (x.length : ℤ) + 1 + c) (.raw (w.getD c false)) =
      tapeAt x w k c := by
  funext i
  simp only [Function.update]
  by_cases h : i = 2 * (x.length : ℤ) + 1 + c
  · subst h; simp only [dite_true]; rw [tapeAt_wit hk c le_rfl hc]
  · rw [dif_neg h]
    simp only [tapeAt]
    by_cases hd : 0 ≤ i ∧ i < 6 * (k : ℤ) ∧ i % 2 = 0
    · rw [if_pos hd, if_pos hd]
    · rw [if_neg hd, if_neg hd]
      by_cases hw : 2 * (x.length : ℤ) + 1 ≤ i ∧ i < 2 * (x.length : ℤ) + 1 + c
      · rw [if_pos ⟨hw.1, by push_cast; omega⟩, if_pos hw]
      · rw [if_neg (by push_cast; omega), if_neg hw]

end Rounds

/-! ### Phase lemmas -/

section Phases

variable {x w : List Bool}

theorem stepW {q : St} {T : ℤ → Sym} {p : ℤ} {q' : St} {a : Sym} {d : Dir}
    (h : δ q (T p) = some (q', a, d)) :
    satTM.run ⟨q, T, p⟩ 1 = ⟨q', Function.update T p a, p + d.shift⟩ :=
  satTM.run_step (c := ⟨q, T, p⟩) h

theorem stepS {q : St} {T : ℤ → Sym} {p : ℤ} {q' : St} {d : Dir}
    (h : δ q (T p) = some (q', T p, d)) : satTM.run ⟨q, T, p⟩ 1 = ⟨q', T, p + d.shift⟩ :=
  satTM.run_step' h

theorem run_succ' (c : satTM.Cfg) (n : ℕ) : satTM.run c (n + 1) = satTM.run (satTM.run c 1) n := by
  rw [add_comm, run_add]

theorem δ_skipD (fl atB : Bool) (s : Sym) : δ (.skipD fl atB) s = some (.seek fl atB, s, .R) := by
  cases s <;> rfl

theorem δ_toWD (fl p q e : Bool) (s : Sym) : δ (.toWD fl p q e) s = some (.toW fl p q e, s, .R) := by
  cases s <;> rfl

theorem δ_back (fl atB : Bool) (s : Sym) (hs : s ≠ .blank) :
    δ (.back fl atB) s = some (.back fl atB, s, .L) := by
  cases s <;> simp_all [δ]

theorem seek_scan {k j : ℕ} (hk : 3 * k ≤ x.length) (fl atB : Bool) :
    satTM.run ⟨.seek fl atB, tapeAt x w k j, 0⟩ (2 * (3 * k)) =
      ⟨.seek fl atB, tapeAt x w k j, 6 * k⟩ := by
  have := satTM.scan2 (.seek fl atB) (.skipD fl atB) (tapeAt x w k j) 0 (3 * k)
    (fun i hi => by rw [zero_add, tapeAt_done i hi]; rfl)
    (fun i _ => δ_skipD fl atB _)
  rw [this]; congr 1; push_cast; ring

theorem read_slot {k j : ℕ} (hk : 3 * k + 3 ≤ x.length) (fl atB : Bool) :
    satTM.run ⟨.seek fl atB, tapeAt x w k j, 6 * k⟩ 6 =
      ⟨.toW fl (x.getD (3 * k) false) (x.getD (3 * k + 1) false) (x.getD (3 * k + 2) false),
        tapeAt x w (k + 1) j, 6 * k + 6⟩ := by
  set T0 := tapeAt x w k j
  set p := x.getD (3 * k) false
  set q := x.getD (3 * k + 1) false
  set e := x.getD (3 * k + 2) false
  have c0 : T0 (6 * k) = .raw true := by
    rw [show (6 * k : ℤ) = 2 * ((3 * k : ℕ) : ℤ) by push_cast; ring]
    exact tapeAt_tag (3 * k) le_rfl (by omega)
  have c1 : T0 (6 * k + 1) = .raw p := by
    rw [show (6 * k : ℤ) + 1 = 2 * ((3 * k : ℕ) : ℤ) + 1 by push_cast; ring]
    exact tapeAt_data (3 * k) (by omega)
  have c2 : T0 (6 * k + 2) = .raw true := by
    rw [show (6 * k : ℤ) + 2 = 2 * ((3 * k + 1 : ℕ) : ℤ) by push_cast; ring]
    exact tapeAt_tag (3 * k + 1) (by omega) (by omega)
  have c3 : T0 (6 * k + 3) = .raw q := by
    rw [show (6 * k : ℤ) + 3 = 2 * ((3 * k + 1 : ℕ) : ℤ) + 1 by push_cast; ring]
    exact tapeAt_data (3 * k + 1) (by omega)
  have c4 : T0 (6 * k + 4) = .raw true := by
    rw [show (6 * k : ℤ) + 4 = 2 * ((3 * k + 2 : ℕ) : ℤ) by push_cast; ring]
    exact tapeAt_tag (3 * k + 2) (by omega) (by omega)
  have c5 : T0 (6 * k + 5) = .raw e := by
    rw [show (6 * k : ℤ) + 5 = 2 * ((3 * k + 2 : ℕ) : ℤ) + 1 by push_cast; ring]
    exact tapeAt_data (3 * k + 2) (by omega)
  set T1 := Function.update T0 (6 * (k : ℤ)) Sym.done
  set T2 := Function.update T1 (6 * (k : ℤ) + 2) Sym.done
  set T3 := Function.update T2 (6 * (k : ℤ) + 4) Sym.done
  have e1 : satTM.run ⟨.seek fl atB, T0, 6 * k⟩ 1 = ⟨.rdP fl, T1, 6 * k + 1⟩ := by
    rw [stepW (q' := .rdP fl) (a := .done) (d := .R) (by rw [c0]; rfl)]
    simp [Dir.shift, T1]
  have e2 : satTM.run ⟨.rdP fl, T1, 6 * k + 1⟩ 1 = ⟨.t2 fl p, T1, 6 * k + 2⟩ := by
    have : T1 (6 * k + 1) = .raw p := by
      simp only [T1]; rw [Function.update_of_ne (by omega)]; exact c1
    rw [stepS (q' := .t2 fl p) (d := .R) (by rw [this]; rfl)]
    simp [Dir.shift]; ring
  have e3 : satTM.run ⟨.t2 fl p, T1, 6 * k + 2⟩ 1 = ⟨.rdQ fl p, T2, 6 * k + 3⟩ := by
    have : T1 (6 * k + 2) = .raw true := by
      simp only [T1]; rw [Function.update_of_ne (by omega)]; exact c2
    rw [stepW (q' := .rdQ fl p) (a := .done) (d := .R) (by rw [this]; rfl)]
    simp [Dir.shift, T2]; ring
  have e4 : satTM.run ⟨.rdQ fl p, T2, 6 * k + 3⟩ 1 = ⟨.t3 fl p q, T2, 6 * k + 4⟩ := by
    have : T2 (6 * k + 3) = .raw q := by
      simp only [T2, T1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact c3
    rw [stepS (q' := .t3 fl p q) (d := .R) (by rw [this]; rfl)]
    simp [Dir.shift]; ring
  have e5 : satTM.run ⟨.t3 fl p q, T2, 6 * k + 4⟩ 1 = ⟨.rdE fl p q, T3, 6 * k + 5⟩ := by
    have : T2 (6 * k + 4) = .raw true := by
      simp only [T2, T1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact c4
    rw [stepW (q' := .rdE fl p q) (a := .done) (d := .R) (by rw [this]; rfl)]
    simp [Dir.shift, T3]; ring
  have e6 : satTM.run ⟨.rdE fl p q, T3, 6 * k + 5⟩ 1 = ⟨.toW fl p q e, T3, 6 * k + 6⟩ := by
    have : T3 (6 * k + 5) = .raw e := by
      simp only [T3, T2, T1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact c5
    rw [stepS (q' := .toW fl p q e) (d := .R) (by rw [this]; rfl)]
    simp [Dir.shift]; ring
  have hT3 : T3 = tapeAt x w (k + 1) j := tapeAt_next_slot
  rw [run_succ' _ 5, e1, run_succ' _ 4, e2, run_succ' _ 3, e3, run_succ' _ 2, e4,
    run_succ' _ 1, e5, e6, hT3]

theorem toW_scan {k j : ℕ} (hk : 3 * k + 3 ≤ x.length) (fl p q e : Bool) :
    satTM.run ⟨.toW fl p q e, tapeAt x w (k + 1) j, 6 * k + 6⟩ (2 * (x.length - 3 * k - 3) + 1) =
      ⟨.inW fl p q e, tapeAt x w (k + 1) j, 2 * x.length + 1⟩ := by
  have hs := satTM.scan2 (.toW fl p q e) (.toWD fl p q e) (tapeAt x w (k + 1) j) (6 * k + 6)
    (x.length - 3 * k - 3)
    (fun i hi => by
      rw [show (6 * k + 6 : ℤ) + 2 * i = 2 * ((3 * k + 3 + i : ℕ) : ℤ) by push_cast; ring,
        tapeAt_tag (3 * k + 3 + i) (by omega) (by omega)]; rfl)
    (fun i _ => δ_toWD fl p q e _)
  rw [run_add, hs]
  have hpos : (6 * k + 6 : ℤ) + 2 * ((x.length - 3 * k - 3 : ℕ) : ℤ) = 2 * x.length := by
    push_cast [Nat.sub_sub, Nat.cast_sub (show 3 * k + 3 ≤ x.length by omega)]; ring
  rw [hpos]
  rw [stepS (q' := .inW fl p q e) (d := .R) (by rw [tapeAt_term (by omega)]; rfl)]
  simp [Dir.shift]

theorem inW_skip {k j : ℕ} (hk : 3 * (k + 1) ≤ x.length) (fl p q e : Bool) :
    satTM.run ⟨.inW fl p q e, tapeAt x w (k + 1) j, 2 * x.length + 1⟩ j =
      ⟨.inW fl p q e, tapeAt x w (k + 1) j, 2 * x.length + 1 + j⟩ := by
  have := satTM.scan1 (.inW fl p q e) .R (tapeAt x w (k + 1) j) (2 * x.length + 1) j
    (fun i hi => by
      simp only [Dir.shift, mul_one]
      rw [tapeAt_wm hk i hi]; rfl)
  rw [this]; simp [Dir.shift]

theorem back_scan (T : ℤ → Sym) (P : ℕ) (fl atB : Bool)
    (hnb : ∀ i : ℕ, i ≤ P → T i ≠ .blank) (hneg : T (-1) = .blank) :
    satTM.run ⟨.back fl atB, T, P⟩ (P + 1 + 1) = ⟨.seek fl atB, T, 0⟩ := by
  have hs := satTM.scan1 (.back fl atB) .L T P (P + 1)
    (fun i hi => by
      simp only [Dir.shift]
      have : (P : ℤ) + i * (-1) = ((P - i : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : i ≤ P)]; ring
      rw [this]
      exact δ_back fl atB _ (hnb (P - i) (by omega)))
  rw [run_add, hs]
  have : (P : ℤ) + ((P + 1 : ℕ) : ℤ) * Dir.L.shift = -1 := by simp [Dir.shift]
  rw [this, stepS (q' := .seek fl atB) (d := .R) (by rw [hneg]; rfl)]
  simp [Dir.shift]

end Phases

/-! ### Rounds -/

section RoundLemmas

variable {x w : List Bool}

/-- Return scan over `n` nonblank cells `0 … n-1`, ending in `seek` at `0`. -/
theorem back_scan' (T : ℤ → Sym) (n : ℕ) (fl atB : Bool)
    (hnb : ∀ i : ℕ, i < n → T i ≠ .blank) (hneg : T (-1) = .blank) :
    satTM.run ⟨.back fl atB, T, (n : ℤ) - 1⟩ (n + 1) = ⟨.seek fl atB, T, 0⟩ := by
  rcases n with _ | n
  · simp only [CharP.cast_eq_zero, zero_sub, zero_add]
    rw [stepS (q' := .seek fl atB) (d := .R) (by rw [hneg]; rfl)]
    simp [Dir.shift]
  · have := back_scan T n fl atB (fun i hi => hnb i (by omega)) hneg
    rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring]
    exact this

theorem mark_cont {k j : ℕ} (hk : 3 * (k + 1) ≤ x.length) (hj : j < w.length) (fl p q : Bool) :
    satTM.run ⟨.inW fl p q false, tapeAt x w (k + 1) j, 2 * x.length + 1 + j⟩ 1 =
      ⟨.back (fl || lit p q (w.getD j false)) false, tapeAt x w (k + 1) (j + 1),
        2 * x.length + j⟩ := by
  rw [stepW (q' := .back (fl || lit p q (w.getD j false)) false) (a := .wm (w.getD j false))
    (d := .L) (by rw [tapeAt_wit hk j le_rfl hj]; rfl), tapeAt_mark hk hj]
  simp [Dir.shift]; ring

theorem mark_end {k j : ℕ} (hk : 3 * (k + 1) ≤ x.length) (hj : j < w.length) (fl p q : Bool) :
    satTM.run ⟨.inW fl p q true, tapeAt x w (k + 1) j, 2 * x.length + 1 + j⟩ 1 =
      ⟨.chkEnd (fl || lit p q (w.getD j false)), tapeAt x w (k + 1) (j + 1),
        2 * x.length + 2 + j⟩ := by
  rw [stepW (q' := .chkEnd (fl || lit p q (w.getD j false))) (a := .wm (w.getD j false))
    (d := .R) (by rw [tapeAt_wit hk j le_rfl hj]; rfl), tapeAt_mark hk hj]
  simp [Dir.shift]; ring

theorem unmark_loop {k : ℕ} (hk : 3 * (k + 1) ≤ x.length) :
    ∀ c : ℕ, c ≤ w.length →
      satTM.run ⟨.unmark, tapeAt x w (k + 1) c, 2 * x.length + c⟩ c =
        ⟨.unmark, tapeAt x w (k + 1) 0, 2 * x.length⟩ := by
  intro c
  induction c with
  | zero => intro _; simp [run]
  | succ c ih =>
    intro hc
    rw [run_succ' _ c]
    have hpos : (2 * (x.length : ℤ) + ((c + 1 : ℕ) : ℤ)) = 2 * x.length + 1 + c := by
      push_cast; ring
    rw [hpos, stepW (q' := .unmark) (a := .raw (w.getD c false)) (d := .L)
      (by rw [tapeAt_wm hk c (by omega)]; rfl), tapeAt_unmark hk (by omega)]
    have := ih (by omega)
    rw [show 2 * (x.length : ℤ) + 1 + c + Dir.L.shift = 2 * x.length + c by simp [Dir.shift]; ring]
    exact this

/-- Nonblank cells of a round tape. -/
theorem nonblank_upto {k j : ℕ} (hk : 3 * k ≤ x.length) (hj : j ≤ w.length) (n : ℕ)
    (hn : n ≤ 2 * x.length + w.length + 1) :
    ∀ i : ℕ, i < n → tapeAt x w k j i ≠ .blank :=
  fun i hi => tapeAt_nonblank hk hj i (by omega) (by omega)

/-- A continuing round on a non-final slot (`e = false`). -/
theorem round_cont {k j : ℕ} (hk : 3 * k + 3 ≤ x.length) (hj : j < w.length) (fl atB : Bool)
    (he : x.getD (3 * k + 2) false = false) :
    satTM.run ⟨.seek fl atB, tapeAt x w k j, 0⟩ (4 * x.length + 2 * j + 4) =
      ⟨.seek (fl || lit (x.getD (3 * k) false) (x.getD (3 * k + 1) false) (w.getD j false)) false,
        tapeAt x w (k + 1) (j + 1), 0⟩ := by
  set p := x.getD (3 * k) false
  set q := x.getD (3 * k + 1) false
  have hk1 : 3 * (k + 1) ≤ x.length := by omega
  rw [show 4 * x.length + 2 * j + 4 =
      2 * (3 * k) + (6 + ((2 * (x.length - 3 * k - 3) + 1) + (j + (1 + (2 * x.length + j + 1 + 1)))))
      by omega]
  rw [run_add, seek_scan (by omega), run_add, read_slot hk, he, run_add, toW_scan hk,
    run_add, inW_skip hk1, run_add, mark_cont hk1 hj]
  have hb := back_scan' (tapeAt x w (k + 1) (j + 1)) (2 * x.length + j + 1)
    (fl || lit p q (w.getD j false)) false
    (nonblank_upto hk1 (by omega) _ (by omega)) tapeAt_neg
  rw [show ((2 * x.length + j + 1 : ℕ) : ℤ) - 1 = 2 * x.length + j by push_cast; ring] at hb
  exact hb

/-- A continuing round on a clause-final slot whose checks pass. -/
theorem round_end {k j : ℕ} (hk : 3 * k + 3 ≤ x.length) (hj : j + 1 = w.length) (fl atB : Bool)
    (he : x.getD (3 * k + 2) false = true)
    (hf : (fl || lit (x.getD (3 * k) false) (x.getD (3 * k + 1) false) (w.getD j false)) = true) :
    satTM.run ⟨.seek fl atB, tapeAt x w k j, 0⟩ (4 * x.length + 2 * j + 6) =
      ⟨.seek false true, tapeAt x w (k + 1) 0, 0⟩ := by
  have hk1 : 3 * (k + 1) ≤ x.length := by omega
  rw [show 4 * x.length + 2 * j + 6 =
      2 * (3 * k) + (6 + ((2 * (x.length - 3 * k - 3) + 1) +
        (j + (1 + (1 + ((j + 1) + (1 + (2 * x.length + 1))))))))
      by omega]
  rw [run_add, seek_scan (by omega), run_add, read_slot hk, he, run_add, toW_scan hk,
    run_add, inW_skip hk1, run_add, mark_end hk1 (by omega), hf]
  have hblank : tapeAt x w (k + 1) (j + 1) (2 * x.length + 2 + j) = .blank := by
    rw [show (2 * (x.length : ℤ) + 2 + j) = 2 * x.length + 1 + w.length by push_cast; omega]
    exact tapeAt_end hk1 (by omega)
  rw [run_add, stepS (q' := .unmark) (d := .L) (by rw [hblank]; rfl)]
  rw [show (2 * (x.length : ℤ) + 2 + j + Dir.L.shift) = 2 * x.length + ((j + 1 : ℕ) : ℤ) by
    simp [Dir.shift]; ring]
  rw [run_add, unmark_loop hk1 (j + 1) (by omega)]
  rw [run_add, stepS (q' := .back false true) (d := .L) (by rw [tapeAt_term hk1]; rfl)]
  have hb := back_scan' (tapeAt x w (k + 1) 0) (2 * x.length) false true
    (nonblank_upto hk1 (by omega) _ (by omega)) tapeAt_neg
  rw [show (2 * (x.length : ℤ) + Dir.L.shift) = ((2 * x.length : ℕ) : ℤ) - 1 by
    simp [Dir.shift]; ring]
  exact hb

theorem ans_state (q : St) (T : ℤ → Sym) (h : ℤ) :
    satTM.ans ⟨q, T, h⟩ = if q = .yes then some true else if q = .no then some false else none := by
  simp only [TM.ans, answerOf]
  by_cases h1 : q = .yes
  · subst h1; simp
  · by_cases h2 : q = .no
    · subst h2; simp
    · simp [h1, h2]

/-- Prefix of a round up to the witness cell. -/
theorem round_prefix {k j : ℕ} (hk : 3 * k + 3 ≤ x.length) (fl atB : Bool) :
    satTM.run ⟨.seek fl atB, tapeAt x w k j, 0⟩
        (2 * (3 * k) + (6 + ((2 * (x.length - 3 * k - 3) + 1) + j))) =
      ⟨.inW fl (x.getD (3 * k) false) (x.getD (3 * k + 1) false) (x.getD (3 * k + 2) false),
        tapeAt x w (k + 1) j, 2 * x.length + 1 + j⟩ := by
  rw [run_add, seek_scan (by omega), run_add, read_slot hk, run_add, toW_scan hk,
    inW_skip (by omega)]

theorem drop_cons3 (n : ℕ) (h : n + 3 ≤ x.length) :
    x.drop n = x.getD n false :: x.getD (n + 1) false :: x.getD (n + 2) false :: x.drop (n + 3) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp [List.getD_eq_getElem, h, show n < x.length by omega, show n + 1 < x.length by omega,
    show n + 2 < x.length by omega]

theorem chk_cons3 (p q e : Bool) (rest : List Bool) (j : ℕ) (fl atB : Bool) :
    chkFrom w (p :: q :: e :: rest) j fl atB =
      if j < w.length then
        (if e then (decide (j + 1 = w.length) && (fl || lit p q (w.getD j false))) &&
          chkFrom w rest 0 false true
        else chkFrom w rest (j + 1) (fl || lit p q (w.getD j false)) false)
      else false := rfl

/-- **Round induction**: from the start of round `k` the machine answers
exactly `chkFrom w (x.drop (3k)) j fl atB`. -/
theorem rounds : ∀ (r k j : ℕ) (fl atB : Bool), x.length = 3 * k + r → j ≤ w.length →
    ∃ N, 0 < N ∧ N ≤ (r + 1) * (2 * (pair x w).length + 6) ∧
      satTM.ans (satTM.run ⟨.seek fl atB, tapeAt x w k j, 0⟩ N) =
        some (chkFrom w (x.drop (3 * k)) j fl atB) ∧
      satTM.ans (satTM.run ⟨.seek fl atB, tapeAt x w k j, 0⟩ (N - 1)) = none := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro k j fl atB hX hj
  have hy := pair_length x w
  rcases r with _ | _ | _ | r
  · -- end of the formula
    have hd : x.drop (3 * k) = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨2 * (3 * k) + 1, by omega, by nlinarith, ?_, ?_⟩
    · rw [run_add, seek_scan (by omega), hd]
      have hterm : tapeAt x w k j (6 * k) = .raw false := by
        rw [show (6 * k : ℤ) = 2 * x.length by push_cast; omega]; exact tapeAt_term (by omega)
      rw [stepS (q' := if atB then .yes else .no) (d := .S) (by rw [hterm]; rfl), ans_state]
      cases atB <;> simp [chkFrom]
    · rw [show 2 * (3 * k) + 1 - 1 = 2 * (3 * k) by omega, seek_scan (by omega), ans_state]
      simp
  · -- one trailing bit
    obtain ⟨a, ha⟩ : ∃ a, x.drop (3 * k) = [a] := List.length_eq_one_iff.1 (by simp; omega)
    have c0 : tapeAt x w k j (6 * k) = .raw true := by
      rw [show (6 * k : ℤ) = 2 * ((3 * k : ℕ) : ℤ) by push_cast; ring]
      exact tapeAt_tag (3 * k) le_rfl (by omega)
    have c1 : tapeAt x w k j (6 * k + 1) = .raw (x.getD (3 * k) false) := by
      rw [show (6 * k : ℤ) + 1 = 2 * ((3 * k : ℕ) : ℤ) + 1 by push_cast; ring]
      exact tapeAt_data (3 * k) (by omega)
    have c2 : tapeAt x w k j (6 * k + 2) = .raw false := by
      rw [show (6 * k : ℤ) + 2 = 2 * x.length by push_cast; omega]; exact tapeAt_term (by omega)
    set T1 := Function.update (tapeAt x w k j) (6 * (k : ℤ)) Sym.done
    have s1 : satTM.run ⟨.seek fl atB, tapeAt x w k j, 6 * k⟩ 1 = ⟨.rdP fl, T1, 6 * k + 1⟩ := by
      rw [stepW (q' := .rdP fl) (a := .done) (d := .R) (by rw [c0]; rfl)]; simp [Dir.shift, T1]
    have s2 : satTM.run ⟨.rdP fl, T1, 6 * k + 1⟩ 1 = ⟨.t2 fl (x.getD (3 * k) false), T1, 6 * k + 2⟩ := by
      have : T1 (6 * k + 1) = .raw (x.getD (3 * k) false) := by
        simp only [T1]; rw [Function.update_of_ne (by omega)]; exact c1
      rw [stepS (q' := .t2 fl (x.getD (3 * k) false)) (d := .R) (by rw [this]; rfl)]
      simp [Dir.shift]; ring
    have hT1 : T1 (6 * k + 2) = .raw false := by
      simp only [T1]; rw [Function.update_of_ne (by omega)]; exact c2
    refine ⟨2 * (3 * k) + 3, by omega, by nlinarith, ?_, ?_⟩
    · rw [show 2 * (3 * k) + 3 = 2 * (3 * k) + (1 + 1 + 1) by ring, run_add, seek_scan (by omega),
        run_add, run_add, s1, s2, stepS (q' := .no) (d := .S) (by rw [hT1]; rfl), ans_state, ha]
      simp [chkFrom]
    · rw [show 2 * (3 * k) + 3 - 1 = 2 * (3 * k) + (1 + 1) by omega, run_add, seek_scan (by omega),
        run_add, s1, s2, ans_state]
      simp
  · -- two trailing bits
    obtain ⟨a, b, hab⟩ : ∃ a b, x.drop (3 * k) = [a, b] :=
      List.length_eq_two.1 (by simp; omega)
    have c0 : tapeAt x w k j (6 * k) = .raw true := by
      rw [show (6 * k : ℤ) = 2 * ((3 * k : ℕ) : ℤ) by push_cast; ring]
      exact tapeAt_tag (3 * k) le_rfl (by omega)
    have c1 : tapeAt x w k j (6 * k + 1) = .raw (x.getD (3 * k) false) := by
      rw [show (6 * k : ℤ) + 1 = 2 * ((3 * k : ℕ) : ℤ) + 1 by push_cast; ring]
      exact tapeAt_data (3 * k) (by omega)
    have c2 : tapeAt x w k j (6 * k + 2) = .raw true := by
      rw [show (6 * k : ℤ) + 2 = 2 * ((3 * k + 1 : ℕ) : ℤ) by push_cast; ring]
      exact tapeAt_tag (3 * k + 1) (by omega) (by omega)
    have c3 : tapeAt x w k j (6 * k + 3) = .raw (x.getD (3 * k + 1) false) := by
      rw [show (6 * k : ℤ) + 3 = 2 * ((3 * k + 1 : ℕ) : ℤ) + 1 by push_cast; ring]
      exact tapeAt_data (3 * k + 1) (by omega)
    have c4 : tapeAt x w k j (6 * k + 4) = .raw false := by
      rw [show (6 * k : ℤ) + 4 = 2 * x.length by push_cast; omega]; exact tapeAt_term (by omega)
    set p := x.getD (3 * k) false
    set q := x.getD (3 * k + 1) false
    set T1 := Function.update (tapeAt x w k j) (6 * (k : ℤ)) Sym.done
    set T2 := Function.update T1 (6 * (k : ℤ) + 2) Sym.done
    have s1 : satTM.run ⟨.seek fl atB, tapeAt x w k j, 6 * k⟩ 1 = ⟨.rdP fl, T1, 6 * k + 1⟩ := by
      rw [stepW (q' := .rdP fl) (a := .done) (d := .R) (by rw [c0]; rfl)]; simp [Dir.shift, T1]
    have s2 : satTM.run ⟨.rdP fl, T1, 6 * k + 1⟩ 1 = ⟨.t2 fl p, T1, 6 * k + 2⟩ := by
      have : T1 (6 * k + 1) = .raw p := by
        simp only [T1]; rw [Function.update_of_ne (by omega)]; exact c1
      rw [stepS (q' := .t2 fl p) (d := .R) (by rw [this]; rfl)]; simp [Dir.shift]; ring
    have s3 : satTM.run ⟨.t2 fl p, T1, 6 * k + 2⟩ 1 = ⟨.rdQ fl p, T2, 6 * k + 3⟩ := by
      have : T1 (6 * k + 2) = .raw true := by
        simp only [T1]; rw [Function.update_of_ne (by omega)]; exact c2
      rw [stepW (q' := .rdQ fl p) (a := .done) (d := .R) (by rw [this]; rfl)]
      simp [Dir.shift, T2]; ring
    have s4 : satTM.run ⟨.rdQ fl p, T2, 6 * k + 3⟩ 1 = ⟨.t3 fl p q, T2, 6 * k + 4⟩ := by
      have : T2 (6 * k + 3) = .raw q := by
        simp only [T2, T1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact c3
      rw [stepS (q' := .t3 fl p q) (d := .R) (by rw [this]; rfl)]; simp [Dir.shift]; ring
    have hT2 : T2 (6 * k + 4) = .raw false := by
      simp only [T2, T1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact c4
    refine ⟨2 * (3 * k) + 5, by omega, by nlinarith, ?_, ?_⟩
    · rw [show 2 * (3 * k) + 5 = 2 * (3 * k) + (1 + 1 + 1 + 1 + 1) by ring, run_add,
        seek_scan (by omega), run_add, run_add, run_add, run_add, s1, s2, s3, s4,
        stepS (q' := .no) (d := .S) (by rw [hT2]; rfl), ans_state, hab]
      simp [chkFrom]
    · rw [show 2 * (3 * k) + 5 - 1 = 2 * (3 * k) + (1 + 1 + 1 + 1) by omega, run_add,
        seek_scan (by omega), run_add, run_add, run_add, s1, s2, s3, s4, ans_state]
      simp
  · -- a complete slot
    have hk : 3 * k + 3 ≤ x.length := by omega
    have hpre := round_prefix (x := x) (w := w) (j := j) hk fl atB
    have hd := drop_cons3 (x := x) (3 * k) hk
    rw [show 3 * k + 3 = 3 * (k + 1) by ring] at hd
    set p := x.getD (3 * k) false
    set q := x.getD (3 * k + 1) false
    set e := x.getD (3 * k + 2) false with he_def
    rw [hd]
    set R0 := 2 * (3 * k) + (6 + ((2 * (x.length - 3 * k - 3) + 1) + j))
    have hR0 : R0 = 2 * x.length + j + 1 := by simp only [R0]; omega
    by_cases hjW : j < w.length
    · by_cases he : e = true
      · by_cases hW : j + 1 = w.length
        · by_cases hf : (fl || lit p q (w.getD j false)) = true
          · -- clause closes successfully
            obtain ⟨N', hN'0, hN'b, hN'a, hN'p⟩ :=
              ih r (by omega) (k + 1) 0 false true (by omega) (by omega)
            have hround := round_end hk hW fl atB he hf
            refine ⟨(4 * x.length + 2 * j + 6) + N', by omega, ?_, ?_, ?_⟩
            · have : 4 * x.length + 2 * j + 6 ≤ 2 * (pair x w).length + 6 := by omega
              nlinarith
            · rw [run_add, hround, hN'a, chk_cons3, if_pos hjW, if_pos he, hf]
              simp [hW]
            · rw [show 4 * x.length + 2 * j + 6 + N' - 1 = (4 * x.length + 2 * j + 6) + (N' - 1) by
                omega, run_add, hround, hN'p]
          · -- clause unsatisfied
            have hf' : (fl || lit p q (w.getD j false)) = false := by simpa using hf
            have hblank : tapeAt x w (k + 1) (j + 1) (2 * x.length + 2 + j) = .blank := by
              rw [show (2 * (x.length : ℤ) + 2 + j) = 2 * x.length + 1 + w.length by push_cast; omega]
              exact tapeAt_end (by omega) (by omega)
            have hm := mark_end (x := x) (w := w) (k := k) (by omega) hjW fl p q
            refine ⟨R0 + 1 + 1, by omega, by nlinarith, ?_, ?_⟩
            · rw [run_add, run_add, hpre, he, hm, hf',
                stepS (q' := .no) (d := .S) (by rw [hblank]; rfl), ans_state, chk_cons3,
                if_pos hjW, if_pos rfl, hf']
              simp
            · rw [show R0 + 1 + 1 - 1 = R0 + 1 by omega, run_add, hpre, he, hm, ans_state]
              simp
        · -- clause shorter than the witness
          have hlt : j + 1 < w.length := by omega
          have hraw : tapeAt x w (k + 1) (j + 1) (2 * x.length + 2 + j) =
              .raw (w.getD (j + 1) false) := by
            rw [show (2 * (x.length : ℤ) + 2 + j) = 2 * x.length + 1 + ((j + 1 : ℕ) : ℤ) by
              push_cast; ring]
            exact tapeAt_wit (by omega) (j + 1) le_rfl hlt
          have hm := mark_end (x := x) (w := w) (k := k) (by omega) hjW fl p q
          refine ⟨R0 + 1 + 1, by omega, by nlinarith, ?_, ?_⟩
          · rw [run_add, run_add, hpre, he, hm,
              stepS (q' := .no) (d := .S) (by rw [hraw]; rfl), ans_state, chk_cons3,
              if_pos hjW, if_pos rfl]
            simp [hW]
          · rw [show R0 + 1 + 1 - 1 = R0 + 1 by omega, run_add, hpre, he, hm, ans_state]
            simp
      · -- non-final slot: continue
        have he' : e = false := by simpa using he
        obtain ⟨N', hN'0, hN'b, hN'a, hN'p⟩ :=
          ih r (by omega) (k + 1) (j + 1) (fl || lit p q (w.getD j false)) false (by omega)
            (by omega)
        have hround := round_cont (x := x) (w := w) hk hjW fl atB he'
        refine ⟨(4 * x.length + 2 * j + 4) + N', by omega, ?_, ?_, ?_⟩
        · have : 4 * x.length + 2 * j + 4 ≤ 2 * (pair x w).length + 6 := by omega
          nlinarith
        · rw [run_add, hround, hN'a, chk_cons3, if_pos hjW, if_neg (by simp [he'])]
        · rw [show 4 * x.length + 2 * j + 4 + N' - 1 = (4 * x.length + 2 * j + 4) + (N' - 1) by
            omega, run_add, hround, hN'p]
    · -- clause longer than the witness
      have hjW' : j = w.length := by omega
      have hblank : tapeAt x w (k + 1) j (2 * x.length + 1 + j) = .blank := by
        rw [hjW']; exact tapeAt_end (by omega) le_rfl
      refine ⟨R0 + 1, by omega, by nlinarith, ?_, ?_⟩
      · rw [run_add, hpre, stepS (q' := .no) (d := .S) (by rw [hblank]; rfl), ans_state,
          chk_cons3, if_neg hjW]
        simp
      · rw [show R0 + 1 - 1 = R0 by omega, hpre, ans_state]
        simp

end RoundLemmas

/-! ### Parsing and the decision theorem -/

section Decision

theorem parse_ok (x w : List Bool) :
    satTM.run (satTM.init (pair x w)) (4 * x.length + 2) =
      ⟨.seek false true, tapeAt x w 0 0, 0⟩ := by
  have hl := pair_length x w
  have hinit : satTM.init (pair x w) = ⟨.P0, satTM.inputTape (pair x w), 0⟩ := rfl
  have hs := satTM.scan2 .P0 .P1 (satTM.inputTape (pair x w)) 0 x.length
    (fun i hi => by rw [zero_add, tape_tag x w i hi]; rfl)
    (fun i hi => by rw [zero_add, tape_data x w i hi]; rfl)
  rw [hinit, show 4 * x.length + 2 = 2 * x.length + (1 + (2 * x.length + 1)) by ring, run_add, hs,
    zero_add, run_add, stepS (q' := .back false true) (d := .L) (by rw [tape_term]; rfl)]
  have hb := back_scan' (satTM.inputTape (pair x w)) (2 * x.length) false true
    (fun i hi => by
      simp only [inputTape]; rw [if_pos ⟨by omega, by omega⟩]; simp)
    (tape_out x w _ (Or.inl (by omega)))
  rw [show (2 * (x.length : ℤ) + Dir.L.shift) = ((2 * x.length : ℕ) : ℤ) - 1 by
    simp [Dir.shift]; ring, hb, tapeAt_zero]

theorem parse_bad : ∀ (ys : List Bool) (T : ℤ → Sym) (p : ℤ),
    (∀ i : ℕ, i < ys.length → T (p + i) = .raw (ys.getD i false)) →
    T (p + ys.length) = .blank → (∀ x w, ys ≠ pair x w) →
    ∃ m, 0 < m ∧ m ≤ ys.length + 1 ∧ (satTM.run ⟨.P0, T, p⟩ m).q = .no ∧
      satTM.ans (satTM.run ⟨.P0, T, p⟩ (m - 1)) = none
  | [], T, p, _, hb, _ => by
    simp only [List.length_nil, CharP.cast_eq_zero, add_zero] at hb
    refine ⟨1, by omega, by simp, ?_, ?_⟩
    · rw [stepS (q' := .no) (d := .S) (by rw [hb]; rfl)]
    · simp [run, ans_state]
  | false :: w, _, _, _, _, hbad => absurd (show false :: w = pair [] w by simp [pair]) (hbad [] w)
  | [true], T, p, hT, hb, _ => by
    have h0 : T p = .raw true := by simpa using hT 0 (by simp)
    have h1 : T (p + 1) = .blank := by simpa using hb
    have one : satTM.run ⟨.P0, T, p⟩ 1 = ⟨.P1, T, p + 1⟩ := by
      rw [stepS (q' := .P1) (d := .R) (by rw [h0]; rfl)]; simp [Dir.shift]
    refine ⟨2, by omega, by simp, ?_, ?_⟩
    · rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, one, stepS (q' := .no) (d := .S) (by rw [h1]; rfl)]
    · rw [show 2 - 1 = 1 from rfl, one, ans_state]; simp
  | true :: b :: rest, T, p, hT, hb, hbad => by
    have h0 : T p = .raw true := by simpa using hT 0 (by simp)
    have h1 : T (p + 1) = .raw b := by simpa using hT 1 (by simp)
    have hT' : ∀ i : ℕ, i < rest.length → T (p + 2 + i) = .raw (rest.getD i false) := by
      intro i hi
      have := hT (i + 2) (by simp; omega)
      rw [show p + ((i + 2 : ℕ) : ℤ) = p + 2 + i by push_cast; ring] at this
      simpa using this
    have hb' : T (p + 2 + rest.length) = .blank := by
      rw [← hb]; congr 1; simp; ring
    have hbad' : ∀ x w, rest ≠ pair x w := fun x w h => hbad (b :: x) w (by simp [pair, h])
    obtain ⟨m, hm0, hm, hq, hans⟩ := parse_bad rest T (p + 2) hT' hb' hbad'
    have one : satTM.run ⟨.P0, T, p⟩ 1 = ⟨.P1, T, p + 1⟩ := by
      rw [stepS (q' := .P1) (d := .R) (by rw [h0]; rfl)]; simp [Dir.shift]
    have one' : satTM.run ⟨.P1, T, p + 1⟩ 1 = ⟨.P0, T, p + 2⟩ := by
      rw [stepS (q' := .P0) (d := .R) (by rw [h1]; rfl)]; simp [Dir.shift]; ring
    have two : satTM.run ⟨.P0, T, p⟩ 2 = ⟨.P0, T, p + 2⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, one, one']
    refine ⟨2 + m, by omega, by simp; omega, by rw [run_add, two]; exact hq, ?_⟩
    rw [show 2 + m - 1 = 2 + (m - 1) by omega, run_add, two]; exact hans

/-- **The SAT verifier decides `V_SAT` in time `2(N+3)²`.** -/
theorem satTM_decides : satTM.Decides V_SAT (fun N => 2 * (N + 3) ^ 2) := by
  intro y
  by_cases hy : ∃ x w, y = pair x w
  · obtain ⟨x, w, rfl⟩ := hy
    have hl := pair_length x w
    obtain ⟨N, hN0, hNb, hNa, hNp⟩ :=
      rounds (x := x) (w := w) x.length 0 0 false true (by simp) (by omega)
    rw [show x.drop (3 * 0) = x by simp] at hNa
    refine ⟨chkFrom w x 0 false true, ⟨(4 * x.length + 2) + N, ?_, ?_, ?_⟩, ?_⟩
    · show _ ≤ 2 * ((pair x w).length + 3) ^ 2
      nlinarith
    · simp only [out]; rw [run_add, parse_ok]; exact hNa
    · apply satTM.none_before halting
      intro _
      rw [show 4 * x.length + 2 + N - 1 = (4 * x.length + 2) + (N - 1) by omega, run_add,
        parse_ok]
      exact hNp
    · constructor
      · intro h; exact ⟨x, w, rfl, h⟩
      · rintro ⟨x', w', heq, h⟩
        obtain ⟨rfl, rfl⟩ := pair_injective heq
        exact h
  · have hbad : ∀ x w, y ≠ pair x w := fun x w h => hy ⟨x, w, h⟩
    obtain ⟨m, hm0, hm, hq, hans⟩ := parse_bad y (satTM.inputTape y) 0
      (fun i hi => by
        simp only [inputTape, zero_add]; rw [if_pos ⟨by omega, by exact_mod_cast hi⟩]; simp)
      (by simp only [inputTape, zero_add]; rw [if_neg (by omega)])
      hbad
    refine ⟨false, ⟨m, ?_, ?_, ?_⟩, ?_⟩
    · show m ≤ 2 * (y.length + 3) ^ 2
      nlinarith
    · simp only [out]
      show satTM.ans (satTM.run ⟨.P0, _, 0⟩ m) = _
      rcases hrun : satTM.run ⟨.P0, satTM.inputTape y, 0⟩ m with ⟨q, T, h⟩
      rw [hrun] at hq; simp only at hq; subst hq
      rw [ans_state]; simp
    · apply satTM.none_before halting
      intro _
      exact hans
    · simp only [Bool.false_eq_true, false_iff, V_SAT, Set.mem_setOf_eq, not_exists, not_and]
      intro x w h; exact absurd h (hbad x w)

/-- **Part III `prop:assignment-P`**: verifying a supplied assignment is in `P_TM`. -/
theorem V_SAT_mem_P_TM : V_SAT ∈ P_TM := by
  refine ⟨satTM, 2 * (Polynomial.X + 3) ^ 2, ?_⟩
  have heq : (fun n : ℕ => (2 * (Polynomial.X + 3) ^ 2 : Polynomial ℕ).eval n) =
      (fun n => 2 * (n + 3) ^ 2) := by funext n; simp
  rw [heq]; exact satTM_decides

/-- **Dense CNF-SAT is in `NP_TM`** (witness = assignment, `|w| ≤ |x|`). -/
theorem SAT_dense_mem_NP_TM : SAT_dense ∈ NP_TM := by
  refine ⟨V_SAT, V_SAT_mem_P_TM, Polynomial.X, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨w, hw, hc⟩
    exact ⟨w, by simpa using hw, x, w, rfl, hc⟩
  · rintro ⟨w, hw, x', w', heq, hc⟩
    obtain ⟨hx, hw'⟩ := pair_injective heq
    subst hx; subst hw'
    exact ⟨w, by simpa using hw, hc⟩

theorem SAT_dense_mem_NP_WCC : SAT_dense ∈ NP_WCC := by
  rw [NP_WCC_eq_NP_TM]; exact SAT_dense_mem_NP_TM

end Decision

/-! ### Semantics: dense encodings of Part I CNF formulas -/

section Semantics

open PVNP.PartI

/-- The three bits of slot `j` of clause `c` over variables `0 … n-1`. -/
def slotBits (n : ℕ) (c : Clause) (j : ℕ) : List Bool :=
  [decide ((j, true) ∈ c), decide ((j, false) ∈ c), decide (j + 1 = n)]

/-- Dense encoding of one clause. -/
def encClause (n : ℕ) (c : Clause) : List Bool := (List.range n).flatMap (slotBits n c)

/-- **Dense encoding of a Part I CNF formula** over variables `0 … n-1`. -/
def encDense (n : ℕ) (F : Formula) : List Bool := F.flatMap (encClause n)

/-- Literal value of slot `i` of clause `c` under `a`. -/
def slotLit (c : Clause) (a : ℕ → Bool) (i : ℕ) : Bool :=
  lit (decide ((i, true) ∈ c)) (decide ((i, false) ∈ c)) (a i)

theorem chk_clause (w : List Bool) (n : ℕ) (c : Clause) (rest : List Bool) (hw : w.length = n) :
    ∀ d j fl atB, j + (d + 1) = n →
      chkFrom w ((List.range' j (d + 1)).flatMap (slotBits n c) ++ rest) j fl atB =
        ((fl || (List.range' j (d + 1)).any (slotLit c (fun i => w.getD i false))) &&
          chkFrom w rest 0 false true) := by
  intro d
  induction d with
  | zero =>
    intro j fl atB hj
    simp only [zero_add, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      slotBits, List.cons_append, List.nil_append]
    rw [chk_cons3, if_pos (by omega), if_pos (by simp; omega)]
    simp [slotLit, show j + 1 = w.length by omega]
  | succ d ih =>
    intro j fl atB hj
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    simp only [slotBits, List.cons_append, List.nil_append]
    rw [chk_cons3, if_pos (by omega), if_neg (by simp; omega), ih (j + 1) _ false (by omega)]
    simp [List.any_cons, slotLit, Bool.or_assoc]

theorem evalClause_eq_any (a : ℕ → Bool) (c : Clause) : evalClause a c = c.any (evalLiteral a) := by
  induction c with
  | nil => rfl
  | cons l c ih => simp [evalClause, ih]

theorem any_slotLit (a : ℕ → Bool) (c : Clause) (n : ℕ) (hc : ∀ l ∈ c, l.1 < n) :
    (List.range n).any (slotLit c a) = evalClause a c := by
  rw [evalClause_eq_any]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, -, h⟩
    simp only [slotLit, lit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨(i, true), h1, by simp [evalLiteral, literalTrue, h2]⟩
    · exact ⟨(i, false), h1, by simp [evalLiteral, literalTrue, h2]⟩
  · rintro ⟨⟨v, pos⟩, hl, h⟩
    refine ⟨v, hc _ hl, ?_⟩
    cases pos <;> cases hv : a v <;> simp_all [evalLiteral, literalTrue, slotLit, lit]

theorem chk_formula (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length = n) :
    ∀ F : Formula, (∀ c ∈ F, ∀ l ∈ c, l.1 < n) →
      chkFrom w (encDense n F) 0 false true = evalFormula (fun i => w.getD i false) F := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro F
  induction F with
  | nil => intro _; rfl
  | cons c F ih =>
    intro hF
    simp only [encDense, List.flatMap_cons] at ih ⊢
    have hcl := chk_clause w (m + 1) c (F.flatMap (encClause (m + 1))) hw m 0 false true (by omega)
    rw [encClause, List.range_eq_range', hcl, ← List.range_eq_range',
      any_slotLit _ c (m + 1) (hF c (by simp)), ih (fun c' hc' => hF c' (by simp [hc']))]
    simp [evalFormula]

theorem chk_clause_len (w : List Bool) (n : ℕ) (c : Clause) (rest : List Bool) :
    ∀ d j fl atB, j + (d + 1) = n →
      chkFrom w ((List.range' j (d + 1)).flatMap (slotBits n c) ++ rest) j fl atB = true →
        w.length = n := by
  intro d
  induction d with
  | zero =>
    intro j fl atB hj h
    simp only [zero_add, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      slotBits, List.cons_append, List.nil_append] at h
    rw [chk_cons3] at h
    split_ifs at h with h1 h2
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
    · simp at h2; omega
  | succ d ih =>
    intro j fl atB hj h
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc] at h
    simp only [slotBits, List.cons_append, List.nil_append] at h
    rw [chk_cons3] at h
    split_ifs at h with h1 h2
    · simp at h2; omega
    · exact ih (j + 1) _ false (by omega) h

theorem evalLiteral_congr (a b : ℕ → Bool) (l : Literal) (h : a l.1 = b l.1) :
    evalLiteral a l = evalLiteral b l := by simp [evalLiteral, h]

theorem evalClause_congr (a b : ℕ → Bool) (n : ℕ) (hab : ∀ i < n, a i = b i) :
    ∀ c : Clause, (∀ l ∈ c, l.1 < n) → evalClause a c = evalClause b c := by
  intro c
  induction c with
  | nil => intro _; rfl
  | cons l c ih =>
    intro hc
    simp only [evalClause]
    rw [evalLiteral_congr a b l (hab _ (hc l (by simp))), ih (fun l' hl' => hc l' (by simp [hl']))]

theorem evalFormula_congr (a b : ℕ → Bool) (n : ℕ) (hab : ∀ i < n, a i = b i) :
    ∀ F : Formula, (∀ c ∈ F, ∀ l ∈ c, l.1 < n) → evalFormula a F = evalFormula b F := by
  intro F
  induction F with
  | nil => intro _; rfl
  | cons c F ih =>
    intro hF
    simp only [evalFormula]
    rw [evalClause_congr a b n hab c (hF c (by simp)), ih (fun c' hc' => hF c' (by simp [hc']))]

theorem encClause_length (n : ℕ) (c : Clause) : (encClause n c).length = 3 * n := by
  induction n with
  | zero => simp [encClause]
  | succ n ih =>
    have : encClause (n + 1) c = (List.range n).flatMap (slotBits (n + 1) c) ++ slotBits (n + 1) c n := by
      simp [encClause, List.range_succ, List.flatMap_append]
    rw [this, List.length_append]
    have h2 : ((List.range n).flatMap (slotBits (n + 1) c)).length = 3 * n := by
      rw [List.length_flatMap]
      have : ∀ j, (slotBits (n + 1) c j).length = 3 := fun j => rfl
      simp [this, List.sum_replicate, mul_comm]
    rw [h2]; simp [slotBits]; ring

/-- **The dense language is CNF-SAT**: for every Part I formula with
variables `< n` (`n ≥ 1`), its dense encoding is in `SAT_dense` iff the
formula is satisfiable. -/
theorem encDense_mem_SAT_iff (n : ℕ) (hn : 1 ≤ n) (F : Formula)
    (hF : ∀ c ∈ F, ∀ l ∈ c, l.1 < n) : encDense n F ∈ SAT_dense ↔ satisfiable F := by
  constructor
  · rintro ⟨w, -, hc⟩
    rcases F with _ | ⟨c, F'⟩
    · exact ⟨fun _ => false, rfl⟩
    · have hlen : w.length = n := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [encDense, List.flatMap_cons] at hc
        rw [encClause, List.range_eq_range'] at hc
        exact chk_clause_len w (m + 1) c _ m 0 false true (by omega) hc
      rw [chk_formula w n hn hlen _ hF] at hc
      exact ⟨_, hc⟩
  · rintro ⟨a, ha⟩
    rcases F with _ | ⟨c, F'⟩
    · exact ⟨[], by simp, rfl⟩
    · set w := (List.range n).map a
      have hlen : w.length = n := by simp [w]
      have hget : ∀ i < n, w.getD i false = a i := by
        intro i hi; simp [w, List.getD_eq_getElem, hi]
      refine ⟨w, ?_, ?_⟩
      · simp only [encDense, List.flatMap_cons, List.length_append, encClause_length]; omega
      · rw [chk_formula w n hn hlen _ hF,
          evalFormula_congr (fun i => w.getD i false) a n hget _ hF]
        exact ha

/-- **Transfer for SAT.** A superpolynomial discrete-curvature lower bound
for dense SAT would prove classical `P_TM ≠ NP_TM`. -/
theorem SAT_curvature_transfer (h : SAT_dense ∉ P_curvRail) : P_TM ≠ NP_TM :=
  curvature_lower_bound_is_classical SAT_dense SAT_dense_mem_NP_TM h

end Semantics

end PVNP.Discrete.SATV
