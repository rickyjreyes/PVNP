import PVNP.TwoPhasePolynomialWriter

/-!
# II-10: instruction-level execution of the original polynomial writers

`TwoPhasePolynomialWriter.build` turns an instruction array into a single-tape machine. This
file proves what that machine does, one instruction at a time, counting actual `MTM.step`
transitions.

After the normalization phase the tape has the left-end sentinel on cell `−1`, work cells on
`[0, len)` and blanks elsewhere (`tapeOf`). Every instruction is executed by a rightward scan
from cell `0` followed by a return to the sentinel:

* `ret_walk`: the return scan;
* `exec_copy`, `exec_take_hit`, `exec_take_miss`, `exec_inc_in`, `exec_inc_end`, `exec_emit_in`,
  `exec_emit_end`, `exec_next_hit`, `exec_next_miss`, `exec_head`: one instruction each, with its
  exact transition count;
* `exec_finish`: the final scan, which turns the output track into input symbols, writes the
  terminating blank and enters the halting state for the first time.

`Steps` records the reached configuration together with the fact that no earlier configuration
is halting, which is what `MTM.FirstHalt` needs.
-/

namespace PVNP.TwoPhasePolynomialWriter

open PartIITuring

/-! ## Work-region tapes -/

/-- Sentinel on cell `−1`, work cells on `[0, len)`, blank elsewhere. -/
def tapeOf (l : List Cell) (i : ℤ) : Sym :=
  if i = -1 then .leftEnd
  else if 0 ≤ i ∧ i < (l.length : ℤ) then .work (l.getD i.toNat emptyCell)
  else .blank

theorem tapeOf_neg_one (l : List Cell) : tapeOf l (-1) = .leftEnd := by simp [tapeOf]

theorem tapeOf_work (l : List Cell) (j : ℕ) (hj : j < l.length) :
    tapeOf l (j : ℤ) = .work l[j] := by
  unfold tapeOf
  rw [if_neg (by omega), if_pos ⟨by omega, by exact_mod_cast hj⟩]
  simp [List.getElem?_eq_getElem hj]

theorem tapeOf_blank (l : List Cell) (j : ℕ) (hj : l.length ≤ j) : tapeOf l (j : ℤ) = .blank := by
  unfold tapeOf
  rw [if_neg (by omega), if_neg (by omega)]

theorem tapeOf_set (l : List Cell) (j : ℕ) (hj : j < l.length) (c : Cell) :
    Function.update (tapeOf l) (j : ℤ) (.work c) = tapeOf (l.set j c) := by
  funext i
  by_cases hi : i = (j : ℤ)
  · subst hi
    rw [Function.update_self, tapeOf_work _ _ (by simpa using hj)]
    simp
  · rw [Function.update_of_ne hi]
    by_cases h1 : i = -1
    · simp [tapeOf, h1]
    · by_cases h2 : 0 ≤ i ∧ i < (l.length : ℤ)
      · have h3 : 0 ≤ i ∧ i < ((l.set j c).length : ℤ) := by simpa using h2
        simp only [tapeOf, if_neg h1, if_pos h2, if_pos h3]
        have hk : j ≠ i.toNat := by omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hk]
      · have h3 : ¬ (0 ≤ i ∧ i < ((l.set j c).length : ℤ)) := by simpa using h2
        simp only [tapeOf, if_neg h1, if_neg h2, if_neg h3]

theorem tapeOf_snoc (l : List Cell) (c : Cell) :
    Function.update (tapeOf l) (l.length : ℤ) (.work c) = tapeOf (l ++ [c]) := by
  funext i
  by_cases hi : i = (l.length : ℤ)
  · subst hi
    rw [Function.update_self, tapeOf_work (l ++ [c]) l.length (by simp)]
    simp
  · rw [Function.update_of_ne hi]
    by_cases h1 : i = -1
    · simp [tapeOf, h1]
    · by_cases h2 : 0 ≤ i ∧ i < (l.length : ℤ)
      · have h3 : 0 ≤ i ∧ i < ((l ++ [c]).length : ℤ) := by
          simp only [List.length_append, List.length_singleton]; omega
        simp only [tapeOf, if_neg h1, if_pos h2, if_pos h3]
        have hk : i.toNat < l.length := by omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
      · have h3 : ¬ (0 ≤ i ∧ i < ((l ++ [c]).length : ℤ)) := by
          simp only [List.length_append, List.length_singleton]; omega
        simp only [tapeOf, if_neg h1, if_neg h2, if_neg h3]

theorem tapeOf_mid (d r : List Cell) (c c' : Cell) :
    Function.update (tapeOf (d ++ c :: r)) (d.length : ℤ) (.work c') = tapeOf (d ++ c' :: r) := by
  rw [tapeOf_set _ _ (by simp)]
  congr 1
  rw [List.set_append_right _ _ (le_refl _)]
  simp

theorem tapeOf_mid_get (d r : List Cell) (c : Cell) :
    tapeOf (d ++ c :: r) (d.length : ℤ) = .work c := by
  rw [tapeOf_work _ _ (by simp)]
  simp

/-! ## Counted, non-halting runs -/

section Machine

variable (P : ℕ × Array Inst)

theorem step_cfg (T : ℤ → Sym) (h : ℤ) (q : State P.2.size) :
    (build P).step (⟨T, h, q⟩ : (build P).Cfg) =
      (⟨Function.update T h (step P.2 P.1 q (T h)).2.1,
        h + (step P.2 P.1 q (T h)).2.2.shift, (step P.2 P.1 q (T h)).1⟩ : (build P).Cfg) := rfl

/-- `k` transitions lead from `c` to `c'`, and none of the first `k` configurations is halting. -/
def Steps (c c' : (build P).Cfg) (k : ℕ) : Prop :=
  (build P).run c k = c' ∧ ∀ t < k, ((build P).run c t).q ≠ State.done

variable {P}

theorem Steps.refl (c : (build P).Cfg) : Steps P c c 0 :=
  ⟨rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩

theorem Steps.trans {c c' c'' : (build P).Cfg} {k k' : ℕ} (h : Steps P c c' k)
    (h' : Steps P c' c'' k') : Steps P c c'' (k + k') := by
  refine ⟨by rw [MTM.run_add, h.1, h'.1], fun t ht => ?_⟩
  by_cases htk : t < k
  · exact h.2 t htk
  · have e : t = k + (t - k) := by omega
    rw [e, MTM.run_add, h.1]
    exact h'.2 (t - k) (by omega)

theorem Steps.cast {c c' : (build P).Cfg} {k k' : ℕ} (h : Steps P c c' k) (hk : k = k') :
    Steps P c c' k' := hk ▸ h

/-- One transition from a non-halting state. -/
theorem Steps.one (T : ℤ → Sym) (h : ℤ) (q q' : State P.2.size) (s' : Sym) (m : Mv)
    (hδ : step P.2 P.1 q (T h) = (q', s', m)) (hq : q ≠ State.done) :
    Steps P (⟨T, h, q⟩ : (build P).Cfg)
      (⟨Function.update T h s', h + m.shift, q'⟩ : (build P).Cfg) 1 := by
  refine ⟨?_, fun t ht => ?_⟩
  · rw [show (1 : ℕ) = 0 + 1 from rfl, MTM.run_succ, MTM.run_zero, step_cfg, hδ]
  · have e : t = 0 := by omega
    subst e
    exact hq

/-- One transition that leaves the scanned symbol unchanged. -/
theorem Steps.one_same (T : ℤ → Sym) (h : ℤ) (q q' : State P.2.size) (m : Mv)
    (hδ : step P.2 P.1 q (T h) = (q', T h, m)) (hq : q ≠ State.done) :
    Steps P (⟨T, h, q⟩ : (build P).Cfg) (⟨T, h + m.shift, q'⟩ : (build P).Cfg) 1 := by
  have := Steps.one (P := P) T h q q' (T h) m hδ hq
  rwa [Function.update_eq_self] at this

/-! ## The return scan -/

/-- From cell `k − 1` the return scan reaches the sentinel and re-enters cell `0` in `k + 1`
transitions. -/
theorem ret_walk (pc : Fin (P.2.size + 1)) (l : List Cell) : ∀ k : ℕ, k ≤ l.length →
    Steps P (⟨tapeOf l, (k : ℤ) - 1, .ret pc⟩ : (build P).Cfg)
      (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg) (k + 1)
  | 0, _ => by
    have h := Steps.one_same (P := P) (tapeOf l) (-1) (.ret pc) (.scan pc) .R
      (by rw [tapeOf_neg_one]; rfl) (by simp)
    simpa [Mv.shift] using h
  | k + 1, hk => by
    have hw := tapeOf_work l k (by omega)
    have h := Steps.one_same (P := P) (tapeOf l) (k : ℤ) (.ret pc) (.ret pc) .L
      (by rw [hw]; rfl) (by simp)
    have e : (((k + 1 : ℕ) : ℤ)) - 1 = (k : ℤ) := by push_cast; ring
    have e2 : (k : ℤ) + Mv.L.shift = (k : ℤ) - 1 := by simp [Mv.shift]; ring
    rw [e]
    rw [e2] at h
    exact (h.trans (ret_walk pc l k (by omega))).cast (by omega)

/-! ## Rightward scans -/

/-- A scan that rewrites every cell of a block `a` by `f` and keeps its state. -/
theorem sweep (pc : Fin (P.2.size + 1)) (f : Cell → Cell) :
    ∀ (a d b : List Cell),
      (∀ c ∈ a, step P.2 P.1 (.scan pc) (.work c) = (.scan pc, .work (f c), .R)) →
      Steps P (⟨tapeOf (d ++ a ++ b), (d.length : ℤ), .scan pc⟩ : (build P).Cfg)
        (⟨tapeOf (d ++ a.map f ++ b), ((d.length + a.length : ℕ) : ℤ), .scan pc⟩ :
          (build P).Cfg) a.length
  | [], d, b, _ => by simpa using Steps.refl (P := P) _
  | c :: a, d, b, h => by
    have h1 := Steps.one (P := P) (tapeOf (d ++ c :: (a ++ b))) (d.length : ℤ) (.scan pc)
      (.scan pc) (.work (f c)) .R (by rw [tapeOf_mid_get]; exact h c (by simp)) (by simp)
    rw [tapeOf_mid] at h1
    have h2 := sweep pc f a (d ++ [f c]) b (fun c' hc' => h c' (by simp [hc']))
    have e1 : d ++ f c :: (a ++ b) = d ++ [f c] ++ a ++ b := by simp
    have e2 : (d.length : ℤ) + Mv.R.shift = ((d ++ [f c]).length : ℤ) := by
      simp [Mv.shift]
    rw [e1, e2] at h1
    have h3 := h1.trans h2
    have e3 : d ++ c :: a ++ b = d ++ c :: (a ++ b) := by simp
    have e4 : d ++ [f c] ++ a.map f ++ b = d ++ (c :: a).map f ++ b := by simp
    have e5 : (d ++ [f c]).length + a.length = d.length + (c :: a).length := by
      simp; omega
    rw [e3, ← e4, ← e5]
    exact h3.cast (by simp; omega)

/-- A scan over a block that changes nothing. -/
theorem sweep_id (pc : Fin (P.2.size + 1)) (a b : List Cell)
    (h : ∀ c ∈ a, step P.2 P.1 (.scan pc) (.work c) = (.scan pc, .work c, .R)) :
    Steps P (⟨tapeOf (a ++ b), 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (a ++ b), (a.length : ℤ), .scan pc⟩ : (build P).Cfg) a.length := by
  have := sweep (P := P) pc id a [] b (by simpa using h)
  simpa using this

/-- Splitting a list at an index. -/
theorem split_at (l : List Cell) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]

theorem set_split (l : List Cell) (j : ℕ) (hj : j < l.length) (c : Cell) :
    l.set j c = l.take j ++ c :: l.drop (j + 1) := by
  rw [List.set_eq_take_append_cons_drop, if_pos hj]

theorem mem_take_index {l : List Cell} {j : ℕ} {c : Cell} (hc : c ∈ l.take j) :
    ∃ (i : ℕ) (hi : i < l.length), i < j ∧ l[i] = c := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  rw [List.length_take] at hi
  exact ⟨i, by omega, by omega, by rw [List.getElem_take]⟩

/-! ## One transition of each instruction -/

/-- Value copied by `copy src`. -/
def srcVal : Source → Cell → Bool
  | .input, c => c.inp.isSome
  | .zero, _ => false
  | .mark k, c => c.flags k

/-- Effect of `copy src dst` on one cell. -/
def cpCell (src : Source) (dst : Mark) (c : Cell) : Cell :=
  {c with flags := Function.update c.flags dst (srcVal src c)}

/-- Clearing one mark. -/
def clrCell (k : Mark) (c : Cell) : Cell := {c with flags := Function.update c.flags k false}

/-- Setting the destination mark. -/
def setDest (c : Cell) : Cell := {c with flags := Function.update c.flags .dest true}

/-- Writing an output bit. -/
def setOut (b : Bool) (c : Cell) : Cell := {c with out := some b}

/-- Three-way branch on an optional bit. -/
def sel3 (v : Option Bool) (b z o : ℕ) : ℕ :=
  match v with
  | none => b
  | some false => z
  | some true => o

variable {pc : Fin (P.2.size + 1)}

theorem step_copy_work {src : Source} {dst : Mark} {next : ℕ}
    (hI : lookup P.2 pc = .copy src dst next) (c : Cell) :
    step P.2 P.1 (.scan pc) (.work c) = (.scan pc, .work (cpCell src dst c), .R) := by
  simp only [step, hI]
  cases src <;> rfl

theorem step_copy_blank {src : Source} {dst : Mark} {next : ℕ}
    (hI : lookup P.2 pc = .copy src dst next) :
    step P.2 P.1 (.scan pc) .blank = (.ret (addr P.2 next), .blank, .L) := by
  simp only [step, hI]

theorem step_take_work {k : Mark} {yes no : ℕ} (hI : lookup P.2 pc = .take k yes no) (c : Cell) :
    step P.2 P.1 (.scan pc) (.work c) =
      if c.flags k then (.ret (addr P.2 yes), .work (clrCell k c), .L)
      else (.scan pc, .work c, .R) := by
  simp only [step, hI]
  rfl

theorem step_take_blank {k : Mark} {yes no : ℕ} (hI : lookup P.2 pc = .take k yes no) :
    step P.2 P.1 (.scan pc) .blank = (.ret (addr P.2 no), .blank, .L) := by
  simp only [step, hI]

theorem step_inc {next : ℕ} (hI : lookup P.2 pc = .inc next) (s : Sym) :
    step P.2 P.1 (.scan pc) s =
      if (asCell s).flags .dest then (.scan pc, s, .R)
      else (.ret (addr P.2 next), .work (setDest (asCell s)), .L) := by
  simp only [step, hI]
  rfl

theorem step_emit {b : Bool} {next : ℕ} (hI : lookup P.2 pc = .emit b next) (s : Sym) :
    step P.2 P.1 (.scan pc) s =
      if (asCell s).out.isSome then (.scan pc, s, .R)
      else (.ret (addr P.2 next), .work (setOut b (asCell s)), .L) := by
  simp only [step, hI]
  rfl

theorem step_next_work {b z o ex : ℕ} (hI : lookup P.2 pc = .nextInput b z o ex) (c : Cell) :
    step P.2 P.1 (.scan pc) (.work c) =
      if c.flags .outer then (.neighbor pc, .work (clrCell .outer c), .R)
      else (.scan pc, .work c, .R) := by
  simp only [step, hI]
  rfl

theorem step_next_blank {b z o ex : ℕ} (hI : lookup P.2 pc = .nextInput b z o ex) :
    step P.2 P.1 (.scan pc) .blank = (.ret (addr P.2 ex), .blank, .L) := by
  simp only [step, hI]

theorem step_neighbor {b z o ex : ℕ} (hI : lookup P.2 pc = .nextInput b z o ex) (s : Sym) :
    step P.2 P.1 (.neighbor pc) s = (.ret (addr P.2 (readBit s b z o)), s, .L) := by
  simp only [step, hI]

theorem step_head {b z o : ℕ} (hI : lookup P.2 pc = .headInput b z o) (s : Sym) :
    step P.2 P.1 (.scan pc) s = (.ret (addr P.2 (readBit s b z o)), s, .L) := by
  simp only [step, hI]

theorem step_finish (hI : lookup P.2 pc = .finish) (s : Sym) :
    step P.2 P.1 (.scan pc) s =
      match (asCell s).out with
      | none => (.done, .blank, .R)
      | some bit => (.scan pc, .raw bit, .R) := by
  simp only [step, hI]
  cases (asCell s).out <;> rfl

/-! ## Whole instructions -/

/-- The scan reads the blank after the work region, turns round and returns. -/
theorem turn_at_end (l : List Cell) (q' : Fin (P.2.size + 1))
    (hδ : step P.2 P.1 (.scan pc) .blank = (.ret q', .blank, .L)) :
    Steps P (⟨tapeOf l, (l.length : ℤ), .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf l, 0, .scan q'⟩ : (build P).Cfg) (l.length + 2) := by
  have hb := tapeOf_blank l l.length le_rfl
  have h1 := Steps.one_same (P := P) (tapeOf l) (l.length : ℤ) (.scan pc) (.ret q') .L
    (by rw [hb]; exact hδ) (by simp)
  have e : (l.length : ℤ) + Mv.L.shift = (l.length : ℤ) - 1 := by simp [Mv.shift]; ring
  rw [e] at h1
  exact (h1.trans (ret_walk q' l l.length le_rfl)).cast (by omega)

/-- **`copy`**: `2·len + 2` transitions. -/
theorem exec_copy {src : Source} {dst : Mark} {next : ℕ}
    (hI : lookup P.2 pc = .copy src dst next) (l : List Cell) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l.map (cpCell src dst)), 0, .scan (addr P.2 next)⟩ : (build P).Cfg)
      (2 * l.length + 2) := by
  have h1 := sweep (P := P) pc (cpCell src dst) l [] [] (fun c _ => step_copy_work hI c)
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add,
    Nat.cast_zero] at h1
  have h2 := turn_at_end (P := P) (pc := pc) (l.map (cpCell src dst)) (addr P.2 next)
    (step_copy_blank hI)
  rw [List.length_map] at h2
  exact (h1.trans h2).cast (by omega)

/-- A scan passes `j` cells unchanged, rewrites cell `j` and returns: `2j + 2` transitions. -/
theorem hit_at (l : List Cell) (j : ℕ) (hj : j < l.length) (c' : Cell) (q' : Fin (P.2.size + 1))
    (hpre : ∀ (i : ℕ) (hi : i < l.length), i < j →
      step P.2 P.1 (.scan pc) (.work l[i]) = (.scan pc, .work l[i], .R))
    (hit : step P.2 P.1 (.scan pc) (.work l[j]) = (.ret q', .work c', .L)) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l.set j c'), 0, .scan q'⟩ : (build P).Cfg) (2 * j + 2) := by
  have hs := split_at l j hj
  have hlen : (l.take j).length = j := by rw [List.length_take]; omega
  have h1 := sweep_id (P := P) pc (l.take j) (l[j] :: l.drop (j + 1)) (fun c hc => by
    obtain ⟨i, hi, hij, rfl⟩ := mem_take_index hc
    exact hpre i hi hij)
  rw [← hs, hlen] at h1
  have h2 := Steps.one (P := P) (tapeOf l) (j : ℤ) (.scan pc) (.ret q') (.work c') .L
    (by rw [tapeOf_work l j hj]; exact hit) (by simp)
  rw [tapeOf_set l j hj] at h2
  have e : (j : ℤ) + Mv.L.shift = (j : ℤ) - 1 := by simp [Mv.shift]; ring
  rw [e] at h2
  have h3 := ret_walk (P := P) q' (l.set j c') j (by rw [List.length_set]; omega)
  exact ((h1.trans h2).trans h3).cast (by omega)

/-- A scan passes the whole work region unchanged, appends a cell and returns:
`2·len + 2` transitions. -/
theorem append_at (l : List Cell) (c' : Cell) (q' : Fin (P.2.size + 1))
    (hpre : ∀ (i : ℕ) (hi : i < l.length),
      step P.2 P.1 (.scan pc) (.work l[i]) = (.scan pc, .work l[i], .R))
    (hit : step P.2 P.1 (.scan pc) .blank = (.ret q', .work c', .L)) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l ++ [c']), 0, .scan q'⟩ : (build P).Cfg) (2 * l.length + 2) := by
  have h1 := sweep_id (P := P) pc l [] (fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact hpre i hi)
  rw [List.append_nil] at h1
  have h2 := Steps.one (P := P) (tapeOf l) (l.length : ℤ) (.scan pc) (.ret q') (.work c') .L
    (by rw [tapeOf_blank l l.length le_rfl]; exact hit) (by simp)
  rw [tapeOf_snoc] at h2
  have e : (l.length : ℤ) + Mv.L.shift = (l.length : ℤ) - 1 := by simp [Mv.shift]; ring
  rw [e] at h2
  have h3 := ret_walk (P := P) q' (l ++ [c']) l.length (by simp)
  exact ((h1.trans h2).trans h3).cast (by omega)

/-- A scan passes the whole work region unchanged and returns: `2·len + 2` transitions. -/
theorem miss_at (l : List Cell) (q' : Fin (P.2.size + 1))
    (hpre : ∀ (i : ℕ) (hi : i < l.length),
      step P.2 P.1 (.scan pc) (.work l[i]) = (.scan pc, .work l[i], .R))
    (hend : step P.2 P.1 (.scan pc) .blank = (.ret q', .blank, .L)) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf l, 0, .scan q'⟩ : (build P).Cfg) (2 * l.length + 2) := by
  have h1 := sweep_id (P := P) pc l [] (fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact hpre i hi)
  rw [List.append_nil] at h1
  exact (h1.trans (turn_at_end (P := P) (pc := pc) l q' hend)).cast (by omega)

/-- **`take`, a mark is found** at the first marked cell `j`. -/
theorem exec_take_hit {k : Mark} {yes no : ℕ} (hI : lookup P.2 pc = .take k yes no)
    (l : List Cell) (j : ℕ) (hj : j < l.length)
    (hpre : ∀ (i : ℕ) (hi : i < l.length), i < j → l[i].flags k = false)
    (hit : l[j].flags k = true) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l.set j (clrCell k l[j])), 0, .scan (addr P.2 yes)⟩ : (build P).Cfg)
      (2 * j + 2) :=
  hit_at l j hj _ _ (fun i hi hij => by rw [step_take_work hI, hpre i hi hij]; rfl)
    (by rw [step_take_work hI, hit]; rfl)

/-- **`take`, no mark.** -/
theorem exec_take_miss {k : Mark} {yes no : ℕ} (hI : lookup P.2 pc = .take k yes no)
    (l : List Cell) (hall : ∀ (i : ℕ) (hi : i < l.length), l[i].flags k = false) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf l, 0, .scan (addr P.2 no)⟩ : (build P).Cfg) (2 * l.length + 2) :=
  miss_at l _ (fun i hi => by rw [step_take_work hI, hall i hi]; rfl) (step_take_blank hI)

/-- **`inc`** inside the work region. -/
theorem exec_inc_in {next : ℕ} (hI : lookup P.2 pc = .inc next) (l : List Cell) (j : ℕ)
    (hj : j < l.length) (hpre : ∀ (i : ℕ) (hi : i < l.length), i < j → l[i].flags .dest = true)
    (hit : l[j].flags .dest = false) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l.set j (setDest l[j])), 0, .scan (addr P.2 next)⟩ : (build P).Cfg)
      (2 * j + 2) :=
  hit_at l j hj _ _
    (fun i hi hij => by
      rw [step_inc hI]
      have : (asCell (.work l[i])).flags .dest = true := hpre i hi hij
      rw [if_pos this])
    (by
      rw [step_inc hI]
      have : ¬ (asCell (.work l[j])).flags .dest = true := by
        show ¬ l[j].flags .dest = true
        rw [hit]; simp
      rw [if_neg this]; rfl)

/-- **`inc`** at the end of the work region: a new cell is created. -/
theorem exec_inc_end {next : ℕ} (hI : lookup P.2 pc = .inc next) (l : List Cell)
    (hall : ∀ (i : ℕ) (hi : i < l.length), l[i].flags .dest = true) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l ++ [setDest emptyCell]), 0, .scan (addr P.2 next)⟩ : (build P).Cfg)
      (2 * l.length + 2) :=
  append_at l _ _
    (fun i hi => by
      rw [step_inc hI]
      have : (asCell (.work l[i])).flags .dest = true := hall i hi
      rw [if_pos this])
    (by rw [step_inc hI]; rfl)

/-- **`emit`** inside the work region. -/
theorem exec_emit_in {b : Bool} {next : ℕ} (hI : lookup P.2 pc = .emit b next) (l : List Cell)
    (j : ℕ) (hj : j < l.length)
    (hpre : ∀ (i : ℕ) (hi : i < l.length), i < j → l[i].out.isSome = true)
    (hit : l[j].out = none) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l.set j (setOut b l[j])), 0, .scan (addr P.2 next)⟩ : (build P).Cfg)
      (2 * j + 2) :=
  hit_at l j hj _ _
    (fun i hi hij => by
      rw [step_emit hI]
      have : (asCell (.work l[i])).out.isSome = true := hpre i hi hij
      rw [if_pos this])
    (by
      rw [step_emit hI]
      have : ¬ (asCell (.work l[j])).out.isSome = true := by
        show ¬ l[j].out.isSome = true
        rw [hit]; simp
      rw [if_neg this]; rfl)

/-- **`emit`** at the end of the work region. -/
theorem exec_emit_end {b : Bool} {next : ℕ} (hI : lookup P.2 pc = .emit b next) (l : List Cell)
    (hall : ∀ (i : ℕ) (hi : i < l.length), l[i].out.isSome = true) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l ++ [setOut b emptyCell]), 0, .scan (addr P.2 next)⟩ : (build P).Cfg)
      (2 * l.length + 2) :=
  append_at l _ _
    (fun i hi => by
      rw [step_emit hI]
      have : (asCell (.work l[i])).out.isSome = true := hall i hi
      rw [if_pos this])
    (by rw [step_emit hI]; rfl)

/-- Input bit of cell `i`, if any. -/
def inpAt (l : List Cell) (i : ℕ) : Option Bool := l[i]?.bind (·.inp)

theorem readBit_tapeOf (l : List Cell) (i : ℕ) (b z o : ℕ) :
    readBit (tapeOf l (i : ℤ)) b z o = sel3 (inpAt l i) b z o := by
  by_cases hi : i < l.length
  · rw [tapeOf_work l i hi]
    simp only [readBit, asCell, inpAt, List.getElem?_eq_getElem hi, Option.bind_some, sel3]
    rcases l[i].inp with _ | (_ | _) <;> rfl
  · rw [tapeOf_blank l i (by omega)]
    simp only [readBit, asCell, emptyCell, inpAt, List.getElem?_eq_none (by omega : l.length ≤ i),
      Option.bind_none, sel3]

/-- **`nextInput`, a mark is found** at cell `j`: the mark is cleared and the input bit of cell
`j + 1` selects the continuation. `2j + 4` transitions. -/
theorem exec_next_hit {b z o ex : ℕ} (hI : lookup P.2 pc = .nextInput b z o ex) (l : List Cell)
    (j : ℕ) (hj : j < l.length)
    (hpre : ∀ (i : ℕ) (hi : i < l.length), i < j → l[i].flags .outer = false)
    (hit : l[j].flags .outer = true) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf (l.set j (clrCell .outer l[j])), 0,
        .scan (addr P.2 (sel3 (inpAt l (j + 1)) b z o))⟩ : (build P).Cfg) (2 * j + 4) := by
  have hs := split_at l j hj
  have hlen : (l.take j).length = j := by rw [List.length_take]; omega
  have h1 := sweep_id (P := P) pc (l.take j) (l[j] :: l.drop (j + 1)) (fun c hc => by
    obtain ⟨i, hi, hij, rfl⟩ := mem_take_index hc
    rw [step_next_work hI, hpre i hi hij]; rfl)
  rw [← hs, hlen] at h1
  have h2 := Steps.one (P := P) (tapeOf l) (j : ℤ) (.scan pc) (.neighbor pc)
    (.work (clrCell .outer l[j])) .R
    (by rw [tapeOf_work l j hj, step_next_work hI, hit]; rfl) (by simp)
  rw [tapeOf_set l j hj] at h2
  set l' := l.set j (clrCell .outer l[j]) with hl'
  have hlen' : l'.length = l.length := by rw [hl', List.length_set]
  have e : (j : ℤ) + Mv.R.shift = ((j + 1 : ℕ) : ℤ) := by simp [Mv.shift]
  rw [e] at h2
  have h3 := Steps.one_same (P := P) (tapeOf l') ((j + 1 : ℕ) : ℤ) (.neighbor pc)
    (.ret (addr P.2 (readBit (tapeOf l' ((j + 1 : ℕ) : ℤ)) b z o))) .L
    (step_neighbor hI _) (by simp)
  have e3 : ((j + 1 : ℕ) : ℤ) + Mv.L.shift = ((j + 1 : ℕ) : ℤ) - 1 := by
    simp [Mv.shift]
  rw [e3] at h3
  have hin : inpAt l' (j + 1) = inpAt l (j + 1) := by
    simp only [inpAt, hl']
    rw [List.getElem?_set_ne (by omega)]
  rw [readBit_tapeOf, hin] at h3
  have h4 := ret_walk (P := P) (addr P.2 (sel3 (inpAt l (j + 1)) b z o)) l' (j + 1)
    (by rw [hlen']; omega)
  exact (((h1.trans h2).trans h3).trans h4).cast (by omega)

/-- **`nextInput`, no mark.** -/
theorem exec_next_miss {b z o ex : ℕ} (hI : lookup P.2 pc = .nextInput b z o ex) (l : List Cell)
    (hall : ∀ (i : ℕ) (hi : i < l.length), l[i].flags .outer = false) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf l, 0, .scan (addr P.2 ex)⟩ : (build P).Cfg) (2 * l.length + 2) :=
  miss_at l _ (fun i hi => by rw [step_next_work hI, hall i hi]; rfl) (step_next_blank hI)

/-- **`headInput`**: two transitions. -/
theorem exec_head {b z o : ℕ} (hI : lookup P.2 pc = .headInput b z o) (l : List Cell) :
    Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
      (⟨tapeOf l, 0, .scan (addr P.2 (sel3 (inpAt l 0) b z o))⟩ : (build P).Cfg) 2 := by
  have h1 := Steps.one_same (P := P) (tapeOf l) 0 (.scan pc)
    (.ret (addr P.2 (readBit (tapeOf l 0) b z o))) .L (step_head hI _) (by simp)
  have e : (0 : ℤ) + Mv.L.shift = ((0 : ℕ) : ℤ) - 1 := by simp [Mv.shift]
  rw [e] at h1
  have h0 := readBit_tapeOf l 0 b z o
  simp only [Nat.cast_zero] at h0
  rw [h0] at h1
  exact h1.trans (ret_walk (P := P) _ l 0 (Nat.zero_le _))

/-! ## The final scan -/

/-- Tape during the final scan: the first `m` cells already hold output symbols. -/
def rawTape (w : List Bool) (m : ℕ) (l : List Cell) (i : ℤ) : Sym :=
  if 0 ≤ i ∧ i < (m : ℤ) then .raw (w.getD i.toNat false) else tapeOf l i

theorem rawTape_zero (w : List Bool) (l : List Cell) : rawTape w 0 l = tapeOf l := by
  funext i
  simp [rawTape]

theorem rawTape_succ (w : List Bool) (m : ℕ) (l : List Cell) :
    Function.update (rawTape w m l) (m : ℤ) (.raw (w.getD m false)) = rawTape w (m + 1) l := by
  funext i
  by_cases hi : i = (m : ℤ)
  · subst hi
    simp [rawTape]
  · rw [Function.update_of_ne hi]
    unfold rawTape
    by_cases h1 : 0 ≤ i ∧ i < (m : ℤ)
    · rw [if_pos h1, if_pos ⟨h1.1, by push_cast; omega⟩]
    · rw [if_neg h1, if_neg (by push_cast; omega)]

/-- **`finish`**: the output track `w` becomes the output word, followed by a blank, and the
machine enters its halting state for the first time after `|w| + 1` transitions. -/
theorem exec_finish (hI : lookup P.2 pc = .finish) (l : List Cell) (w : List Bool)
    (hw : w.length ≤ l.length) (hout : ∀ (j : ℕ) (hj : j < l.length), l[j].out = w[j]?) :
    ∃ T : ℤ → Sym, Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
        (⟨T, (w.length : ℤ) + 1, .done⟩ : (build P).Cfg) (w.length + 1) ∧
      (∀ i : ℕ, i < w.length → T (i : ℤ) = .raw (w.getD i false)) ∧
      T (w.length : ℤ) = .blank := by
  -- the scan over the output track
  have hscan : ∀ m : ℕ, m ≤ w.length →
      Steps P (⟨tapeOf l, 0, .scan pc⟩ : (build P).Cfg)
        (⟨rawTape w m l, (m : ℤ), .scan pc⟩ : (build P).Cfg) m := by
    intro m
    induction m with
    | zero => intro _; rw [rawTape_zero]; exact Steps.refl _
    | succ m ih =>
      intro hm
      have hml : m < l.length := by omega
      have hcell : rawTape w m l (m : ℤ) = .work l[m] := by
        unfold rawTape
        rw [if_neg (by omega), tapeOf_work l m hml]
      have ho : (asCell (.work l[m])).out = some (w.getD m false) := by
        show l[m].out = _
        rw [hout m hml, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
      have h1 := Steps.one (P := P) (rawTape w m l) (m : ℤ) (.scan pc) (.scan pc)
        (.raw (w.getD m false)) .R (by rw [hcell, step_finish hI, ho]) (by simp)
      rw [rawTape_succ] at h1
      have e : (m : ℤ) + Mv.R.shift = ((m + 1 : ℕ) : ℤ) := by simp [Mv.shift]
      rw [e] at h1
      exact (ih (by omega)).trans h1
  have h1 := hscan w.length le_rfl
  -- the cell after the output has no output bit
  have ho : (asCell (rawTape w w.length l (w.length : ℤ))).out = none := by
    unfold rawTape
    rw [if_neg (by omega)]
    by_cases hl : w.length < l.length
    · rw [tapeOf_work l _ hl]
      show l[w.length].out = none
      rw [hout _ hl, List.getElem?_eq_none le_rfl]
    · rw [tapeOf_blank l _ (by omega)]
      rfl
  have h2 := Steps.one (P := P) (rawTape w w.length l) (w.length : ℤ) (.scan pc) .done .blank .R
    (by rw [step_finish hI, ho]) (by simp)
  have e : (w.length : ℤ) + Mv.R.shift = (w.length : ℤ) + 1 := by simp [Mv.shift]
  rw [e] at h2
  refine ⟨_, h1.trans h2, fun i hi => ?_, by simp⟩
  rw [Function.update_of_ne (by omega)]
  unfold rawTape
  rw [if_pos ⟨by omega, by exact_mod_cast hi⟩]
  simp

end Machine

end PVNP.TwoPhasePolynomialWriter
