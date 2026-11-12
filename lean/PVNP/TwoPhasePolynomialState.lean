import PVNP.TwoPhasePolynomialExec

/-!
# II-10: the work region as counters, marks and an output prefix

During the run of the original polynomial writers the work region always has a simple shape:

* the input bits `x` on the first cells;
* the accumulator marks on a prefix of length `acc`, the destination marks on a prefix of length
  `dst`;
* the outer and inner loop marks on intervals `[oLo, oHi)` and `[iLo, iHi)`;
* the output bits on a prefix (`out`).

`St` records these numbers and `cells` rebuilds the cell list. Each instruction of the machine
maps such a state to another one (`Exec.copy_acc_outer`, …, `Exec.head`). `Exec P pc s pc' s' m`
says that the machine goes from instruction `pc` on state `s` to instruction `pc'` on state `s'`
by executing at most `m` instructions, each of which costs at most `2·len + 4` transitions.
-/

namespace PVNP.TwoPhasePolynomialWriter

open PartIITuring

/-- Abstract state of the work region. -/
@[ext] structure St where
  x : List Bool
  len : ℕ
  acc : ℕ
  dst : ℕ
  oLo : ℕ
  oHi : ℕ
  iLo : ℕ
  iHi : ℕ
  out : List Bool

namespace St

/-- Mark `k` on cell `j`. -/
def flag (s : St) (k : Mark) (j : ℕ) : Bool :=
  match k with
  | .acc => decide (j < s.acc)
  | .dest => decide (j < s.dst)
  | .outer => decide (s.oLo ≤ j ∧ j < s.oHi)
  | .inner => decide (s.iLo ≤ j ∧ j < s.iHi)

/-- Everything recorded lies inside the work region. -/
def WF (s : St) : Prop :=
  s.x.length ≤ s.len ∧ s.acc ≤ s.len ∧ s.dst ≤ s.len ∧ s.oHi ≤ s.len ∧ s.iHi ≤ s.len ∧
    s.out.length ≤ s.len

end St

/-- Cell `j` of the state. -/
def cellAt (s : St) (j : ℕ) : Cell := ⟨s.x[j]?, fun k => s.flag k j, s.out[j]?⟩

/-- The work region. -/
def cells (s : St) : List Cell := (List.range s.len).map (cellAt s)

@[simp] theorem cells_length (s : St) : (cells s).length = s.len := by simp [cells]

theorem cells_get (s : St) (j : ℕ) (hj : j < (cells s).length) : (cells s)[j] = cellAt s j := by
  simp [cells]

theorem Cell.ext' {c d : Cell} (h1 : c.inp = d.inp) (h2 : c.flags = d.flags) (h3 : c.out = d.out) :
    c = d := by
  cases c; cases d
  rw [Cell.mk.injEq]
  exact ⟨h1, h2, h3⟩

theorem flag_shift {a b i : ℕ} (hi : i ≠ a) :
    decide (a + 1 ≤ i ∧ i < b) = decide (a ≤ i ∧ i < b) :=
  decide_eq_decide.2 ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

theorem flag_succ {a i : ℕ} (hi : i ≠ a) : decide (i < a + 1) = decide (i < a) :=
  decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩

theorem cells_map (g : Cell → Cell) (s s' : St) (hlen : s'.len = s.len)
    (h : ∀ j, j < s.len → g (cellAt s j) = cellAt s' j) : (cells s).map g = cells s' := by
  unfold cells
  rw [List.map_map, hlen]
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.1 hj)

theorem cells_set (s s' : St) (j : ℕ) (c : Cell) (hlen : s'.len = s.len)
    (hc : c = cellAt s' j) (h : ∀ i, i < s.len → i ≠ j → cellAt s' i = cellAt s i) :
    (cells s).set j c = cells s' := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    have hi : i < s.len := by simpa using h1
    rw [List.getElem_set, cells_get, cells_get]
    split_ifs with hij
    · subst hij; exact hc
    · exact (h i hi (Ne.symm hij)).symm

theorem cells_snoc (s s' : St) (c : Cell) (hlen : s'.len = s.len + 1) (hc : c = cellAt s' s.len)
    (h : ∀ i, i < s.len → cellAt s' i = cellAt s i) : cells s ++ [c] = cells s' := by
  unfold cells
  rw [hlen, List.range_succ, List.map_append, List.map_singleton, hc]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (h i (List.mem_range.1 hi)).symm

theorem inpAt_cells (s : St) (hw : s.x.length ≤ s.len) (i : ℕ) : inpAt (cells s) i = s.x[i]? := by
  unfold inpAt
  by_cases hi : i < s.len
  · rw [List.getElem?_eq_getElem (by simpa using hi), cells_get]
    rfl
  · rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by omega)]
    rfl

/-! ## Counted instruction runs -/

section Exec

variable (P : ℕ × Array Inst)

theorem lookup_addr {p : Array Inst} {i : ℕ} {inst : Inst} (h : p[i]? = some inst) :
    lookup p ((addr p i : Fin (p.size + 1)) : ℕ) = inst := by
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.1 h
  simp only [lookup, addr, Nat.min_eq_left (le_of_lt hi), h, Option.getD_some]

/-- From instruction `pc` on state `s` the machine reaches instruction `pc'` on state `s'`, after
at most `m` instructions of at most `2·len + 4` transitions each. -/
def Exec (pc : ℕ) (s : St) (pc' : ℕ) (s' : St) (m : ℕ) : Prop :=
  s.WF → s'.WF ∧ s.len ≤ s'.len ∧ ∃ k,
    Steps P (⟨tapeOf (cells s), 0, .scan (addr P.2 pc)⟩ : (build P).Cfg)
      (⟨tapeOf (cells s'), 0, .scan (addr P.2 pc')⟩ : (build P).Cfg) k ∧
    k ≤ m * (2 * s'.len + 4)

variable {P}

theorem Exec.refl (pc : ℕ) (s : St) : Exec P pc s pc s 0 :=
  fun hw => ⟨hw, le_rfl, 0, Steps.refl _, by simp⟩

theorem Exec.trans {pc pc' pc'' : ℕ} {s s' s'' : St} {m m' : ℕ} (h1 : Exec P pc s pc' s' m)
    (h2 : Exec P pc' s' pc'' s'' m') : Exec P pc s pc'' s'' (m + m') := by
  intro hw
  obtain ⟨hw1, hl1, k1, hs1, hk1⟩ := h1 hw
  obtain ⟨hw2, hl2, k2, hs2, hk2⟩ := h2 hw1
  refine ⟨hw2, le_trans hl1 hl2, k1 + k2, hs1.trans hs2, ?_⟩
  have : m * (2 * s'.len + 4) ≤ m * (2 * s''.len + 4) := Nat.mul_le_mul_left _ (by omega)
  calc k1 + k2 ≤ m * (2 * s''.len + 4) + m' * (2 * s''.len + 4) := by omega
    _ = (m + m') * (2 * s''.len + 4) := by ring

theorem Exec.mono {pc pc' : ℕ} {s s' : St} {m m' : ℕ} (h : Exec P pc s pc' s' m) (hm : m ≤ m') :
    Exec P pc s pc' s' m' := by
  intro hw
  obtain ⟨hw1, hl1, k1, hs1, hk1⟩ := h hw
  exact ⟨hw1, hl1, k1, hs1, le_trans hk1 (Nat.mul_le_mul_right _ hm)⟩

/-- Replace the target state by an equal one; the equality may use well-formedness. -/
theorem Exec.to {pc pc' : ℕ} {s t s' : St} {m : ℕ} (h : Exec P pc s pc' t m)
    (e : s.WF → t = s') : Exec P pc s pc' s' m := by
  intro hw
  have := e hw
  subst this
  exact h hw

/-- One instruction, from its transition-level statement. -/
theorem Exec.single {pc pc' : ℕ} {s s' : St} {k : ℕ} (hwf : s.WF → s'.WF) (hlen : s.len ≤ s'.len)
    (hk : s.WF → k ≤ 2 * s'.len + 4)
    (h : s.WF → Steps P (⟨tapeOf (cells s), 0, .scan (addr P.2 pc)⟩ : (build P).Cfg)
      (⟨tapeOf (cells s'), 0, .scan (addr P.2 pc')⟩ : (build P).Cfg) k) :
    Exec P pc s pc' s' 1 :=
  fun hw => ⟨hwf hw, hlen, k, h hw, by have := hk hw; omega⟩

/-! ### `copy` -/

theorem Exec.copy {pc next : ℕ} {src : Source} {dst : Mark}
    (hI : P.2[pc]? = some (.copy src dst next)) (s s' : St) (hlen : s'.len = s.len)
    (hwf : s.WF → s'.WF) (hcell : ∀ j, j < s.len → cpCell src dst (cellAt s j) = cellAt s' j) :
    Exec P pc s next s' 1 := by
  refine Exec.single hwf (by omega) (k := 2 * s.len + 2) (fun _ => by omega) (fun _ => ?_)
  have h := exec_copy (P := P) (lookup_addr hI) (cells s)
  rwa [cells_map _ s s' hlen hcell, cells_length] at h

/-- `outer := acc`. -/
theorem Exec.copy_acc_outer {pc next : ℕ} (hI : P.2[pc]? = some (.copy (.mark .acc) .outer next))
    (s : St) : Exec P pc s next {s with oLo := 0, oHi := s.acc} 1 := by
  refine Exec.copy hI s _ rfl (fun hw => ?_) (fun j _ => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
    exact ⟨h1, h2, h3, h2, h5, h6⟩
  · refine Cell.ext' rfl (funext fun k => ?_) rfl
    cases k <;> simp [cpCell, cellAt, srcVal, St.flag]

/-- `dest := 0`. -/
theorem Exec.clear_dest {pc next : ℕ} (hI : P.2[pc]? = some (.copy .zero .dest next)) (s : St) :
    Exec P pc s next {s with dst := 0} 1 := by
  refine Exec.copy hI s _ rfl (fun hw => ?_) (fun j _ => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
    exact ⟨h1, h2, Nat.zero_le _, h4, h5, h6⟩
  · refine Cell.ext' rfl (funext fun k => ?_) rfl
    cases k <;> simp [cpCell, cellAt, srcVal, St.flag]

/-- `inner := input presence`. -/
theorem Exec.copy_input_inner {pc next : ℕ} (hI : P.2[pc]? = some (.copy .input .inner next))
    (s : St) : Exec P pc s next {s with iLo := 0, iHi := s.x.length} 1 := by
  refine Exec.copy hI s _ rfl (fun hw => ?_) (fun j _ => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
    exact ⟨h1, h2, h3, h4, h1, h6⟩
  · refine Cell.ext' rfl (funext fun k => ?_) rfl
    cases k <;> simp [cpCell, cellAt, srcVal, St.flag]
    by_cases hj : j < s.x.length <;> simp [hj]

/-- `acc := dest`. -/
theorem Exec.copy_dest_acc {pc next : ℕ} (hI : P.2[pc]? = some (.copy (.mark .dest) .acc next))
    (s : St) : Exec P pc s next {s with acc := s.dst} 1 := by
  refine Exec.copy hI s _ rfl (fun hw => ?_) (fun j _ => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
    exact ⟨h1, h3, h3, h4, h5, h6⟩
  · refine Cell.ext' rfl (funext fun k => ?_) rfl
    cases k <;> simp [cpCell, cellAt, srcVal, St.flag]

/-! ### `take` -/

/-- `take outer`, a mark is left. -/
theorem Exec.take_outer_hit {pc yes no : ℕ} (hI : P.2[pc]? = some (.take .outer yes no)) (s : St)
    (h : s.oLo < s.oHi) : Exec P pc s yes {s with oLo := s.oLo + 1} 1 := by
  refine Exec.single (fun hw => hw) le_rfl (k := 2 * s.oLo + 2) (fun hw => ?_) (fun hw => ?_)
  · have := hw.2.2.2.1
    show 2 * s.oLo + 2 ≤ 2 * s.len + 4
    omega
  · have hj : s.oLo < (cells s).length := by have := hw.2.2.2.1; simp; omega
    have hx := exec_take_hit (P := P) (lookup_addr hI) (cells s) s.oLo hj
      (fun i hi hij => by rw [cells_get]; simp [cellAt, St.flag]; omega)
      (by rw [cells_get]; simp [cellAt, St.flag]; omega)
    rwa [cells_set s {s with oLo := s.oLo + 1} s.oLo _ rfl (by
      rw [cells_get]
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k <;> simp [clrCell, cellAt, St.flag]) (fun i _ hi => by
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k
      · rfl
      · rfl
      · exact flag_shift hi
      · rfl)] at hx

/-- `take outer`, no mark. -/
theorem Exec.take_outer_miss {pc yes no : ℕ} (hI : P.2[pc]? = some (.take .outer yes no)) (s : St)
    (h : s.oHi ≤ s.oLo) : Exec P pc s no s 1 := by
  refine Exec.single (fun hw => hw) le_rfl (k := 2 * s.len + 2) (fun _ => by omega) (fun _ => ?_)
  have hx := exec_take_miss (P := P) (lookup_addr hI) (cells s)
    (fun i hi => by rw [cells_get]; simp [cellAt, St.flag]; omega)
  rwa [cells_length] at hx

/-- `take inner`, a mark is left. -/
theorem Exec.take_inner_hit {pc yes no : ℕ} (hI : P.2[pc]? = some (.take .inner yes no)) (s : St)
    (h : s.iLo < s.iHi) : Exec P pc s yes {s with iLo := s.iLo + 1} 1 := by
  refine Exec.single (fun hw => hw) le_rfl (k := 2 * s.iLo + 2) (fun hw => ?_) (fun hw => ?_)
  · have := hw.2.2.2.2.1
    show 2 * s.iLo + 2 ≤ 2 * s.len + 4
    omega
  · have hj : s.iLo < (cells s).length := by have := hw.2.2.2.2.1; simp; omega
    have hx := exec_take_hit (P := P) (lookup_addr hI) (cells s) s.iLo hj
      (fun i hi hij => by rw [cells_get]; simp [cellAt, St.flag]; omega)
      (by rw [cells_get]; simp [cellAt, St.flag]; omega)
    rwa [cells_set s {s with iLo := s.iLo + 1} s.iLo _ rfl (by
      rw [cells_get]
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k <;> simp [clrCell, cellAt, St.flag]) (fun i _ hi => by
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k
      · rfl
      · rfl
      · rfl
      · exact flag_shift hi)] at hx

/-- `take inner`, no mark. -/
theorem Exec.take_inner_miss {pc yes no : ℕ} (hI : P.2[pc]? = some (.take .inner yes no)) (s : St)
    (h : s.iHi ≤ s.iLo) : Exec P pc s no s 1 := by
  refine Exec.single (fun hw => hw) le_rfl (k := 2 * s.len + 2) (fun _ => by omega) (fun _ => ?_)
  have hx := exec_take_miss (P := P) (lookup_addr hI) (cells s)
    (fun i hi => by rw [cells_get]; simp [cellAt, St.flag]; omega)
  rwa [cells_length] at hx

/-! ### `inc` and `emit` -/

/-- `dest := dest + 1`; the work region grows if needed. -/
theorem Exec.inc {pc next : ℕ} (hI : P.2[pc]? = some (.inc next)) (s : St) :
    Exec P pc s next {s with dst := s.dst + 1, len := max s.len (s.dst + 1)} 1 := by
  intro hw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  have hwf : ({s with dst := s.dst + 1, len := max s.len (s.dst + 1)} : St).WF :=
    ⟨by show s.x.length ≤ max s.len (s.dst + 1); omega,
      by show s.acc ≤ max s.len (s.dst + 1); omega,
      by show s.dst + 1 ≤ max s.len (s.dst + 1); omega,
      by show s.oHi ≤ max s.len (s.dst + 1); omega,
      by show s.iHi ≤ max s.len (s.dst + 1); omega,
      by show s.out.length ≤ max s.len (s.dst + 1); omega⟩
  refine ⟨hwf, by show s.len ≤ max s.len (s.dst + 1); omega, ?_⟩
  by_cases hd : s.dst < s.len
  · have hx := exec_inc_in (P := P) (lookup_addr hI) (cells s) s.dst (by simpa using hd)
      (fun i hi hij => by rw [cells_get]; simp [cellAt, St.flag]; omega)
      (by rw [cells_get]; simp [cellAt, St.flag])
    rw [cells_set s {s with dst := s.dst + 1, len := max s.len (s.dst + 1)} s.dst _
      (by show max s.len (s.dst + 1) = s.len; omega) (by
      rw [cells_get]
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k <;> simp [setDest, cellAt, St.flag]) (fun i _ hi => by
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k
      · rfl
      · exact flag_succ hi
      · rfl
      · rfl)] at hx
    refine ⟨_, hx, ?_⟩
    show 2 * s.dst + 2 ≤ 1 * (2 * max s.len (s.dst + 1) + 4)
    omega
  · have hdl : s.dst = s.len := by omega
    have hx := exec_inc_end (P := P) (lookup_addr hI) (cells s)
      (fun i hi => by
        rw [cells_get]; simp [cellAt, St.flag]
        have : i < s.len := by simpa using hi
        omega)
    rw [cells_snoc s {s with dst := s.dst + 1, len := max s.len (s.dst + 1)} _
      (by show max s.len (s.dst + 1) = s.len + 1; omega) (by
      refine Cell.ext' ?_ (funext fun k => ?_) ?_
      · show (none : Option Bool) = s.x[s.len]?
        rw [List.getElem?_eq_none h1]
      · cases k <;> simp [setDest, emptyCell, cellAt, St.flag] <;> omega
      · show (none : Option Bool) = s.out[s.len]?
        rw [List.getElem?_eq_none h6]) (fun i hi => by
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k <;> simp [cellAt, St.flag]
      omega)] at hx
    refine ⟨_, hx, ?_⟩
    show 2 * (cells s).length + 2 ≤ 1 * (2 * max s.len (s.dst + 1) + 4)
    rw [cells_length]
    omega

/-- One more output bit; the work region grows if needed. -/
theorem Exec.emit {pc next : ℕ} {b : Bool} (hI : P.2[pc]? = some (.emit b next)) (s : St) :
    Exec P pc s next {s with out := s.out ++ [b], len := max s.len (s.out.length + 1)} 1 := by
  intro hw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  have hwf : ({s with out := s.out ++ [b], len := max s.len (s.out.length + 1)} : St).WF :=
    ⟨by show s.x.length ≤ max s.len (s.out.length + 1); omega,
      by show s.acc ≤ max s.len (s.out.length + 1); omega,
      by show s.dst ≤ max s.len (s.out.length + 1); omega,
      by show s.oHi ≤ max s.len (s.out.length + 1); omega,
      by show s.iHi ≤ max s.len (s.out.length + 1); omega,
      by show (s.out ++ [b]).length ≤ max s.len (s.out.length + 1)
         rw [List.length_append, List.length_singleton]; omega⟩
  refine ⟨hwf, by show s.len ≤ max s.len (s.out.length + 1); omega, ?_⟩
  have hother : ∀ i, i ≠ s.out.length → (s.out ++ [b])[i]? = s.out[i]? := by
    intro i hi
    by_cases hlt : i < s.out.length
    · rw [List.getElem?_append_left hlt]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  have hnew : (s.out ++ [b])[s.out.length]? = some b := by simp
  by_cases hd : s.out.length < s.len
  · have hx := exec_emit_in (P := P) (b := b) (lookup_addr hI) (cells s) s.out.length
      (by simpa using hd)
      (fun i hi hij => by
        rw [cells_get]
        show (s.out[i]?).isSome = true
        rw [List.getElem?_eq_getElem hij]; rfl)
      (by
        rw [cells_get]
        show s.out[s.out.length]? = none
        exact List.getElem?_eq_none le_rfl)
    rw [cells_set s {s with out := s.out ++ [b], len := max s.len (s.out.length + 1)}
      s.out.length _ (by show max s.len (s.out.length + 1) = s.len; omega) (by
      rw [cells_get]
      refine Cell.ext' rfl rfl ?_
      show some b = (s.out ++ [b])[s.out.length]?
      rw [hnew]) (fun i _ hi => by
      refine Cell.ext' rfl rfl ?_
      show (s.out ++ [b])[i]? = s.out[i]?
      exact hother i hi)] at hx
    refine ⟨_, hx, ?_⟩
    show 2 * s.out.length + 2 ≤ 1 * (2 * max s.len (s.out.length + 1) + 4)
    omega
  · have hdl : s.out.length = s.len := by omega
    have hx := exec_emit_end (P := P) (b := b) (lookup_addr hI) (cells s)
      (fun i hi => by
        rw [cells_get]
        show (s.out[i]?).isSome = true
        have : i < s.len := by simpa using hi
        rw [List.getElem?_eq_getElem (by omega)]; rfl)
    rw [cells_snoc s {s with out := s.out ++ [b], len := max s.len (s.out.length + 1)} _
      (by show max s.len (s.out.length + 1) = s.len + 1; omega) (by
      refine Cell.ext' ?_ (funext fun k => ?_) ?_
      · show (none : Option Bool) = s.x[s.len]?
        rw [List.getElem?_eq_none h1]
      · cases k <;> simp [setOut, emptyCell, cellAt, St.flag] <;> omega
      · show some b = (s.out ++ [b])[s.len]?
        rw [← hdl, hnew]) (fun i hi => by
      refine Cell.ext' rfl rfl ?_
      show (s.out ++ [b])[i]? = s.out[i]?
      exact hother i (by omega))] at hx
    refine ⟨_, hx, ?_⟩
    show 2 * (cells s).length + 2 ≤ 1 * (2 * max s.len (s.out.length + 1) + 4)
    rw [cells_length]
    omega

/-! ### `nextInput` and `headInput` -/

/-- `nextInput`, a mark is left on cell `oLo`: it is cleared and the input bit of cell `oLo + 1`
selects the continuation. -/
theorem Exec.next_hit {pc b z o ex : ℕ} (hI : P.2[pc]? = some (.nextInput b z o ex)) (s : St)
    (h : s.oLo < s.oHi) :
    Exec P pc s (sel3 s.x[s.oLo + 1]? b z o) {s with oLo := s.oLo + 1} 1 := by
  refine Exec.single (fun hw => hw) le_rfl (k := 2 * s.oLo + 4) (fun hw => ?_) (fun hw => ?_)
  · have := hw.2.2.2.1
    show 2 * s.oLo + 4 ≤ 2 * s.len + 4
    omega
  · have hj : s.oLo < (cells s).length := by have := hw.2.2.2.1; simp; omega
    have hx := exec_next_hit (P := P) (lookup_addr hI) (cells s) s.oLo hj
      (fun i hi hij => by rw [cells_get]; simp [cellAt, St.flag]; omega)
      (by rw [cells_get]; simp [cellAt, St.flag]; omega)
    rw [inpAt_cells s hw.1] at hx
    rwa [cells_set s {s with oLo := s.oLo + 1} s.oLo _ rfl (by
      rw [cells_get]
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k <;> simp [clrCell, cellAt, St.flag]) (fun i _ hi => by
      refine Cell.ext' rfl (funext fun k => ?_) rfl
      cases k
      · rfl
      · rfl
      · exact flag_shift hi
      · rfl)] at hx

/-- `nextInput`, no mark. -/
theorem Exec.next_miss {pc b z o ex : ℕ} (hI : P.2[pc]? = some (.nextInput b z o ex)) (s : St)
    (h : s.oHi ≤ s.oLo) : Exec P pc s ex s 1 := by
  refine Exec.single (fun hw => hw) le_rfl (k := 2 * s.len + 2) (fun _ => by omega) (fun _ => ?_)
  have hx := exec_next_miss (P := P) (lookup_addr hI) (cells s)
    (fun i hi => by rw [cells_get]; simp [cellAt, St.flag]; omega)
  rwa [cells_length] at hx

/-- `headInput`: the input bit of cell `0` selects the continuation. -/
theorem Exec.head {pc b z o : ℕ} (hI : P.2[pc]? = some (.headInput b z o)) (s : St) :
    Exec P pc s (sel3 s.x[0]? b z o) s 1 := by
  refine Exec.single (fun hw => hw) le_rfl (k := 2) (fun _ => by omega) (fun hw => ?_)
  have hx := exec_head (P := P) (lookup_addr hI) (cells s)
  rwa [inpAt_cells s hw.1] at hx

/-! ### `finish` -/

/-- The final scan on a well-formed state shows exactly the output prefix. -/
theorem finish_state {pc : ℕ} (hI : P.2[pc]? = some .finish) (s : St) (hw : s.WF) :
    ∃ T : ℤ → Sym, Steps P (⟨tapeOf (cells s), 0, .scan (addr P.2 pc)⟩ : (build P).Cfg)
        (⟨T, (s.out.length : ℤ) + 1, .done⟩ : (build P).Cfg) (s.out.length + 1) ∧
      (∀ i : ℕ, i < s.out.length → T (i : ℤ) = .raw (s.out.getD i false)) ∧
      T (s.out.length : ℤ) = .blank :=
  exec_finish (P := P) (lookup_addr hI) (cells s) s.out (by simpa using hw.2.2.2.2.2)
    (fun j hj => by rw [cells_get]; rfl)

end Exec

end PVNP.TwoPhasePolynomialWriter
