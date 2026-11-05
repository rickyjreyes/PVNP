import PVNP.UniformSimMath

/-!
# Milestone 5, part 5: from the input to the parsed lattice description

* `machine_phase`: a simulated machine runs from its entry instruction to its first halting time.
* `pre_machines`: after `init`, the lattice machine and the encoder have run; the `lat` and `enc`
  tracks hold their outputs `latCode` and `cfgCode (enc x)`.
* `parse_trip`: the parse of the lattice description marks the prefix, the box, the members and
  the first box cell.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

/-- A representation on one track survives changes confined to an independent track. -/
theorem FRep.of_agree {C Γ T' : Type} {L1 : Lens C (FCell Γ)} {L2 : Lens C T'} {blank : Γ}
    {d : C} {l l' : List C} {T : ℤ → Γ} {h : ℤ}
    (hrep : FRep L1.get blank l T h) (hag : Agree L2 d l l')
    (hind : ∀ t c, L1.get (L2.set t c) = L1.get c) (hd : L1.get d = ⟨blank, blank, none, none⟩) :
    FRep L1.get blank l' T h := by
  obtain ⟨hlen, hcell⟩ := hag
  have hlo := hrep.hlo
  have hhi := hrep.hhi
  refine ⟨fun j hj => ?_, fun i hi => hrep.out i (by omega), by omega, by omega⟩
  rw [hcell j hj, hind]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl]; exact hrep.cell j hjl
  · rw [List.getD_eq_default _ _ (by omega), hd]
    have h1 := hrep.out j (Or.inl (by omega))
    have h2 := hrep.out (-(j : ℤ) - 1) (Or.inr (by omega))
    have h3 : headAt h j = none := by
      unfold headAt; rw [if_neg (by omega), if_neg (by omega)]
    rw [h1, h2, h3]

theorem inputTape_nat (M : MTM) (x : List Bool) (j : ℕ) :
    M.inputTape x j = Spec.inSym M x[j]? := by
  by_cases hj : j < x.length
  · rw [M.inputTape_ne_blank (by omega) (by exact_mod_cast hj)]
    simp [Spec.inSym, List.getElem?_eq_getElem hj]
  · rw [M.inputTape_blank (Or.inr (by exact_mod_cast (Nat.le_of_not_lt hj))),
      List.getElem?_eq_none (by omega)]
    rfl

theorem inputTape_negSide (M : MTM) (x : List Bool) (j : ℕ) :
    M.inputTape x (-(j : ℤ) - 1) = M.blank := M.inputTape_blank (Or.inl (by omega))

theorem headAt_zero (j : ℕ) : headAt 0 j = if j = 0 then some true else none := by
  unfold headAt
  by_cases hj : j = 0
  · subst hj; simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg hj]

/-- The folded input tape with the head on cell `0`. -/
def initFC (M : MTM) (x : List Bool) (j : ℕ) : FCell M.Γ :=
  ⟨Spec.inSym M x[j]?, M.blank, if j = 0 then some true else none, none⟩

theorem frep_init {C : Type} (M : MTM) (L : Lens C (FCell M.Γ)) (x : List Bool) (l : List C)
    (hl : x.length ≤ l.length) (hl1 : 1 ≤ l.length)
    (hcell : ∀ (j : ℕ) (hj : j < l.length), L.get l[j] = initFC M x j) :
    FRep L.get M.blank l (M.inputTape x) 0 := by
  refine ⟨fun j hj => ?_, fun i hi => M.inputTape_blank (by omega), by omega, by omega⟩
  rw [hcell j hj, initFC, inputTape_nat, inputTape_negSide, headAt_zero]

namespace Spec

variable (σ : Spec)

/-! ### Machine phases -/

theorem machine_phase (M : MTM) (L : Lens (Cell σ) (FCell M.Γ)) (LB : Lens (Buf σ) (SimBuf M.Q))
    (simI : M.Q → Ins σ) (exitI : Ins σ)
    (hfwd : ∀ q, σ.fwd (simI q) = gF M L LB q)
    (hbwd : ∀ q, σ.bwd (simI q) = gB M L LB)
    (hext : ∀ q, σ.ext (simI q) = gE M L LB σ.dflt)
    (hb0 : LB.get σ.buf0 = SimBuf.start M.Q)
    (hnext : ∀ q b, σ.next (simI q) b =
      match (LB.get b).nq with
      | some q' => if haltingQ M q' then .inl exitI else .inl (simI q')
      | none => .inl exitI)
    (z : List Bool) (l : List (Cell σ)) (hrep : FRep L.get M.blank l (M.inputTape z) 0)
    {t : ℕ} (hf : M.FirstHalt z t) :
    ∃ l', RN σ.prog ((if haltingQ M M.q0 then exitI else simI M.q0), l) (exitI, l') t ∧
      FRep L.get M.blank l' (M.run (M.init z) t).tape (M.run (M.init z) t).head ∧
      Agree L σ.dflt l l' ∧ l'.length ≤ l.length + t := by
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    have hq : haltingQ M M.q0 = true := (haltingQ_iff M _).2 hf.1
    rw [if_pos hq]
    exact ⟨l, RN.refl _, hrep, Agree.refl _ _ _, by omega⟩
  · have hq : haltingQ M M.q0 = false := by
      have := hf.2 0 h0
      rw [Bool.eq_false_iff]
      exact fun h => this ((haltingQ_iff M _).1 h)
    rw [if_neg (by rw [hq]; decide)]
    exact σ.sim_loop M L LB simI exitI hfwd hbwd hext hb0 hnext t (M.init z) l hrep
      (fun s hs => by
        rw [Bool.eq_false_iff]
        exact fun h => hf.2 s hs ((haltingQ_iff M _).1 h))
      ((haltingQ_iff M _).2 hf.1) h0

theorem machine_phase_L (z : List Bool) (l : List (Cell σ))
    (hrep : FRep σ.latL.get σ.ML.blank l (σ.ML.inputTape z) 0) {t : ℕ}
    (hf : σ.ML.FirstHalt z t) :
    ∃ l', RN σ.prog (σ.latEntry, l) (σ.latExit, l') t ∧
      FRep σ.latL.get σ.ML.blank l' (σ.ML.run (σ.ML.init z) t).tape
        (σ.ML.run (σ.ML.init z) t).head ∧
      Agree σ.latL σ.dflt l l' ∧ l'.length ≤ l.length + t :=
  σ.machine_phase σ.ML σ.latL σ.sLL Ins.simL σ.latExit (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl (fun q b => by rcases hq : b.sL.nq with _ | q' <;> simp [next, sLL, hq]) z l hrep hf

theorem machine_phase_E (z : List Bool) (l : List (Cell σ))
    (hrep : FRep σ.encL.get σ.ME.blank l (σ.ME.inputTape z) 0) {t : ℕ}
    (hf : σ.ME.FirstHalt z t) :
    ∃ l', RN σ.prog (σ.encEntry, l) (.parse, l') t ∧
      FRep σ.encL.get σ.ME.blank l' (σ.ME.run (σ.ME.init z) t).tape
        (σ.ME.run (σ.ME.init z) t).head ∧
      Agree σ.encL σ.dflt l l' ∧ l'.length ≤ l.length + t :=
  σ.machine_phase σ.ME σ.encL σ.sEL Ins.simE .parse (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl (fun q b => by rcases hq : b.sE.nq with _ | q' <;> simp [next, sEL, hq]) z l hrep hf

theorem machine_phase_D (z : List Bool) (l : List (Cell σ))
    (hrep : FRep σ.decL.get σ.MD.blank l (σ.MD.inputTape z) 0) {t : ℕ}
    (hf : σ.MD.FirstHalt z t) :
    ∃ l', RN σ.prog (σ.decEntry, l) (.dread, l') t ∧
      FRep σ.decL.get σ.MD.blank l' (σ.MD.run (σ.MD.init z) t).tape
        (σ.MD.run (σ.MD.init z) t).head ∧
      Agree σ.decL σ.dflt l l' ∧ l'.length ≤ l.length + t :=
  σ.machine_phase σ.MD σ.decL σ.sDL Ins.simD .dread (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl (fun q b => by rcases hq : b.sD.nq with _ | q' <;> simp [next, sDL, hq]) z l hrep hf

/-! ### The machines witnessing uniformity -/

/-- The machines of `σ` compute the lattice description, the initial code and the decoder within
polynomial bounds. -/
structure Correct where
  pL : Polynomial ℕ
  pE : Polynomial ℕ
  pD : Polynomial ℕ
  hL : ∀ y : List Bool,
    σ.ML.Outputs y (latCode σ.W.d (σ.W.R y.length) (σ.W.Λ y.length)) (pL.eval y.length)
  hE : ∀ x : List Bool,
    σ.ME.Outputs x (cfgCode σ.W.bits σ.W.d (σ.W.R x.length) (σ.W.Λ x.length) (σ.W.enc x))
      (pE.eval x.length)
  hD : ∀ (n : ℕ) (C : (Fin σ.W.d → ℤ) → σ.W.S),
    σ.MD.Outputs (List.replicate n true ++ false :: cfgCode σ.W.bits σ.W.d (σ.W.R n) (σ.W.Λ n) C)
      (decOut (σ.W.dec n C)) (pD.eval n)

/-! ### From the input to the parse -/

/-- Cells before the parse: the input and cell-`0` flag, the `lat` and `enc` tracks, defaults
elsewhere. -/
def baseCell (x : List Bool) (j : ℕ) (a : FCell σ.ML.Γ) (e : FCell σ.ME.Γ) : Cell σ :=
  {σ.dflt with inp := x[j]?, fst := decide (j = 0), lat := a, enc := e}

/-- `l` consists of base cells. -/
def IsBase (x : List Bool) (l : List (Cell σ)) : Prop :=
  ∀ (j : ℕ) (hj : j < l.length), l[j] = σ.baseCell x j l[j].lat l[j].enc

theorem isBase_init (x : List Bool) :
    σ.IsBase x ((List.range (max x.length 1)).map (σ.initCell x)) := by
  intro j hj
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem isBase_agree_lat (x : List Bool) {l l' : List (Cell σ)} (hb : σ.IsBase x l)
    (hl : max x.length 1 ≤ l.length) (hag : Agree σ.latL σ.dflt l l') : σ.IsBase x l' := by
  intro j hj
  rw [hag.2 j hj]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, hb j hjl]
    rfl
  · rw [List.getD_eq_default _ _ (by omega)]
    simp only [baseCell, latL, List.getElem?_eq_none (show x.length ≤ j by omega),
      show ¬ j = 0 by omega, decide_false]
    rfl

theorem isBase_agree_enc (x : List Bool) {l l' : List (Cell σ)} (hb : σ.IsBase x l)
    (hl : max x.length 1 ≤ l.length) (hag : Agree σ.encL σ.dflt l l') : σ.IsBase x l' := by
  intro j hj
  rw [hag.2 j hj]
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem _ _ hjl, hb j hjl]
    rfl
  · rw [List.getD_eq_default _ _ (by omega)]
    simp only [baseCell, encL, List.getElem?_eq_none (show x.length ≤ j by omega),
      show ¬ j = 0 by omega, decide_false]
    rfl

/-- Output convention: the output occupies the cells of the list. -/
theorem shows_len {M : MTM} {L : Lens (Cell σ) (FCell M.Γ)} {l : List (Cell σ)} {c : M.Cfg}
    {y : List Bool} (hrep : FRep L.get M.blank l c.tape c.head) (hs : M.Shows c y) :
    y.length ≤ l.length := by
  by_contra h
  have h1 := hs.1 l.length (by omega)
  rw [hrep.out l.length (Or.inl le_rfl)] at h1
  exact M.inp_ne_blank _ h1.symm

theorem shows_cell {M : MTM} {c : M.Cfg} {y : List Bool} (hs : M.Shows c y) (j : ℕ)
    (hj : j ≤ y.length) : c.tape j = Spec.inSym M y[j]? := by
  rcases Nat.lt_or_ge j y.length with h | h
  · rw [hs.1 j h, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]; rfl
  · have : j = y.length := by omega
    subst this
    rw [hs.2, List.getElem?_eq_none le_rfl]; rfl

/-- **The machine phases.**  After `init`, `simL*` and `simE*`, the program is at `parse` with the
lattice description on the `lat` track and the initial configuration code on the `enc` track. -/
theorem pre_machines (hC : σ.Correct) (x : List Bool) (hg : σ.guard = false ∨ PS.run .tag x = .ok) :
    ∃ (l : List (Cell σ)) (k : ℕ) (cL : σ.ML.Cfg) (cE : σ.ME.Cfg),
      RN σ.prog (.init, x.map σ.lift) (.parse, l) k ∧
      k ≤ 1 + hC.pL.eval x.length + hC.pE.eval x.length ∧
      FRep σ.latL.get σ.ML.blank l cL.tape cL.head ∧
      σ.ML.Shows cL (latCode σ.W.d (σ.W.R x.length) (σ.W.Λ x.length)) ∧
      FRep σ.encL.get σ.ME.blank l cE.tape cE.head ∧
      σ.ME.Shows cE (cfgCode σ.W.bits σ.W.d (σ.W.R x.length) (σ.W.Λ x.length) (σ.W.enc x)) ∧
      σ.IsBase x l ∧ max x.length 1 ≤ l.length ∧
      l.length ≤ max x.length 1 + hC.pL.eval x.length + hC.pE.eval x.length := by
  obtain ⟨hl0, hg0⟩ := σ.init_trip x
  set l0 := (List.range (max x.length 1)).map (σ.initCell x) with hl0def
  have hlen0 : l0.length = max x.length 1 := by simp [hl0def]
  -- the initialization trip
  have hs0 : σ.prog.stepP (.init, x.map σ.lift) = .inl (σ.latEntry, l0) := by
    rw [← hl0]
    apply σ.stepP_inl_of
    show (if σ.guard && (σ.prog.trip .init (x.map σ.lift)).2.g != .ok then _ else _) = _
    rw [hg0]
    rcases hg with hg | hg
    · simp [hg]
    · simp [hg]
  -- the lattice machine
  have hrepL : FRep σ.latL.get σ.ML.blank l0 (σ.ML.inputTape x) 0 :=
    frep_init σ.ML σ.latL x l0 (by omega) (by omega) (fun j hj => by
      simp only [hl0def, List.getElem_map, List.getElem_range]; rfl)
  have hrepE : FRep σ.encL.get σ.ME.blank l0 (σ.ME.inputTape x) 0 :=
    frep_init σ.ME σ.encL x l0 (by omega) (by omega) (fun j hj => by
      simp only [hl0def, List.getElem_map, List.getElem_range]; rfl)
  obtain ⟨tL, htL, hfL, hsL⟩ := hC.hL x
  obtain ⟨l1, hrn1, hrep1, hag1, hlen1⟩ := σ.machine_phase_L x l0 hrepL hfL
  have hrepE1 : FRep σ.encL.get σ.ME.blank l1 (σ.ME.inputTape x) 0 :=
    FRep.of_agree hrepE hag1 (fun _ _ => rfl) rfl
  obtain ⟨tE, htE, hfE, hsE⟩ := hC.hE x
  obtain ⟨l2, hrn2, hrep2, hag2, hlen2⟩ := σ.machine_phase_E x l1 hrepE1 hfE
  have hrepL2 := FRep.of_agree hrep1 hag2 (fun _ _ => rfl) rfl
  have hb1 := σ.isBase_agree_lat x (σ.isBase_init x) (by simp) hag1
  have hb2 := σ.isBase_agree_enc x hb1 (by have := hag1.1; omega) hag2
  refine ⟨l2, 1 + tL + tE, _, _, ?_, by omega, hrepL2, hsL, hrep2, hsE, hb2,
    by have := hag1.1; have := hag2.1; omega, by omega⟩
  have h01 : RN σ.prog (.init, x.map σ.lift) (σ.latEntry, l0) 1 := RN.single hs0
  have := (h01.trans hrn1).trans hrn2
  simpa [latExit] using this

end Spec

end PVNP.UniformSim

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

namespace Spec

variable (σ : Spec)

/-! ### The parse -/

/-- A fetch-only round trip: identity backward pass, no extension. -/
theorem trip_fwd_get (i : Ins σ) (hb : ∀ b a, σ.bwd i b a = (a, b)) (he : ∀ b, σ.ext i b = none)
    (l : List (Cell σ)) (bufAt : ℕ → Buf σ) (h0 : bufAt 0 = σ.buf0)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (σ.fwd i (bufAt j) l[j]).2 = bufAt (j + 1)) :
    (σ.prog.trip i l).1.length = l.length ∧
      (∀ (j : ℕ) (hj : j < l.length) (hj' : j < (σ.prog.trip i l).1.length),
        (σ.prog.trip i l).1[j] = (σ.fwd i (bufAt j) l[j]).1) ∧
      (σ.prog.trip i l).2 = bufAt l.length := by
  rw [σ.trip_fwd i hb he l, ← h0]
  refine ⟨fscan_length _ _ _, fun j hj _ => ?_, fscan_spec_buf _ l bufAt hstep⟩
  exact fscan_spec_get _ l bufAt hstep j hj

/-- Phase of the parse after `j` cells. -/
def phP (R Bd j : ℕ) : Fin 3 := if j ≤ R then 0 else if j ≤ R + 1 + Bd then 1 else 2

/-- Buffer of the parse after `j` cells. -/
def bufP (R Bd j : ℕ) : Buf σ :=
  {σ.buf0 with ph := phP R Bd j, f1 := decide (0 < j), f2 := decide (R + 2 ≤ j)}

/-- The cells after the parse. -/
def parsed (R Bd : ℕ) (bm : ℕ → Bool) (j : ℕ) (c : Cell σ) : Cell σ :=
  {c with
    pre := decide (j < R)
    box := decide (R + 1 ≤ j ∧ j < R + 1 + Bd)
    mem := decide (R + 1 ≤ j ∧ j < R + 1 + Bd) && bm j
    rfst := decide (j = R + 1)
    rul := decide (j = R + 1)
    pp := decide (j = 0 ∧ 0 < R)
    gp := decide (j = R + 1)}

theorem parse_cell (R Bd : ℕ) (hBd : 1 ≤ Bd) (bm : ℕ → Bool) (j : ℕ) (a : Cell σ)
    (hpre : j < R → a.lat.r = σ.ML.inp true)
    (hsep : j = R → a.lat.r = σ.ML.inp false)
    (hbm : R + 1 ≤ j → j < R + 1 + Bd → a.lat.r = σ.ML.inp (bm j))
    (hend : j = R + 1 + Bd → a.lat.r = σ.ML.blank) :
    σ.fwd .parse (σ.bufP R Bd j) a = (σ.parsed R Bd bm j a, σ.bufP R Bd (j + 1)) := by
  have hne : σ.ML.inp false ≠ σ.ML.inp true := fun h => Bool.false_ne_true (σ.ML.inp_inj h)
  have e7 : decide (0 < j + 1) = true := decide_eq_true (by omega)
  rcases Nat.lt_or_ge j R with h1 | h1
  · have hph : phP R Bd j = 0 := by unfold phP; rw [if_pos (by omega)]
    have hph' : phP R Bd (j + 1) = 0 := by unfold phP; rw [if_pos (by omega)]
    have e1 : decide (j < R) = true := decide_eq_true h1
    have e2 : decide (R + 1 ≤ j ∧ j < R + 1 + Bd) = false := decide_eq_false (by omega)
    have e3 : decide (j = R + 1) = false := decide_eq_false (by omega)
    have e4 : decide (j = 0 ∧ 0 < R) = !decide (0 < j) := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; rw [decide_eq_true (by omega), decide_eq_false (by omega)]; rfl
      · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
    have e5 : decide (R + 2 ≤ j) = false := decide_eq_false (by omega)
    have e6 : decide (R + 2 ≤ j + 1) = false := decide_eq_false (by omega)
    simp only [fwd, bufP, hph, hpre h1, if_true, parsed, hph', e1, e2, e3, e4, e5, e6, e7,
      Bool.false_and]
  rcases Nat.lt_or_ge R j with h2 | h2
  · have e1 : decide (j < R) = false := decide_eq_false (by omega)
    have e4 : decide (j = 0 ∧ 0 < R) = false := decide_eq_false (by omega)
    have e8 : decide (0 < j) = true := decide_eq_true (by omega)
    have e6 : decide (R + 2 ≤ j + 1) = true := decide_eq_true (by omega)
    rcases Nat.lt_or_ge j (R + 1 + Bd) with h3 | h3
    · have hph : phP R Bd j = 1 := by unfold phP; rw [if_neg (by omega), if_pos (by omega)]
      have hph' : phP R Bd (j + 1) = 1 := by
        unfold phP; rw [if_neg (by omega), if_pos (by omega)]
      have hnb : σ.ML.inp (bm j) ≠ σ.ML.blank := σ.ML.inp_ne_blank _
      have e2 : decide (R + 1 ≤ j ∧ j < R + 1 + Bd) = true := decide_eq_true (by omega)
      have e3 : decide (j = R + 1) = !decide (R + 2 ≤ j) := by
        by_cases h : j = R + 1
        · subst h; simp
        · simp [h]; omega
      simp only [fwd, bufP, hph, hbm (by omega) h3, if_neg hnb, parsed, hph', symBit_inp, e1, e2,
        e3, e4, e6, e7, e8, Bool.true_and]
    · have e2 : decide (R + 1 ≤ j ∧ j < R + 1 + Bd) = false := decide_eq_false (by omega)
      have e3 : decide (j = R + 1) = false := decide_eq_false (by omega)
      have e5 : decide (R + 2 ≤ j) = true := decide_eq_true (by omega)
      rcases Nat.lt_or_ge (R + 1 + Bd) j with h4 | h4
      · have hph : phP R Bd j = 2 := by unfold phP; rw [if_neg (by omega), if_neg (by omega)]
        have hph' : phP R Bd (j + 1) = 2 := by
          unfold phP; rw [if_neg (by omega), if_neg (by omega)]
        simp only [fwd, bufP, hph, parsed, hph', e1, e2, e3, e4, e5, e6, e7, e8, Bool.false_and]
      · have hj : j = R + 1 + Bd := by omega
        have hph : phP R Bd j = 1 := by unfold phP; rw [if_neg (by omega), if_pos (by omega)]
        have hph' : phP R Bd (j + 1) = 2 := by
          unfold phP; rw [if_neg (by omega), if_neg (by omega)]
        simp only [fwd, bufP, hph, hend hj, if_true, parsed, hph', e1, e2, e3, e4, e5, e6, e7, e8,
          Bool.false_and]
  · have hj : j = R := by omega
    have hph : phP R Bd j = 0 := by unfold phP; rw [if_pos (by omega)]
    have hph' : phP R Bd (j + 1) = 1 := by unfold phP; rw [if_neg (by omega), if_pos (by omega)]
    have e1 : decide (j < R) = false := decide_eq_false (by omega)
    have e2 : decide (R + 1 ≤ j ∧ j < R + 1 + Bd) = false := decide_eq_false (by omega)
    have e3 : decide (j = R + 1) = false := decide_eq_false (by omega)
    have e4 : decide (j = 0 ∧ 0 < R) = false := decide_eq_false (by omega)
    have e5 : decide (R + 2 ≤ j) = false := decide_eq_false (by omega)
    have e6 : decide (R + 2 ≤ j + 1) = false := decide_eq_false (by omega)
    simp only [fwd, bufP, hph, hsep hj, if_neg hne, parsed, hph', e1, e2, e3, e4, e5, e6, e7,
      Bool.false_and]

/-- **The parse trip.** -/
theorem parse_trip (R Bd : ℕ) (hBd : 1 ≤ Bd) (bm : ℕ → Bool) (l : List (Cell σ))
    (hlat : ∀ (j : ℕ) (hj : j < l.length),
      (j < R → l[j].lat.r = σ.ML.inp true) ∧ (j = R → l[j].lat.r = σ.ML.inp false) ∧
      (R + 1 ≤ j → j < R + 1 + Bd → l[j].lat.r = σ.ML.inp (bm j)) ∧
      (j = R + 1 + Bd → l[j].lat.r = σ.ML.blank)) :
    (σ.prog.trip .parse l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip .parse l).1.length) (hj' : j < l.length),
        (σ.prog.trip .parse l).1[j] = σ.parsed R Bd bm j l[j] := by
  have hc : ∀ (j : ℕ) (hj : j < l.length),
      σ.fwd .parse (σ.bufP R Bd j) l[j] = (σ.parsed R Bd bm j l[j], σ.bufP R Bd (j + 1)) :=
    fun j hj => σ.parse_cell R Bd hBd bm j l[j] (hlat j hj).1 (hlat j hj).2.1 (hlat j hj).2.2.1
      (hlat j hj).2.2.2
  obtain ⟨hlen, hget, -⟩ := σ.trip_fwd_get .parse (fun _ _ => rfl) (fun _ => rfl) l
    (σ.bufP R Bd) (by simp [bufP, phP]; rfl) (fun j hj => by rw [hc j hj])
  refine ⟨hlen, fun j hj hj' => ?_⟩
  rw [hget j hj' hj, hc j hj']

end Spec

end PVNP.UniformSim
