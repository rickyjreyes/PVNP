import PVNP.CookLevinGen
import PVNP.UniformSimPre

/-!
# CL-1, part 3: the generator followed by a decider

For a control program `G` (the Cook–Levin generator) and a manuscript Turing machine `S` (a
decider for `SAT_dense`), `decProg G S` is one round-trip sweep program whose data cells pair a
generator cell with a folded tape cell of `S`:

1. it runs `G` on the first component (`dec_lift`, `dec_lift_exit`);
2. one round trip copies the `out` track of `G` onto the folded tape of `S` as `S`'s input,
   with the head on cell `0` (`dec_conv`);
3. it simulates `S` one step per round trip (`simTrip_spec`) and answers when `S` halts
   (`dec_sim_loop`, `dec_sim_halt`).

`dec_halts` is the end-to-end statement, with an explicit bound on the round-trip cost.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim PVNP.PartI PVNP.CookLevin
open PVNP.PartIITuring

section Decide

variable (G : Ctrl) (S : MTM)

/-- The blank folded cell. -/
def fc0 : FCell S.Γ := ⟨S.blank, S.blank, none, none⟩

/-- The folded track of a decider cell. -/
def dL : Lens (Cell × FCell S.Γ) (FCell S.Γ) :=
  ⟨Prod.snd, fun t c => (c.1, t), fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The simulation buffer. -/
def dLB : Lens (Buf × SimBuf S.Q) (SimBuf S.Q) :=
  ⟨Prod.snd, fun t b => (b.1, t), fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- Conversion of one cell: the output bit becomes the input symbol of `S`. -/
def convF (b : Buf × SimBuf S.Q) (a : Cell × FCell S.Γ) :
    (Cell × FCell S.Γ) × (Buf × SimBuf S.Q) :=
  ((a.1, ⟨Spec.inSym S a.1.out, S.blank, if b.2.first then some true else none, none⟩),
    (b.1, {b.2 with first := false}))

/-- Halting states of `S`. -/
def hQ (q : S.Q) : Bool := decide (q = S.qacc ∨ q = S.qrej)

/-- An initial generator buffer for the non-generator instructions. -/
def buf0 : Buf := (false, RS.start)

/-- **The decider**: run `G`, convert its output, simulate `S`. -/
def decProg : Prog where
  D := Cell × FCell S.Γ
  I := G.C ⊕ (Unit ⊕ S.Q)
  B := Buf × SimBuf S.Q
  lift b := (liftC b, fc0 S)
  start := .inl G.start
  init
    | .inl c => ((G.op c).init, SimBuf.start S.Q)
    | .inr _ => (buf0, SimBuf.start S.Q)
  fwd
    | .inl c => fun b a => ((((G.op c).fwd b.1 a.1).1, a.2), (((G.op c).fwd b.1 a.1).2, b.2))
    | .inr (.inl _) => convF S
    | .inr (.inr q) => gF S (dL S) (dLB S) q
  ext
    | .inl c => fun b => ((G.op c).ext b.1).map fun a => (a, fc0 S)
    | .inr (.inl _) => fun _ => none
    | .inr (.inr _) => gE S (dL S) (dLB S) (dflt, fc0 S)
  bwd
    | .inl _ => fun b a => (a, b)
    | .inr (.inl _) => fun b a => (a, b)
    | .inr (.inr _) => gB S (dL S) (dLB S)
  next
    | .inl c => fun b => match G.prog.next c b.1 with
        | .inl c' => .inl (.inl c')
        | .inr _ => .inl (.inr (.inl ()))
    | .inr (.inl _) => fun _ =>
        if hQ S S.q0 then .inr (decide (S.q0 = S.qacc)) else .inl (.inr (.inr S.q0))
    | .inr (.inr _) => fun b => match ((dLB S).get b).nq with
        | some q' => if hQ S q' then .inr (decide (q' = S.qacc)) else .inl (.inr (.inr q'))
        | none => .inr false

/-! ## Running the generator on the first component -/

theorem bscan_idd {D B : Type} : ∀ (b : B) (l : List D), bscan (fun b a => (a, b)) b l = (l, b)
  | _, [] => rfl
  | b, a :: l => by simp [bscan, bscan_idd b l]

theorem fscan_lift_dec (c : G.C) (sb : SimBuf S.Q) : ∀ (b : Buf) (l : List Cell),
    fscan ((decProg G S).fwd (.inl c)) (b, sb) (l.map (·, fc0 S)) =
      ((fscan (G.op c).fwd b l).1.map (·, fc0 S), ((fscan (G.op c).fwd b l).2, sb))
  | b, [] => rfl
  | b, a :: l => by
    simp only [List.map_cons, fscan]
    have ih := fscan_lift_dec c sb ((G.op c).fwd b a).2 l
    have e : (decProg G S).fwd (.inl c) (b, sb) (a, fc0 S) =
        ((((G.op c).fwd b a).1, fc0 S), (((G.op c).fwd b a).2, sb)) := rfl
    rw [e]
    simp only
    rw [ih]

theorem dec_trip_gen (c : G.C) (l : List Cell) :
    (decProg G S).trip (.inl c) (l.map (·, fc0 S)) =
      ((G.prog.trip c l).1.map (·, fc0 S), ((G.prog.trip c l).2, SimBuf.start S.Q)) := by
  rw [Ctrl.trip_unfold]
  have hb : (decProg G S).bwd (.inl c) = fun b a => (a, b) := rfl
  have hi : (decProg G S).init (.inl c) = ((G.op c).init, SimBuf.start S.Q) := rfl
  have he : ∀ b, (decProg G S).ext (.inl c) b = ((G.op c).ext b.1).map fun a => (a, fc0 S) :=
    fun _ => rfl
  simp only [Prog.trip, Prog.mid, Prog.fpass, hb, hi, he]
  rw [bscan_idd, fscan_lift_dec]
  simp only [List.map_append, Prod.mk.injEq, and_true]
  congr 1
  cases (G.op c).ext (fscan (G.op c).fwd (G.op c).init l).2 <;> rfl

theorem dec_next_gen (c : G.C) (l : List Cell) :
    (decProg G S).next (.inl c) ((decProg G S).trip (.inl c) (l.map (·, fc0 S))).2 =
      match G.prog.next c (G.prog.trip c l).2 with
      | .inl c' => .inl (.inl c')
      | .inr _ => .inl (.inr (.inl ())) := by
  rw [dec_trip_gen]; rfl

theorem dec_step_gen {c c' : G.C} {l l' : List Cell} (h : G.prog.stepP (c, l) = .inl (c', l')) :
    (decProg G S).stepP (.inl c, l.map (·, fc0 S)) = .inl (.inl c', l'.map (·, fc0 S)) := by
  simp only [Prog.stepP] at h ⊢
  rw [dec_next_gen, dec_trip_gen]
  rcases hn : G.prog.next c (G.prog.trip c l).2 with c₁ | a
  · rw [hn] at h
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rw [hn] at h; simp at h

theorem dec_exit_gen {c : G.C} {a : Bool} {l l' : List Cell}
    (h : G.prog.stepP (c, l) = .inr (a, l')) :
    (decProg G S).stepP (.inl c, l.map (·, fc0 S)) = .inl (.inr (.inl ()), l'.map (·, fc0 S)) := by
  simp only [Prog.stepP] at h ⊢
  rw [dec_next_gen, dec_trip_gen]
  rcases hn : G.prog.next c (G.prog.trip c l).2 with c₁ | a'
  · rw [hn] at h; simp at h
  · rw [hn] at h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl

/-- **Lifting the generator's runs.** -/
theorem dec_lift : ∀ {s s' : G.prog.I × List G.prog.D} {k : ℕ}, RN G.prog s s' k →
    RN (decProg G S) (.inl s.1, s.2.map (·, fc0 S)) (.inl s'.1, s'.2.map (·, fc0 S)) k := by
  intro s s' k h
  induction h with
  | refl s => exact RN.refl _
  | @step s s₂ s₃ k hstep _ ih =>
    obtain ⟨c, l⟩ := s
    obtain ⟨c₂, l₂⟩ := s₂
    exact RN.step (dec_step_gen G S hstep) ih

theorem dec_lift_exit {c : G.C} {a : Bool} {l l' : List Cell}
    (h : G.prog.stepP (c, l) = .inr (a, l')) :
    RN (decProg G S) (.inl c, l.map (·, fc0 S)) (.inr (.inl ()), l'.map (·, fc0 S)) 1 :=
  RN.single (dec_exit_gen G S h)

/-! ## The conversion trip -/

theorem fscan_conv (y : List Bool) : ∀ (l : List Cell) (j0 : ℕ) (b : Buf) (sb : SimBuf S.Q),
    sb.first = decide (j0 = 0) →
    (∀ (j : ℕ) (hj : j < l.length), l[j].out = y[j0 + j]?) →
    ∀ (j : ℕ) (hj : j < (fscan (convF S) (b, sb) (l.map (·, fc0 S))).1.length),
      ((fscan (convF S) (b, sb) (l.map (·, fc0 S))).1[j]).2 = initFC S y (j0 + j)
  | [], _, _, _, _, _, j, hj => by simp [fscan] at hj
  | a :: l, j0, b, sb, hf, ho, 0, _ => by
    simp only [List.map_cons, fscan, List.getElem_cons_zero, convF, initFC]
    have h0 := ho 0 (by simp)
    simp only [List.getElem_cons_zero, add_zero] at h0
    rw [h0, hf, add_zero]
    by_cases hj0 : j0 = 0 <;> simp [hj0]
  | a :: l, j0, b, sb, hf, ho, j + 1, hj => by
    simp only [List.map_cons, fscan, List.getElem_cons_succ]
    have := fscan_conv y l (j0 + 1) b {sb with first := false} (by simp)
      (fun j hj => by
        have := ho (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this, show j0 + (j + 1) = j0 + 1 + j by ring]) j
      (by simpa [fscan, fscan_length] using hj)
    rw [show j0 + (j + 1) = j0 + 1 + j by ring]
    exact this

/-- **The conversion trip** puts the output word `y` on the folded tape of `S` as its input,
with the head on cell `0`. -/
theorem dec_conv (y : List Bool) (l : List Cell) (hl : y.length < l.length)
    (ho : ∀ (j : ℕ) (hj : j < l.length), l[j].out = y[j]?) :
    FRep (dL S).get S.blank ((decProg G S).trip (.inr (.inl ())) (l.map (·, fc0 S))).1
        (S.inputTape y) 0 ∧
      ((decProg G S).trip (.inr (.inl ())) (l.map (·, fc0 S))).1.length = l.length := by
  have he : ∀ b, (decProg G S).ext (.inr (.inl ())) b = none := fun _ => rfl
  have hfw : (decProg G S).fwd (.inr (.inl ())) = convF S := rfl
  have hi : (decProg G S).init (.inr (.inl ())) = (buf0, SimBuf.start S.Q) := rfl
  have htrip : ((decProg G S).trip (.inr (.inl ())) (l.map (·, fc0 S))).1 =
      (fscan (convF S) (buf0, SimBuf.start S.Q) (l.map (·, fc0 S))).1 := by
    have h1 : (decProg G S).trip (.inr (.inl ())) (l.map (·, fc0 S)) =
        bscan (fun b a => (a, b)) ((decProg G S).fpass (.inr (.inl ())) (l.map (·, fc0 S))).2
          ((decProg G S).mid (.inr (.inl ())) (l.map (·, fc0 S))) := rfl
    rw [h1, bscan_idd]
    simp only [Prog.mid, Prog.fpass, he, hfw, hi, Option.toList_none, List.append_nil]
  rw [htrip]
  have hlen : (fscan (convF S) (buf0, SimBuf.start S.Q) (l.map (·, fc0 S))).1.length = l.length :=
    by rw [fscan_length, List.length_map]
  refine ⟨frep_init S (dL S) y _ (by omega) (by omega) (fun j hj => ?_), hlen⟩
  have := fscan_conv S y l 0 buf0 (SimBuf.start S.Q) rfl (fun j hj => by rw [zero_add]; exact ho j hj)
    j hj
  rwa [zero_add] at this

theorem dec_next_conv (b : Buf × SimBuf S.Q) :
    (decProg G S).next (.inr (.inl ())) b =
      if hQ S S.q0 then .inr (decide (S.q0 = S.qacc)) else .inl (.inr (.inr S.q0)) := rfl

/-! ## Simulating `S` -/

theorem dec_trip_sim (q : S.Q) (l : List (Cell × FCell S.Γ)) :
    (decProg G S).trip (.inr (.inr q)) l =
      simTrip S (dL S) (dLB S) (dflt, fc0 S) q (buf0, SimBuf.start S.Q) l := rfl

theorem dec_next_sim (q : S.Q) (b : Buf × SimBuf S.Q) :
    (decProg G S).next (.inr (.inr q)) b = match ((dLB S).get b).nq with
      | some q' => if hQ S q' then .inr (decide (q' = S.qacc)) else .inl (.inr (.inr q'))
      | none => .inr false := rfl

theorem stepP_inl' {P : Prog} {i i' : P.I} {l : List P.D} (h : P.next i (P.trip i l).2 = .inl i') :
    P.stepP (i, l) = .inl (i', (P.trip i l).1) := by
  simp only [Prog.stepP, h]

theorem stepP_inr' {P : Prog} {i : P.I} {a : Bool} {l : List P.D}
    (h : P.next i (P.trip i l).2 = .inr a) : P.stepP (i, l) = .inr (a, (P.trip i l).1) := by
  simp only [Prog.stepP, h]

theorem run_step_comm' (c : S.Cfg) (s : ℕ) : S.run (S.step c) s = S.run c (s + 1) := by
  rw [show s + 1 = 1 + s by ring, MTM.run_add]; rfl

/-- One simulated step of `S`, and the state it reports. -/
theorem dec_sim_one (c : S.Cfg) (l : List (Cell × FCell S.Γ))
    (hrep : FRep (dL S).get S.blank l c.tape c.head) :
    FRep (dL S).get S.blank ((decProg G S).trip (.inr (.inr c.q)) l).1 (S.step c).tape
        (S.step c).head ∧
      (decProg G S).next (.inr (.inr c.q)) ((decProg G S).trip (.inr (.inr c.q)) l).2 =
        (if hQ S (S.step c).q then .inr (decide ((S.step c).q = S.qacc))
          else .inl (.inr (.inr (S.step c).q))) ∧
      ((decProg G S).trip (.inr (.inr c.q)) l).1.length ≤ l.length + 1 := by
  obtain ⟨hrep1, hnq, -, hhi, -⟩ := simTrip_spec S (dL S) (dLB S) (dflt, fc0 S) c.q
    (buf0, SimBuf.start S.Q) rfl l c.tape c.head hrep
  have hc : (⟨c.tape, c.head, c.q⟩ : S.Cfg) = c := rfl
  rw [hc] at hrep1 hnq
  refine ⟨hrep1, ?_, hhi⟩
  rw [dec_next_sim, dec_trip_sim, hnq]

/-- **The simulation loop**: `t` non-halting steps of `S`, one round trip each. -/
theorem dec_sim_loop : ∀ (t : ℕ) (c : S.Cfg) (l : List (Cell × FCell S.Γ)),
    FRep (dL S).get S.blank l c.tape c.head → (∀ s ≤ t, hQ S (S.run c s).q = false) →
    ∃ l', RN (decProg G S) (.inr (.inr c.q), l) (.inr (.inr (S.run c t).q), l') t ∧
      FRep (dL S).get S.blank l' (S.run c t).tape (S.run c t).head ∧ l'.length ≤ l.length + t := by
  intro t
  induction t with
  | zero => intro c l hrep _; exact ⟨l, RN.refl _, hrep, by omega⟩
  | succ t ih =>
    intro c l hrep hnh
    obtain ⟨hrep1, hn, hlen1⟩ := dec_sim_one G S c l hrep
    have hrun1 : S.run c 1 = S.step c := rfl
    have hnh1 : hQ S (S.step c).q = false := by rw [← hrun1]; exact hnh 1 (by omega)
    rw [hnh1, if_neg (by decide)] at hn
    obtain ⟨l', hr, hrep', hlen'⟩ := ih (S.step c) _ hrep1
      (fun s hs => by rw [run_step_comm']; exact hnh (s + 1) (by omega))
    rw [run_step_comm'] at hr hrep'
    exact ⟨l', RN.cast_k (RN.step (stepP_inl' hn) hr) (by ring), hrep', by omega⟩

/-! ## End to end -/

theorem dec_lift_input (x : List Bool) :
    x.map (decProg G S).lift = (x.map liftC).map (·, fc0 S) := by
  simp only [List.map_map]; rfl

/-- **Generator, conversion and simulation.**  If `G` reaches a state whose exit leaves the
word `y` on its `out` track within `k` round trips, and `S` first halts on `y` at time `t`, then
`decProg G S` halts with `S`'s answer at a round-trip cost below an explicit bound. -/
theorem dec_halts (x y : List Bool) {cf : G.C} {l : List Cell} {k : ℕ}
    (hgen : RN G.prog (G.start, x.map liftC) (cf, l) k)
    (hexit : G.prog.stepP (cf, l) = .inr (true, l))
    (hyl : y.length < l.length) (hout : ∀ (j : ℕ) (hj : j < l.length), l[j].out = y[j]?)
    {t : ℕ} (hf : S.FirstHalt y t) :
    ∃ C, (decProg G S).Halts ((decProg G S).start, x.map (decProg G S).lift)
        (decide ((S.run (S.init y) t).q = S.qacc)) C ∧
      C ≤ (k + t + 2) * (2 * (x.length + k + t + 1) + 3) := by
  have hl0 : l.length ≤ x.length + k := by
    have := hgen.length_le_add; simpa using this
  have r1 : RN (decProg G S) ((decProg G S).start, x.map (decProg G S).lift)
      (.inl cf, l.map (·, fc0 S)) k := by
    rw [dec_lift_input]; exact dec_lift G S hgen
  have r2 := dec_lift_exit G S hexit
  obtain ⟨hrep, hlen⟩ := dec_conv G S y l hyl hout
  have hq0 : (S.run (S.init y) 0).q = S.q0 := rfl
  rcases t with _ | t
  · -- `S` halts at once
    have hh : hQ S S.q0 = true := by
      have := hf.1; rw [hq0] at this; simpa [hQ, MTM.Halting] using this
    have hs : (decProg G S).stepP (.inr (.inl ()), l.map (·, fc0 S)) =
        .inr (decide (S.q0 = S.qacc), ((decProg G S).trip (.inr (.inl ())) (l.map (·, fc0 S))).1) :=
      stepP_inr' (by rw [dec_next_conv, if_pos hh])
    obtain ⟨C, hC, hCle⟩ := RN.halts (r1.trans r2) hs
    refine ⟨C, by rwa [hq0], le_trans hCle ?_⟩
    simp only [List.length_map]
    exact Nat.mul_le_mul (by omega) (by omega)
  · -- the simulation runs
    have hh0 : hQ S S.q0 = false := by
      have := hf.2 0 (by omega); rw [hq0] at this
      simpa [hQ, MTM.Halting] using this
    have hs : (decProg G S).stepP (.inr (.inl ()), l.map (·, fc0 S)) =
        .inl (.inr (.inr S.q0), ((decProg G S).trip (.inr (.inl ())) (l.map (·, fc0 S))).1) :=
      stepP_inl' (by rw [dec_next_conv, if_neg (by rw [hh0]; decide)])
    have r3 := RN.single hs
    obtain ⟨l2, r4, hrep2, hlen2⟩ := dec_sim_loop G S t (S.init y) _ hrep (fun s hs' => by
      have := hf.2 s (by omega)
      simpa [hQ, MTM.Halting] using this)
    obtain ⟨-, hn, -⟩ := dec_sim_one G S (S.run (S.init y) t) l2 hrep2
    have hstep : S.step (S.run (S.init y) t) = S.run (S.init y) (t + 1) := (MTM.run_succ _ _ _).symm
    have hh : hQ S (S.run (S.init y) (t + 1)).q = true := by
      have := hf.1; simpa [hQ, MTM.Halting] using this
    rw [hstep, if_pos hh] at hn
    have hfin := stepP_inr' hn
    obtain ⟨C, hC, hCle⟩ := RN.halts (((r1.trans r2).trans r3).trans r4) hfin
    have hCle' : C ≤ (k + 1 + 1 + t + 1) * (2 * l2.length + 3) := hCle
    refine ⟨C, hC, le_trans hCle' ?_⟩
    have : l2.length ≤ x.length + k + t := by rw [hlen] at hlen2; omega
    exact Nat.mul_le_mul (by omega) (by omega)

end Decide

end PVNP.CookLevin.Gen
