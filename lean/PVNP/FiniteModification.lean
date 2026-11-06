import PVNP.CookLevinDecide

/-!
# Closure of `P_TM` under finite modification

If `L'` is decided in polynomial time and `L` agrees with `L'` on all words of length at least
`N`, then `L ∈ P_TM` (`P_TM_of_eventually_eq`).

The decider is the round-trip sweep program `fmProg S N τ`, compiled by `Prog.toTM`:

* its first round trip reads up to `N` input bits into a bounded buffer and puts the input on
  the folded tape of the manuscript machine `S`, with the head on cell `0`;
* if the input is shorter than `N`, it answers `τ x` (a finite table);
* otherwise it simulates `S` one step per round trip (`simTrip_spec`).

The simulation lemmas `gsim_loop` and `gsim_halt` are stated for any program whose simulation
instructions perform `simTrip`.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim PVNP.PartIITuring

/-! ## Simulation inside any sweep program -/

section GenSim

variable (S : MTM) (P : Prog) (L : Lens P.D (FCell S.Γ)) (LB : Lens P.B (SimBuf S.Q))
  (dfl : P.D) (b0 : P.B) (simI : S.Q → P.I)

/-- The simulation instructions of `P` perform `simTrip` and answer at a halting state. -/
structure SimSpec : Prop where
  hb0 : LB.get b0 = SimBuf.start S.Q
  trip : ∀ q l, P.trip (simI q) l = simTrip S L LB dfl q b0 l
  next : ∀ q b, P.next (simI q) b = match (LB.get b).nq with
    | some q' => if hQ S q' then .inr (decide (q' = S.qacc)) else .inl (simI q')
    | none => .inr false

variable {S P L LB dfl b0 simI}

theorem gsim_one (h : SimSpec S P L LB dfl b0 simI) (c : S.Cfg) (l : List P.D)
    (hrep : FRep L.get S.blank l c.tape c.head) :
    FRep L.get S.blank (P.trip (simI c.q) l).1 (S.step c).tape (S.step c).head ∧
      P.next (simI c.q) (P.trip (simI c.q) l).2 =
        (if hQ S (S.step c).q then .inr (decide ((S.step c).q = S.qacc))
          else .inl (simI (S.step c).q)) ∧
      (P.trip (simI c.q) l).1.length ≤ l.length + 1 := by
  obtain ⟨hrep1, hnq, -, hhi, -⟩ := simTrip_spec S L LB dfl c.q b0 h.hb0 l c.tape c.head hrep
  have hc : (⟨c.tape, c.head, c.q⟩ : S.Cfg) = c := rfl
  rw [hc] at hrep1 hnq
  rw [h.trip]
  refine ⟨hrep1, ?_, hhi⟩
  rw [h.next, hnq]

/-- `t` non-halting steps of `S`, one round trip each. -/
theorem gsim_loop (h : SimSpec S P L LB dfl b0 simI) : ∀ (t : ℕ) (c : S.Cfg) (l : List P.D),
    FRep L.get S.blank l c.tape c.head → (∀ s ≤ t, hQ S (S.run c s).q = false) →
    ∃ l', RN P (simI c.q, l) (simI (S.run c t).q, l') t ∧
      FRep L.get S.blank l' (S.run c t).tape (S.run c t).head ∧ l'.length ≤ l.length + t := by
  intro t
  induction t with
  | zero => intro c l hrep _; exact ⟨l, RN.refl _, hrep, by omega⟩
  | succ t ih =>
    intro c l hrep hnh
    obtain ⟨hrep1, hn, hlen1⟩ := gsim_one h c l hrep
    have hrun1 : S.run c 1 = S.step c := rfl
    have hnh1 : hQ S (S.step c).q = false := by rw [← hrun1]; exact hnh 1 (by omega)
    rw [hnh1, if_neg (by decide)] at hn
    obtain ⟨l', hr, hrep', hlen'⟩ := ih (S.step c) _ hrep1
      (fun s hs => by rw [run_step_comm']; exact hnh (s + 1) (by omega))
    rw [run_step_comm'] at hr hrep'
    exact ⟨l', RN.cast_k (RN.step (stepP_inl' hn) hr) (by ring), hrep', by omega⟩

/-- **Simulating `S` to its first halting time.**  From the input tape of `y` (head on cell `0`)
in state `simI S.q0`, the program halts with `S`'s answer after `t` round trips if `S` first
halts at time `t + 1`. -/
theorem gsim_halts (h : SimSpec S P L LB dfl b0 simI) (y : List Bool) (l : List P.D)
    (hrep : FRep L.get S.blank l (S.inputTape y) 0) {t : ℕ} (hf : S.FirstHalt y (t + 1)) :
    ∃ l', RN P (simI S.q0, l) (simI (S.run (S.init y) t).q, l') t ∧ l'.length ≤ l.length + t ∧
      P.stepP (simI (S.run (S.init y) t).q, l') =
        .inr (decide ((S.run (S.init y) (t + 1)).q = S.qacc),
          (P.trip (simI (S.run (S.init y) t).q) l').1) := by
  obtain ⟨l2, r, hrep2, hlen2⟩ := gsim_loop h t (S.init y) l hrep (fun s hs' => by
    have := hf.2 s (by omega)
    simpa [hQ, MTM.Halting] using this)
  refine ⟨l2, r, hlen2, ?_⟩
  obtain ⟨-, hn, -⟩ := gsim_one h (S.run (S.init y) t) l2 hrep2
  have hstep : S.step (S.run (S.init y) t) = S.run (S.init y) (t + 1) := (MTM.run_succ _ _ _).symm
  have hh : hQ S (S.run (S.init y) (t + 1)).q = true := by
    have := hf.1; simpa [hQ, MTM.Halting] using this
  rw [hstep, if_pos hh] at hn
  exact stepP_inr' hn

end GenSim

theorem tripCost_le' (P : Prog) (i : P.I) (l : List P.D) : P.tripCost i l ≤ 2 * l.length + 3 := by
  unfold Prog.tripCost
  cases P.ext i (P.fpass i l).2 <;> simp

/-! ## Reading a bounded prefix -/

section Scan

variable (N : ℕ)

/-- Number of bits read (saturating at `N`) and the bits. -/
abbrev Scan := Fin (N + 1) × (Fin N → Bool)

/-- Read one cell. -/
def scanStep (s : Scan N) : Option Bool → Scan N
  | some v => if h : (s.1 : ℕ) < N then (⟨s.1 + 1, Nat.succ_lt_succ h⟩, Function.update s.2 ⟨s.1, h⟩ v)
      else s
  | none => s

/-- The bits read. -/
def scanned (s : Scan N) : List Bool :=
  List.ofFn fun i : Fin s.1 => s.2 ⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ s.1.isLt)⟩

theorem scan_fold : ∀ (x : List Bool) (s : Scan N),
    ((x.map some).foldl (scanStep N) s).1.val = min (s.1.val + x.length) N ∧
      (∀ i : Fin N, i.val < s.1.val → ((x.map some).foldl (scanStep N) s).2 i = s.2 i) ∧
      (∀ i : Fin N, s.1.val ≤ i.val → (hi : i.val - s.1.val < x.length) →
        ((x.map some).foldl (scanStep N) s).2 i = x[i.val - s.1.val])
  | [], s => by
    refine ⟨by simp; have := s.1.isLt; omega, fun _ _ => rfl, fun i _ hi => absurd hi (by simp)⟩
  | b :: x, s => by
    simp only [List.map_cons, List.foldl_cons]
    by_cases h : s.1.val < N
    · have e : scanStep N s (some b) =
          (⟨s.1 + 1, Nat.succ_lt_succ h⟩, Function.update s.2 ⟨s.1, h⟩ b) := by
        simp [scanStep, h]
      rw [e]
      obtain ⟨h1, h2, h3⟩ := scan_fold x (⟨s.1 + 1, Nat.succ_lt_succ h⟩,
        Function.update s.2 ⟨s.1, h⟩ b)
      simp only at h1 h2 h3
      refine ⟨by rw [h1]; simp; omega, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
      · rw [h2 i (by omega), Function.update_of_ne (by intro e; rw [e] at hi; simp at hi)]
      · by_cases hi : i.val = s.1.val
        · have hi' : i = ⟨s.1, h⟩ := Fin.ext hi
          subst hi'
          rw [h2 _ (by simp)]
          simp
        · rw [h3 i (by omega) (by simp at hi2; omega)]
          have : i.val - s.1.val = (i.val - (s.1.val + 1)) + 1 := by omega
          simp only [this, List.getElem_cons_succ]
    · have e : scanStep N s (some b) = s := by simp [scanStep, h]
      rw [e]
      obtain ⟨h1, h2, h3⟩ := scan_fold x s
      refine ⟨by rw [h1]; simp; omega, h2, fun i hi1 hi2 => ?_⟩
      exfalso; have := i.isLt; omega

/-- **The bounded prefix.**  After reading `x` from the empty scan, the count is `min |x| N`, and
when `|x| < N` the bits read are exactly `x`. -/
theorem scan_short (x : List Bool) (hx : x.length < N) :
    ((x.map some).foldl (scanStep N) (0, fun _ => false)).1.val = x.length ∧
      scanned N ((x.map some).foldl (scanStep N) (0, fun _ => false)) = x := by
  obtain ⟨h1, -, h3⟩ := scan_fold N x (0, fun _ => false)
  simp only [Fin.val_zero, zero_add] at h1 h3
  have hc : ((x.map some).foldl (scanStep N) (0, fun _ => false)).1.val = x.length := by
    rw [h1]; omega
  refine ⟨hc, ?_⟩
  apply List.ext_getElem
  · simp [scanned, hc]
  · intro i h1' h2'
    simp only [scanned, List.getElem_ofFn]
    have := h3 ⟨i, by omega⟩ (Nat.zero_le _) (by simp; omega)
    simpa using this

theorem scan_long (x : List Bool) (hx : N ≤ x.length) :
    ((x.map some).foldl (scanStep N) (0, fun _ => false)).1.val = N := by
  obtain ⟨h1, -, -⟩ := scan_fold N x (0, fun _ => false)
  simp only [Fin.val_zero, zero_add] at h1
  rw [h1]; omega

end Scan

/-! ## The program -/

section FM

variable (S : MTM) (N : ℕ) (τ : List Bool → Bool)

/-- The folded track. -/
def fL : Lens (Option Bool × FCell S.Γ) (FCell S.Γ) :=
  ⟨Prod.snd, fun t c => (c.1, t), fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The simulation buffer. -/
def fLB : Lens (Scan N × SimBuf S.Q) (SimBuf S.Q) :=
  ⟨Prod.snd, fun t b => (b.1, t), fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- First trip: read the prefix and mark the head on cell `0`. -/
def fmF (b : Scan N × SimBuf S.Q) (a : Option Bool × FCell S.Γ) :
    (Option Bool × FCell S.Γ) × (Scan N × SimBuf S.Q) :=
  ((a.1, ⟨a.2.r, a.2.l, if b.2.first then some true else none, a.2.pl⟩),
    (scanStep N b.1 a.1, {b.2 with first := false}))

/-- **The finite-modification decider.** -/
def fmProg : Prog where
  D := Option Bool × FCell S.Γ
  I := Unit ⊕ S.Q
  B := Scan N × SimBuf S.Q
  lift b := (some b, ⟨S.inp b, S.blank, none, none⟩)
  start := .inl ()
  init _ := ((0, fun _ => false), SimBuf.start S.Q)
  fwd
    | .inl _ => fmF S N
    | .inr q => gF S (fL S) (fLB S N) q
  ext
    | .inl _ => fun b => if b.2.first then some (none, ⟨S.blank, S.blank, some true, none⟩)
        else none
    | .inr _ => gE S (fL S) (fLB S N) (none, fc0 S)
  bwd
    | .inl _ => fun b a => (a, b)
    | .inr _ => gB S (fL S) (fLB S N)
  next
    | .inl _ => fun b => if (b.1.1 : ℕ) < N then .inr (τ (scanned N b.1))
        else if hQ S S.q0 then .inr (decide (S.q0 = S.qacc)) else .inl (.inr S.q0)
    | .inr _ => fun b => match ((fLB S N).get b).nq with
        | some q' => if hQ S q' then .inr (decide (q' = S.qacc)) else .inl (.inr q')
        | none => .inr false

theorem fm_simSpec : SimSpec S (fmProg S N τ) (fL S) (fLB S N) (none, fc0 S)
    ((0, fun _ => false), SimBuf.start S.Q) Sum.inr :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The first trip's forward pass. -/
theorem fscan_fm (x : List Bool) : ∀ (j0 : ℕ) (s : Scan N) (sb : SimBuf S.Q), sb.first = decide (j0 = 0) →
    ((fscan (fmF S N) (s, sb) ((x.drop j0).map (fmProg S N τ).lift)).2.1 =
        ((x.drop j0).map some).foldl (scanStep N) s) ∧
      ((fscan (fmF S N) (s, sb) ((x.drop j0).map (fmProg S N τ).lift)).2.2.first =
        (sb.first && decide (x.drop j0 = []))) ∧
      ∀ (j : ℕ) (hj : j < (fscan (fmF S N) (s, sb) ((x.drop j0).map (fmProg S N τ).lift)).1.length),
        ((fscan (fmF S N) (s, sb) ((x.drop j0).map (fmProg S N τ).lift)).1[j]).2 =
          initFC S x (j0 + j) := by
  intro j0
  induction h : x.length - j0 generalizing j0 with
  | zero =>
    intro s sb _
    have hd : x.drop j0 = [] := List.drop_eq_nil_of_le (by omega)
    simp [hd, fscan]
  | succ m ih =>
    intro s sb hf
    have hlt : j0 < x.length := by omega
    have hd : x.drop j0 = x[j0] :: x.drop (j0 + 1) := List.drop_eq_getElem_cons hlt
    obtain ⟨i1, i2, i3⟩ := ih (j0 + 1) (by omega) (scanStep N s (some x[j0]))
      {sb with first := false} (by simp)
    rw [hd]
    simp only [List.map_cons, fscan]
    have e : fmF S N (s, sb) ((fmProg S N τ).lift x[j0]) =
        ((some x[j0], ⟨S.inp x[j0], S.blank, if sb.first then some true else none, none⟩),
          (scanStep N s (some x[j0]), {sb with first := false})) := rfl
    simp only [e]
    refine ⟨i1, ?_, fun j hj => ?_⟩
    · rw [i2]; simp [hlt]
    · rcases j with _ | j
      · simp only [List.getElem_cons_zero, fmProg, initFC, add_zero]
        rw [hf, List.getElem?_eq_getElem hlt]
        by_cases h0 : j0 = 0 <;> simp [h0, Spec.inSym]
      · simp only [List.getElem_cons_succ]
        rw [i3 j (by simpa [fscan_length] using hj), show j0 + 1 + j = j0 + (j + 1) by ring]

/-- **The first trip.** -/
theorem fm_first (x : List Bool) :
    FRep (fL S).get S.blank ((fmProg S N τ).trip (.inl ()) (x.map (fmProg S N τ).lift)).1
        (S.inputTape x) 0 ∧
      ((fmProg S N τ).trip (.inl ()) (x.map (fmProg S N τ).lift)).1.length = max x.length 1 ∧
      (((fmProg S N τ).trip (.inl ()) (x.map (fmProg S N τ).lift)).2.1 =
        (x.map some).foldl (scanStep N) (0, fun _ => false)) := by
  rcases x with _ | ⟨b, x⟩
  · -- the empty input: one fresh cell with the head
    have e0 : (fmProg S N τ).trip (.inl ()) (([] : List Bool).map (fmProg S N τ).lift) =
        ([(none, ⟨S.blank, S.blank, some true, none⟩)], ((0, fun _ => false), SimBuf.start S.Q)) :=
      rfl
    rw [e0]
    refine ⟨frep_init S (fL S) [] _ (by simp) (by simp) (fun j hj => ?_), by simp, rfl⟩
    simp only [List.length_singleton, Nat.lt_one_iff] at hj
    subst hj
    rfl
  · obtain ⟨i1, i2, i3⟩ := fscan_fm S N τ (b :: x) 0 (0, fun _ => false) (SimBuf.start S.Q) rfl
    simp only [List.drop_zero] at i1 i2 i3
    have hne : ((SimBuf.start S.Q).first && decide (b :: x = [])) = false := by simp
    rw [hne] at i2
    have htrip : (fmProg S N τ).trip (.inl ()) ((b :: x).map (fmProg S N τ).lift) =
        ((fscan (fmF S N) ((0, fun _ => false), SimBuf.start S.Q)
            ((b :: x).map (fmProg S N τ).lift)).1 ++
          (if (fscan (fmF S N) ((0, fun _ => false), SimBuf.start S.Q)
            ((b :: x).map (fmProg S N τ).lift)).2.2.first
            then some ((none, ⟨S.blank, S.blank, some true, none⟩) : Option Bool × FCell S.Γ)
            else none).toList,
          (fscan (fmF S N) ((0, fun _ => false), SimBuf.start S.Q)
            ((b :: x).map (fmProg S N τ).lift)).2) :=
      bscan_idd _ _
    rw [htrip, i2]
    simp only [Bool.false_eq_true, if_false, Option.toList_none, List.append_nil]
    have hlen : (fscan (fmF S N) ((0, fun _ => false), SimBuf.start S.Q)
        ((b :: x).map (fmProg S N τ).lift)).1.length = (b :: x).length := by
      rw [fscan_length, List.length_map]
    refine ⟨frep_init S (fL S) (b :: x) _ (by omega) (by rw [hlen]; simp) (fun j hj => ?_),
      by rw [hlen]; simp, i1⟩
    have := i3 j hj
    simpa [fL] using this

/-- Short inputs are answered from the table in one round trip. -/
theorem fm_short (x : List Bool) (hx : x.length < N) :
    (fmProg S N τ).stepP (.inl (), x.map (fmProg S N τ).lift) =
      .inr (τ x, ((fmProg S N τ).trip (.inl ()) (x.map (fmProg S N τ).lift)).1) := by
  obtain ⟨-, -, hb⟩ := fm_first S N τ x
  obtain ⟨hc, hs⟩ := scan_short N x hx
  apply stepP_inr'
  show (if (((fmProg S N τ).trip (.inl ()) (x.map (fmProg S N τ).lift)).2.1.1 : ℕ) < N
      then _ else _) = _
  rw [hb, hc, if_pos hx, hs]

/-- Long inputs: the program halts with `S`'s answer. -/
theorem fm_long (x : List Bool) (hx : N ≤ x.length) {t : ℕ} (hf : S.FirstHalt x t) :
    ∃ C, (fmProg S N τ).Halts ((fmProg S N τ).start, x.map (fmProg S N τ).lift)
        (decide ((S.run (S.init x) t).q = S.qacc)) C ∧
      C ≤ (t + 1) * (2 * (x.length + t + 1) + 3) := by
  obtain ⟨hrep, hlen, hb⟩ := fm_first S N τ x
  have hc := scan_long N x hx
  have hq0 : (S.run (S.init x) 0).q = S.q0 := rfl
  set l1 := ((fmProg S N τ).trip (.inl ()) (x.map (fmProg S N τ).lift)).1 with hl1
  have hnext : (fmProg S N τ).next (.inl ())
      ((fmProg S N τ).trip (.inl ()) (x.map (fmProg S N τ).lift)).2 =
      if hQ S S.q0 then .inr (decide (S.q0 = S.qacc)) else .inl (.inr S.q0) := by
    show (if (((fmProg S N τ).trip (.inl ()) (x.map (fmProg S N τ).lift)).2.1.1 : ℕ) < N
      then _ else _) = _
    rw [hb, hc, if_neg (lt_irrefl N)]
  rcases t with _ | t
  · have hh : hQ S S.q0 = true := by
      have := hf.1; rw [hq0] at this; simpa [hQ, MTM.Halting] using this
    rw [if_pos hh] at hnext
    refine ⟨_, .last (stepP_inr' hnext), ?_⟩
    have := tripCost_le' (fmProg S N τ) (.inl ()) (x.map (fmProg S N τ).lift)
    simp only [List.length_map] at this
    show (fmProg S N τ).tripCost (.inl ()) (x.map (fmProg S N τ).lift) ≤ _
    omega
  · have hh0 : hQ S S.q0 = false := by
      have := hf.2 0 (by omega); rw [hq0] at this
      simpa [hQ, MTM.Halting] using this
    rw [if_neg (by rw [hh0]; decide)] at hnext
    have r1 := RN.single (stepP_inl' hnext)
    obtain ⟨l2, r2, hlen2, hstep⟩ := gsim_halts (fm_simSpec S N τ) x l1 hrep hf
    obtain ⟨C, hC, hCle⟩ := RN.halts (r1.trans r2) hstep
    have hCle' : C ≤ (1 + t + 1) * (2 * l2.length + 3) := hCle
    refine ⟨C, hC, le_trans hCle' ?_⟩
    have : l2.length ≤ x.length + t + 1 := by rw [hlen] at hlen2; omega
    exact Nat.mul_le_mul (by omega) (by omega)

end FM

/-! ## Closure of `P_TM` -/

/-- **`P_TM` is closed under finite modification.**  If `L'` is decided in polynomial time and
`L` agrees with `L'` on every word of length at least `N`, then `L` is decided in polynomial time
too. -/
theorem P_TM_of_eventually_eq {L L' : Set (List Bool)} (h : L' ∈ P_TM) (N : ℕ)
    (hLL : ∀ x : List Bool, N ≤ x.length → (x ∈ L ↔ x ∈ L')) : L ∈ P_TM := by
  classical
  obtain ⟨S, c, e, -, -, hhalt, hacc⟩ := P_TM_subset_P_Turing h
  let τ : List Bool → Bool := fun x => decide (x ∈ L)
  refine ⟨(fmProg S N τ).toTM,
    (Polynomial.C c * (Polynomial.X + 1) ^ e + 1) *
      (2 * (Polynomial.X + Polynomial.C c * (Polynomial.X + 1) ^ e + 1) + 3) + 2 * Polynomial.X + 5,
    fun x => ?_⟩
  have hpos : ∀ n : ℕ, c * max n 1 ^ e ≤ c * (n + 1) ^ e := fun n =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  by_cases hx : x.length < N
  · -- the table
    have hs := fm_short S N τ x hx
    have hcost := tripCost_le' (fmProg S N τ) (fmProg S N τ).start (x.map (fmProg S N τ).lift)
    obtain ⟨s, hs', h1, h2⟩ := Prog.toTM_firstAnswer _ x (.last hs)
    dsimp only at hs'
    refine ⟨τ x, ⟨s, le_trans hs' ?_, h1, h2⟩, by simp [τ]⟩
    simp only [List.length_map] at hcost
    dsimp only
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    omega
  · obtain ⟨t, ht, hft⟩ := hhalt x
    obtain ⟨C, hC, hCle⟩ := fm_long S N τ x (by omega) hft
    obtain ⟨s, hs', h1, h2⟩ := Prog.toTM_firstAnswer _ x hC
    refine ⟨_, ⟨s, le_trans hs' ?_, h1, h2⟩, ?_⟩
    · have ht' : t ≤ c * (x.length + 1) ^ e := le_trans ht (hpos _)
      dsimp only
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
      have := Nat.mul_le_mul (show t + 1 ≤ c * (x.length + 1) ^ e + 1 by omega)
        (show 2 * (x.length + t + 1) + 3 ≤ 2 * (x.length + c * (x.length + 1) ^ e + 1) + 3 by omega)
      omega
    · rw [decide_eq_true_iff, ← S.accepts_iff_of_firstHalt hft, hacc x, hLL x (by omega)]

end PVNP.CookLevin.Gen
