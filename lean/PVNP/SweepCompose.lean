import PVNP.SweepDiv

/-!
# Sequential composition of verified sweep programs

A `Prog` bundles its data alphabet, so two verified programs cannot be chained directly.

* `ProgOn D` is a sweep program over a **fixed** alphabet `D`. `toProg` and `ofProg` translate
  between the two descriptions. `(ofProg P).toProg = P` holds by structure eta.
* `seq A B e` runs on instructions `A.I ⊕ B.I` with buffers `A.B ⊕ B.B`. It runs `A`, redirects
  `A`'s transition into its exit instruction `e` to `B`'s start, then runs `B`. Each scan, trip,
  cost and step of the composite is the corresponding one of `A` or `B` (`fscan_inl`,
  `bscan_inl`, `trip_inl`, `tripCost_inl`, `stepP_inl_ne`, `stepP_inl_exit` and their `inr`
  versions).
* `ReachFirst P e s l c`: from `s`, the program enters `e` for the **first** time, with data `l`
  and cost exactly `c`. This is the interface for exact cost addition. The existing `done`
  instructions loop, so plain `Reach` would allow extra loop trips.
* `seq_reach`, the **composition theorem**: if `A` first-arrives at `e` from `(a, l)` with output
  `l₁` and cost `c₁`, and `B` reaches `(e_B, l₂)` from `(start, l₁)` with cost `c₂`, then
  `seq A B e` reaches `(inr e_B, l₂)` from `(inl a, l)` with cost exactly `c₁ + c₂`.
  `seq_tm` is the same statement on the compiled single-tape Turing machine.
* `div_first`: long division first-arrives at `done`, with the same exact cost and outputs as
  `div_reach`. It is ready for composition.
-/

namespace PVNP.Discrete.Sweep

/-- A sweep program over a fixed data alphabet `D`. -/
structure ProgOn (D : Type) [Fintype D] [DecidableEq D] where
  I : Type
  B : Type
  [finI : Fintype I]
  [decI : DecidableEq I]
  [finB : Fintype B]
  [decB : DecidableEq B]
  lift : Bool → D
  start : I
  init : I → B
  fwd : I → B → D → D × B
  ext : I → B → Option D
  bwd : I → B → D → D × B
  next : I → B → I ⊕ Bool

namespace ProgOn

attribute [instance] ProgOn.finI ProgOn.decI ProgOn.finB ProgOn.decB

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The underlying program. -/
def toProg (A : ProgOn D) : Prog where
  D := D
  I := A.I
  B := A.B
  lift := A.lift
  start := A.start
  init := A.init
  fwd := A.fwd
  ext := A.ext
  bwd := A.bwd
  next := A.next

/-- Every program is a program over its own alphabet. -/
def ofProg (P : Prog) : ProgOn P.D where
  I := P.I
  B := P.B
  lift := P.lift
  start := P.start
  init := P.init
  fwd := P.fwd
  ext := P.ext
  bwd := P.bwd
  next := P.next

theorem toProg_ofProg (P : Prog) : (ofProg P).toProg = P := rfl

/-- **Sequential composition**: run `A` until it would enter its exit `e`, then run `B`. -/
def seq (A B : ProgOn D) (e : A.I) : ProgOn D where
  I := A.I ⊕ B.I
  B := A.B ⊕ B.B
  lift := A.lift
  start := .inl A.start
  init
    | .inl i => .inl (A.init i)
    | .inr j => .inr (B.init j)
  fwd
    | .inl i => fun b d => match b with
      | .inl a => ((A.fwd i a d).1, .inl (A.fwd i a d).2)
      | .inr c => (d, .inr c)
    | .inr j => fun b d => match b with
      | .inr c => ((B.fwd j c d).1, .inr (B.fwd j c d).2)
      | .inl a => (d, .inl a)
  ext
    | .inl i => fun b => match b with
      | .inl a => A.ext i a
      | .inr _ => none
    | .inr j => fun b => match b with
      | .inr c => B.ext j c
      | .inl _ => none
  bwd
    | .inl i => fun b d => match b with
      | .inl a => ((A.bwd i a d).1, .inl (A.bwd i a d).2)
      | .inr c => (d, .inr c)
    | .inr j => fun b d => match b with
      | .inr c => ((B.bwd j c d).1, .inr (B.bwd j c d).2)
      | .inl a => (d, .inl a)
  next
    | .inl i => fun b => match b with
      | .inl a => match A.next i a with
        | .inl i' => if i' = e then .inl (.inr B.start) else .inl (.inl i')
        | .inr x => .inr x
      | .inr _ => .inr false
    | .inr j => fun b => match b with
      | .inr c => match B.next j c with
        | .inl j' => .inl (.inr j')
        | .inr x => .inr x
      | .inl _ => .inr false

variable (A B : ProgOn D) (e : A.I)

/-! ### The composite mirrors its components -/

theorem fscan_inl (i : A.I) : ∀ (a : A.B) (l : List D),
    fscan ((seq A B e).fwd (.inl i)) (.inl a) l =
      ((fscan (A.fwd i) a l).1, .inl (fscan (A.fwd i) a l).2)
  | _, [] => rfl
  | a, x :: l => by
    have ih := fscan_inl i (A.fwd i a x).2 l
    simp only [fscan] at ih ⊢
    show _ = (((A.fwd i a x).1 :: (fscan (A.fwd i) (A.fwd i a x).2 l).1),
      Sum.inl (fscan (A.fwd i) (A.fwd i a x).2 l).2)
    rw [show (seq A B e).fwd (.inl i) (.inl a) x = ((A.fwd i a x).1, .inl (A.fwd i a x).2)
      from rfl, ih]

theorem fscan_inr (j : B.I) : ∀ (c : B.B) (l : List D),
    fscan ((seq A B e).fwd (.inr j)) (.inr c) l =
      ((fscan (B.fwd j) c l).1, .inr (fscan (B.fwd j) c l).2)
  | _, [] => rfl
  | c, x :: l => by
    have ih := fscan_inr j (B.fwd j c x).2 l
    simp only [fscan] at ih ⊢
    rw [show (seq A B e).fwd (.inr j) (.inr c) x = ((B.fwd j c x).1, .inr (B.fwd j c x).2)
      from rfl, ih]

theorem bscan_inl (i : A.I) (a : A.B) : ∀ l : List D,
    bscan ((seq A B e).bwd (.inl i)) (.inl a) l =
      ((bscan (A.bwd i) a l).1, .inl (bscan (A.bwd i) a l).2)
  | [] => rfl
  | x :: l => by
    have ih := bscan_inl i a l
    simp only [bscan] at ih ⊢
    rw [ih]
    rfl

theorem bscan_inr (j : B.I) (c : B.B) : ∀ l : List D,
    bscan ((seq A B e).bwd (.inr j)) (.inr c) l =
      ((bscan (B.bwd j) c l).1, .inr (bscan (B.bwd j) c l).2)
  | [] => rfl
  | x :: l => by
    have ih := bscan_inr j c l
    simp only [bscan] at ih ⊢
    rw [ih]
    rfl

theorem trip_inl (i : A.I) (l : List D) :
    (seq A B e).toProg.trip (.inl i) l =
      ((A.toProg.trip i l).1, .inl (A.toProg.trip i l).2) := by
  have hf : (seq A B e).toProg.fpass (.inl i) l =
      ((A.toProg.fpass i l).1, .inl (A.toProg.fpass i l).2) := fscan_inl A B e i (A.init i) l
  have hm : (seq A B e).toProg.mid (.inl i) l = A.toProg.mid i l := by
    unfold Prog.mid; rw [hf]; rfl
  unfold Prog.trip
  rw [hm, hf]
  exact bscan_inl A B e i _ _

theorem trip_inr (j : B.I) (l : List D) :
    (seq A B e).toProg.trip (.inr j) l =
      ((B.toProg.trip j l).1, .inr (B.toProg.trip j l).2) := by
  have hf : (seq A B e).toProg.fpass (.inr j) l =
      ((B.toProg.fpass j l).1, .inr (B.toProg.fpass j l).2) := fscan_inr A B e j (B.init j) l
  have hm : (seq A B e).toProg.mid (.inr j) l = B.toProg.mid j l := by
    unfold Prog.mid; rw [hf]; rfl
  unfold Prog.trip
  rw [hm, hf]
  exact bscan_inr A B e j _ _

theorem tripCost_inl (i : A.I) (l : List D) :
    (seq A B e).toProg.tripCost (.inl i) l = A.toProg.tripCost i l := by
  have hf : (seq A B e).toProg.fpass (.inl i) l =
      ((A.toProg.fpass i l).1, .inl (A.toProg.fpass i l).2) := fscan_inl A B e i (A.init i) l
  unfold Prog.tripCost; rw [hf]; rfl

theorem tripCost_inr (j : B.I) (l : List D) :
    (seq A B e).toProg.tripCost (.inr j) l = B.toProg.tripCost j l := by
  have hf : (seq A B e).toProg.fpass (.inr j) l =
      ((B.toProg.fpass j l).1, .inr (B.toProg.fpass j l).2) := fscan_inr A B e j (B.init j) l
  unfold Prog.tripCost; rw [hf]; rfl

theorem next_of_stepP {P : Prog} {i i' : P.I} {l l' : List P.D}
    (h : P.stepP (i, l) = .inl (i', l')) :
    P.next i (P.trip i l).2 = .inl i' ∧ (P.trip i l).1 = l' := by
  simp only [Prog.stepP] at h
  split at h
  · rename_i k hk
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hk, rfl⟩
  · simp at h

theorem stepP_inl_ne {i i' : A.I} {l l' : List D}
    (h : A.toProg.stepP (i, l) = .inl (i', l')) (hne : i' ≠ e) :
    (seq A B e).toProg.stepP (.inl i, l) = .inl (.inl i', l') := by
  obtain ⟨k1, k2⟩ := next_of_stepP h
  have hn : (seq A B e).toProg.next (.inl i) (.inl (A.toProg.trip i l).2) = .inl (.inl i') := by
    show (match A.next i (A.toProg.trip i l).2 with
      | .inl i' => if i' = e then Sum.inl (Sum.inr B.start) else Sum.inl (Sum.inl i')
      | .inr x => Sum.inr x) = _
    rw [show A.next i (A.toProg.trip i l).2 = .inl i' from k1]
    exact if_neg hne
  simp only [Prog.stepP, trip_inl]
  rw [hn, k2]

theorem stepP_inl_exit {i : A.I} {l l' : List D} (h : A.toProg.stepP (i, l) = .inl (e, l')) :
    (seq A B e).toProg.stepP (.inl i, l) = .inl (.inr B.start, l') := by
  obtain ⟨k1, k2⟩ := next_of_stepP h
  have hn : (seq A B e).toProg.next (.inl i) (.inl (A.toProg.trip i l).2) =
      .inl (.inr B.start) := by
    show (match A.next i (A.toProg.trip i l).2 with
      | .inl i' => if i' = e then Sum.inl (Sum.inr B.start) else Sum.inl (Sum.inl i')
      | .inr x => Sum.inr x) = _
    rw [show A.next i (A.toProg.trip i l).2 = .inl e from k1]
    exact if_pos rfl
  simp only [Prog.stepP, trip_inl]
  rw [hn, k2]

theorem stepP_inr {j j' : B.I} {l l' : List D} (h : B.toProg.stepP (j, l) = .inl (j', l')) :
    (seq A B e).toProg.stepP (.inr j, l) = .inl (.inr j', l') := by
  obtain ⟨k1, k2⟩ := next_of_stepP h
  have hn : (seq A B e).toProg.next (.inr j) (.inr (B.toProg.trip j l).2) = .inl (.inr j') := by
    show (match B.next j (B.toProg.trip j l).2 with
      | .inl j' => Sum.inl (Sum.inr j')
      | .inr x => Sum.inr x) = _
    rw [show B.next j (B.toProg.trip j l).2 = .inl j' from k1]
  simp only [Prog.stepP, trip_inr]
  rw [hn, k2]

end ProgOn

/-! ### First arrival and the composition theorem -/

/-- `ReachFirst P e s l c`: from `s`, the program enters `e` for the first time, with data `l`,
after round trips of total cost exactly `c`. -/
inductive ReachFirst (P : Prog) (e : P.I) : P.I × List P.D → List P.D → ℕ → Prop
  | last {s : P.I × List P.D} {l : List P.D} :
      P.stepP s = .inl (e, l) → ReachFirst P e s l (P.tripCost s.1 s.2)
  | step {s : P.I × List P.D} {i : P.I} {l₁ l : List P.D} {c : ℕ} :
      P.stepP s = .inl (i, l₁) → i ≠ e → ReachFirst P e (i, l₁) l c →
        ReachFirst P e s l (P.tripCost s.1 s.2 + c)

/-- A first arrival is in particular a reach. -/
theorem ReachFirst.reach {P : Prog} {e : P.I} {s : P.I × List P.D} {l : List P.D} {c : ℕ}
    (h : ReachFirst P e s l c) : P.Reach s (e, l) c := by
  induction h with
  | last hs => exact Prog.Reach.single P hs
  | step hs _ _ ih => exact Prog.Reach.step hs ih

namespace ProgOn

variable {D : Type} [Fintype D] [DecidableEq D] (A B : ProgOn D) (e : A.I)

theorem reachFirst_lift {s : A.toProg.I × List A.toProg.D} {l : List A.toProg.D} {c : ℕ}
    (h : ReachFirst A.toProg e s l c) :
    (seq A B e).toProg.Reach (.inl s.1, s.2) (.inr B.start, l) c := by
  induction h with
  | @last s l hs =>
    have h1 := Prog.Reach.single (seq A B e).toProg (stepP_inl_exit A B e hs)
    rwa [tripCost_inl] at h1
  | @step s i l₁ l c hs hne _ ih =>
    have h1 := Prog.Reach.step (stepP_inl_ne A B e hs hne) ih
    rwa [tripCost_inl] at h1

theorem reach_lift_inr {s s' : B.toProg.I × List B.toProg.D} {c : ℕ}
    (h : B.toProg.Reach s s' c) :
    (seq A B e).toProg.Reach (.inr s.1, s.2) (.inr s'.1, s'.2) c := by
  induction h with
  | refl s => exact Prog.Reach.refl _
  | @step s s₁ s₂ c hs _ ih =>
    have h1 := Prog.Reach.step (stepP_inr A B e hs) ih
    rwa [tripCost_inr] at h1

/-- **The composition theorem.** If `A` first-arrives at `e` from `(a, l)` with output `l₁` and
cost `c₁`, and `B` reaches `(e_B, l₂)` from its start on `l₁` with cost `c₂`, then the composite
reaches `(inr e_B, l₂)` from `(inl a, l)` with cost exactly `c₁ + c₂`. -/
theorem seq_reach {a : A.I} {l l₁ l₂ : List D} {eB : B.I} {c₁ c₂ : ℕ}
    (hA : ReachFirst A.toProg e (a, l) l₁ c₁) (hB : B.toProg.Reach (B.start, l₁) (eB, l₂) c₂) :
    (seq A B e).toProg.Reach (.inl a, l) (.inr eB, l₂) (c₁ + c₂) :=
  Prog.Reach.trans _ (reachFirst_lift A B e hA) (reach_lift_inr A B e hB)

/-- **The composition theorem on the compiled Turing machine.** -/
theorem seq_tm {a : A.I} {l l₁ l₂ : List D} {eB : B.I} {c₁ c₂ : ℕ}
    (hA : ReachFirst A.toProg e (a, l) l₁ c₁) (hB : B.toProg.Reach (B.start, l₁) (eB, l₂) c₂)
    (T : ℤ → Sym D) (hT : (seq A B e).toProg.Repr T l) :
    ∃ T', (seq A B e).toProg.Repr T' l₂ ∧
      (seq A B e).toProg.toTM.run ⟨.fwd (.inl a) ((seq A B e).init (.inl a)), T, 0⟩ (c₁ + c₂) =
        ⟨.fwd (.inr eB) ((seq A B e).init (.inr eB)), T', 0⟩ :=
  (seq A B e).toProg.reach_run (seq_reach A B e hA hB) T hT

end ProgOn

end PVNP.Discrete.Sweep

/-! ### Long division in first-arrival form -/

namespace PVNP.Discrete.SweepArith

open PVNP.Discrete.Sweep

theorem divI_ne_done (N Dsh : ℕ) : divI N Dsh ≠ DivI.done := by
  unfold divI; split_ifs <;> decide

/-- The division loop, with first arrival at `done`. -/
theorem div_loop_first (W D N₀ : ℕ) (hD : 0 < D) : ∀ (k : ℕ) (l : List DCell) (Qt : ℕ),
    l.length = W → vM l = 2 ^ k → vD l = D * 2 ^ k →
    N₀ = Qt * (2 * (D * 2 ^ k)) + vN l → vN l < 2 * (D * 2 ^ k) → vQ l = Qt % 2 ^ W →
    ∃ l', ReachFirst divProg DivI.done (divI (vN l) (vD l), l) l' ((k + 1) * (2 * W + 2)) ∧
      vQ l' = (N₀ / D) % 2 ^ W ∧ vN l' = N₀ % D := by
  intro k
  induction k with
  | zero =>
    intro l Qt hlen hm hd hinv hlt hq
    have hne : l ≠ [] := by
      rintro rfl
      have h0 : (2 : ℕ) ^ 0 ≠ 0 := by positivity
      exact h0 hm.symm
    obtain ⟨l₁, hs, _, _, hm1, hq1, hn1⟩ := dstep l hne
    have hm0 : vM l₁ = 0 := by rw [hm1, hm]; rfl
    rw [if_pos hm0] at hs
    have hinv2 : N₀ = Qt * (2 * vD l) + vN l := by rw [hd]; exact hinv
    have hlt2 : vN l < 2 * vD l := by rw [hd]; exact hlt
    obtain ⟨k1, k2⟩ := div_arith N₀ Qt (vN l) (vD l) hinv2 hlt2
    rw [← hn1] at k1 k2
    rw [hq, hlen, mod_shift] at hq1
    obtain ⟨Qt', hQt'⟩ : ∃ Qt', Qt' = 2 * Qt + (if vD l ≤ vN l then 1 else 0) := ⟨_, rfl⟩
    rw [← hQt'] at k1 hq1
    have hd0 : vD l = D := by rw [hd, pow_zero, mul_one]
    rw [hd0] at k1 k2
    have hdiv : N₀ / D = Qt' := by
      rw [k1, Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt k2, zero_add]
    have hmod : N₀ % D = vN l₁ := by
      rw [k1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k2]
    refine ⟨l₁, ?_, by rw [hq1, hdiv], hmod.symm⟩
    have h := ReachFirst.last (P := divProg) (e := DivI.done) hs
    rw [tripCost_div, hlen] at h
    simpa using h
  | succ k ih =>
    intro l Qt hlen hm hd hinv hlt hq
    have hne : l ≠ [] := by
      rintro rfl
      have h0 : (2 : ℕ) ^ (k + 1) ≠ 0 := by positivity
      exact h0 hm.symm
    obtain ⟨l₁, hs, hlen1, hd1, hm1, hq1, hn1⟩ := dstep l hne
    have hm1' : vM l₁ = 2 ^ k := by rw [hm1, hm, pow_succ]; omega
    have hd1' : vD l₁ = D * 2 ^ k := by
      rw [hd1, hd, pow_succ, ← mul_assoc]; omega
    have hm0 : vM l₁ ≠ 0 := by rw [hm1']; positivity
    rw [if_neg hm0] at hs
    have hpk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hinv2 : N₀ = Qt * (2 * vD l) + vN l := by rw [hd]; exact hinv
    have hlt2 : vN l < 2 * vD l := by rw [hd]; exact hlt
    obtain ⟨k1, k2⟩ := div_arith N₀ Qt (vN l) (vD l) hinv2 hlt2
    rw [← hn1] at k1 k2
    rw [hq, hlen, mod_shift] at hq1
    obtain ⟨Qt', hQt'⟩ : ∃ Qt', Qt' = 2 * Qt + (if vD l ≤ vN l then 1 else 0) := ⟨_, rfl⟩
    rw [← hQt'] at k1 hq1
    have hvd2 : vD l = 2 * (D * 2 ^ k) := by rw [hd, hpk]; ring
    rw [hvd2] at k1 k2
    obtain ⟨l', hr, hq'', hn''⟩ := ih l₁ Qt' (by rw [hlen1, hlen]) hm1' hd1' k1 k2 hq1
    refine ⟨l', ?_, hq'', hn''⟩
    have h := ReachFirst.step (P := divProg) (e := DivI.done) hs (divI_ne_done _ _) hr
    rw [tripCost_div, hlen] at h
    convert h using 1
    ring

/-- Long division from `prep`, with first arrival at `done`. -/
theorem div_reach_first (l : List DCell) (hl : l ≠ []) (K D : ℕ) (hD : 0 < D)
    (hd : vD l = D * 2 ^ K) (hm : vM l = 2 ^ K) (hq : vQ l = 0)
    (hlt : vN l < 2 * (D * 2 ^ K)) :
    ∃ l', ReachFirst divProg DivI.done (DivI.prep, l) l' ((K + 2) * (2 * l.length + 2)) ∧
      vQ l' = vN l / D ∧ vN l' = vN l % D := by
  have hfr : (fscan gP (divProg.init DivI.prep) l).2.fr = true :=
    gscan_fr gP (fun _ _ => rfl) _ l hl
  have hF : (fscan gP (divProg.init DivI.prep) l).1 = l := gscan_gP _ l
  obtain ⟨p1, _, p3, p4⟩ := hscan_hP _ hfr l hl
  have hm0 : vM l ≠ 0 := by rw [hm]; positivity
  have hs : divProg.stepP (DivI.prep, l) = .inl (divI (vN l) (vD l), l) := by
    have ht := trip_eq_div DivI.prep gP hP rfl rfl l
    rw [hF] at ht
    simp only [Prog.stepP, ht, p1]
    rw [show divProg.next DivI.prep = dnext from rfl, dnext_eq _ (vN l) (vD l) (vM l) p3 p4,
      if_neg hm0]
  obtain ⟨l', hr, hq', hn'⟩ := div_loop_first l.length D (vN l) hD K l 0 rfl hm hd
    (by ring) hlt (by rw [hq]; simp)
  refine ⟨l', ?_, ?_, hn'⟩
  · have h := ReachFirst.step (P := divProg) (e := DivI.done) hs (divI_ne_done _ _) hr
    rw [tripCost_div] at h
    convert h using 1
    ring
  · have hN := val_lt (l.map DCell.n)
    rw [List.length_map] at hN
    rw [hq', Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self (vN l) D) hN)]

/-- **`W`-bit long division in first-arrival form**, ready for `ProgOn.seq_reach`. -/
theorem div_first (W N D : ℕ) (hN : N < 2 ^ W) (hD : 0 < D) (hDW : D < 2 ^ W) :
    ∃ l', ReachFirst divProg DivI.done (DivI.prep, divInput W N D) l'
        ((W + 2) * (4 * W + 2)) ∧ vQ l' = N / D ∧ vN l' = N % D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := divInput_spec W N D
  have hW2 : 2 ^ (2 * W) = 2 ^ W * 2 ^ W := by rw [two_mul, pow_add]
  have hpos : 0 < 2 ^ W := by positivity
  have hW0 : W ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hDW
    omega
  have hN2 : N < 2 ^ (2 * W) := by rw [hW2]; nlinarith
  have hD2 : D * 2 ^ W < 2 ^ (2 * W) := by rw [hW2]; nlinarith
  have hM2 : 2 ^ W < 2 ^ (2 * W) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [Nat.mod_eq_of_lt hN2] at h1
  rw [Nat.mod_eq_of_lt hD2] at h2
  rw [Nat.mod_eq_of_lt hM2] at h4
  have hne : divInput W N D ≠ [] := by
    intro h; rw [h, List.length_nil] at h5; omega
  have hlt : vN (divInput W N D) < 2 * (D * 2 ^ W) := by rw [h1]; nlinarith
  obtain ⟨l', hr, hq, hn⟩ := div_reach_first (divInput W N D) hne W D hD h2 h4 h3 hlt
  refine ⟨l', ?_, by rw [hq, h1], by rw [hn, h1]⟩
  rw [h5] at hr
  convert hr using 1
  ring

end PVNP.Discrete.SweepArith
