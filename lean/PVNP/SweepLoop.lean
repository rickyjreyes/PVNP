import PVNP.SweepCompose

/-!
# Loops of verified sweep programs

`ProgOn.seq` composes programs in sequence. Data-dependent iteration needs a loop:
- the gcd of normalized rationals;
- sums over a mode set;
- the terms of a Taylor recurrence.

* `loop T B eT eB` runs the test `T`. On `T`'s exit `eT` it runs the body `B`, and on `B`'s exit
  `eB` it returns to `T`'s start. Any other exit `eF` of `T` is an exit of the loop. Scans, trips
  and costs are those of `seq T B eT` (`loop_trip_inl`, `loop_trip_inr`, `loop_tripCost_inl`,
  `loop_tripCost_inr`).
* `loop_stepP_*`: the loop's steps are the steps of `T` and `B`, with the two redirections.
* `loop_reachFirst`, the **loop theorem**:
  - *Iterations:* for `k < n`, the single-trip test sends `(T.start, l_k)` to `(eT, m_k)`, and
    the body first-arrives at `eB` from `(B.start, m_k)` with output `l_{k+1}` and cost `b_k`.
  - *Stop:* at `l_n` the test sends `(T.start, l_n)` to `(eF, out)`.
  - *Conclusion:* the loop first-arrives at `inl eF` from `(inl T.start, l_0)` with output `out`.
  - *Cost:* exactly `Σ_{k<n} (t_k + b_k) + t_n`, where `t_k` is the test's trip cost on `l_k`.

  The number of iterations `n` is determined by the data.
* `loop_tm`: the same on the compiled single-tape Turing machine.
-/

namespace PVNP.Discrete.Sweep

namespace ProgOn

variable {D : Type} [Fintype D] [DecidableEq D]

/-- **The loop combinator.** Run the test `T`. At its exit `eT` run the body `B`, and at the body's
exit `eB` return to the test's start. Every other exit of the test is an exit of the loop. -/
def loop (T B : ProgOn D) (eT : T.I) (eB : B.I) : ProgOn D :=
  { seq T B eT with
    next := fun i => match i with
      | .inl i => fun b => match b with
        | .inl a => match T.next i a with
          | .inl i' => if i' = eT then .inl (.inr B.start) else .inl (.inl i')
          | .inr x => .inr x
        | .inr _ => .inr false
      | .inr j => fun b => match b with
        | .inr c => match B.next j c with
          | .inl j' => if j' = eB then .inl (.inl T.start) else .inl (.inr j')
          | .inr x => .inr x
        | .inl _ => .inr false }

variable (T B : ProgOn D) (eT : T.I) (eB : B.I)

theorem loop_trip_inl (i : T.I) (l : List D) :
    (loop T B eT eB).toProg.trip (.inl i) l =
      ((T.toProg.trip i l).1, .inl (T.toProg.trip i l).2) :=
  trip_inl T B eT i l

theorem loop_trip_inr (j : B.I) (l : List D) :
    (loop T B eT eB).toProg.trip (.inr j) l =
      ((B.toProg.trip j l).1, .inr (B.toProg.trip j l).2) :=
  trip_inr T B eT j l

theorem loop_tripCost_inl (i : T.I) (l : List D) :
    (loop T B eT eB).toProg.tripCost (.inl i) l = T.toProg.tripCost i l :=
  tripCost_inl T B eT i l

theorem loop_tripCost_inr (j : B.I) (l : List D) :
    (loop T B eT eB).toProg.tripCost (.inr j) l = B.toProg.tripCost j l :=
  tripCost_inr T B eT j l

theorem loop_stepP_inl_ne {i i' : T.I} {l l' : List D}
    (h : T.toProg.stepP (i, l) = .inl (i', l')) (hne : i' ≠ eT) :
    (loop T B eT eB).toProg.stepP (.inl i, l) = .inl (.inl i', l') := by
  obtain ⟨k1, k2⟩ := next_of_stepP h
  have hn : (loop T B eT eB).toProg.next (.inl i) (.inl (T.toProg.trip i l).2) =
      .inl (.inl i') := by
    show (match T.next i (T.toProg.trip i l).2 with
      | .inl i' => if i' = eT then Sum.inl (Sum.inr B.start) else Sum.inl (Sum.inl i')
      | .inr x => Sum.inr x) = _
    rw [show T.next i (T.toProg.trip i l).2 = .inl i' from k1]
    exact if_neg hne
  simp only [Prog.stepP, loop_trip_inl]
  rw [hn, k2]

theorem loop_stepP_inl_exit {i : T.I} {l l' : List D}
    (h : T.toProg.stepP (i, l) = .inl (eT, l')) :
    (loop T B eT eB).toProg.stepP (.inl i, l) = .inl (.inr B.start, l') := by
  obtain ⟨k1, k2⟩ := next_of_stepP h
  have hn : (loop T B eT eB).toProg.next (.inl i) (.inl (T.toProg.trip i l).2) =
      .inl (.inr B.start) := by
    show (match T.next i (T.toProg.trip i l).2 with
      | .inl i' => if i' = eT then Sum.inl (Sum.inr B.start) else Sum.inl (Sum.inl i')
      | .inr x => Sum.inr x) = _
    rw [show T.next i (T.toProg.trip i l).2 = .inl eT from k1]
    exact if_pos rfl
  simp only [Prog.stepP, loop_trip_inl]
  rw [hn, k2]

theorem loop_stepP_inr_ne {j j' : B.I} {l l' : List D}
    (h : B.toProg.stepP (j, l) = .inl (j', l')) (hne : j' ≠ eB) :
    (loop T B eT eB).toProg.stepP (.inr j, l) = .inl (.inr j', l') := by
  obtain ⟨k1, k2⟩ := next_of_stepP h
  have hn : (loop T B eT eB).toProg.next (.inr j) (.inr (B.toProg.trip j l).2) =
      .inl (.inr j') := by
    show (match B.next j (B.toProg.trip j l).2 with
      | .inl j' => if j' = eB then Sum.inl (Sum.inl T.start) else Sum.inl (Sum.inr j')
      | .inr x => Sum.inr x) = _
    rw [show B.next j (B.toProg.trip j l).2 = .inl j' from k1]
    exact if_neg hne
  simp only [Prog.stepP, loop_trip_inr]
  rw [hn, k2]

theorem loop_stepP_inr_exit {j : B.I} {l l' : List D}
    (h : B.toProg.stepP (j, l) = .inl (eB, l')) :
    (loop T B eT eB).toProg.stepP (.inr j, l) = .inl (.inl T.start, l') := by
  obtain ⟨k1, k2⟩ := next_of_stepP h
  have hn : (loop T B eT eB).toProg.next (.inr j) (.inr (B.toProg.trip j l).2) =
      .inl (.inl T.start) := by
    show (match B.next j (B.toProg.trip j l).2 with
      | .inl j' => if j' = eB then Sum.inl (Sum.inl T.start) else Sum.inl (Sum.inr j')
      | .inr x => Sum.inr x) = _
    rw [show B.next j (B.toProg.trip j l).2 = .inl eB from k1]
    exact if_pos rfl
  simp only [Prog.stepP, loop_trip_inr]
  rw [hn, k2]

/-- **One body run inside the loop.** A first arrival of the body at `eB`, followed by a first
arrival of the loop at `inl eF` from the test's start, is a first arrival of the loop at
`inl eF`. -/
theorem loop_body_then {eF : T.I} (hTF : T.start ≠ eF) {s : B.toProg.I × List B.toProg.D}
    {l₁ : List D} {c₁ : ℕ} (hB : ReachFirst B.toProg eB s l₁ c₁) {l₂ : List D} {c₂ : ℕ}
    (hL : ReachFirst (loop T B eT eB).toProg (.inl eF) (.inl T.start, l₁) l₂ c₂) :
    ReachFirst (loop T B eT eB).toProg (.inl eF) (.inr s.1, s.2) l₂ (c₁ + c₂) := by
  revert hL
  induction hB with
  | @last s l hs =>
    intro hL
    have h1 := ReachFirst.step (P := (loop T B eT eB).toProg) (e := .inl eF)
      (loop_stepP_inr_exit T B eT eB hs) (fun h => hTF (Sum.inl.inj h)) hL
    rwa [loop_tripCost_inr] at h1
  | @step s i l₁ l c hs hne _ ih =>
    intro hL
    have h1 := ReachFirst.step (P := (loop T B eT eB).toProg) (e := .inl eF)
      (loop_stepP_inr_ne T B eT eB hs hne) (fun h => Sum.inl_ne_inr h.symm) (ih hL)
    rw [loop_tripCost_inr, ← Nat.add_assoc] at h1
    exact h1

/-- **The loop theorem.** For `k < n`, suppose the single-trip test sends `(T.start, l_k)` to
`(eT, m_k)`, and the body first-arrives at `eB` from `(B.start, m_k)` with output `l_{k+1}` and
cost `b_k`. Suppose at `l_n` the test sends `(T.start, l_n)` to `(eF, out)`. Then the loop
first-arrives at `inl eF` from `(inl T.start, l₀)` with output `out`. The cost is exactly
`Σ_{k<n} (t_k + b_k) + t_n`, where `t_k` is the test's trip cost on `l_k`. -/
theorem loop_reachFirst {eF : T.I} (hTF : T.start ≠ eF) (hFT : eF ≠ eT) :
    ∀ (n : ℕ) (l m : ℕ → List D) (b : ℕ → ℕ) (out : List D),
      (∀ k < n, T.toProg.stepP (T.start, l k) = .inl (eT, m k)) →
      (∀ k < n, ReachFirst B.toProg eB (B.start, m k) (l (k + 1)) (b k)) →
      T.toProg.stepP (T.start, l n) = .inl (eF, out) →
      ReachFirst (loop T B eT eB).toProg (.inl eF) (.inl T.start, l 0) out
        (∑ k ∈ Finset.range n, (T.toProg.tripCost T.start (l k) + b k) +
          T.toProg.tripCost T.start (l n)) := by
  intro n
  induction n with
  | zero =>
    intro l m b out _ _ hstop
    have h1 := ReachFirst.last (P := (loop T B eT eB).toProg) (e := .inl eF)
      (loop_stepP_inl_ne T B eT eB hstop hFT)
    rw [loop_tripCost_inl] at h1
    simpa using h1
  | succ n ih =>
    intro l m b out hT hB hstop
    have ih' := ih (fun k => l (k + 1)) (fun k => m (k + 1)) (fun k => b (k + 1)) out
      (fun k hk => hT (k + 1) (by omega)) (fun k hk => hB (k + 1) (by omega)) hstop
    have hbody := loop_body_then T B eT eB hTF (hB 0 (by omega)) ih'
    have h1 := ReachFirst.step (P := (loop T B eT eB).toProg) (e := .inl eF)
      (loop_stepP_inl_exit T B eT eB (hT 0 (by omega))) (fun h => Sum.inl_ne_inr h.symm)
      hbody
    rw [loop_tripCost_inl] at h1
    convert h1 using 1
    rw [Finset.sum_range_succ']
    ring

/-- **The loop theorem on the compiled Turing machine.** -/
theorem loop_tm {eF : T.I} (hTF : T.start ≠ eF) (hFT : eF ≠ eT) (n : ℕ) (l m : ℕ → List D)
    (b : ℕ → ℕ) (out : List D)
    (hT : ∀ k < n, T.toProg.stepP (T.start, l k) = .inl (eT, m k))
    (hB : ∀ k < n, ReachFirst B.toProg eB (B.start, m k) (l (k + 1)) (b k))
    (hstop : T.toProg.stepP (T.start, l n) = .inl (eF, out))
    (Tp : ℤ → Sym D) (hTp : (loop T B eT eB).toProg.Repr Tp (l 0)) :
    ∃ Tp', (loop T B eT eB).toProg.Repr Tp' out ∧
      (loop T B eT eB).toProg.toTM.run
          ⟨.fwd (.inl T.start) ((loop T B eT eB).init (.inl T.start)), Tp, 0⟩
          (∑ k ∈ Finset.range n, (T.toProg.tripCost T.start (l k) + b k) +
            T.toProg.tripCost T.start (l n)) =
        ⟨.fwd (.inl eF) ((loop T B eT eB).init (.inl eF)), Tp', 0⟩ :=
  (loop T B eT eB).toProg.reach_run
    (loop_reachFirst T B eT eB hTF hFT n l m b out hT hB hstop).reach Tp hTp

end ProgOn

end PVNP.Discrete.Sweep
