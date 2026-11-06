import PVNP.CrossingTrace

/-!
# Actual machine one-sided tape splicing

Changing an untouched half of the bi-infinite tape cannot affect a
machine execution segment before the head reaches that half.
This is a genuine finite-control Turing-machine step/run result, not
an assumption of rectangularity of a complete crossing record.
-/

namespace PVNP.CrossingSplice

open PVNP.Discrete

def mixTape {A : Type*} (cut : ℤ) (l r : ℤ → A) : ℤ → A :=
  fun i => if i < cut then l i else r i

theorem mixTape_left {A : Type*} (cut : ℤ) (l r : ℤ → A) (i : ℤ)
    (hi : i < cut) : mixTape cut l r i = l i := by
  simp [mixTape, hi]

theorem mixTape_right {A : Type*} (cut : ℤ) (l r : ℤ → A) (i : ℤ)
    (hi : cut ≤ i) : mixTape cut l r i = r i := by
  simp [mixTape, not_lt.mpr hi]

theorem update_mix_left {A : Type*} (cut i : ℤ)
    (l r : ℤ → A) (v : A) (hi : i < cut) :
    Function.update (mixTape cut l r) i v =
      mixTape cut (Function.update l i v) r := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [mixTape, hi]
  · by_cases hc : j < cut
    · simp [mixTape, hc, hj, Ne.symm hj]
    · simp [mixTape, hc, hj, Ne.symm hj]

theorem update_mix_right {A : Type*} (cut i : ℤ)
    (l r : ℤ → A) (v : A) (hi : cut ≤ i) :
    Function.update (mixTape cut l r) i v =
      mixTape cut l (Function.update r i v) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [mixTape, not_lt.mpr hi]
  · by_cases hc : j < cut
    · simp [mixTape, hc, hj, Ne.symm hj]
    · simp [mixTape, hc, hj, Ne.symm hj]

/-- Even a terminating or cross-boundary step depends only on the
half of the tape currently scanned by the machine. -/
theorem next_splice_left (M : TM) (cut : ℤ) (c : M.Cfg)
    (r : ℤ → M.Γ) (hc : c.head < cut) :
    M.next {c with tape := mixTape cut c.tape r} =
      {M.next c with tape := mixTape cut (M.next c).tape r} := by
  have hread : mixTape cut c.tape r c.head = c.tape c.head :=
    mixTape_left cut c.tape r c.head hc
  cases h : M.δ c.q (c.tape c.head) with
  | none =>
      simp [TM.next, TM.step, hread, h]
  | some instr =>
      obtain ⟨q, sym, move⟩ := instr
      simp [TM.next, TM.step, hread, h, update_mix_left, hc]

theorem next_splice_right (M : TM) (cut : ℤ) (c : M.Cfg)
    (l : ℤ → M.Γ) (hc : cut ≤ c.head) :
    M.next {c with tape := mixTape cut l c.tape} =
      {M.next c with tape := mixTape cut l (M.next c).tape} := by
  have hread : mixTape cut l c.tape c.head = c.tape c.head :=
    mixTape_right cut l c.tape c.head hc
  cases h : M.δ c.q (c.tape c.head) with
  | none =>
      simp [TM.next, TM.step, hread, h]
  | some instr =>
      obtain ⟨q, sym, move⟩ := instr
      simp [TM.next, TM.step, hread, h, update_mix_right, hc]

/-- Finite left-side execution agrees, including head, control and
all left writes, until the machine first reaches the right half. -/
theorem run_splice_left (M : TM) (cut : ℤ) (c : M.Cfg)
    (r : ℤ → M.Γ) :
    ∀ t : Nat, (∀ s < t, (M.run c s).head < cut) →
      M.run {c with tape := mixTape cut c.tape r} t =
        {M.run c t with tape := mixTape cut (M.run c t).tape r} := by
  intro t
  induction t with
  | zero =>
      intro _
      rfl
  | succ t ih =>
      intro hside
      have hprev := ih (by
        intro s hs
        exact hside s (by omega))
      calc
        M.run {c with tape := mixTape cut c.tape r} (t + 1) =
            M.next (M.run {c with tape := mixTape cut c.tape r} t) :=
          M.run_succ _ t
        _ = M.next {M.run c t with tape := mixTape cut (M.run c t).tape r} := by
          rw [hprev]
        _ = {M.next (M.run c t) with
              tape := mixTape cut (M.next (M.run c t)).tape r} :=
          next_splice_left M cut (M.run c t) r (hside t (by omega))
        _ = {M.run c (t + 1) with
              tape := mixTape cut (M.run c (t + 1)).tape r} := by
          rw [M.run_succ]

/-- Identical output throughout an execution segment confined left. -/
theorem answer_splice_left (M : TM) (cut : ℤ) (c : M.Cfg)
    (r : ℤ → M.Γ) (t : Nat)
    (hside : ∀ s < t, (M.run c s).head < cut) :
    M.ans (M.run {c with tape := mixTape cut c.tape r} t) =
      M.ans (M.run c t) := by
  rw [run_splice_left M cut c r t hside]
  rfl


/-- Symmetric finite-run splicing: while the head remains at or to the
right of the cut, changing the entire left tape does not change the
right-side execution or the control trace. -/
theorem run_splice_right (M : TM) (cut : ℤ) (c : M.Cfg)
    (l : ℤ → M.Γ) :
    ∀ t : Nat, (∀ s < t, cut ≤ (M.run c s).head) →
      M.run {c with tape := mixTape cut l c.tape} t =
        {M.run c t with tape := mixTape cut l (M.run c t).tape} := by
  intro t
  induction t with
  | zero =>
      intro _
      rfl
  | succ t ih =>
      intro hside
      have hprev := ih (by
        intro s hs
        exact hside s (by omega))
      calc
        M.run {c with tape := mixTape cut l c.tape} (t + 1) =
            M.next (M.run {c with tape := mixTape cut l c.tape} t) :=
          M.run_succ _ t
        _ = M.next {M.run c t with tape := mixTape cut l (M.run c t).tape} := by
          rw [hprev]
        _ = {M.next (M.run c t) with
              tape := mixTape cut l (M.next (M.run c t)).tape} :=
          next_splice_right M cut (M.run c t) l (hside t (by omega))
        _ = {M.run c (t + 1) with
              tape := mixTape cut l (M.run c (t + 1)).tape} := by
          rw [M.run_succ]

theorem answer_splice_right (M : TM) (cut : ℤ) (c : M.Cfg)
    (l : ℤ → M.Γ) (t : Nat)
    (hside : ∀ s < t, cut ≤ (M.run c s).head) :
    M.ans (M.run {c with tape := mixTape cut l c.tape} t) =
      M.ans (M.run c t) := by
  rw [run_splice_right M cut c l t hside]
  rfl

end PVNP.CrossingSplice
