import PVNP.DiscreteMachines

/-!
# Generic execution lemmas for ordinary Turing machines

Reusable lemmas for proving correctness of explicit `PVNP.Discrete.TM`
constructions:

* `run_one`, `run_step`: a single step from a known transition.
* `scan1`: a one-state scan that rewrites every visited cell with itself.
* `scan2`: an alternating two-state scan moving right two cells per round.
* `frozen`, `none_before`: if every answering state halts, an answer at time
  `N` together with no answer at time `N - 1` implies no answer at any
  earlier time.  This reduces first-answer proofs to two configurations.
-/

namespace PVNP.Discrete.TM

variable (M : TM)

theorem run_one (c : M.Cfg) : M.run c 1 = M.next c := rfl

theorem run_step {c : M.Cfg} {q' : M.Λ} {a : M.Γ} {d : Dir}
    (h : M.δ c.q (c.tape c.head) = some (q', a, d)) :
    M.run c 1 = ⟨q', Function.update c.tape c.head a, c.head + d.shift⟩ := by
  rw [run_one]; simp [next, step, h]

theorem run_step' {q : M.Λ} {T : ℤ → M.Γ} {p : ℤ} {q' : M.Λ} {d : Dir}
    (h : M.δ q (T p) = some (q', T p, d)) :
    M.run ⟨q, T, p⟩ 1 = ⟨q', T, p + d.shift⟩ := by
  rw [M.run_step (c := ⟨q, T, p⟩) h]
  simp

/-- One-state scan that leaves the tape unchanged. -/
theorem scan1 (s : M.Λ) (d : Dir) (T : ℤ → M.Γ) (p : ℤ) (n : ℕ)
    (h : ∀ i : ℕ, i < n → M.δ s (T (p + i * d.shift)) = some (s, T (p + i * d.shift), d)) :
    M.run ⟨s, T, p⟩ n = ⟨s, T, p + n * d.shift⟩ := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_succ, ih (fun i hi => h i (by omega)), ← run_one,
      M.run_step' (h n (by omega))]
    congr 1; push_cast; ring

/-- Two-state alternating scan to the right, two cells per round. -/
theorem scan2 (s1 s2 : M.Λ) (T : ℤ → M.Γ) (p : ℤ) (n : ℕ)
    (h1 : ∀ i : ℕ, i < n → M.δ s1 (T (p + 2 * i)) = some (s2, T (p + 2 * i), Dir.R))
    (h2 : ∀ i : ℕ, i < n → M.δ s2 (T (p + 2 * i + 1)) = some (s1, T (p + 2 * i + 1), Dir.R)) :
    M.run ⟨s1, T, p⟩ (2 * n) = ⟨s1, T, p + 2 * n⟩ := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, run_add, run_add,
      ih (fun i hi => h1 i (by omega)) (fun i hi => h2 i (by omega)),
      M.run_step' (h1 n (by omega))]
    simp only [Dir.shift]
    rw [show p + 2 * (n : ℤ) + 1 = p + 2 * n + 1 from rfl, M.run_step' (h2 n (by omega))]
    simp only [Dir.shift]; push_cast; ring_nf

/-- In a machine whose answering states halt, an answering configuration is frozen. -/
theorem frozen (hhalt : ∀ c : M.Cfg, M.ans c ≠ none → M.step c = none)
    (c : M.Cfg) (m : ℕ) (hm : M.ans (M.run c m) ≠ none) :
    ∀ k, M.run c (m + k) = M.run c m := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, run_succ, ih]
    simp [next, hhalt _ hm]

/-- Reduce "no earlier answer" to the configuration one step before. -/
theorem none_before (hhalt : ∀ c : M.Cfg, M.ans c ≠ none → M.step c = none)
    (c : M.Cfg) {N : ℕ} (hprev : 0 < N → M.ans (M.run c (N - 1)) = none) :
    ∀ m < N, M.ans (M.run c m) = none := by
  intro m hm
  by_contra hne
  have := M.frozen hhalt c m hne (N - 1 - m)
  rw [show m + (N - 1 - m) = N - 1 by omega] at this
  exact hne (by rw [← this]; exact hprev (by omega))

end PVNP.Discrete.TM
