import PVNP.ToroidalDiagonal

/-!
# Phase XVI: arbitrary-CNF finite toroidal consistency

A formula-dependent finite ring can store one Boolean assignment in each
row, copy it to the next row, and check one clause per row.  Closing the
ring yields a finite constraint system with a lock if and only if the
original CNF is satisfiable.

This is a *logical* construction, not a physical WCT locking solution.
Every row carries an entire assignment, and this theorem does not establish
an admissible constant-alphabet lattice, continuum energy minimizer,
convergence of a dynamical flow, robust measurement or computation time.
In particular it does not close the original I-37 claim or imply P ≠ NP.
-/

namespace PVNP.ToroidalCNFLock

open PVNP.PartI PVNP.CrossingSAT PVNP.ToroidalDiagonal

/-- A row is a Boolean assignment to the logical variables.  Consecutive
rows agree, the last row closes onto the first, and row j satisfies clause j.
The repeated full assignment is charged as part of the representation;
nothing is claimed about a physical implementation of these row constraints. -/
def Lock (F : Formula) (rows : ℕ → (ℕ → Bool)) : Prop :=
  (∀ j < F.length, rows (j + 1) = rows j) ∧
  rows F.length = rows 0 ∧
  (∀ (j : ℕ) (hj : j < F.length),
    evalClause (rows j) F[j] = true)

/-- The elementary ring-connectivity lemma for row assignments. -/
theorem rows_constant (F : Formula) (rows : ℕ → (ℕ → Bool))
    (h : ∀ j < F.length, rows (j + 1) = rows j) :
    ∀ j ≤ F.length, rows j = rows 0 := by
  intro j
  induction j with
  | zero =>
      intro _
      rfl
  | succ j ih =>
      intro hj
      calc
        rows (j + 1) = rows j := h j (by omega)
        _ = rows 0 := ih (by omega)

/-- **Arbitrary finite CNF:** a logical toroidal lock exists exactly when
the formula is satisfiable.  This does not say the lock can be found quickly,
nor that a physical toroidal system realizes the local checks. -/
theorem lock_iff_satisfiable (F : Formula) :
    (∃ rows : ℕ → (ℕ → Bool), Lock F rows) ↔ satisfiable F := by
  constructor
  · rintro ⟨rows, hedges, _, hclauses⟩
    refine ⟨rows 0, (evalFormula_iff (rows 0) F).2 ?_⟩
    intro c hc
    obtain ⟨j, hj, hcj⟩ := (List.mem_iff_getElem).1 hc
    have hrow := hclauses j hj
    have hident : rows j = rows 0 :=
      rows_constant F rows hedges j (by omega)
    rw [hident, hcj] at hrow
    exact hrow
  · rintro ⟨assignment, hformula⟩
    refine ⟨fun _ => assignment, ?_, rfl, ?_⟩
    · intro j hj
      rfl
    · intro j hj
      exact (evalFormula_iff assignment F).1 hformula
        (F[j]) ((List.mem_iff_getElem).2 ⟨j, hj, rfl⟩)

/-- An uncharged, formula-independent notion of cyclic agreement cannot be
sound and complete for CNF-SAT.  It has a constant-row lock even when the
supplied CNF is the provably contradictory inverted-seam ring. -/
theorem bare_ring_lock_not_sat_classifier :
    ¬ (∀ F : Formula,
      satisfiable F ↔
        ∃ rows : ℕ → (ℕ → Bool), ∀ j : ℕ, rows (j + 1) = rows j) := by
  intro h
  have hbare : ∃ rows : ℕ → (ℕ → Bool),
      ∀ j : ℕ, rows (j + 1) = rows j :=
    ⟨fun _ _ => false, fun _ => rfl⟩
  exact odd_ring_unsat 0 ((h (ringFormula 0 true)).2 hbare)

end PVNP.ToroidalCNFLock
