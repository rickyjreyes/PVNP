import PVNP.ToroidalCNFLock

/-!
# Phase XVII: logical toroidal consistency with finite Boolean row alphabets

Unlike the Phase XVI function-valued row over all natural indices, this
representation has `n` Boolean cells per row (`Fin n → Bool`). The periodic
constraint still checks a complete CNF clause on its assigned row, so the
clause check may involve non-neighbouring columns. It is not a continuum
WCT solution or a nearest-neighbor-only physical lattice.

The assignment family is indexed by ℕ for convenience; only rows 0 through
|F| are queried by the constraint. The finite trace can be serialized in
(|F| + 1)*n Boolean cells.
-/
namespace PVNP.ToroidalFiniteRows

open PVNP.PartI PVNP.CrossingSAT PVNP.CircuitCNF

/-- Extend a finite Boolean row by false outside its declared columns. -/
def rowValuation (n : ℕ) (row : Fin n → Bool) : ℕ → Bool :=
  fun j => if h : j < n then row ⟨j, h⟩ else false

/-- Finite-alphabet logical toroidal lock with a clause checked on each
row and explicit periodic closing condition. -/
def RowLock (F : Formula) (n : ℕ) (rows : ℕ → Fin n → Bool) : Prop :=
  (∀ j < F.length, rows (j + 1) = rows j) ∧
  rows F.length = rows 0 ∧
  (∀ (j : ℕ) (hj : j < F.length),
    evalClause (rowValuation n (rows j)) F[j] = true)

/-- A formula whose variables are bounded by n has a finite-alphabet
logical toroidal lock precisely when it is satisfiable. This is a CSP
representation theorem, not a physical locking result. -/
theorem rowLock_iff_satisfiable (F : Formula) (n : ℕ)
    (hF : Bounded F n) :
    (∃ rows : ℕ → Fin n → Bool, RowLock F n rows) ↔ satisfiable F := by
  constructor
  · rintro ⟨rows, heq, _, hclause⟩
    refine ⟨rowValuation n (rows 0), (evalFormula_iff _ F).2 ?_⟩
    intro c hc
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hc
    have hchain : ∀ k ≤ F.length, rows k = rows 0 := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
          intro hk
          calc
            rows (k + 1) = rows k := heq k (by omega)
            _ = rows 0 := ih (by omega)
    have hr : rows j = rows 0 := hchain j (by omega)
    have hcl := hclause j hj
    rw [hr, hget] at hcl
    exact hcl
  · rintro ⟨a, ha⟩
    let v : Fin n → Bool := fun j => a j.val
    have hagree : Agree n a (rowValuation n v) := by
      intro j hj
      simp [rowValuation, hj, v]
    have hvalid : Holds (rowValuation n v) F :=
      holds_congr hF hagree ((evalFormula_iff a F).1 ha)
    refine ⟨fun _ => v, ?_, rfl, ?_⟩
    · intro j hj; rfl
    · intro j hj
      exact hvalid (F[j]) ((List.mem_iff_getElem).2 ⟨j, hj, rfl⟩)

/-- The queried trace is a concrete finite list of finite-bit rows. -/
def finiteTrace (F : Formula) (n : ℕ) (rows : ℕ → Fin n → Bool) :
    List (Fin n → Bool) :=
  (List.range (F.length + 1)).map rows

/-- Exactly |F|+1 finite-bit rows are needed to record the entire logical
ring witness, including its closing row. -/
theorem finiteTrace_length (F : Formula) (n : ℕ)
    (rows : ℕ → Fin n → Bool) :
    (finiteTrace F n rows).length = F.length + 1 := by
  simp [finiteTrace]

end PVNP.ToroidalFiniteRows
