# III-22: arrow-of-time status and exact formal no-go

**Original manuscript:** Part III, §8, `Arrow of Time: Limits of the Claim`.
**Inventory status:** `Open (interpretive / no theorem)`, unchanged.

The paragraph rejects any asserted equivalence between physical P/NP class
relations and retrocausality. It does not define a physical retrocausality
predicate, an entropy functional, a class of initial conditions, or a
time-reversal map. Consequently there is no precise mathematical statement
in III-22 whose proof would close the original claim.

## A mathematical theorem that is well-posed

`lean/PVNP/ArrowOfTime.lean` contains four **new proof candidates**:

- `involution_monotone_eq`: a scalar nondecreasing on all states of an
  involutive update is preserved pointwise;
- `involution_no_global_strict_increase`: no everywhere-strict scalar
  arrow exists for such an update;
- `time_reversal_monotone_eq`: if `next (reverse (next s)) = reverse s`
  and entropy is reversal-invariant, then global nondecrease forces
  conservation along each step;
- `time_reversal_no_global_strict_increase`: in the same model an
  everywhere-strict entropy arrow is impossible.

The proofs are elementary order arguments. This does **not** establish a
thermodynamic arrow from WCT, nor any result about SAT or P versus NP.
It also does not claim that real thermodynamics satisfies a global
monotonicity premise at each microscopic state.

## Verification gate

The branch includes the module in `lean/PVNP.lean` and includes the four
declarations in `lean/audit/AxiomAudit.lean`. These are **unverified Lean
candidates** until the pinned toolchain confirms:

```bash
cd lean
lake build PVNP.ArrowOfTime
lake build PVNP
lake env lean audit/AxiomAudit.lean | tee axiom-audit.txt
python3 audit/check_axioms.py audit/AxiomAudit.lean axiom-audit.txt
```

GitHub Actions runner allocation remains blocked under issue #59.
No changes to the 91-claim completion percentages are authorized.
