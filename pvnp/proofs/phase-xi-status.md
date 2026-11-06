# Phase XI: an explicit no-subquadratic SAT theorem and auditable proof ledger

**Scope.** This checkpoint continues Phase X from merged PR #43, commit
`dd7138bf7a839cbfa0ce55b9f2a12323e5e2a916`. It does not resolve the
classical P-versus-NP problem.

## New Lean declaration

`lean/PVNP/PhaseXIQuadratic.lean` states

```lean
def UniformSubquadratic (M : TM) : Prop :=
  ∀ C : ℕ, 0 < C →
    ∃ N₀ : ℕ, ∀ x : List Bool, N₀ ≤ x.length →
      C * ftime M x < x.length ^ 2

theorem sat_no_uniform_subquadratic {M : TM} {T : ℕ → ℕ}
    (hM : M.Decides SAT_dense T) : ¬ UniformSubquadratic M
```

The theorem follows from the existing unconditional Phase X matrix-family
result `CrossingSATMatrix.quadratic_arbitrarily_large`:

For every ordinary single-tape machine `M` deciding `SAT_dense` in
some total time bound `T`, and every threshold `N₀`, there exists an
**unsatisfiable** input `x` with `|x| ≥ N₀` and

```
|x|² ≤ 384 * symbolBits M * ftime M x.
```

Here `symbolBits M = Nat.log 2 (Fintype.card (M.Λ × Dir) + 1) + 1`,
which is positive for any machine.

If `UniformSubquadratic M` held, take the integer multiplier
`C = 384 * symbolBits M > 0`, and then choose the length threshold
from its definition. The Phase X hard instance at that threshold yields
both `C * ftime M x < |x|²` and `|x|² ≤ C * ftime M x`, contradiction.

This repackages the known **quadratic** result in the conventional
quantified uniform `o(N²)` form. It does not prove `SAT_dense ∉ P_TM`,
because quadratic computation is polynomial, and it does not improve the
matrix lower-bound exponent.

## Source-of-truth dashboard

Run either command from the repository root:

```sh
python3 pvnp/tools/lean_progress.py --check
python3 pvnp/tools/lean_progress.py --markdown
python3 pvnp/tools/lean_progress.py --json
```

The script parses `pvnp/proofs/manuscript-lean-inventory.md` and independently crosschecks each claim against
the current manuscript coverage table (91 claims). It also reads the Phase X/XI principal theorem names
from `lean/audit/AxiomAudit.lean`, with a specific check for the new theorem.

| Manuscript | Exact | Restricted | Refuted | Open | Total |
|---|---:|---:|---:|---:|---:|
| Part I | 28 | 1 | 6 | 6 | 41 |
| Part II | 26 | 1 | 0 | 1 | 28 |
| Part III | 21 | 0 | 0 | 1 | 22 |
| **Total** | **75** | **2** | **6** | **8** | **91** |

An exact manuscript statement receives a 100% formalization bar only
when verified on a green CI head. A refuted statement has a verified
counterexample, **not** a completed proof of its original claim. Restricted
and open theorems have no fabricated numeric completion estimate.

The current amended-manuscript count is 75/91 exact. The original October 27 inventory was 70 Exact / 2 Restricted / 11 Refuted / 8 Open; the changes reflect corrected statements, not proofs of their original false forms.

The 91-claim inventory is distinct from new Phase X/XI supporting theorems;
this checkpoint does not change those counts.

## Remaining mathematical obligations

1. `CrossingSAT.SATLowerBound` (`SAT_dense ∉ P_TM`) is **OPEN**. The
   Phase IX equivalent target `SATSuperpolynomial` is also open.
2. The non-uniform circuit lower-bound premise `SAT_dense ∉ PPoly`
   remains **OPEN** and is stronger than the classical target.
3. CL-1, the *uniform polynomial-time* reduction of all `NP_TM` languages
   to `SAT_dense`, is **OPEN**. Phase X supplies signed *non-uniform*
   projections, not this theorem.
4. Physical bridge M1, universal physical lower bound M2 and certified
   lattice-to-continuum convergence M3-C remain **OPEN**.
5. The original manuscript's 11 refuted claims remain refuted, and its
   restricted claims are not promoted without discharging their exact gaps.

## Verification requirements

CI must successfully complete the full Lean kernel import-tree build,
Phase X and XI targeted builds, axiom audit restricted to `propext`,
`Classical.choice` and `Quot.sound`, the 91-claim progress validation,
other targeted checks, and the PDF workflow. No `sorry`, `admit`,
`native_decide` or custom axiom is introduced.
