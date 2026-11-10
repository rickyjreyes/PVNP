# PVNP Phase XVII: Mathematical frontier and originality audit

**Date:** 10 November 2026. **Stacked on:** Phase XVI draft PR #68.
**Status:** new Phase XVII Lean theorems need exact-head compilation and axiom audit.

## Verified baseline and non-promotion rule

The author's current 91-claim inventory remains **78 Exact / 2 Restricted /
4 Refuted / 7 Open**. User-supplied Phase XVI Windows Lean logs show
targeted and full builds pass (7,240 and 7,379 jobs) and 9 Python tests pass
at commit 16ab4f8. The full final permitted-axiom audit validator output
was not supplied, so that audit gate cannot be asserted as complete.

Phase XVII's new Lean files are **proof candidates until separately built**.
Passing finite Python experiments is not a substitute for kernel
verification. No original claim is promoted here.

## Priority II-10: a checkable part of the actual writer

`lean/PVNP/TwoPhasePolynomialWriter.lean` now contains the candidate theorem
`writer_clock_eq_polynomial`: the exact coefficient list extracted by
the actual polynomial writer, reversed into program execution order, has
Horner value equal to `p.eval n`. Its proof reuses the existing
`PVNP.CookLevin.Gen.horner_hcoeffs` theorem, rather than establishing a
second incompatible arithmetic specification.

This removes an arithmetic coefficient-order question from the proof
frontier, *conditional on Lean compiling the new bridge*. It does NOT
prove that the actual generated `MTM.step` implements the Horner
operation or produces the correct output tape.

`pvnp/phase_xvi/writer_certificate.py` adds:

- Finite-control entry, instruction-arity, branch-address and jump safety.
- Reachability enumeration for generated control instructions.
- Bounded actual-interpreter runs, exact output comparison, and
  observed first-halt execution/step-budget checks.
- Adversarial cases for the original input and window writers.

A local independent implementation of the window machine previously
passed 434 finite cases. Those cases are a mathematical/software smoke
test only; the new CI tests against the **actual repository source**
must be run on the current branch.

**Precisely missing:** inductive operational invariants for the actual
`TwoPhasePolynomialWriter.step`, including the input-presence marks,
Horner accumulator, destination counters, output-prefix append, return
head motion, first halt, and the total polynomial transition bound.
Prove `MTM.Outputs` and `FP` for both original writers. Only that would
justify upgrading II-10 from Restricted to Exact.

## Priority I-37: concrete finite Boolean-cell toroidal constraints

`pvnp/phase_xvi/boolean_torus_reduction.py` constructs an explicit
**standard propositional** torus-CNF reduction. For a CNF formula F
with n declared Boolean variables and m clauses, set k=max(1,m).
Each toroidal row j contains n Boolean variables x[j,i].

For every j and i, include two binary clauses encoding

  x[j,i] ↔ x[(j+1) mod k,i].

Put the j-th original clause in row j by replacing each literal on
variable i with that row's variable x[j,i].

The transformed CNF has:

- Exactly **n k Boolean variables**.
- Exactly **2 n k + m clauses**.
- Maximum clause width **max(2, original maximum width)**.
- A uniform generator using O(nk + input clause occurrences) operations,
  measured in the declared n,m parameters.
- Equality constraints between vertically adjacent cells (including
  the periodic seam), but **original clause constraints can span
  distant columns**. Therefore this is a bounded-arity **constraint
  graph**, not a nearest-neighbor physical lattice.

**Correctness proof, independent of finite tests:** a satisfying
assignment to F, repeated in every row, satisfies all equality clauses
and row clauses. Conversely, every satisfying assignment to the torus
must agree between successive rows in every column; chaining these
equalities gives the same n-bit assignment in every row, which
satisfies each original clause. Thus SAT(F) iff SAT(torus(F)).

All edge cases, including m=0, n=0 and empty clauses, are included.

**Executed finite check:** 1,464 CNFs with 2 variables, ≤3 clauses,
width ≤2: 951 satisfiable, 513 unsatisfiable, **0 disagreements**.
Four independent test methods passed in 0.068 s in the local
minimal Python test harness. The repository-specific regression tests
also require their own exact-head run.

`lean/PVNP/ToroidalFiniteRows.lean` is a candidate Lean analogue
restricted to a finite n-bit row alphabet. Only rows 0..m are queried.
It proves the logical row-lock equivalence under an explicit variable
bound, plus a finite-trace-length lemma, once kernel-verified.

**Novelty: not established, likely standard.** Variable replication,
equality clauses, and polynomial-size CNF encodings are established
techniques, related to Cook-Levin tableaux and Tseitin transformations.
The finite torus presentation alone must not be advertised as an
original SAT breakthrough.

**Missing original I-37:** true spatial locality, fixed finite
physical cell alphabet, admissible nonlinear WCT field dynamics,
stable toroidal locks, convergence, robust readout and all charged
preparation costs.

## Priority I-31: sharp normalized-ray separator price

`lean/PVNP/SeparatorNormalizedRay.lean` proposes an exact theorem.
Let a,e,r,δ be nonnegative reals, with quadratic ray energy E=a²e
and linearly scaling contrast C=a r. If the charged readout requires
δ≤a r, then

  δ² e ≤ a² (r² e).

The proof multiplies the two nonnegative factors
`(a*r - δ)` and `(a*r + δ)`, then multiplies the resulting
square inequality by e≥0. Equality holds when δ=a r, so
the coefficient is sharp for this one-ray model.

This complements Phase XVI's small-amplitude obstruction and spells
out exactly what a detector contrast can rescue.

**Novelty: elementary algebra, not an original WCT theorem.**
The frozen continuum I-31 problem still requires a **uniform**
positive cost-to-contrast ratio across all admissible trajectories.
That assertion is not established by the ray inequality.

## I-16 and related P versus NP research barriers

Do not interpret the following as a proof that every lower-bound
strategy must fail. It is an originality/barrier checklist:

- **Relativization:** Baker, Gill, Solovay (1975), *Relativizations
  of the P =? NP Question*. A lower-bound argument based solely on
  oracle-invariant diagonalization does not suffice.
- **Natural proofs:** Razborov and Rudich (1997), *Natural Proofs*,
  JCSS 55(1). Applies conditionally to broad families of efficiently
  recognizable circuit properties under cryptographic assumptions.
- **Algebrization:** Aaronson and Wigderson (2009), *Algebrization:
  A New Barrier in Complexity Theory*.
  https://eccc.weizmann.ac.il/eccc-reports/2008/TR08-005/Paper.pdf

See also standard Tseitin-style CNF encodings:
G. S. Tseitin, *On the Complexity of Derivation in Propositional Calculus*
(1968): https://yurichev.com/mirrors/SAT/Tseitin/Tseitin1968_en.pdf

Any proposed I-16 breakthrough must identify exactly which quantifier
or computational bottleneck defeats these barriers. Existing quadratic
single-tape lower bounds do not prove a universal superpolynomial
SAT lower bound. The conditional `SATLowerBound ↔ P_TM ≠ NP_TM`
does not prove either direction unconditionally.

## Status of the other targets

| Original claim | Needed mathematical contribution |
|---|---|
| I-32 | Algorithm- and encoding-independent interface lower bound or a precise countermodel, beyond a chosen graph rail |
| I-3 | Physically admissible formula-dependent field evolution and sound/complete robust readout |
| I-11 | Certified charged numerical simulation of frozen continuum PDE with polynomial complexity and a genuine TM-to-physical realization |
| I-2 | Independently constructed, verifiable nonconstructible family with a correct language-complexity bridge |
| III-22 | Original text is interpretive. Separate draft PR #67 investigates an elementary reversible-dynamics entropy obstruction and must be evaluated on its own terms |

## Reproducibility and acceptance gates

From the stacked Phase XVII worktree:

```bash
python -m unittest discover -s pvnp/tests -p 'test_phase_xvi_*.py'
python -m unittest discover -s pvnp/tests -p 'test_phase_xvii_*.py'
python pvnp/phase_xvi/status.py --check
python -m pvnp.phase_xvi.boolean_torus_reduction

cd lean
lake build PVNP.TwoPhasePolynomialWriter PVNP.ToroidalFiniteRows PVNP.SeparatorNormalizedRay
lake build PVNP
lake env lean audit/AxiomAudit.lean > axiom-audit.txt
python audit/check_axioms.py audit/AxiomAudit.lean axiom-audit.txt
```

The current container does **not** have the pinned Lean toolchain or
network access to retrieve one. No current-head kernel build has
been executed here. The new Lean proof candidates must remain unverified
until the external exact-head build is supplied.

A successful build and clean audit certify the *statements actually
written*, not the original physical assumptions or novelty.
