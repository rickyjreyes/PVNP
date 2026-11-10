# PVNP Phase XVI: compute-exhaustive nine-claim research, first implemented pass

**Date:** 10 November 2026  
**Original manuscript inventory:** `pvnp/proofs/manuscript-lean-inventory.md`  
**Status:** research branch, new Lean files require successful exact-head build and axiom audit

## Ground rules

This phase has nine original *Restricted/Open* targets and does **not** change
the official ledger (78 Exact, 2 Restricted, 4 Refuted, 7 Open, total 91).
The original four refutations remain preserved. The progress bars in
`pvnp/phase_xvi/targets.json` are explicitly subjective work estimates and
are not a claim that a theorem is true or that an unproved hypothesis holds.

No finite exhaustion can establish a universal asymptotic lower bound. No
formula-dependent logical SAT encoding is a physical WCT device until the
frozen dynamics, representation, preparation and readout costs are proved.

## I-37: arbitrary-CNF *logical* toroidal consistency

New Lean file: `lean/PVNP/ToroidalCNFLock.lean`.

Let (F=(c_0,\ldots,c_{m-1})) be any finite CNF formula. Define a
finite toroidal **logical constraint** with one Boolean assignment (a_j)
per row (j\in\{0,\ldots,m\}). Require:

1. (a_{j+1}=a_j) for each (0\le j<m);
2. (a_m=a_0) across the closing seam;
3. (c_j(a_j)=\mathrm{true}) for each (0\le j<m).

**Candidate Lean theorem:** `ToroidalCNFLock.lock_iff_satisfiable`:
a finite constraint lock exists if and only if (F) is satisfiable.

*Forward argument:* agreement along the ring implies all row assignments
are (a_0); each clause is therefore true under (a_0).
*Backward argument:* repeat any satisfying assignment in every row.
This also covers (m=0) and the empty clause.

**Separate obstruction:** cyclic agreement without formula-dependent
constraints is not a SAT criterion. The formula ((x_0)\land(\neg x_0))
is unsatisfiable, yet the all-false row assignment is a cyclic lock.
The companion candidate Lean theorem is
`ToroidalCNFLock.bare_ring_lock_not_sat_classifier`.

**Very important scope limit:** the row alphabet contains a full
(n)-bit assignment. The theorem is an abstract local ring consistency
statement, not a bounded-alphabet WCT torus, a physical stationary point,
an attractor, an efficient decision procedure, or an I-37 resolution.
It does not establish a resource lower bound or (P\ne NP).

### Independently executed finite experiments

The Python reference `pvnp/phase_xvi/finite_torus.py` independently
enumerates candidate row assignments rather than calling the SAT oracle
inside the ring search. Two bounded exhaustive searches completed:

| Variables | Max clauses | Max clause width | Formulas checked | SAT | UNSAT | Disagreements |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 3 | 3 | 75,895 | 69,774 | 6,121 | 0 |
| 4 | 3 | 2 | 52,060 | 46,853 | 5,207 | 0 |
| **Total** | | | **127,955** | **116,627** | **11,328** | **0** |

The finite checks are evidence for the candidate formal theorem only.
They are not substituted for its Lean proof and do not establish the
quantified physical statement.

Reproduce the bounded searches:

```bash
python -m pvnp.phase_xvi.finite_torus --variables 3 --max-clauses 3 --max-width 3
python -m pvnp.phase_xvi.finite_torus --variables 4 --max-clauses 3 --max-width 2
```

## I-31: quadratic amplitude-scaling obstruction

New Lean file: `lean/PVNP/SeparatorAmplitude.lean`.

Suppose the interface energy restricted to an amplitude ray is
(E(a\psi)=a^2e), with finite (e\ge 0), and **all** (a>0)
remain admissible without any detector normalization. There is no
strict positive constant (c) such that (E(a\psi)\ge c) for every
positive (a). For any (c>0), choose

```text
a = c / (2 * (e + c + 1)).
```

Then (0<a<1) and (a^2 e<c), contradicting such a bound. The proposed
Lean theorem is `SeparatorAmplitude.no_uniform_quadratic_price`.

This is not a refutation of the **frozen** I-31 claim. A fixed robust
readout contrast, amplitude constraint, or normalization may exclude
the small-amplitude rays. The actual physical admissibility/contrast
hypotheses must be analyzed before applying this obstruction.

`pvnp/phase_xvi/scaling.py` constructs exact rational counterexamples,
with 500 parameter-grid checks in its test.

## Other seven targets: exact remaining mathematical obligations

| Claim | Status | Unresolved original-claim obligation |
|---|---|---|
| II-10 | Restricted | Actual polynomial-radius MTM execution invariants, original input/writer full output, first halt, polynomial bound |
| I-32 | Open | A representation-independent expander price for *every* admissible decider, respecting known parity bypasses |
| I-3 | Open | Formula-dependent physical flow, convergence and robust sound/complete detector |
| I-11 | Restricted | Charged, accuracy-certified continuum PDE/TM simulation in both directions |
| I-2 | Open | Construct an independently certified verifiable nonconstructible wavefield family |
| I-16 | Open | Superpolynomial SAT lower bound for every uniform decider; known polynomial lower bounds do not imply it |
| III-22 | Open | Editorial treatment as an interpretive arrow-of-time remark, unless a non-vacuous quantified mathematical proposition is supplied |

**No claims are promoted** in this pass. In particular, the general
`TwoPhasePolynomialWriter` and `TwoPhasePrefixWriter` definitions
are compiled candidates, but not the unrestricted II-10 FP theorem.

## Verification

A new `test_phase_xvi_polynomial_writer.py` probes the II-10 Python
candidate against adversarial input lengths, radius-zero boundaries and
higher-degree Horner coefficient lists. These added II-10 tests have
**not yet been executed against the exact GitHub PR head**, and passing
them would not establish the unrestricted machine-output theorem.

Two new Lean modules are included in `lean/PVNP.lean` and their principal
theorems in `lean/audit/AxiomAudit.lean`. They require exact-head
Lean 4.23.0 compilation and allowed-axiom checks. A successful Python
test cannot substitute for Lean kernel verification.

```bash
# In repository root
python -m unittest discover -s pvnp/tests -p 'test_phase_xvi_*.py'
python pvnp/phase_xvi/status.py --check
python pvnp/phase_xvi/status.py

# In lean/
lake build PVNP.ToroidalCNFLock PVNP.SeparatorAmplitude
lake build PVNP
lake env lean audit/AxiomAudit.lean | tee axiom-audit.txt
python audit/check_axioms.py audit/AxiomAudit.lean axiom-audit.txt
```

### Execution evidence

An independent local Python run of the six Phase XVI tests reported:
`Ran 6 tests ... OK`, including 11,155 exhaustive finite CNF cases
and 500 exact rational scaling checks. The larger finite search results
above were also executed locally. The newly written Lean modules have
**not yet been compiled in this environment**; the repo/CI or a local
user Lean run must confirm them. No Python or Lean pass is claimed
without actual observed output.

## Next mathematical work

1. Discharge the unrestricted original `MTM.Outputs` invariants for
   II-10 using the existing polynomial-writer program, not a surrogate.
2. For I-37, replace full-assignment row symbols with explicitly charged
   bounded local gadgets and prove the corresponding physical realization
   or exhibit an obstruction.
3. For I-31, determine whether the actual WCT readout constraints provide
   a uniform contrast that blocks the amplitude-scaling counterexample.
4. Run independent I-16 lower-bound strategies without treating a
   finite-horizon or single-tape polynomial lower bound as (P\ne NP).
5. Maintain the other claims as separate mathematical research tracks.
