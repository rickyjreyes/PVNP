# Phase XIII: constructive original W_M writers and quantitative SAT readout

**Starting point:** PR #57 merge `612e14f` (6 November 2026).
**Verification blocker:** the main workflow and its rerun both terminated **before any job steps**. This is not a Lean compiler error and is not evidence that the Phase XII Lean declarations compile. Do not report kernel verification until a full job runs.

## II-10, exact original W_M canonical encodings

### Deterministic reference writer

`pvnp/two_phase_reference.py` directly implements the canonical window and initial-configuration bit outputs from `TwoPhaseUniform`.

For `L=p(|x|)` and `R=L+1`, the 1D interval `[-L,L]` has `2L+1` active cells. The box `[-R,R]` contributes two exterior cells. The exact window code is

```text
unary radius          separator   canonical 1D membership bitmap
1^(L+1)               0           0 1^(2L+1) 0
```

of length `3L+5`, in agreement with `TwoPhaseUniform.originalWindowCode_polynomial_length`. An independent implementation enumerates every `site 1 R j` and applies the actual interval predicate.

The encoded initial configuration uses the author's original `encCfg M L (M.init x)` states, ordered from `-L` to `L`: original input symbols in `[0,n)`, blank elsewhere, the initial head on cell zero, and phase bit zero. The machine-specific `stateBits` mapping must be provided explicitly. The script never substitutes a decision-bit encoder or silently guesses the Lean `Fintype.equivFin` ordering.

The tests check every Boolean input through length 5 against the literal enumeration, several natural-coefficient polynomials including the zero polynomial, empty input, boundary cells, exact lengths, head location, and fixed-width state output.

### Lean window lemma

`TwoPhaseWindowShape.lean` proves the exact site mapping and bitmap predicate for every in-range index:

```lean
site 1 (L+1) j 0 = (j : ℤ) - (L+1 : ℕ)

site 1 (L+1) j ∈ window L ↔ (0 < j ∧ j < 2*(L+1))
```

These are the key finite-window facts required for a verified output writer.

**Still missing:** an explicit `MTM` that writes the *complete* `originalWindowCode` and `originalInputCode` with Lean-proved polynomial transition bounds. Python algorithms and bit-length bounds do not prove `FP` and do not close II-10. A later formal transducer should reuse the existing Horner sweep counter and the exact bitmap lemma, then implement and verify copying the input and serializing `stateBits`.

## I-3, logical-energy threshold

`PhasePenaltyGap.lean` adds four exact analytical statements (pending kernel validation):

1. For any unsatisfiable three-CNF `F` and any phase field `θ`, `Elogic θ F ≥ 1/8`.
2. `Sat F ↔ ∃ θ, Elogic θ F < 1/8`.
3. If a reported energy has certified absolute error `eps` and its upper error bar is below `1/8`, the reported phase field certifies SAT.
4. Conversely, no unsatisfiable formula has such a certificate.

These follow from the pre-existing `roundPhase_satisfies` and `psi_sat_completeness` results. The strict threshold concerns the **formula-dependent logical penalty** alone, not convergence of a wavefield PDE, physical signal-to-noise, computational preparation, or efficiency. This is a quantitative witness theorem, not a polynomial-time SAT algorithm or a solution to P vs NP.

## Other original claims

I-11 still requires a charged physical-to-classical simulation. I-16 remains open beyond the known unconditional quadratic single-tape SAT lower bound. I-31 requires a continuum-uniform physical separator price. I-32 requires an algorithm-independent expander hardness theorem. I-2 requires independent nonconstructibility, I-37 requires an arbitrary-formula physical toroidal lock construction, and III-22 is an interpretive remark rather than a quantified theorem.

**Manuscript ledger:** unchanged at 78 Exact / 2 Restricted / 4 Refuted / 7 Open of 91. The new supporting theorems do not justify promoting any original claim. The historical inventory and all refuted counterexamples remain untouched.

## Commands

```bash
python3 -m unittest discover -s pvnp/tests -p 'test_two_phase_reference.py'
cd lean
lake build PVNP
lake build PVNP.TwoPhaseWindowShape PVNP.PhasePenaltyGap
lake env lean audit/AxiomAudit.lean
```

Review exact-head CI results before merging. A failure before job allocation is not a successful test.
