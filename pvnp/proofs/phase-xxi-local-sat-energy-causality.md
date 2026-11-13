# Phase XXI research candidate: WCT SAT-energy locality under charged finite propagation

**Date:** 13 November 2026
**Base:** main at d0de39784f8fd6821c18f85c3bc7627599c63ec0
**Lean:** `lean/PVNP/WCTLocalSATEnergy.lean`
**Status:** Lean proof candidate pending exact-head hosted compilation and axiom audit.
**Classical P versus NP:** open.
**Physical WCT P versus NP:** open.

## Result

The pre-existing sign-blind interwoven WCT energy obeys
`SAT(F) ↔ (∃ admissible Ψ, E_SB(F,Ψ) < 1/8) ↔ (Emin_SB(F) = 0)`
for nonnegative λ and μ.

Select between two **fixed** already-certified 3-CNFs:
* `Fxor`: satisfiable;
* `G`: unsatisfiable.

Define `distalFormula(b) := if b then Fxor else G`, with the chosen source
bit `b := c j` residing at position `j` of a raw, spatially distributed
Boolean input configuration `c : Fin n → Bool`.

For every finite list of arbitrary radius-limited local update machines
with their individual time budgets charged, let

`totalReach := Σ stage.rounds * stage.radius`.

If a fixed decoder observes only the first `m` sites after these charged
stages and determines the correct WCT sign-blind SAT energy threshold on
**every** input `c`, then:

```text
j.val < totalReach stages + m
```

The same statement is proved for the zero-ground-energy criterion. For
the last input site `j=n-1` this gives:

```text
n ≤ totalReach stages + m
```

A no-go corollary rules out every such finite local pipeline when the
source bit lies outside its cumulative causal cone.

The proof is *algorithm-independent within the frozen finite-radius
staged class*: all local rules, radii, numbers of stages, and readout
functions are quantified, while their costs are explicit.

## Proof dependencies

* `InterwovenSAT.Fxor_sat`, `InterwovenSAT.G_unsat`;
* `InterwovenSAT.sat_iff_energySB_lt_eighth`,
  `InterwovenSAT.sat_iff_EminSB_eq_zero`;
* `MultiStageCausality.multistage_required_coverage_for_bit`.

This is a **new linking lemma**, not a new claim that the SAT lower bound
or channel packing theorem has been derived from the nonlinear PDE.
No assumption of a WCT physical PDE-to-discrete simulation is added.

## Limitations, including the important adversarial bypass

The family `distalFormula` contains just TWO fixed formulas. Its
satisfiability is a single distal Boolean input bit. Hence it is an easy
family, not a candidate for superpolynomial SAT hardness.

The lower bound is **linear spatial latency** when local signal
speed and readout width are fixed. The argument does not exclude a
linear-time solver, a polynomial-time TM solver, or nonlocal physical
architectures. A large prefix decoder, nonlocal input relocation, or
higher-radius paid stage can eliminate this *particular* bottleneck.

The map `c ↦ distalFormula(c j)` specifies the mathematical SAT
predicate; it does NOT transport the distal source bit to the decoder
for free. The charged computation acts on the actual raw spatial input.

The interwoven energy is a finite configuration-space energy and is NOT
the Hamiltonian of the frozen torus PDE. Physical realization, robust
measurement, and the input-uniform PDE/discrete bridge remain open.

A universal exponential lower bound for unrestricted SAT, a physical
WCT P/NP separation, and classical P ≠ NP remain unproved.

## Verification

```bash
cd lean
lake exe cache get
lake build PVNP.WCTLocalSATEnergy
lake build PVNP
lake env lean audit/AxiomAudit.lean > audit-output.txt
python3 audit/check_axioms.py audit/AxiomAudit.lean audit-output.txt
```

Do not merge or upgrade a manuscript claim on the strength of an
unverified candidate. After the exact-head checks pass, classify the new
theorems as *supporting results*, without changing any of the existing
four Open manuscript claims.


## Extended explicit CNF encoding (same PR)

`lean/PVNP/WCTDistributedSAT.lean` strengthens the earlier two-formula
selector to a *syntactically explicit, linearly sized family*.

For each spatial input `c : Fin n → Bool`, define `sourceFormula c`
with exactly `n+1` triple-literal 3-CNF clauses. Its first clause
forces `x₀=true`; the clause corresponding to each input bit `c i`
requires `x₀` if `c i=true`, and `¬x₀` otherwise.

Hence, with no SAT decision oracle in formula construction,

```text
Sat (sourceFormula c) ↔ ∀ i, c i = true.
```

A pair of raw input configurations differing at exactly any position
`j` (one all-true, the other false at `j`) has opposite SAT truth.
The complete preprocessed/local-computed/readout pipeline cannot
distinguish them unless

```text
j.val < totalReach stages + m.
```

This is also proved for the sign-blind energy predicate
`∃ Ψ, Admissible Ψ ∧ energySB (sourceFormula c) lam mu Ψ < 1/8`
and the ground energy predicate `EminSB (sourceFormula c) lam mu = 0`.

The same model restrictions remain: the source is a raw spatial input;
every stage is local and explicitly charged, the output only observes a
prefix, and the formula is a fixed mathematical interpretation rather
than a spatial PDE encoding. The family remains algorithmically easy
(AND of input bits), so the result is linear, not superpolynomial.

The exact-head Lean build and axiom audit must pass before labeling
these declarations kernel-verified.
