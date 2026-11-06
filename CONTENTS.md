# PVNP manuscript map

**Repository:** [rickyjreyes/PVNP](https://github.com/rickyjreyes/PVNP)  
**Author:** Richard J. Reyes  
**Revision sources:** October 27, 2026

| Part | Manuscript | PDF | LaTeX | Scope |
|---|---|---|---|---|
| I | [Curvature-bounded wave computation](pvnp/preprints/part-i-curvature-bounded-wave-computation/README.md) | [paper.pdf](pvnp/preprints/part-i-curvature-bounded-wave-computation/paper.pdf) | [main.tex](pvnp/papers/part-i-curvature-bounded-wave-computation/main.tex) | Conditional model-relative lower-bound program |
| II | [Discrete WCC / Turing equivalence](pvnp/preprints/part-ii-discrete-wcc-turing-equivalence/README.md) | [paper.pdf](pvnp/preprints/part-ii-discrete-wcc-turing-equivalence/paper.pdf) | [main.tex](pvnp/papers/part-ii-discrete-wcc-turing-equivalence/main.tex) | Uniform discrete simulation and separated physical-bridge obligation |
| III | [Critical reassessment of physical complexity](pvnp/preprints/part-iii-physical-complexity-reassessment/README.md) | [paper.pdf](pvnp/preprints/part-iii-physical-complexity-reassessment/paper.pdf) | [main.tex](pvnp/papers/part-iii-physical-complexity-reassessment/main.tex) | Corrected resource assumptions, explicit counterexamples, conditional conclusions |

## Publication identifiers

- **Part I:** [10.5281/zenodo.17743607](https://doi.org/10.5281/zenodo.17743607) — original work dated May 7, 2025.
- **Part II:** [10.5281/zenodo.17732642](https://doi.org/10.5281/zenodo.17732642) — original work dated November 26, 2025.
- **Part III:** [10.5281/zenodo.17783074](https://doi.org/10.5281/zenodo.17783074) — original work dated December 1, 2025.

The PDFs in this repository are revised manuscripts and should not be conflated with the original Zenodo release versions.

## Verified Phase VI and Phase VIII results (November 2026)

- **Phase VI:** [Periodic-torus H² well-posedness and F-1 continuum flux](pvnp/proofs/phase-vi-torus-flux-status.md), in `TorusWellPosed.lean` and `TorusFlux.lean`; [merged PR #40](https://github.com/rickyjreyes/PVNP/pull/40).
- **Phase VIII:** [Full crossing-sequence splicing and single-tape SAT lower bounds](pvnp/proofs/phase-viii-separation-status.md), in `CrossingHennie.lean`, `CrossingSAT.lean`, `CrossingSATSets.lean`; [merged PR #38](https://github.com/rickyjreyes/PVNP/pull/38).
- **Phase IX:** [Exact target, invariant tests and no-go theorems](pvnp/proofs/phase-ix-universal-lower-bound-status.md), in `SATTarget.lean`, `TseitinSAT.lean`, `VerifierCrossing.lean`. `SATLowerBound` is not proved.
- **Status:** All three PR #40 checks passed. Classical `P ≠ NP` remains open; amended manuscript inventory: 73 Exact, 2 Restricted, 8 Refuted, 8 Open (historical 70 Exact / 11 Refuted retained).

## Outstanding mathematics

The universal lower-bound claim, physical curvature-to-discrete resource equivalence, and any physical or classical `P` versus `NP` separation remain open proof obligations. See each manuscript's scope notes.

## Lean verification

[Lean overview](lean/README.md) · [Part I](lean/PVNP/PartI.lean) · [Part II](lean/PVNP/PartII.lean) · [Part III](lean/PVNP/PartIII.lean) · [Scope ledger](lean/formalization.yaml).

## Curvature-barrier test

[Polynomial-curvature witness encoding theorem and limitations](pvnp/proofs/curvature-barrier-audit.md) · [Lean discrete proof](lean/PVNP/CurvatureBarrier.lean).

## Four lower-bound tests (2026-10-27)

[Communication, proof complexity, routing, and PDE-metastability audit](pvnp/proofs/four-lower-bound-tests.md) · [Lean modules](lean/README.md).

## Physical communication resource bridge

[Counterexamples, sharp fixed-boundary lower bound, and Lean-verified discrete cut-communication transfer](pvnp/proofs/curvature-communication-bridge.md) · [Lean module](lean/PVNP/CurvatureCommunication.lean).

## Actual WCT PDE finite-time readout bridge

[Hamiltonian and gradient-flow transport estimates, source provenance, and limitations](pvnp/proofs/wct-pde-transport-bound.md) · [Lean algebraic formalization](lean/PVNP/HamiltonianTransport.lean).

## Phase-sensitive WCT observability

[Mean-zero coherent detector finite-time curvature bound, nodal counterexample, and full scope](pvnp/proofs/phase-sensitive-observability.md) · [Lean algebraic module](lean/PVNP/PhaseObservability.lean).

## Independent auxiliary mathematics (not the original proof)

[Fixed-mass nodal coercivity supplement](pvnp/preprints/supplement-fixed-mass-nodal-coercivity/README.md) · [LaTeX](pvnp/papers/supplement-fixed-mass-nodal-coercivity/main.tex) · [Lean finite proof](lean/PVNP/FixedMassNodal.lean).

The supplement is kept outside Parts I–III and does not modify any original-proof claim.

## Full proof completion and scaling falsifier

[Full PVNP end-to-end proof completion charter](pvnp/PROOF_COMPLETION_CHARTER.md) · [Exact expanding-domain Hamiltonian countermodel](pvnp/proofs/expanding-domain-hamiltonian-mode.md) · [Lean algebra](lean/PVNP/ExpandingDomain.lean) · [Executable checks](pvnp/tests/check_expanding_mode.py).

## Split 3-CNF distributed communication and robust channel

[Indexed 3-CNF reduction, all-protocol finite-alphabet cut bound, noise-aware packing and scope](pvnp/proofs/split-3sat-reliable-channel.md) · [Lean semantics and transcript theorem](lean/PVNP/SplitSATCapacity.lean) · [Exhaustive checks](pvnp/tests/test_split_three_sat.py).

[Finite-band robust WCT readout: conserved mass, spectral dimension and noise packing](pvnp/proofs/bandlimited-noisy-wave-packing.md) — separate analytic resource theorem, not a universal SAT lower bound.
