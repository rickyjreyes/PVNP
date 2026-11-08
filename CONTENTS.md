# PVNP publication and source map

**Repository:** [rickyjreyes/PVNP](https://github.com/rickyjreyes/PVNP)  
**Author:** Richard J. Reyes

## Current primary release: consolidated technical volume

**[Wave-Constrained Computation: Formal Equivalence, Physical Resource Bounds, and the P versus NP Problem](pvnp/preprints/consolidated-wave-computation/README.md)**

The [single consolidated PDF](pvnp/preprints/consolidated-wave-computation/paper.pdf) binds the three revised studies and the independent fixed-mass nodal supplement with one new scope and provenance introduction. The authoritative master is [consolidated LaTeX](pvnp/papers/consolidated-wave-computation/main.tex).

The three original works retain their own historical release dates, DOIs, LaTeX source, and technical qualifications. This compilation does not create three newly dated papers. A PDF link is usable only once its build has succeeded; the known [CI runner blocker](https://github.com/rickyjreyes/PVNP/issues/59) can prevent the release build.

## Publication identifiers and archival sources

| Part | Original manuscript | Published record | Original LaTeX |
|---|---|---|---|
| I | Curvature-bounded wave computation (May 7, 2025) | [Zenodo DOI 10.5281/zenodo.17743607](https://doi.org/10.5281/zenodo.17743607) | [Part I source](pvnp/papers/part-i-curvature-bounded-wave-computation/main.tex) |
| II | Discrete WCC / Turing equivalence (November 26, 2025) | [Zenodo DOI 10.5281/zenodo.17732642](https://doi.org/10.5281/zenodo.17732642) | [Part II source](pvnp/papers/part-ii-discrete-wcc-turing-equivalence/main.tex) |
| III | Physical complexity reassessment (December 1, 2025) | [Zenodo DOI 10.5281/zenodo.17783074](https://doi.org/10.5281/zenodo.17783074) | [Part III source](pvnp/papers/part-iii-physical-complexity-reassessment/main.tex) |
| Appendix | Independent fixed-mass nodal coercivity (October 2026) | Separate auxiliary note | [Supplement source](pvnp/papers/supplement-fixed-mass-nodal-coercivity/main.tex) |

The original repository PDFs were generated from revised LaTeX, not necessarily identical to the original Zenodo uploads. They are archived compilation assets, and the build now outputs one primary PDF. Git history preserves original versions.

[**7 November 2026 source-to-Lean release audit**](pvnp/proofs/pdf-lean-reconciliation-20261107.md): original claim corrections, exact scope of physical and discrete proofs, PDF rebuild status, and verification requirements.

## Formalization boundary

The amended 91-claim inventory currently records **78 Exact, 2 Restricted, 4 Refuted, 7 Open**. An Exact conditional implication does not prove its unverified premises. Neither classical P versus NP nor physical WCC separation is proved. Recent Phase XII/XIII integration awaits full kernel CI, and a PDF build cannot replace Lean verification.

## Verified Phase VI and Phase VIII results (November 2026)

- **Phase VI:** [Periodic-torus H² well-posedness and F-1 continuum flux](pvnp/proofs/phase-vi-torus-flux-status.md), in `TorusWellPosed.lean` and `TorusFlux.lean`; [merged PR #40](https://github.com/rickyjreyes/PVNP/pull/40).
- **Phase VIII:** [Full crossing-sequence splicing and single-tape SAT lower bounds](pvnp/proofs/phase-viii-separation-status.md), in `CrossingHennie.lean`, `CrossingSAT.lean`, `CrossingSATSets.lean`; [merged PR #38](https://github.com/rickyjreyes/PVNP/pull/38).
- **Phase IX:** [Exact target, invariant tests and no-go theorems](pvnp/proofs/phase-ix-universal-lower-bound-status.md), in `SATTarget.lean`, `TseitinSAT.lean`, `VerifierCrossing.lean`. `SATLowerBound` is not proved.
- **Status:** All three PR #40 checks passed. Classical `P ≠ NP` remains open; amended manuscript inventory: 78 Exact, 2 Restricted, 4 Refuted, 7 Open (historical 70 Exact / 11 Refuted and intermediate 73 Exact / 8 Refuted retained). I-10 is conditional on observable mixing; I-13 uses quiescent finite-support growth; I-12 is a charged-encoder conditional counterargument; I-20 separates explicit-state description length from a succinct certificate.

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
