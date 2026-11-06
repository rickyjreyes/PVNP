# PVNP — full proof-completion charter and falsifiability ledger

**Mission:** Pursue the *entire* Wave Curvature Computation / P-versus-NP research program. Preserve and audit the original proofs, complete the distinct discrete, physical, and classical bridges wherever mathematics permits, formalize genuine claims in Lean, and publish explicit counterexamples or precisely delimited obstructions whenever a proposed theorem fails.

**Do not redefine success as merely passing CI.** A conditional theorem, finite model experiment, or Lean proof of an assumed premise is not a proof of the premise itself. A restricted WCC separation is not automatically classical P ≠ NP. This document records the intended final goal while accurately tracking the current mathematical status.

## Deliverable families and completion conditions

| ID | Deliverable | Current condition | Completion gate |
|---|---|---|---|
| O1 | Preserve original May/November/December 2025 versions, prior citations and historical proof claims | Revised trilogy and historical DOI references indexed | Maintain original-vs-revised claim ledger with precise source anchors; never retroactively rewrite historic publication claims |
| O2 | Complete signed SAT encoding and polynomial NP verification | Finite Boolean/Lambda core and logical zero-penalty theorem; Lean support | Specify one uniform instance/witness language, prove yes/no semantics and polynomial verification including physical admissibility |
| O3 | Fully formal discrete WCC ⇄ deterministic TM simulations and verifier equivalence | Analytic uniform finite-state simulation; Lean supporting local rules | Lean actual universal machine configuration, encoded runtime/space, two-way simulation, and NP witness quantifiers |
| O4 | Derive selected physical WCC evolution from declared action or freeze independent PDE | Several *distinct* maintained PDE models, no claimed parent-action identity | Fix one action, state space, boundary conditions, evolution/solution concept, and prove existence/conservation/physical well-posedness as required |
| O5 | Curvature, phase, nodes, finite-time readout resource inequalities | Model-relative transport and fixed-domain nodal coercivity; algebraic Lean modules | Full PDE/functional analytical proof and formalization, including noise thresholds and causal detector |
| O6 | Input-length uniform resource accounting and adversarial channel tests | **OPEN**: expanding-domain exact nonlinear plane-wave countermodel shows uniform cost is not automatic | Explicit uniform domain, mass/energy, detector, noise, bandwidth, spectral gap, feature width, precision, time and implementation scaling; bound any hidden resources |
| O7 | Locked-expander / hard SAT family and algorithm-independent resource hardness | **OPEN**: exponential interface premise conditional; polynomial per-state curvature countermodels exist | Prove lower bound against **every** admissible correct decider, not just fixed paths, resolution, enumeration, gradient flow, or particular encodings; handle algebraic bypasses |
| O8 | A common physically verifiable language outside the physically feasible deterministic class | **OPEN**: conditional schema only | Show a physically admissible polynomial resource verifier + polynomial-size witnesses and independent uniform deterministic separation for exactly the same language |
| O9 | Classical P/NP claim via exact class equivalence or wholly classical lower bound | **OPEN**: symbolic simulation does not preserve physical costs | Prove a classical universal SAT lower bound or both resource-faithful class identifications for one identical language universe; no circular assumption of P ≠ NP |
| O10 | Complete formal proof & reproducibility program | Lean supports multiple separate restricted lemmas; continuum formalization incomplete | Every principal theorem typechecks with stated assumptions, no sorry/custom axioms, PDF/repository agree, independent adversarial review and reproductions |

## Dependency logic

- O2 + O3 establish discrete *semantics*, not physics.
- O4 + O5 + O6 establish a well-specified **physical resource model**.
- O7 + O8 are the essential **physical P/NP separation** steps, requiring all-algorithm quantifiers. No polynomial verifier or one hard-to-generate state substitutes for them.
- O9 is an **additional** classical bridge; even a proved physical separation would leave it open unless the physical and classical models coincide under proved polynomially faithful mappings.
- O10 certifies work only to the extent its hypotheses were actually established. O1 preserves provenance through revisions.

## Mandatory adversarial bypass suite

1. Static state storage in bounded-degree graphs with polynomial curvature.
2. Smooth disjoint-bump SAT witness encodings with linear density-curvature expenditure.
3. GF(2) Gaussian elimination on Tseitin expanders; do not infer unrestricted hardness from resolution lower bounds.
4. Constant/affine zero-Laplacian channels and slowly switched traveling waves.
5. Phase-only and uniform-phase evolutions versus local mass-only detectors.
6. Nodal high-frequency degeneration without positive mass.
7. **Expanding-domain exact Hamiltonian plane waves with fixed mass, bounded Hamiltonian, fixed-time phase contrast and vanishing density curvature**.
8. Nonlocal readouts, free phase references, analog precision, time multiplexing, and hidden initialization/actuation resources.
9. Polynomial-algorithm adversaries, uniformity, and the difference between a hard target state and a hard decision language.

## Verified / conditional / refuted labels

A manuscript claim may be marked:

- **Analytically proved under named hypotheses:** standard rigorous derivation available; model, constants and quantifiers explicitly visible.
- **Lean kernel verified:** a separately identified formal statement compiles, with no sorry/admit/custom axiom. Does not expand the statement's scope.
- **Conditional:** the conclusion follows after explicitly assumed bridge hypotheses; no evidence the hypotheses have been established.
- **Refuted as stated:** a concrete counterexample for exactly the claimed assumptions exists. Preserve the counterexample and revise the claim.
- **Open:** the necessary bound, model equivalence, or universality has not been shown.

## Publication / merge gate

Do not title the repository or any PDF as having **proved P ≠ NP** unless the actual same-language unrestricted separation and all necessary reduction steps have been independently checked. Keep original historical titles with an accompanying current-scope warning. Review model/frozen parameter changes against source provenance. Merge scoped Lean/code/prose changes only after relevant CI passes.

## Immediate next research after expanding-domain obstruction

Freeze a **resource-scaled channel and computational device family** as input size \(n\) increases. Decide whether volume and detector extent are polynomially charged, and define noise margin, precision and total source work. Then search for a physically meaningful, model-wide *information-distinguishability → resource* inequality with those quantities explicit. Test the resulting inequality against the exact nonlinear mode family before transferring it to SAT. In parallel, use standard algorithmic bypasses to attack the required universal expander hardness premise.

**Final objective remains the full theorem or a definitive mathematical obstruction—not a relabeled partial result.**

## New verified direction: split-input SAT and bounded-precision cut (October 27, 2026)

The [split 3-CNF proof](proofs/split-3sat-reliable-channel.md) formalizes actual tripled 3-literal clause satisfiability and proves the all-protocol deterministic bound `2^n <= q^m` for split-input SAT under complete-transcript rectangularity and q-level/m-slot accounting. This supports O2's finite Boolean semantics and O6's bounded-alphabet resource estimates. The physical analog noise-to-q packing estimate remains a separate analytical step conditional on amplitude and adversarial error rails. **O7 and O9 are still OPEN**: this family has an O(n) centralized solver, so its private-input bottleneck does not show classical SAT hardness.

## Conserved-mass finite-band reliable-readout packing (O6)

The [sphere-packing supplement](proofs/bandlimited-noisy-wave-packing.md) proves analytically that N independently decodable noisy complex D-mode readout states at fixed conserved mass M must satisfy `N <= (1+sqrt(M)/eta)^(2D)`. This is a universal bound over that specified codebook class, **not** an all-algorithm SAT bound, because an SAT decider need not separately decode all assignments. It is currently outside Lean and does not establish the link between an actual PDE trajectory and a distributed communication transcript.

## ASTRA status update (2 November 2026)

This dated update supplements, and does not rewrite, the table above. Details and exact Lean names: [ASTRA completion report](proofs/astra-completion-report.md); frozen physical model and resource-by-resource status: [physical-model-freeze.md](proofs/physical-model-freeze.md).

- **O3 — complete for the frozen discrete model.** Kernel-checked `P_WCC = P_TM` and `NP_WCC = NP_TM` from explicit simulations in both directions (`PVNP.Discrete.P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM`), plus flat machine serialization.
- **O5 / O6 — partial.** The bandlimited packing theorem above is now Lean-verified (`PVNP.Packing.complex_receiver_packing`, `subspace_receiver_packing`); `C_Θ ≤ ‖Δψ‖²/(4ε²)` is proved as a Lebesgue-integral inequality; energy→curvature, distinguishability→curvature and bandwidth preservation are refuted in Lean.
- **O7 / O9 — new obstruction theorems.** `p_vs_np_discrete_transfer` and `curvature_lower_bound_is_classical`: within the discrete model, any time or curvature lower bound for an NP language *is* a classical P ≠ NP proof, and polynomial curvature rails add nothing (`P_TM_eq_curvature_rail`). The physical universal lower bound remains **OPEN** (missing implications M1–M3).
- **O8 — OPEN.** **O10 — advanced** (36-declaration axiom audit enforced in CI; Python cross-checks).
- **Second tranche (same day).** `P_TM ⊆ NP_TM` and `P_WCC ⊆ NP_WCC` unconditionally (`PSubsetNP`); genuine `L²`-torus Fourier receiver packing (`FourierTorusReceiver`); sharp circle spectral gap and the impossibility of a domain-uniform Poincaré constant (`CircleSpectralGap`); exact classical solutions of the frozen WCT PDE realizing the expanding-domain countermodel (`WCTPlaneWave`). O2 still lacks a Lean CNF-evaluating TM (`SAT ∈ NP_TM`).
- **O2 (same day).** CNF-SAT under the dense encoding is in `NP_TM` and `NP_WCC` with an explicit, kernel-checked verifier machine (`SATVerifier`: `satTM_decides`, `SAT_dense_mem_NP_TM`, `encDense_mem_SAT_iff`); Part III's `L_check ∈ P` is proved (`V_SAT_mem_P_TM`). Cook–Levin NP-completeness is not formalized.

## Verified integration update (6 November 2026)

**O4 and the torus-specific part of O5:** Phase VI PR [#40](https://github.com/rickyjreyes/PVNP/pull/40) integrated global H² well-posedness and the PDE-derived localized-mass flux inequality in Lean on the periodic torus, with explicit `L > 0`, `γ > 0`, solution and detector hypotheses. This does **not** close O6's resource scaling for every input family, O7's universal computational hardness or M3-C lattice-to-continuum convergence. [Phase VI theorem ledger](proofs/phase-vi-torus-flux-status.md).

**O7 and O9:** Phase VIII PR [#38](https://github.com/rickyjreyes/PVNP/pull/38) proves full single-tape crossing-sequence splicing and a near-quadratic time lower bound for `SAT_dense`. It does not exclude all polynomial-time SAT deciders and does not establish `P ≠ NP`. The missing statement is `CrossingSAT.SATLowerBound`. [Phase VIII status](proofs/phase-viii-separation-status.md).

**O7, Phase IX:** the per-input target is proved equivalent to `SATLowerBound` and to
`conj:wcc_depth` for `SAT_dense` (`SATTarget`).
- Two candidate invariants fail, with kernel-checked counterexamples:
  - expander/Tseitin instances (`TseitinSAT`, component parity);
  - crossing information (`VerifierCrossing`, `V_SAT ∈ P_TM`).
- `SATLowerBound` is not proved. [Phase IX status](proofs/phase-ix-universal-lower-bound-status.md).

**O7, Phase X:**
- `P_TM ⊆ P/poly` (`TMCircuit.P_TM_subset_Ppoly`).
- Non-uniform Cook–Levin for `SAT_dense` (`CircuitCookLevin.SAT_dense_mem_Ppoly_iff`).
- So a superpolynomial circuit lower bound for any NP language would prove `SATLowerBound`
  (`satLowerBound_of_NP_not_Ppoly`). That lower bound is open.
- [Phase X status](proofs/phase-x-circuit-route-status.md).

**O10:** All three exact-head PR #40 checks passed (`lean`, `phase-iii-targeted`, PDF `build`). The standard-axiom audit is part of the full Lean job. Manually dated status entries above should be read as historical checkpoints; [the formalization ledger](../lean/formalization.yaml) remains authoritative. The manuscript inventory remains 70 Exact, 2 Restricted, 11 Refuted, 8 Open.
