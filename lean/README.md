# PVNP Lean verification — extended formalization

**Scope:** Exact finite Boolean semantics, deterministic local WCC dynamics, and finite Boolean-hypercube inequalities. This is a mechanized **consistent mathematical core**, not proof of the complete manuscripts or of P ≠ NP.

Run `cd lean && lake update && lake exe cache get && lake build`. CI rejects `sorry`, `admit`, and custom `axiom` declarations in the PVNP modules.

| Part | Files | Formally targeted |
|---|---|---|
| I | [Core](PVNP/PartI.lean), [Extended](PVNP/PartIExtended.lean) | Signed Boolean literals, arbitrary finite CNF satisfaction, equivalent zero-penalty encoding, unsatisfiable opposite unit clauses, conditional class separation |
| II | [Core](PVNP/PartII.lean), [Extended](PVNP/PartIIExtended.lean) | Finite deterministic replay, radius-one local WCC machine with fixed rule and boundary state, locality, quantization step/trajectory compatibility under commuting semantics |
| III | [Core](PVNP/PartIII.lean), [Extended](PVNP/PartIIIExtended.lean) | Zero symbolic Laplacian of distinct states, denominator counterexample, positive squared regularizer, witnesses, finite hypercube directional boundary counts and normalized influence ≤ n |

**Open/unformalized obligations:** Uniform polynomial-time Turing equivalence with encoded runtime and machines; quantum field PDE existence, Sobolev estimates and stability; exact physical curvature-energy bounds; exponential locked-expander lower bounds against *all* algorithms; physically admissible NP witness existence; classical and physical P vs NP. These cannot be marked verified without valid theorems and missing hypotheses. No custom axioms stand in for those statements.

[Detailed proof status](formalization.yaml).

### New curvature-barrier test
[CurvatureBarrier.lean](PVNP/CurvatureBarrier.lean) establishes explicit polynomial *state-encoding* upper bounds on bounded-degree graph Laplacians. These bounds do not prove a solver for SAT. See [analytic note](../pvnp/proofs/curvature-barrier-audit.md).

## Four lower-bound attempts
[Communication](PVNP/Communication.lean) · [Tseitin parity](PVNP/Tseitin.lean) · [Layout and escape time](PVNP/PhysicalBounds.lean) · [Mathematical interpretation](../pvnp/proofs/four-lower-bound-tests.md). These prove restricted inequalities, not unrestricted physical P versus NP.

## Physical communication bridge test
[CurvatureCommunication.lean](PVNP/CurvatureCommunication.lean) formalizes both an affine zero-curvature counterexample and a direct linear bound for a concrete fixed-boundary, paid-slot physical implementation of an exact deterministic DISJ protocol. See the [analytical note](../pvnp/proofs/curvature-communication-bridge.md) for a causal slow-wave counterexample and the sharp 1D Dirichlet inequality. These do not establish a universal WCT curvature cost per bit.

## Actual-PDE readout cost attempt
[HamiltonianTransport.lean](PVNP/HamiltonianTransport.lean) checks cubic–quintic coercivity and algebraic finite-time curvature-tradeoff implications. The [analytical note](../pvnp/proofs/wct-pde-transport-bound.md) derives the conditional localized-mass current bound from the maintained projection-free Hamiltonian PDE and separately treats the real Swift–Hohenberg gradient flow. Continuum PDE conservation, flux integration and Sobolev embedding remain outside this Lean module.

## Phase-sensitive coherent observability
[PhaseObservability.lean](PVNP/PhaseObservability.lean) contains kernel-checkable algebra and explicit no-go identities for global phase and nodal weights. The [analytic note](../pvnp/proofs/phase-sensitive-observability.md) derives a 1/T finite-time mean-zero detector cost from the maintained projection-free PDE and a node-dependent noncoercivity counterexample. The continuum Fourier/PDE calculus is not yet Lean formalized.

## Independent fixed-mass nodal-coercivity supplement
[FixedMassNodal.lean](PVNP/FixedMassNodal.lean) formalizes the node-tolerant fixed-mass curvature inequality on a connected two-site graph and an abstract readout-cost transfer. The [standalone LaTeX supplement](../pvnp/papers/supplement-fixed-mass-nodal-coercivity/main.tex) proves the continuum compactness theorem analytically, not in Lean. It is separate from all versions of the original P-versus-NP proof.

## Expanding-domain test
[ExpandingDomain.lean](PVNP/ExpandingDomain.lean) formalizes the vanishing density-curvature coefficient for growing volume with fixed mass and a representative bounded Hamiltonian energy expression. The [analytic exact PDE mode](../pvnp/proofs/expanding-domain-hamiltonian-mode.md) demonstrates that conservation rails do not automatically supply input-size-uniform curvature coefficients.

## Actual split 3-CNF and finite-alphabet capacity
[SplitSATCapacity.lean](PVNP/SplitSATCapacity.lean) verifies the complete indexed tripled-literal SAT reduction to DISJ and the all-protocol deterministic bounded-alphabet transcript bound 2^n ≤ q^m (binary m ≥ n), conditional on rectangle/correctness properties. The [robust-noise physical packing analysis](../pvnp/proofs/split-3sat-reliable-channel.md) is conventional mathematics and is not Lean certified as a WCT PDE channel result.

## Issues #10 and #11: October 27, 2026 checkpoint

**LocalityLowerBound.lean** establishes an unconditional *linear* latency obstruction against
**all** radius-one local rules on a direct finite tape with fixed left-end
readout: the bit at distance `t+1` cannot influence cell zero in `t`
rounds. This is not a universal computational or curvature lower bound.
The theorem intentionally does not apply to nonlocal decoders or
encodings that move the input information to the output site.

**TMCellCompiler.lean** provides the explicit arbitrary transition-table
to radius-one head-marker rule and basic one-cell correspondence lemmas.
The globally valid single-head simulation, boundary treatment, and
uniform binary code for descriptions remain open.

**ReplayCost.lean** produces a serialized exact finite stencil sweep and
proves a cubic *unit-cost interpreter budget* in
`n+|w|+|description|+cells+rounds`. The definition charges list access and
table lookup; the proof does **not** yet provide an instruction-by-instruction
ordinary Turing-machine simulation. The complete bidirectional polynomial
equivalence and P/NP class equalities are therefore **not Lean verified**.

See [the exact proof and obstruction ledger](../pvnp/proofs/issue-10-11-formal-audit.md).

### Further source extensions under PR #14

[RadiusCausality.lean](PVNP/RadiusCausality.lean) expresses the general
radius `r` information cone: after `t` rounds, a prefix of `m` output
cells can depend only on the first `t*r+m` initial cells. This extends to
*any* decoder of that finite prefix, and yields a direct-input last-bit
impossibility for `n=t*r+m+1`. A nonlocal encoding that copies the far
bit to the first cell is an explicit counterexample to applying the bound
when input processing is uncharged. These theorems concern symbolic
finite-state locality, not continuous phase or curvature physics.

[TMGlobal.lean](PVNP/TMGlobal.lean) introduces a distinct Turing configuration
(tape/head/control) and a canonical marked WCC encoding. The per-cell
compiled TM tape-write agreement is a global update theorem, but
complete head-movement preservation and all-step simulation are still open.

### Finite machine descriptions and stationary-head complete traces

[MachineCode.lean](PVNP/MachineCode.lean) and
[FiniteWCCCode.lean](PVNP/FiniteWCCCode.lean) provide injective binary
table representations for arbitrary **finite** TM instruction tables
and finite-alphabet radius-one WCC rules, with explicit polynomial
bit counts. The generic old `RadiusOneMachine State` does **not**
restrict `State` to a finite effective alphabet; that older type is
too broad to claim polynomial-time Turing simulation without a
finitely described rule.

[TMStayTrace.lean](PVNP/TMStayTrace.lean) proves actual all-time
compiled WCC trajectory correspondence for the **stationary-head**
finite TM subclass. This result is intentionally restricted: it does
not solve moving-head simulation, boundary handling, machine-code
parsing, actual TM instruction costs, or the general P/NP theorems.

The working definition of done for #11 is still **OPEN**.

## October 28, 2026 verification checkpoint — Issues #10/#11

**Verified expanded baseline:** [Lean CI at commit `9077a840`](https://github.com/rickyjreyes/PVNP/actions/runs/40701665817) passed the complete import tree and all targeted #10/#11 files. This includes the radius-r causal cone, finite-local two-stage preprocessing propagation, machine-code bit-grid representation, and the stationary-head full trace.

**Further #10 source:** `RadiusCausality.no_prefix_decoder_last_bit_general` handles arbitrary tape lengths whenever `t*r + m < n`. `two_stage_prefix` and `two_stage_prefix_decoder_equal` charge separate encoder and compute stages, with causal reach `e*r_e + t*r_c`. `no_two_stage_prefix_last_bit` upgrades that to an all-input impossibility when `e*r_e + t*r_c + m < n`. The final corollary was added after the confirmed green baseline; inspect CI of the precise current head before calling it verified. This does not bound the Turing runtime of arbitrary nonlocal input encoders or continuum phase detectors.

**Further #11 source:** `TMCellCompiler` now checks both moving-head arrival directions and the no-spontaneous-head rule. `TMHeadMotion` targets the original-head vacating and destination-arrival obligations for left/right/stay moves on explicitly interior bounded tapes. These are one-step theorems, not full arbitrary-head trajectory correspondence.

**Outstanding completion gate:** Model a complete safe moving-head TM trace and prove global one-head preservation; serialize/parse finite TM and WCC rule descriptions with runtime bounds; construct a genuine ordinary TM interpreter (with instruction-count proof) for WCC, including input, witness, description, workspace, and round costs; derive uniform P and NP equivalence for the exact finite model. Until then, #11 remains open. A symbolic WCC result is not a curvature-resource theorem.


### New head-support proof target

[TMHeadSupport.lean](PVNP/TMHeadSupport.lean) formalizes the negative
side of the moving-head invariant: outside the previous head's
radius-one three-cell neighborhood, **no head marker can be created**
by a compiled step, regardless of the transition table. The premise is
the canonical one-head TM encoding already defined in `TMGlobal`.
This is not the uniqueness theorem: for a completely general
configuration, whether a marker appears at one of the three candidate
sites still depends on the transition direction. Complete moving-head
traces and P/NP class equality remain open. Verify the file by
current-head Lean CI before describing it as kernel checked.

## ASTRA completion checkpoint — 2 November 2026 (issues #10, #11, #12, #15)

Full report: [`pvnp/proofs/astra-completion-report.md`](../pvnp/proofs/astra-completion-report.md). Frozen physical model: [`pvnp/proofs/physical-model-freeze.md`](../pvnp/proofs/physical-model-freeze.md). Axiom audit: [`audit/AxiomAudit.lean`](audit/AxiomAudit.lean) (CI fails on any axiom beyond `propext`, `Classical.choice`, `Quot.sound`).

**#11 — PROVED for the frozen discrete model.** `DiscreteMachines` defines an ordinary finite single-tape TM and a finite quiescent radius-one WCC on `ℤ`, a shared first-answer decision semantics, and `P_TM`, `P_WCC`, `NP_TM`, `NP_WCC` with explicit polynomial time and witness bounds. `TMtoWCC` proves exact real-time simulation for every transition case; `WCCtoTM` builds an explicit alternating shifted-sweep TM with time `1 + (T+1)(n+2T+5)`; `ComplexityEquivalence` derives `P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM` and `p_vs_np_discrete_transfer`. `MachineSerialization` gives a flat binary machine code with verified round trip, canonical rejection, injectivity and size bound, and normalizes every TM to a serializable table. Not formalized: radius-`r`/`d`-dimensional lattices, non-local poly-time encoders, a universal TM.

**#15 — PROVED.** `BandlimitedNoisyPacking` (Haar-volume packing; `N ≤ (1+√M/η)^{2D}`; projected-subspace version; capacity and mass corollaries), `FourierReceiverProjection` (mode count; WCT nonlinearity leaves finite support), `DecisionVsEncodingCounterexample` (storage bound is not a decision bound).

**#10 — PARTIAL.** `DiscreteCurvatureRail` proves discrete curvature is polynomially bounded for every embedding, `P_curvRail = P_TM`, and that a discrete curvature lower bound for an NP language would prove `P_TM ≠ NP_TM`. The universal physical lower bound remains OPEN (missing implications M1–M3 in the freeze document).

**#12 — PARTIAL (gate met).** `PartIIIAnalytic` (Lebesgue-integral curvature bound, Laplacian zero-cost counterexample, high-frequency counterexample with real derivatives/integrals) and `PhysicalComplexityClasses` (time invariant / curvature not invariant under representation change, telescoping and interface conditionals, exact boundary identity, parity, vacuous variation class, class logic, well-posedness).

No classical `P ≠ NP`, physical class separation, or universal SAT lower bound is claimed.
