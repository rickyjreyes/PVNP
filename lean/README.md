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
