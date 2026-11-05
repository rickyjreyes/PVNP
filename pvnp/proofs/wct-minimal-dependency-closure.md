# WCT-dependent P-vs-NP route: exact minimum proof obligations

**Status:** Conditional mathematical bridge only. Updated November 5, 2026.
**Source:** Part I `lem:separator-price`, `prop:locked-expander-full`, `lem:lower`; Part III resource audit.
**Lean:** `lean/PVNP/WCTDependencyClosure.lean`.

## What is already proved

1. The discrete model equals ordinary TM computation: `P_WCCD_eq_P_TM`,
   `NP_WCCD_eq_NP_TM` (any fixed finite dimension, with the model-specific
   encoding convention).
2. `SAT_dense_mem_NP_TM` and an exact Boolean witness verifier.
3. The full conditional all-decider implication from a **charged interface
   lower bound** to `PhysSemantics.Hard SAT_dense`:
   `WCTDependencyClosure.interface_growth_implies_hardness`.
4. From just **one direction** `P_TM ⊆ S.Pphys` and a universal physical
   SAT barrier, infer `P_TM ≠ NP_TM`:
   `WCTDependencyClosure.physical_hardness_plus_TM_realization`.
   Neither the converse `S.Pphys ⊆ P_TM` nor a claim about physical
   NP classes is logically needed for this particular implication.
5. `WCTDependencyClosure.full_interface_route` composes all hypotheses,
   and `no_route_under_classical_collapse` verifies the incompatibility
   of those hypotheses with `P_TM = NP_TM`.
6. `indicator_physical_barrier_iff_TM` proves that the existing exact
   constant-amplitude PDE subclass with charged polynomial-time indicator
   encoders excludes SAT **iff classical SAT is outside P_TM**.
   That example does not establish physical computation in the evolution.

## The *actual* WCT-specific statements that remain unproved

The five WCT foundational postulates are not a substitute for the following
mathematical claims. All quantifiers below must refer to one fixed admissible
physical device class `S`, with charged input encoder, evolution, measurement,
precision, detector, decoder, and uniform resource rails.

**H1. Physical realization (one way suffices).**

  `P_TM ⊆ S.Pphys`

For every classical polynomial-time language, construct a uniform WCT
implementation within polynomially bounded resources. An encoder that solves
the language before initializing a constant field gives a valid inclusion for
an encoder-charged class, but is **not** a demonstration of WCT evolution
performing the computation. A stronger hardware-computational implementation
would require an independent uniform construction.

**H2. Uniform interface price.**

For one **fixed** charged resource rail `r`, a nonzero coefficient `κ`
and all admissible deciders `D` and inputs `x`:

  `κ * area(D,x) ≤ S.cost D r x`.

This must be derived from the actual PDE/energy/trajectory and robust
measurement definitions, with no hidden restrictions on allowable
representations or solvers. The existing `conditional_product_lower_bound`
only assumes it, and changing a field representation can change curvature
without changing computation.

**H3. Algorithm-independent interface growth.**

For **every** correct SAT decider `D` and **every threshold** `N`, at least
one input `x` of length `n ≥ N` must satisfy

  `B(n) ≤ area(D,x)`.

This requires arbitrarily large hard lengths, not necessarily every length.

This includes algebraic shortcuts, globally organized updates, phase-based
channels, and encodings not forced to traverse an enumerated witness list.
Existing WCT/PVNP expansions and mode-packing theorems do **not** prove H3.
In particular, an expander with O(n) edges does not force exponential
interface area for arbitrary implementations.

**H4. Superpolynomial geometric growth.**

The proposed `κ B(n)` must eventually dominate **every** polynomial
resource bound, with uniform constants independent of the algorithm.
The typical candidate is `B(n) = c 2^(γ n)` for positive constants; the
mathematical exponential-versus-polynomial dominance itself is standard.
The hard step is establishing H3 with such a `B`, not the asymptotic
comparison.

The new Lean theorem verifies **H1 + H2 + H3 + H4 implies P ≠ NP**, with the
quantifier order explicit. It does not assert H1-H4.

## What testing WCT in the physical world can and cannot establish

Experiments could test the selected evolution equation, curvature-feedback
law, confinement stability, detector dynamics, and positive interface costs
on particular fabricated device families and bounded input sizes. Those
tests cannot establish the H3 universal assertion for all algorithms or
all input lengths, nor prove H1 as a theorem about every polynomial-time TM.

WCT mass emergence, Koide geometry, and the 3-D Sobolev threshold are not
necessary to this minimum computational route. The foundations most relevant
to H2/H3 are the curvature-feedback and curvature-regulated stability
postulates, but those postulates alone do **not** imply universal SAT hardness.

## Why this is not yet full closure

The new formalization composes existing certified definitions and proves
the logical bridge, with no custom axioms. It is **not** an unconditional
proof of classical P ≠ NP or of a physical WCT separation. H3 is presently
the central open and potentially false premise, while H1 and H2 need
model-specific verification.

The next work must either derive H3 from the selected WCT dynamics for
*every* admissible SAT algorithm, or exhibit a valid counterexample
satisfying the stated H1/H2/resource hypotheses. Formalizing an
unconditional implication from an unproved H3 would not constitute closure.
