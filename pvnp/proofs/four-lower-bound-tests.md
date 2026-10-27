# Four lower-bound attempts — verified scope and counterroutes

**Date:** October 27, 2026. These are model-relative tests, not a proof of physical or classical P ≠ NP. Prior related works: deterministic communication complexity of disjointness, resolution lower bounds for Tseitin contradictions, VLSI bisection bounds, and metastable escape-time estimates.

## Experiment A. Exact communication bottleneck

Split a formula between parties Alice and Bob, with private bit strings a,b of length n. For each i, Alice contributes the unit constraint z_i when a_i=1; Bob contributes ¬z_i when b_i=1. The joint CNF is satisfiable iff no i has a_i=b_i=1. This is DISJ_n, and padding (z_i∨z_i∨z_i) maintains 3-CNF width without affecting semantics.

Consider the 2^n yes-instances (x, ¬x). If a deterministic protocol gives the same accepting transcript to (x, ¬x) and (y, ¬y), the transcript's combinatorial rectangle also contains (x, ¬y) and (y, ¬x). Both must be disjoint; hence x=y. Every distinct x therefore has a distinct accepting transcript. Consequently there are at least 2^n transcripts. If all transcript strings have fixed length at most BT bits (and timing or round metadata conveys no additional information), then

    2^n ≤ 2^(BT), hence B*T ≥ n.

**Lean module:** `lean/PVNP/Communication.lean` formalizes the fooling-set injectivity and transcript count. The reduction's complexity lower bound is classical and is restricted to partitioned-input deterministic protocols. A centralized SAT solver can read the whole input in O(n), so this does not yield an exponential SAT bound.

## Experiment B. Expander proof complexity

For charge-labeled graph incidence equations over GF(2),
sum_v sum_e incident(v,e)*x_e = sum_e (sum_v incident(v,e))*x_e = 0,
because each edge is incident to exactly two vertices. If the total charge is odd, the equations are inconsistent. This is a short GF(2) algebraic certificate.

Standard results (e.g., exponential resolution lower bounds for Tseitin contradictions on bounded-degree expander graphs) establish an exponential cost for *resolution refutations*, not all algorithms. Gaussian elimination bypasses the restriction.

A valid transfer theorem would require a **uniform extraction map** from *every* accepted WCC refutation in a defined restricted machine class to a resolution proof of size ≤ poly(n+WCC_resource). If the corresponding resolution lower bound is 2^{αn}, then any such resource R must obey (n+R)^k ≥ 2^{αn}, hence R ≥ 2^{αn/k}−n. No such universal extraction theorem is currently proved.

**Lean module:** `lean/PVNP/Tseitin.lean` kernel-proves the GF(2) parity obstruction, not the literature's exponential resolution theorem. It also highlights a polynomial-time alternative outside resolution.

## Experiment C. 2D geometric routing

Suppose a layout uses a square of side L and area A≥L². Every balanced vertex partition needs b simultaneous distinct edge channels across the corresponding geometric cut. Suppose at most k channels per unit cut length are permitted and the cut has length at most L. Then b≤kL, and

    b² ≤ k² A.

In particular, if b≥αn with k fixed, then A≥(αn/k)². This is a conditional quadratic area bound, not exponential. It requires a planar/single-layer simultaneous routing model with no time-multiplexed reuse, no free crossings or nonlocal connectivity, a justified balanced partition, and a physical layout metric. It does not transfer automatically to unrestricted WCC continuous fields or 3D systems.

**Lean module:** `lean/PVNP/PhysicalBounds.lean` checks the algebraic area inequality given the explicit cut assumptions. Constructing a physical graph embedding theorem is still open.

## Experiment D. Curvature dynamics and metastability

For a memoryless trapped state with probability 0<p≤1 of escaping each round, mean escape time satisfies E=1+(1−p)E, hence E=1/p. Therefore if one proves p≤exp(−βΔE) and a barrier ΔE≥cn, then

    E≥exp(βcn).

The exponential conclusion depends *entirely* on a demonstrated small escape probability for the actual dynamics. The number of attractors or energy minima alone is insufficient: a global reset map sends every state to the target in one step.

**Lean module:** `lean/PVNP/PhysicalBounds.lean` checks the escape-time recurrence and conditional lower bound; no WCT PDE hitting-time theorem is claimed.

## Comparative outcome

| Approach | Proven under specified hypotheses | Not proven |
|---|---|---|
| Communication | ≥2^n deterministic transcripts for split DISJ; BT≥n when fixed BT-bit transcripts | Exponential SAT running time or curvature cost |
| Resolution | GF(2) parity contradiction; conditional resolution-proof extraction transfer | Proof extraction for all WCC solvers |
| Routing | b²≤k²A under cut/channel hypotheses | Universal WCC geometry lower bound |
| Metastability | E=1/p; E≥1/q when p≤q | Exponentially small WCT escape rate |

**Research conclusion:** The strongest immediately applicable lower bound is a linear communication-cut barrier for a restricted architecture. A conditional exponential lower bound is available for resolution-like proof systems or metastable local stochastic dynamics only after validating the respective restrictive assumptions. None of these establishes an unconditional separation of polynomial-time physical WCC P and NP, much less classical P versus NP.

### Relevant prior mathematics

- D. communication lower bound via fooling sets: https://reu.dimacs.rutgers.edu/~ac1606/communication%20complexity.pdf
- Tseitin resolution lower-bound survey: https://www.sciencedirect.com/science/article/pii/S0168007222000811
- F. T. Leighton, VLSI lower bounds: https://dspace.mit.edu/entities/publication/b0fb2340-0ac2-4f3d-9fe6-454e8a091156
