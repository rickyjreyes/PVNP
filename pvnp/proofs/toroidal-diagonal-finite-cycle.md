# Toroidal diagonalization experiment: finite cyclic Boolean consistency

**Scope:** A discrete and genuinely periodic (cyclic) feedback test. This is **not** a SAT time lower bound, a universal self-reference theorem, or a claim of P != NP.

## Construction

For each `n ≥ 0`, introduce Boolean wires `b₀,…,bₙ`. Impose `bᵢ₊₁=bᵢ` for every `i<n`, then close the loop either with `bₙ=b₀` (even seam) or `bₙ≠b₀` (one negation, odd seam).

The construction is a finite ring with a twisted or untwisted Boolean seam. No infinite precision, continuous torus dynamics, or arbitrary computational oracle is assumed.

The CNF encoding uses two binary clauses per ordinary equality edge and two binary clauses for the closing seam. It is encoded by the existing `SATV.encDense` into `SAT_dense`, with `n+1` Boolean variables.

The exact finite consequences are:

- **Even seam:** the constant-zero assignment satisfies the loop.
- **Odd seam:** the chain implies `bₙ=b₀`, which contradicts `bₙ≠b₀`. No assignment satisfies the loop.
- **Size:** the formula has exactly `2n+2` clauses, and its dense binary encoding has length `3(n+1)(2n+2)`, quadratic in `n`.
- **Language level:** the family itself is easily decided by looking at the closing-seam bit. The odd loop is an unsatisfiable SAT input, not a hard SAT input.

## Lean artifact

`lean/PVNP/ToroidalDiagonal.lean` defines:

- `edgeFormula`, `seamFormula`, `ringFormula`, `encRing`
- `edge_chain_constant`, `odd_ring_no_state`, `even_ring_has_state`
- `odd_ring_unsat`, `even_ring_sat`
- `ring_bounded`, `odd_encRing_not_SAT`, `even_encRing_mem_SAT`
- `ringFormula_length`, `encRing_length`

The file is included in the `PVNP` import tree and the axiom audit. GitHub Actions must confirm the exact head before any assertion of kernel-checked completion.

## What this rules out, and what it leaves open

Putting a direct negation on the toroidal seam creates a contradiction, not an algorithm-independent decision lower bound. A loop of Boolean equalities with an even seam has a fixed point, so topology alone does not guarantee inconsistency.

The construction does *not* enumerate and defeat all polynomial-time SAT algorithms, and there is no uniformly polynomial-time self-reference reduction from arbitrary polynomial-time machine codes here. The key unsolved obstacle remains `CrossingSAT.SATLowerBound`, equivalent to excluding every polynomial-time `SAT_dense` decider.

A next experiment could replace each equality edge with a bounded-step machine transition relation and systematically test whether the resulting consistency formula tracks the machine's actual input and answer, rather than inserting an independent contradiction. That further construction must keep its size and verification overhead uniform; it must not assume the desired lower bound.
