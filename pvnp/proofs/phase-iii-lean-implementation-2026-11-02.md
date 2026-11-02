# PVNP Phase III Lean implementation ledger, 2 November 2026

This is an **incremental proof implementation**, not completion of the full
Phase III research program. The original historical Parts I–III, public DOI
records and website metadata were not modified in this branch. Part IV has not
been drafted or published.

## Verified code on the branch

Pinned toolchain: Lean 4.23.0 / repository-pinned Mathlib.

Targeted CI: [run 41540246765](https://github.com/rickyjreyes/PVNP/actions/runs/41540246765)
at code commit `518da92dc70b284383b71c4dd4615b505a77ae7a`: **success**.
All three modules individually built through the kernel. The targeted
workflow also rejected `sorry`, `admit`, and custom `axiom` declarations.
The full-project build and 123-declaration axiom audit require their
separate GitHub Actions run on the current PR head.

| Obligation | New code | Actually proved | Remains open |
|---|---|---|---|
| D-1 | `lean/PVNP/WCCDFiniteSupport.lean` | `InCone`, `off_bounds`, `init_blank_outside`, `run_blank_outside`, `run_blank_left`, `run_blank_right`, `run_blank_transverse`: finite rectangular causal support for the exact Moore-neighborhood WCCD model | Explicit finite-support encoding, polynomial single-tape simulator, converse `P_WCCD d ⊆ P_TM`, NP equivalence |
| M3-G | `lean/PVNP/WCTLatticeGlobalBounds.lean` | `coordinate_norm_sq_le_mass`, `coordinate_norm_le_sqrt_mass`, `solution_uniform_coordinate_bound`, `exists_local_solution_bounded` | Global extension and uniqueness from the local Picard–Lindelöf solutions |
| M3-C | `lean/PVNP/WCTMeshScaling.lean` | `mesh_flux_prefactor`: `4|h⁻²|h = 4/h` for positive h; `mesh_flux_prefactor_unit`: the same prefactor is `4n` for `h=1/n` | Consistency, stability, reconstruction, error constants, continuum convergence, and a potentially sharper mesh-uniform transport estimate |
| F-1 | No new proof | Existing lattice flux equality and inequality remain in `WCTLattice.lean` | Continuum flux derivation in Lean |
| M3-T | No new proof | Existing external whole-plane theory remains in `rickyjreyes/math` | Global torus well-posedness in Lean |

## Interpretation of the M3-C scaling result

The prefactor `4|a|ω` is an intermediate factor in the *existing* lattice
commutator estimate. For `a = h⁻²` and detector weight differences bounded
by `ω = h`, that factor is `4/h`. This algebraic observation does **not**
show that the total best constant must diverge: other factors and norms may
depend on h, and a sharper commutator estimate might retain cancellations.
It does, however, prohibit silently claiming a mesh-uniform conclusion from
the current estimate without tracking those dependencies.

## Publication scope and next proofs

A fourth paper should distinguish these successful restricted theorems
from D-1, M3-G, M3-C, F-1 and M3-T full obligations. M1 certified physical
simulation and M2 universal physical lower bounds remain open, as does
classical P versus NP. The existing formalization ledger remains the
authoritative register of theorems and their exact scopes.

No original papers, public metadata, research issues or PRs were modified
outside this implementation branch. No PR was merged or issue closed.
