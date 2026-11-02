# Definition-match bridge to `rickyjreyes/math` (optional, not part of the `PVNP` library)

`MathBridge.lean` imports both PVNP (`PVNP.WCTPlaneWave`, `PVNP.WCTLattice`) and the external
library `rickyjreyes/math` (`MathProofs.CubicQuinticFlow`). It proves that the two code bases
use **the same equation**:

| Ingredient | PVNP definition | External definition | Bridge theorem |
|---|---|---|---|
| Nonlinearity | `-β‖z‖²z + γ‖z‖⁴z` (`WCTPlaneWave.plane_wave_solves`, `WCTLattice.nlin`) | `ReyesMath.Sobolev.fnl` | `fnl_eq_pvnp`, `fnl_eq_lattice` |
| Laplacian | `WCTPlaneWave.lap` (coordinate second derivatives on `ℝ × ℝ`) | `ReyesMath.Sobolev.lapS` (`= Δ`) | `d1_comp`, `d2_comp`, `lap_comp`, `lap_comp_mathlib` |
| `(Δ+κ)` and `(Δ+κ)²` | `WCTPlaneWave.shifted κ`, `opK κ` | `AS k`, `AS k ∘ AS k` with `κ = k²` | `shifted_comp`, `opK_comp` |
| Hamiltonian density | `WCTPlaneWave.hamDensity` | `‖AS k ψ‖² + nfun β γ ψ` (integrand of `H2.energy`) | `hamDensity_comp` |

All of these hold for every Schwartz function `ψ` on `ℝ²`, transported to `ℝ × ℝ` by the
standard linear isometry `emb (x₁, x₂) = x₁e₀ + x₂e₁`.

**What does not match.** The external well-posedness theory is set in `H²(ℝ²)`, on the whole
plane. The frozen PVNP model `WCT-Phys` uses periodic boxes and tori, whose plane-wave states
are not in `H²(ℝ²)`. Two consequences follow.

- The external theorems are reusable for the **whole-space** variant of the model.
- They do **not** settle well-posedness on the torus. That question remains obligation M3-T in
  `pvnp/proofs/remaining-obstructions.md`.

## Verification record (2026-11-02)

The external commit is `rickyjreyes/math@30a5ddc9271a107c355024a7241f13d86ec496a9`. It was built
against the same pinned toolchain and Mathlib as PVNP (Lean v4.23.0, Mathlib `37df177`). The
`MathProofs.CubicQuinticFlow` closure is 11 modules and 11,890 lines.

| Declaration | Axioms reported by `#print axioms` |
|---|---|
| `ReyesMath.Sobolev.global_wellposed` | `propext`, `Classical.choice`, `Quot.sound` |
| `ReyesMath.Sobolev.conservation` | `propext`, `Classical.choice`, `Quot.sound` |
| `ReyesMath.Sobolev.continuous_dependence` | `propext`, `Classical.choice`, `Quot.sound` |
| `ReyesMath.Sobolev.norm_toSp_sq_le` | `propext`, `Classical.choice`, `Quot.sound` |
| `ReyesMath.Sobolev.exists_global` | `propext`, `Classical.choice`, `Quot.sound` |
| `ReyesMath.Sobolev.ode_unique` | `propext`, `Classical.choice`, `Quot.sound` |
| every `PVNP.MathBridge` theorem | `propext`, `Classical.choice`, `Quot.sound` |

`norm_toSp_sq_le` is the a priori bound `‖u‖²_{H²} ≤ 3(E + 3β²M/16γ) + (2 + 3k⁴)M`.

Reproduce as follows. Use a checkout of `rickyjreyes/math` at the commit above, with its
`lean/.lake/packages` pointing to PVNP's packages (the Mathlib revision is the same).

```bash
(cd math/lean && lake build MathProofs.CubicQuinticFlow)
LP=$(cd PVNP/lean && lake env printenv LEAN_PATH)
(cd math/lean && LEAN_PATH=$LP:$PWD/.lake/build/lib/lean lean ../../PVNP/lean/bridge/MathBridge.lean)
```

Running the last command should print only the `#print axioms` lines.
