# I-31: the uniform separator price fails for the frozen trajectory class

**Date:** 12 November 2026
**Claim:** Part I, Hypothesis `lem:separator-price` (inventory row I-31)
**Outcome:** REFUTED for the frozen physical trajectory class. Status changes from Open to Refuted.
**Lean:** `lean/PVNP/SeparatorFrozen.lean` (namespace `PVNP.SeparatorFrozen`)

## 1. The hypothesis

> For all admissible fields used by a specified class of machines,
> `Φ(ψ) ≥ κ₀ 𝓗^{d−1}(∂𝓡_ψ)` with `κ₀ > 0` independent of the input length and encoding.

* `Φ(ψ) = ∫ (|∇ψ|² + |Θ[ψ]|²)` is the cumulative curvature functional of Part I ("Semantic
  Curvature Complexity"), with `Θ` the WCT curvature operator ("e.g. the Laplacian divided by
  `g(ψ)`"; Part III uses `Θ_ε = −Δψ ψ̄/(|ψ|² + ε²)`).
* `∂𝓡_ψ` is the decision interface: the boundary of the region where a pointwise readout of the
  field lies above its threshold. This is the "decoded cut" of the mesh-price paragraph, which
  uses "a scalar K-Lipschitz readout on opposite sides of a threshold with margins η".
* In the frozen model `WCT-Phys` (`physical-model-freeze.md`), the field lives on the torus of
  side `L_n`, a declared polynomially bounded function of the input length, and evolves by
  `i∂ₜψ = (Δ+κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ` without forcing.

The inventory recorded the open question as: "A uniform price for the physical trajectory class
remains open."

## 2. Counterexample

Fix an amplitude `A ≠ 0`. On the torus of side `L` take the exact solution

```
ψ_t(x) = A · exp(i(2π x₁ / L − ω t)),   ω = (κ − (2π/L)²)² − β|A|² + γ|A|⁴
```

(`traj`, `traj_solves`, `traj_periodic`). Its modulus is `|A|` for every `L` and `t`
(`traj_norm`).

* **Fixed contrast.** The readout `Re ψ_t` reaches `|A|` and `−|A|` inside the fundamental domain
  at every time (`traj_contrast`). Both decisions are present with the same margin for every `L`.
* **Bounded cost.** For every curvature operator with `|Θ[ψ]| ≤ c|Δψ|` pointwise,
  `Φ(ψ_t) ≤ 4π²|A|² + 16π⁴c²|A|²/L²` (`Phi_traj_le`). This covers `Θ = Δ` (`c = 1`,
  `lap_dominated`), `Θ_ε` (`c = 1/(2ε)`, `thetaEps_dominated`) and `Δψ/g` with `g ≥ g₀ > 0`.
* **Growing interface.** At every time, a vertical segment of length `L` of the fundamental domain
  lies on the frontier of `{Re ψ_t > 0}` (`segment_subset`), so the Euclidean length of the
  interface is at least `L` (`interface_ge`, `hausdorff_segment`).

Hence (`no_uniform_separator_price`): for every `κ₀ > 0` and amplitude bound `a` there is `L₀` such
that every state of every such trajectory with `0 < |A| ≤ a` on a torus of side `L ≥ L₀` satisfies

```
Φ(ψ_t) < κ₀ · 𝓗¹(∂𝓡_{ψ_t}).
```

`separator_price_hypothesis_false` states the negation of the hypothesis directly, and
`separator_price_false_thetaEps` instantiates it with the operator of Part III.

### The fields are used by a decider

`stripe_device_decides`: the encoder writes amplitude `+1` for members of a language and `−1`
otherwise, and the sign of `Re ψ` at the origin at time `0` is the answer. For a language in
`P_TM` this is a charged polynomial-time encoder of the kind `PhysicalAudit.polyEnc` admits; the
decoder reads the real part of the single Fourier coefficient, which is a receiver of the frozen
model. `stripe_device_violates`: every state of every run violates the price once `L ≥ L₀`,
with `L₀` independent of the input.

### A modulus readout fails as well

`no_uniform_price_modulus`: the three-mode initial datum `g(x) = (a/2)(1 + cos(2πx₁/L))` has
`Φ(g) ≤ π²a² + 4π⁴c²a²/L²` (`Phi_bump_le`) while the frontier of `{|g| > a/2}` has length at least
`L` (`bump_interface_ge`). So the failure does not depend on reading a quadrature.

## 3. What is true instead

The price fails because the transition between the two readout values is spread over a width
proportional to `L`. For a transition of bounded width there is a price:

* `layer_price`: if a profile passes from `≤ −η` to `≥ η` across an interval of width `w`, then
  `∫ |f'|² ≥ 4η²/w`. Integrated along an interface, this is `4η²/w` per unit length.
* `layer_price_sharp`: the linear profile attains it.
* `SeparatorPrice.mesh_price` (existing): with a jump of at least `δ` across every face of a
  decoded cut, the price is `δ²/h` per unit area.

A uniform `κ₀` therefore needs a uniform bound on transition widths (sharp interfaces). The frozen
model imposes no such bound, and its exact solutions violate it.

## 4. Checks requested before reclassification

`PUBLIC_RELEASE_READINESS.md` and `docs/PR74_RECONCILIATION.md` asked that a refutation be checked
against the exact quantifiers, admissible fields, detector and contrast, `Φ`, readout geometry and
normalization.

| Check | How the counterexample meets it |
|---|---|
| Quantifiers | `∀ κ₀ > 0, ∃ L₀, ∀ L ≥ L₀, ∀ A (0 < \|A\| ≤ a), ∀ t`: a violation (`no_uniform_separator_price`). `κ₀` may not depend on the input length or the encoding, and `L` grows with the input length. |
| Admissible fields | Exact solutions of the frozen PDE (`traj_solves`), periodic on the torus (`traj_periodic`). The encoding is one Fourier mode with amplitude `±1`, written by a polynomial-time encoder for any language in `P_TM`; the three-mode datum is likewise exact. |
| Detector and contrast | The readout `Re ψ` reaches `±\|A\|` in the fundamental domain at every time (`traj_contrast`): the margin does not shrink with `L`. The modulus readout `{\|g\| > a/2}` is covered separately (`no_uniform_price_modulus`). |
| `Φ` | The manuscript's `∫ (\|∇ψ\|² + \|Θ[ψ]\|²)` for every `Θ` with `\|Θ[ψ]\| ≤ c\|Δψ\|`; instantiated for `Δ` and for Part III's `Θ_ε` (`separator_price_false_thetaEps`). |
| Readout geometry | The frontier of the decision region `{Re ψ > 0}` intersected with the fundamental domain `[0, L)²`, measured by the Euclidean Hausdorff measure `𝓗¹` (`interface_ge`). |
| Normalization | The amplitude is fixed; the mass `\|A\|²L²` grows polynomially with `L_n`. The frozen model charges the mass but does not fix it. Under a fixed-mass normalization the contrast would decay like `1/L`, which is the different, contrast-losing scenario of `SeparatorAmplitude`. |

## 5. Scope

* The counterexample uses the growth of `L_n` with the input length, which the frozen model
  allows and which the hypothesis forbids `κ₀` to depend on. On a torus of fixed side the
  stripes need frequency growth to lengthen the interface, and then `Φ` grows faster than the
  interface; this module does not decide the fixed-domain question.
* For a machine class restricted to deciders of one language outside `P_TM`, the stripe device
  is not available as a decider. The hypothesis is a per-field inequality, and the fields above
  are admissible fields of the frozen model, so the hypothesis as stated fails; a version
  restricted to the fields of deciders of one hard language is not settled here.
* Measures: `Φ` is a Lebesgue integral in `ℝ≥0∞`, so the upper bounds need no integrability
  hypotheses. The interface is measured with `μH[1]` on `EuclideanSpace ℝ (Fin 2)`.

Nothing here bears on classical P versus NP.

## 6. Verification

Local, Lean 4.23.0: `lake build PVNP` succeeded (7,387 jobs) and the axiom audit reported
648 declarations with only `propext`, `Classical.choice` and `Quot.sound`, including the 21
declarations of this module.
