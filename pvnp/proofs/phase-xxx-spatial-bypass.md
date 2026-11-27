# Phase XXX: bypassing the spatial barrier (27 November 2026)

Base: `main` at `97a49b0` (Phase XXIX merged). New Lean modules:
- `lean/PVNP/SweepMul.lean`
- `lean/PVNP/FrozenResonance.lean`

New numerical probe: `pvnp/phase_xxix/detector_experiment.py` (evidence only).

## Outcome

- **Proved.** Verified shift-and-add multiplication on the repository's single-tape TM, with an
  exact transition count. This is the next piece of the arithmetic library.
- **Proved.** The resonance structure relevant to normal forms and modified energies:
  - no small divisors on `T²_{2π}` with integer `κ`;
  - quartets resonant for both phases are trivial;
  - but the frozen dispersion alone has **nontrivial** resonances, on which radial energy
    multipliers do not vanish.
  The route "normal form plus only trivial resonances" to polynomial analyticity bounds is
  therefore closed. The resonant system itself would have to be controlled.
- **Evidence only.** The detector bit converges with far fewer Fourier modes than the full state.
  The gap is orders of magnitude over the horizons tested.
- **Open.**
  - a polynomial lower bound on the analyticity radius;
  - a rigorous detector-specific bound;
  - division, rational, fixed-point and complex arithmetic, `π`, convolution, the Taylor
    recurrence and the end-to-end TM evaluator;
  - `P_phys ⊆ P_TM`.
- I-11 stays Restricted; issue #99 stays open; I-2, I-16 and I-32 stay Open. **Classical P versus
  NP remains unresolved.**

## 1. Verified multiplication (`SweepMul`)

Cells carry multiplicand `x`, multiplier `y` and accumulator `acc` (little-endian).
`mulProg` has four instructions:
- `prep`: reports the zero test and the low bit of `y`;
- `add`: the forward pass shifts `x` left while ripple-adding the old `x` into `acc`;
- `skip`: shift only;
- `done`.

The backward pass of `add`/`skip` shifts `y` right and reports the zero test and low bit of the
new `y`, which select the next instruction. The invariant is `acc + x·y ≡ A₀ + X·Y (mod 2ⁿ)`.

| Theorem | Statement |
|---|---|
| `mul_reach` | `done` is reached after exactly `(trips Y + 1)(2n + 2)` TM transitions, where `trips Y` is the bit length of `Y`, with `acc = (A₀ + X·Y) mod 2ⁿ` |
| `mul_exact` | if `A₀ = 0` and `X·Y < 2ⁿ`, then `acc = X·Y` in at most `(n + 1)(2n + 2)` transitions |
| `mul_tm` | the same on the compiled single-tape TM (`Prog.reach_run`) |

Together with Phase XXIX's addition, subtraction and comparison, this covers the ring operations
on fixed-width binary integers. **Not built**:
- long division (designed as `n` compare–subtract–shift trips);
- rational and fixed-point arithmetic with certified rounding;
- complex arithmetic;
- rational approximation of `π` and `C_A`;
- finite convolution and the Taylor coefficient recurrence;
- the end-to-end evaluator for the analytic regime of Phase XXIX.

## 2. Modified energies and normal forms: do the dispersive techniques transfer?

**Derivation.** Take the cubic part and a radial weight `w`. The time derivative of
`E_w(ψ) = Σ_k w(|k|²)|ψ̂_k|²` is a quartic form over quartets `k₁ − k₂ + k₃ = k`.
- Its symmetrized multiplier is `m = w(|k₁|²) − w(|k₂|²) + w(|k₃|²) − w(|k|²)`.
- In the interaction picture it carries the phase `e^{iΦt}`, where
  `Φ = ω(k₁) − ω(k₂) + ω(k₃) − ω(k)`.
- A normal form (integration by parts in time) divides the non-resonant part by `Φ` and leaves
  higher-order remainders.
- The resonant part (`Φ = 0`) has no oscillation. It vanishes only where `m` does.

**Kernel-checked facts** (`FrozenResonance`):
- `no_small_divisors`: on `L = 2π` with integer `κ`, `Φ ∈ ℤ`, so a non-resonant quartet has
  `|Φ| ≥ 1`.
- `doubly_resonant_trivial`, `radial_vanish`: a quartet resonant for both the Schrödinger phase
  and the frozen phase has `{|k₁|², |k₃|²} = {|k₂|², |k|²}`, and every radial multiplier
  vanishes on it.
- `nontrivial_resonance`, `nontrivial_resonance_real`: the frozen dispersion alone has nontrivial
  resonances. For `κ = 0`, the quartet `(−4,−3), (−4,−1), (−2,−2), (−2,−4)` has
  `|kᵢ|² = (25, 17, 8, 20)` and `Φ = 0`, and the `H¹` multiplier equals `−4`.

**Search.** A search over `|kᵢ| ≤ 6` finds nontrivial resonant quartets at every `κ` tested:
about 2% of resonant quartets for `κ = 0`, 4% for `κ = 1` and 11% for `κ = 3`.

**Consequence.** Every radial modified energy, `H^s` or analytic, keeps a non-oscillating
resonant flux. Its long-time effect is governed by the resonant system, just as the NLS
rectangles on `T²` drive the known energy cascades. The polynomial-growth arguments for NLS on
`T²` also use Strichartz and bilinear estimates that depend on the curvature of the dispersion
surface. Here `ω(ξ) = (κ − |ξ|²)²` has a degenerate Hessian:
- the radial second derivative `−4κ + 12|ξ|²` vanishes on `|ξ|² = κ/3`;
- the angular curvature `−4(κ − |ξ|²)` vanishes on `|ξ|² = κ`;
- for `κ = 0`, the Hessian degenerates at the origin.

These hypotheses therefore **do not transfer automatically**. A polynomial lower bound on the
radius remains open.

## 3. Detector-specific approximation

The physical readout is quadratic and low-frequency: `J(ψ) = (2π)⁻² ∫ cos x |ψ|²`.
- **Static bound.** Truncating a *fixed* state changes `J` only through products of a tail
  coefficient with a coefficient one mode away. So the static truncation error is quadratic in the
  tail away from the cutoff boundary.
- **Dynamic error.** The error does not vanish to that order. Nonlinear coupling feeds the
  projection error back into the low modes at first order, though with much smaller constants.
- **Rigour.** The rigorous detector bound in the repository (`weak_detector_lipschitz`) uses the
  full weak-norm error. No sharper detector-specific theorem is proved here.

**Numerical evidence** (`pvnp/phase_xxix/detector_experiment.py`; results in
`pvnp/phase_xxix/results/`). The exact Galerkin system was run on `T²_{2π}` with `κ = 0` and
`β = γ = 1` for cutoffs `K`, and compared with a reference cutoff `K_ref`.

| Data, time | `K` | full-state `L²` error | detector error |
|---|---|---|---|
| trigonometric, `A = 1`, `t = 20` (`K_ref = 32`) | 6 | `1.7·10⁻⁴` | `3.8·10⁻⁶` |
| | 8 | `8.9·10⁻⁵` | `7.3·10⁻⁸` |
| | 12 | `7.7·10⁻⁶` | `1.6·10⁻¹⁰` |
| | 16 | `9.5·10⁻⁸` | `8.7·10⁻¹⁵` |
| random analytic, `A = 0.3`, `t = 10` (`K_ref = 24`) | 6 | `2.9·10⁻⁵` | `2.0·10⁻⁸` |
| | 12 | `1.7·10⁻⁶` | `1.2·10⁻¹²` |
| | 16 | `3.4·10⁻⁸` | `1.1·10⁻¹⁴` |

- The detector error is many orders of magnitude below the full-state error. For the larger
  cutoffs it is roughly the square of the full-state error, consistent with the static quadratic
  structure plus a smaller first-order dynamic feedback.
- **Consistency checks.** Halving `dt` changes `J` by `≤ 2·10⁻⁷` (trigonometric) and
  `≤ 3·10⁻⁹` (random). An independent Strang-splitting integrator of the *unprojected* equation
  agrees to `≤ 5·10⁻⁶` and `≤ 4·10⁻⁸`.
- An earlier random run at `A = 1` and `dt = 2·10⁻³` became numerically unstable (explicit RK4
  with large `γ|ψ|⁴`) and is discarded.
- The `L²` errors near `10⁻⁸` include floating-point cancellation.

**Interpretation.**
- These finite-horizon data suggest that the decision bit needs far fewer modes than full-state
  accuracy. A superpolynomial mode count for the *state* would therefore not imply one for the
  *detector*.
- They do not prove a detector-specific bound. Nor do they show that the detector stays cheap
  over polynomial horizons, where the resonant cascade (§2) could feed back into the low modes.

## 4. What the spatial obstruction is, and is not

| Level | Status |
|---|---|
| (a) Exponential deterioration of a sufficient bound | **Proved upper bound** (Phase XXIX): the cutoff `∝ 4^{T/τ}` |
| (b) Actual exponential decay of the analyticity radius | **Not established.** Converged numerics (Phase XXIX) show accelerating decay over finite windows. The nontrivial resonances (§2) provide a plausible mechanism. |
| (c) Exponential growth of the significant Fourier modes | **Not established.** For analytic data it is equivalent to (b) up to constants. |
| (d) Exponential cost of a specific algorithm (Fourier truncation with the certified integrator) | **Not established.** It would follow from (b). |
| (e) Unavoidable cost across all representations | **Not established.** It does not follow from (a)–(d). The detector evidence (§3) points the other way for the decision bit. |

## 5. Separation (I-2, I-16, I-32)

Three candidate sources of new invariants were examined.
- **Resonant cascades and nonlinear frequency interactions.** These are properties of one
  dynamical system. Any invariant built from them constrains devices that obey that dynamics,
  not every uniform SAT decider. A Turing machine deciding SAT has no frequencies. To force a cost
  on *every* decider, the invariant would have to be preserved by polynomial-time simulation. Such
  invariants reduce to running time (Phase XXVI).
- **Observable-specific complexity.** The cost of computing the detector bit is a property of the
  device's encoding. If SAT is encoded in the bit, computing the bit is as hard as SAT, whatever
  that hardness is. That restates the target.
- **Computational histories.** Analysed in Phase XXVI. They reduce to time complexity.

**Constructive side.** The fast detector evidence concerns simulating a given device, not deciding
SAT. The SAT-encoding devices of earlier phases need exponentially many trajectories or
exponential horizons. No polynomial-time SAT decider emerged.

No new representation-independent invariant was found, and no previously refuted argument is
repeated. `CrossingSAT.SATLowerBound` is neither proved nor refuted. **Classical P versus NP
remains unresolved.**

## Verification

Local, Lean 4.23.0, on the Lean tree of commit `8aabffe`:
- `lake build PVNP` passed (7,432 jobs). `PVNP.SweepMul` and `PVNP.FrozenResonance` build without
  warnings.
- `lake env lean audit/AxiomAudit.lean` with `audit/check_axioms.py` passed for all 1,212
  registered declarations, including the 33 new ones: 24 in `SweepMul` and 9 in
  `FrozenResonance`. They use only `propext`, `Classical.choice` and `Quot.sound`, and no
  `sorryAx` occurs.

Later commits change documentation, the numerical probes and their recorded output, tests, and
generated dashboard data only. The dashboard, status registry, manuscript-alignment and
release-document checks, the Python suite and `git diff --check` pass. Hosted CI is recorded on
the pull request.
