# Phase XXXI: detector-specific bounds, verified division, and the separation question (27 November 2026)

Base: `main` at `ce45ceb` (Phase XXX merged). New Lean modules:
- `lean/PVNP/SweepDiv.lean`
- `lean/PVNP/DetectorQuadratic.lean`

New tooling: an obligation registry `pvnp/phase_xxxi/obligations.json` and its evaluator
`pvnp/phase_xxxi/progress.py`, which computes the twelve progress bars (§6), with the test
`pvnp/tests/test_phase_xxxi_progress.py`.

## Outcome

- **Proved.** Verified binary long division on the repository's single-tape TM. For `W`-bit
  operands it computes the quotient and remainder in exactly `(W + 2)(4W + 2)` transitions. With
  `p` fractional bits it returns the correctly rounded-down dyadic quotient, certified by
  `q/2^p ≤ N/D < (q + 1)/2^p`.
- **Proved.** The detector sees the Fourier tail only quadratically. For a detector of bandwidth
  `r` and a truncation whose complement has mode size `≥ N`,
  `|J(v) − J(P_S v)| ≤ 3 C_det e^{σr} e^{−2σN} A_σ(v)²`. The full state has the rate `e^{−σN}`.
  The bound is instantiated on the SAT device's actual detector.
- **Derived, not kernel-checked.** The same doubled exponent holds dynamically along the Galerkin
  flow, with a factor `e^{C(M)T}` (§2.2). This halves the cutoff. It does not make long horizons
  polynomial, because the proved analyticity radius still decays like `4^{−T/τ}`.
- **Open.**
  - the dynamic detector theorem in Lean;
  - fixed-point multiplication, signed, complex and rational arithmetic;
  - the constant `C_A`, polynomial evaluation, convolution and the Taylor recurrence on the TM;
  - the end-to-end evaluator (#99);
  - a polynomial radius bound;
  - `P_TM ⊆ P_phys` without hidden computation (#103);
  - I-2, I-16 and I-32.
- **Status.** I-11 stays Restricted (subjective estimate 77% → 79%). Issues #99 and #103 stay
  open. I-2, I-16 and I-32 stay Open. **Classical P versus NP remains unresolved.**

## 1. Verified long division (`SweepDiv`)

**Encoding.** Cells carry four little-endian tracks:
- the remainder `n`;
- the shifted divisor `d = D·2^k`;
- the quotient `q`;
- a marker `m = 2^k`.

The cell alphabet has 16 symbols.

**Program.** `divProg` runs restoring division with four instructions.
- `prep` compares `n` with `d`, most significant bit first, and tests `m ≠ 0`.
- `sub` and `nosub`:
  - the forward pass of `sub` ripple-subtracts `d` from `n`;
  - both forward passes shift the new quotient bit into `q`;
  - the backward pass shifts `d` and `m` right, compares the new `n` with the new `d`, and tests the
    new marker. These two results select the next instruction.
- `done`.

The comparison reuses Phase XXIX's `cmpOf_step`, read from the most significant end (`cmpOf_msb`).

**Invariant.** `N₀ = Q·(2·D·2^k) + n` and `n < 2·D·2^k`.

| Theorem | Statement |
|---|---|
| `div_loop` | from `divI n d` with marker `2^k`, `done` after exactly `(k + 1)(2W + 2)` transitions, with `q = (N₀/D) mod 2^W` and `n = N₀ mod D` |
| `div_reach`, `div_tm` | from `prep` with `d = D·2^K`, `m = 2^K`, `q = 0` and `N₀ < 2·D·2^K`: quotient `N₀/D` and remainder `N₀ mod D` after exactly `(K + 2)(2W + 2)` transitions |
| `div_exact`, `div_exact_tm` | for `N < 2^W` and `0 < D < 2^W`, on the explicit `2W`-cell layout `divInput W N D`, the compiled TM computes `N/D` and `N mod D` in exactly `(W + 2)(4W + 2)` transitions |
| `fixdiv_certified` | `⌊N·2^p/D⌋ / 2^p ≤ N/D < (⌊N·2^p/D⌋ + 1)/2^p` |
| `fixdiv_tm` | with `N·2^p < 2^W`, the TM returns `q` with `q/2^p ≤ N/D < (q + 1)/2^p` in exactly `(W + 2)(4W + 2)` transitions |

**Representation sizes.** Operands have `W` bits and the tape `2W` cells. The count
`4W² + 10W + 4` is quadratic, as for schoolbook division on one tape.

**Layout.** `divInput` places the divisor `W` cells higher. This is a fixed, data-independent
placement, built by `bitsOf` and `mkCells` with proved values (`divInput_spec`). Producing this
layout from two operands written at the same offset would be one more data movement (`W` shift
trips). That step is not verified here.

**Integer arithmetic.** With Phase XXIX's addition, subtraction and comparison and Phase XXX's
multiplication, the fixed-width integer operations on the TM are now complete, each with an
exact transition count.

## 2. Detector-specific convergence

The physical readout is `J(v) = ∫ χ|ψ|² = Re⟨v, χv⟩` (`Jdet`, `Jdet_eq_re`).

The existing bound (`weak_detector_lipschitz`) is linear in the error:
`|J(v) − J(w)| ≤ C_det (‖v‖ + ‖w‖) ‖v − w‖`, with `C_det = L⁻¹ Σ|χ̂|`.

### 2.1 Static bound (kernel-checked, `DetectorQuadratic`)

Write `w = P_S v` and `t = v − w`.

**Spectral locality.** If `χ̂` vanishes outside `size ≤ r`, then `χt` has coefficients only
within distance `r` of `S^c`. Define the boundary layer
`B = {k ∈ S : size(k − j) ≤ r for some j ∉ S}` and `b = P_B v`. Then exactly
(`detector_split`):

`J(v) − J(P_S v) = Re(⟨t, χt⟩ + ⟨t, χb⟩ + ⟨b, χt⟩)`.

The two identities behind this are `inner_layer_left` and `inner_layer_right`:
`⟨w, χt⟩ = ⟨b, χt⟩` and `⟨t, χw⟩ = ⟨t, χb⟩`.

**Bounds.**

| Theorem | Statement |
|---|---|
| `detector_layer_bound` | `|J(v) − J(P_S v)| ≤ C_det ‖t‖ (‖t‖ + 2‖b‖)`: every term contains two tail-type factors |
| `layer_le`, `layer_size` | layer modes have size `≥ N − r`, so `‖b‖ ≤ e^{−σ(N−r)} A_σ(v)` |
| `detector_static_quadratic` | `|J(v) − J(P_S v)| ≤ C_det e^{−σN}(e^{−σN} + 2e^{−σ(N−r)}) A_σ(v)²` |
| `detector_band_quadratic` | for bandwidth `r ≥ 0`: `≤ 3 C_det e^{σr} e^{−2σN} A_σ(v)²` |
| `device_detector_quadratic` | the SAT device's detector `χ = L⁻¹(1 + cos(2πx₁/L))` has bandwidth 1 (`device_band`), so `≤ 3 C_det e^{σ} e^{−2σN} A_σ(v)²` |

**Comparison.**
- Full state: `‖t‖ ≤ e^{−σN} A_σ(v)` (`tail_le`).
- Linear detector bound: `2 C_det ‖v‖ e^{−σN} A_σ(v)`.

For accuracy `ε` the static cutoff drops from `N ≈ log(1/ε)/σ` to `N ≈ log(1/ε)/(2σ)`.

### 2.2 Dynamic bound (derivation; not kernel-checked)

**Setup.**
- `u` is the PDE solution and `u_N` the Galerkin solution with `u_N(0) = P_N u(0)`.
- `M` bounds `A_σ` of both on `[0, T]`. This holds uniformly in `N` by Phase XXIX's cutoff-independent
  propagation, with `σ = σ_T = σ₀4^{−⌊T/τ⌋}`.
- The dual-weighted norm is `|e|_{−σ}² = Σ_k e^{−2σ|k|}|ê_k|²`.

**Steps.**

(a) **Weight inequality.** `e^{−σ|k|} ≤ e^{σ|k−j|} e^{−σ|j|}`, since `|j| ≤ |k| + |k − j|`.

(b) **Module estimate.**
- Young's inequality on `ℓ¹ ∗ ℓ²` and (a) give `|uφ|_{−σ} ≤ ‖e^{σ|·|}û‖_{ℓ¹} |φ|_{−σ}`.
- In `H²` coordinates, `‖e^{σ|·|}û‖_{ℓ¹} ≤ c_L A_σ(u)` by Cauchy–Schwarz with
  `Σ(1 + q_L(k))^{−2} < ∞`. This is the mechanism of `Analytic.asum_mulH`.
- Conjugation preserves `|·|_{−σ}`.

(c) **Dual tail.** `|Q_N u|_{−σ} ≤ e^{−2σN} A_σ(u)`, because `e^{−σ|k|} = e^{−2σ|k|} e^{σ|k|}`.
The discarded modes enter the dual norm with the doubled exponent.

(d) **Error equation.** Let `e = P_N u − u_N`. Then `∂_t e = −iωe − iP_N[F(u) − F(u_N)]`.
- The dispersion is skew in every diagonal weighted norm, and `P_N` is a contraction.
- Split `F(u) − F(u_N) = [F(u) − F(P_N u)] + [F(P_N u) − F(u_N)]`.
- Each monomial difference has one factor `Q_N u` or `e` (or a conjugate) and other factors with
  `A_σ ≤ M`.
- By (b) and (c): `d/dt |e|_{−σ} ≤ C_F(M)|e|_{−σ} + C_F(M) M e^{−2σN}`, with
  `C_F(M) = c(|β|M² + |γ|M⁴)`.

(e) **Gronwall.** Since `e(0) = 0`, `|e(T)|_{−σ} ≤ T e^{C_F(M)T} C_F(M) M e^{−2σN}`.

(f) **Detector.** Split `J(u) − J(u_N) = [J(u) − J(P_N u)] + [J(P_N u) − J(u_N)]`.
- The first bracket is §2.1.
- The second is `Re⟨e, χ(P_N u + u_N)⟩`. Its modulus is at most `|e|_{−σ} A_σ(χ(P_N u + u_N))`,
  which is at most `2 c A_σ(χ) M |e|_{−σ}`.

**Result.** `|J(u(T)) − J(u_N(T))| ≤ C(M, χ)(1 + T e^{C_F(M)T}) e^{−2σ_T N}`.

The residual is quadratically small in the dual norm because the detector pairs the error only
with analytic functions. This is the dual-weighted residual principle of the specification.

**Formal gaps** (registry C2.1–C2.5):
- the dual analogue of `aw_mulH_le` in the `ℓ²` framework;
- differentiability of the dual norm along the projected PDE solution and the Galerkin error;
- the inhomogeneous Gronwall step;
- composition with the propagation theorem.

**Consequence.** The cutoff needed for detector accuracy `ε` is
`N ≈ (C_F T + log(C/ε))/(2σ_T)`, half the full-state value. With `σ_T = σ₀4^{−⌊T/τ⌋}` it still
grows like `4^{T/τ}`. The exponential stability factor enters only logarithmically. The detector
does not remove the spatial barrier for long horizons. Removing it needs a polynomial lower bound
on the radius, which remains open.

**Numerical consistency** (Phase XXX recorded runs; evidence only). Fitted decay rates per unit
cutoff:

| Data, interval | Full state | Detector | Ratio |
|---|---|---|---|
| trigonometric, `A = 1`, `t = 20`, `K = 8 → 12` | 0.61 | 1.53 | 2.5 |
| random analytic, `A = 0.3`, `t = 10`, `K = 6 → 12` | 0.47 | 1.62 | 3.4 |

Ratios of at least 2 are consistent with the bound, which is an upper bound. Values at `K = 16`
are at roundoff and are excluded.

## 3. Arithmetic library and the evaluator (#99)

**Verified on the compiled TM, each with an exact transition count:**

| Operation | Theorem | Phase |
|---|---|---|
| addition | `add_tm` | XXIX |
| subtraction | `sub_tm` | XXIX |
| comparison | `cmp_tm` | XXIX |
| multiplication | `mul_tm`, `mul_exact` | XXX |
| division | `div_exact_tm` | XXXI |
| fixed-point division with certified rounding | `fixdiv_tm` | XXXI |

**Reduction found this phase.** On `T²_{2π}` with integer `κ`, the frequencies `ω(k)` are integers
(`FrozenResonance.om_cast`). The phases `e^{−iωt}` at rational `t` then need only Taylor series of
`cos` and `sin`. Their term counts are linear in `|ωt|` and the precision, as for the exponential
(`ExpTaylor`, `ExpTaylorBits`). So `π` is not needed on `T²_{2π}`. It enters only through other
side lengths.

The algebra constant `C_A` involves `Σ_k (1 + q_L(k))^{−2}`. That sum needs a certified tail
bound, by integral comparison.

**Missing infrastructure.** The sweep-program model has no sequential-composition theorem. Each
`Prog` is standalone. Polynomial evaluation, convolution, the Taylor recurrence and the
evaluator are compositions of verified primitives with tape-layout changes between them. A
composition theorem for sweep programs, with exact costs and layout conversions, is therefore the
next concrete obligation on the machine side.

**Not done.**
- fixed-point multiplication with rounding;
- signed, complex and normalized rational arithmetic;
- `C_A`, polynomial evaluation, convolution and the Taylor recurrence;
- the explicit uniform evaluator and its runtime.

Issue #99 stays open. `P_phys ⊆ P_TM` is proved only in the restricted senses already recorded
for I-11.

## 4. `P_TM ⊆ P_phys` without hidden computation (#103, I-3, I-37)

**What exists.**
- the static equivalence of satisfiability with toroidal locking (`SpatialLocking.sat_iff_locked`);
- false-well trapping of every energy-monotone evolution (`SATDynamics.energy_monotone_trapped`);
- the theorem that charged zero-mode devices decide exactly `P_TM`
  (`ContinuumPrecision.zeroDev_languages_eq_P_TM`).

The last gives `P_TM` inside a physical class only through the preparation, which carries the
computation. Issue #103 excludes this.

**Requirements this phase identifies for an embedding where the evolution computes:**
- **Linear part.** The free flow is diagonal: each `|v̂_k|` is constant, so it transfers no
  information between modes. Any computation must come from the nonlinearity.
- **Nonlinear exchange.** In the normal-form picture, persistent energy exchange between shells
  requires resonant quartets. Nontrivial ones exist (`FrozenResonance.nontrivial_resonance`). This
  is necessary for computation, not sufficient.
- **Robust readout.** A readout over `T(n)` simulated steps needs control of the analyticity
  radius over that horizon. The proved radius decays exponentially in `T/τ`. A certified
  embedding would therefore come with a certified simulation whose cost is exponential in
  `T/τ`. That is consistent with both directions remaining open.

No TM embedding is constructed and no scoped impossibility is proved. Issue #103 stays open,
I-3 Restricted, I-37 unchanged.

## 5. Separation (I-2, I-16, I-32): this phase's candidates, both directions

**The four properties required of an invariant `μ`:**
1. defined for every uniform decider, independently of representation;
2. polynomially bounded for some decider of each language in `P`;
3. superpolynomial for every SAT decider;
4. not reducible by definition to running time.

**Candidates from this phase:**
- (A) the detector mode complexity `N_det(device, ε)`;
- (B) the dual-weighted residual size;
- (C) the decay rate of the analyticity radius.

**Findings:**
- **Property 1 fails for all three.** They are defined only for devices of the frozen PDE family. A
  Turing machine deciding SAT has no Fourier modes.
- **Constant-field devices.** Even inside the family, charged zero-mode devices have
  `N_det = 0` and decide exactly `P_TM` (`zeroDev_languages_eq_P_TM`). A SAT device of that kind,
  with a SAT decider in its preparation, also has `N_det = 0`. Property 3 fails unless the
  preparation is charged, and then `μ` reduces to the preparation's running time, failing
  property 4.
- **Kernel-checked attacks on related invariant families:**

| Attack | Result | Theorem |
|---|---|---|
| Tseitin parity | global constraint coupling collapses to component parity | `TseitinSAT.tseitin_mem_SAT_dense_iff_comp` |
| Verifier crossing | crossing information is attained at quadratic level by `V_SAT ∈ P_TM` | `VerifierCrossing.crossingInfo_V_SAT` |
| Finite horizons | every bounded-horizon lower bound is defeated by a table | `FiniteHorizon.fast_through_horizon` |
| Expanding domains | domain-uniform coercivity fails | `WCTPlaneWave.expanding_domain_countermodel` |
| Resonant quartets | invariants assuming trivial resonances fail | `FrozenResonance.nontrivial_resonance` |

- **Analyzed, not formalized:**
  - **Relativization.** Every route from (A)–(C) to property 3 passes through simulation-preserved
    properties: Phase XXIX simulation in one direction, zero-mode embedding in the other. An
    argument built only from such properties relativizes, and oracles with `P = NP` exist.
  - **Natural proofs.** (A)–(C) are not properties of Boolean functions, so the barrier does not
    apply to them directly. Any extension to circuits through device compilation would have to
    avoid being constructive and large, and nothing in (A)–(C) indicates how.
  - **Algebrization.** Arguments that use only simulation-preserved properties also survive
    low-degree extensions of the oracle. The algebrization barrier therefore applies to the same
    routes.
  - **Degenerate dispersion.** The degenerate Hessian of `ω` blocks the transfer of Strichartz
    and bilinear estimates (Phase XXX). It weakens upper bounds and creates no lower bound.
  - **Search versus decision.** SAT is self-reducible: `n + 1` adaptive decision queries find an
    assignment. The search/decision gap gives no separation lever.

**`P = NP` side.** The only SAT-correct devices in the repository with decision margins need
exponential resources (sideband amplification and the exponential end-to-end device of Phase
XXII). Halving the cutoff exponent changes `N` by a factor of at most 2. It does not change the
exponential horizon scaling. No polynomial SAT procedure emerges.

**Conclusion.** No candidate satisfies the four properties. No previously refuted argument is
repeated as progress. `CrossingSAT.SATLowerBound` and `SATTarget.SATSuperpolynomial` are neither
proved nor refuted. **Classical P versus NP remains unresolved.**

## 6. Progress, computed from obligations

`python3 pvnp/phase_xxxi/progress.py --check` evaluates `pvnp/phase_xxxi/obligations.json` and
recomputes these bars from the repository.

**Counting rule.**
- A mathematical obligation counts only if it is `proved` or `refuted` and every Lean
  declaration it cites is registered in `lean/audit/AxiomAudit.lean` and declared under
  `lean/PVNP`.
- A process obligation counts only if it is `done` and its file check passes.
- Derivations and analyses never count.

The subjective column is a separate judgement.

```
     category                                                                     computed                 subjective (not computed)
C1   Detector-specific bound, static truncation                                   [####################] 100% (5/5)   100%
C2   Detector-specific bound, Galerkin dynamics                                   [....................]   0% (0/5)    45%
C3   Spatial complexity and the analyticity radius                                [#############.......]  67% (4/6)    55%
C4   Verified TM integer arithmetic                                               [####################] 100% (5/5)   100%
C5   TM fixed-point, rational, signed and complex arithmetic; certified rounding  [####................]  20% (1/5)    25%
C6   Constants and series on the TM                                               [###.................]  17% (1/6)    15%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [###########.........]  57% (4/7)    60%
C8   P_TM in P_phys: controlled SAT dynamics and TM embedding (#103, I-3, I-37)   [##########..........]  50% (2/4)    35%
C9   Universal separation (I-2, I-16, I-32)                                       [....................]   0% (0/3)     0%
C10  Adversarial falsification with kernel-checked counterexamples                [###########.........]  55% (6/11)    70%
C11  Phase XXXI execution pipeline (repository state at commit time)              [#################...]  86% (6/7)    80%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

**Reading the bars.**
- C11.7 (hosted CI at the exact pull-request head, and the merge) is recorded on the pull request.
  It cannot be checked inside the commit it verifies.
- **C12 is the only bar that measures classical P versus NP. It is 0.**

## Verification

Local, Lean 4.23.0, on the Lean tree of commit `0510b55`:
- `lake build PVNP` passed (7,434 jobs). `PVNP.SweepDiv` and `PVNP.DetectorQuadratic` build
  without warnings.
- `lake env lean audit/AxiomAudit.lean` with `audit/check_axioms.py` passed for all 1,255
  registered declarations, including the 43 new ones: 27 in `SweepDiv` and 16 in
  `DetectorQuadratic`. They use only `propext`, `Classical.choice` and `Quot.sound`, and no
  `sorryAx` occurs.

Later commits change documentation, the obligation registry and its evaluator, tests, and
generated dashboard data only. The dashboard, status registry, manuscript-alignment and
release-document checks, the Python suite, the progress check and `git diff --check` pass.
Hosted CI is recorded on the pull request.
