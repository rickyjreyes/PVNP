# Phase XXXI (continued): the dynamic detector theorem (27 November 2026)

Base: `main` at `ec856e5` (PR #114 merged). New Lean module: `lean/PVNP/DetectorDynamic.lean`
(39 declarations).

## State on resumption

The dual-residual integration had already finished before this resumption.
- `DualResidual` is in `lean/PVNP.lean`, the Lean workflow and the axiom audit on `main`
  (`ec856e5`).
- Hosted CI passed at the exact head `605226e`, including the audit of 1,269 declarations.

Nothing was redone.

## Outcome

- **Proved (kernel-checked).** The dynamic detector theorem along the nonlinear Galerkin flow,
  uniformly in the fine Fourier cutoff. The quadratic rate `e^{−2σN}` is proved for the evolution,
  not assumed from the static bound. The price is the stability factor `e^{(K_F + 1/2)T}`.
- **Derived, not kernel-checked:**
  - the exact adjoint (dual-weighted residual) representation of the detector error (§3);
  - the passage from the fine Galerkin trajectory to the PDE solution (registry C2.5).
- **Answer to the mode-count question.**
  - With the proved radius `σ_T = σ₀4^{−⌊T/τ⌋}`, polynomially many modes suffice for a
    margin-`m` readout when the horizon is `T = O(τ log n)`.
  - The required cutoff grows like `4^{T/τ}` for longer horizons.
  - A polynomial lower bound on the radius would give polynomially many modes for polynomial
    horizons.
  - The detector is no longer the obstruction; the radius is (§4).
- **Separation.** Observable-specific complexity is a simulation, that is upper-bound, tool. It
  yields no representation-independent invariant and no SAT algorithm (§6).
- **Status.** I-11 stays Restricted; #99 and #103 stay open; I-2, I-16 and I-32 stay Open.
  **Classical P versus NP remains unresolved.**

## 1. The theorem (`DetectorDynamic`)

**Setting.**
- `u` and `w` are physical-picture Galerkin trajectories on mode sets `S ⊆ S'`:
  `u' = −i(A_S u + P_S F(u))`, and likewise for `w` on `S'`.
- Every mode outside `S` has size `≥ N`.
- Both trajectories stay in the analytic ball `A_σ ≤ M` on `[0, T]`. Phase XXIX's cutoff-independent
  propagation gives this uniformly in `S` and `S'`, with `σ = σ_T` (`Analytic.galerkin_analytic`,
  `asq_mono`).

**Constants.**
- `K_F(M) = 3|β|C_A²M² + 5|γ|C_A⁴M⁴`;
- `G(M) = |β|C_A²M³ + |γ|C_A⁴M⁵`.

| Theorem | Statement |
|---|---|
| `dnorm_Fnl_sub_le` | dual Lipschitz bound: `|F(a) − F(b)|_{−σ} ≤ K_F(M) |a − b|_{−σ}` on the analytic ball |
| `hasDerivAt_dsq`, `deriv_dsq_le` | energy identity and inequality: `d/dt |w − u|²_{−σ} ≤ 2K_F |w − u|²_{−σ} + 2|w − u|_{−σ} e^{−2σN} G(M)`; the dispersion cancels exactly |
| `galerkin_dual_gronwall` | `|w(t) − u(t)|²_{−σ} ≤ gronwallBound(|w(0) − u(0)|²_{−σ}, 2K_F + 1, (e^{−2σN}G)², t)` |
| `detector_dual_bound` | `|J(v) − J(w)| ≤ C_A A_σ(χ)(A_σ(v) + A_σ(w)) |v − w|_{−σ}` |
| `galerkin_detector_dynamic` | the detector error at `T` in terms of the initial dual error |
| `galerkin_detector_dynamic_data` | from common analytic data `u(0) = P_S u₀`, `w(0) = P_{S'} u₀`: `|J(w(T)) − J(u(T))| ≤ 2 C_A A_σ(χ) M e^{−2σN} ((A_σ(u₀)² + G(M)² T) e^{(2K_F+1)T})^{1/2}` |
| `cutoff_for_margin` | if `2σN ≥ log(B/m)`, then `B e^{−2σN} ≤ m` |

The bound does not depend on `S'`. The fine trajectory may be arbitrarily fine.

## 2. The argument

1. **Dual norm.** `D_σ = diag(e^{−σ|k|})` is a bounded operator with `|v|_{−σ} = ‖D_σ v‖`
   (`Dw`, `dnorm_sq`). It satisfies the triangle inequality and is invariant under
   conjugation (`dnorm_conjH`).
2. **Module and product estimates.**
   - `|v·w|_{−σ} ≤ C_A A_σ(v)|w|_{−σ}` (`dnorm_mulH_le`, from `DualResidual.dsq_mulH_le`).
   - Telescoping over the five factors of the quintic term and the three of the cubic term gives
     `K_F` (`dnorm_mulH_sub_le`, `dnorm_Fnl_sub_le`).
3. **Error equation**, mode by mode on `S'` (`field_diff`). Let `e = w − u`. Then
   `e'_k = −iω_k e_k − i(F(w) − P_S F(u))_k`, and
   `F(w) − P_S F(u) = [F(w) − F(u)] + [F(u) − P_S F(u)]`.
   - The first bracket is controlled by step 2.
   - The second is the tail of the coarse nonlinearity outside `S`. In the dual norm it has the
     doubled exponent: `≤ e^{−2σN} A_σ(F(u)) ≤ e^{−2σN} G(M)` (`DualResidual.dsq_tail_le`,
     `anorm_Fnl_le`).
4. **Energy.**
   - `|e|²_{−σ}` is a finite sum on `S'`, so it is differentiable (`hasDerivAt_dsq`).
   - The dispersion contributes `Re⟨e_k, −iω_k e_k⟩ = 0`.
   - Cauchy–Schwarz on `S'` gives the inequality (`deriv_dsq_le`).
   - With `2ab ≤ a² + b²`, the derivative is at most `(2K_F + 1)|e|²_{−σ} + (e^{−2σN}G)²`.
5. **Gronwall** (`le_gronwallBound_of_liminf_deriv_right_le`, `gronwallBound_le`).
6. **Detector.**
   - `J(v) − J(w) = Re(⟨v − w, χv⟩ + ⟨w, χ(v − w)⟩)`.
   - Each pairing is `⟨D_σ x, A_σ y⟩`, so it is bounded by `|x|_{−σ} A_σ(y)` (`inner_dual`).
7. **Initial error.** `P_{S'}u₀ − P_S u₀` lives outside `S`, so
   `|·|²_{−σ} ≤ e^{−4σN} A_σ(u₀)²` (`dsq_annulus_le`).

## 3. The adjoint representation (derivation; not kernel-checked)

**Equations.** The error satisfies `e' = (L + B(t))e + r(t)`, where:
- `L = −iω` is skew;
- `B(t)e = −i∫₀¹ DF(u + s e)[e] ds` is the secant linearization, which is real-linear in `e`;
- `r = −i Q_S F(u)` is the residual.

**The adjoint.** Let `z` solve `z' = Lz − B(t)*z` with `z(T) = χ(w(T) + u(T))`. The adjoint is
taken for the real inner product `Re⟨·,·⟩`. Then `d/dt Re⟨z, e⟩ = Re⟨z, r⟩`, so exactly

`J(w(T)) − J(u(T)) = Re⟨z(0), e(0)⟩ + ∫₀ᵀ Re⟨z(t), r(t)⟩ dt`.

**Existence.** In the interaction picture the adjoint is a linear ODE with bounded continuous
coefficients. It is finite-dimensional on `S'`, so it exists globally.

**Regularity.** The multiplication operators in `B(t)*` are bounded on the analytic space by the
algebra estimate. Hence `A_σ(z(t)) ≤ e^{K_F(T−t)} A_σ(z(T))`. The adjoint stays analytic with
the same radius `σ_T`. It does not lose radius, because the equation is linear with analytic
coefficients.

**Why the quadratic cancellation persists.**
- `r` and `e(0)` live outside `S`.
- `z` is analytic, so `|Q_S z| ≤ e^{−σN} A_σ(z)`.
- Hence `|⟨z, r⟩| ≤ e^{−σN}A_σ(z) · e^{−σN}A_σ(F(u))`. Each pairing carries the doubled
  exponent.

**Relation to the formal proof.** The formal proof uses the equivalent energy formulation. The
bound `A_σ(z(t)) ≤ e^{K_F(T−t)}A_σ(z(T))` is the dual statement of the dual-norm stability
proved in `galerkin_dual_gronwall`. It is not assumed that the static cancellation persists. The
representation shows why it does, and the theorem proves the resulting bound.

## 4. Do polynomially many Fourier modes suffice for a reliable readout?

**Cutoff.** Write `B = 2C_A A_σ(χ) M ((A_σ(u₀)² + G²T) e^{(2K_F+1)T})^{1/2}`. By
`cutoff_for_margin`, the cutoff

`N ≥ [(K_F(M) + 1/2)T + log(2C_A A_σ(χ) M (A_σ(u₀)² + G²T)^{1/2}/m)] / (2σ_T)`

fixes a margin-`m` readout. It is uniform in the fine cutoff.

**With the proved radius `σ_T = σ₀4^{−⌊T/τ⌋}`:**
- for `T = O(τ log n)`, the cutoff `N` is polynomial in `n`, and the mode count `~N²` on `T²` is
  polynomial;
- for `T = n^c`, `N` is `4^{Θ(n^c/τ)}`, which is exponential;
- the stability factor enters only through `log`, as the term `(K_F + 1/2)T`.

**Reduction.** The detector-specific question reduces exactly to the radius question (registry
C3.5). If `σ_T ≥ 1/poly(T)` were proved, then:
- the detector cutoff would be polynomial for polynomial horizons;
- the remaining cost would be time stepping, which is already polynomial by Phase XXVIII, and
  arithmetic.

**Numerical difficulty versus decision hardness.** The exponential mode count is a property of
the proved radius bound, and possibly of the dynamics. It is not a property of SAT.

## 5. Arithmetic and the evaluator (#99)

Unchanged this round. Verified on the compiled TM:
- addition, subtraction and comparison (Phase XXIX);
- multiplication (Phase XXX);
- long division and certified fixed-point division (Phase XXXI).

**The missing infrastructure is a sequential-composition theorem for sweep programs.** It must
handle layout conversion and exact cost addition. Every remaining machine obligation is a
composition of verified primitives:
- fixed-point multiplication with rounding;
- signed, complex and normalized rational arithmetic;
- the constant `C_A`;
- polynomial evaluation, convolution and the Taylor recurrence;
- coefficient access;
- the evaluator.

The obstacle is concrete. A `Prog` bundles its data alphabet, so composing two programs over
the same alphabet needs either a program record parametrized by the alphabet, or casts along
`P.D = Q.D`. Issue #99 stays open.

## 6. Separation: does observable-specific complexity give an invariant or an algorithm?

**Candidate.** Let `N_det(D, x, m)` be the least cutoff for which the Galerkin readout of device
`D` on input `x` has margin `m`. The dynamic theorem gives an *upper* bound on it.

**Representation-independent invariant? No.**
- `N_det` is defined only for devices of the frozen PDE family, through their dynamics and input
  encoding. A Turing machine has no Fourier modes.
- The device-free version `μ(L) = inf_D max_x N_det(D, x, m)` collapses:
  - charged zero-mode devices decide exactly `P_TM` with a one-mode field
    (`ContinuumPrecision.zeroDev_languages_eq_P_TM`);
  - a SAT decider placed in the preparation gives `N_det = 1` for SAT as well;
  - charging the preparation makes `μ` the preparation's Turing time, which is circular.
- The four required properties fail exactly as for the Phase XXXI candidates.

**Efficient SAT construction? No.**
- The theorem simulates short-horizon analytic devices efficiently, up to the unbuilt evaluator.
  A SAT-deciding device in that regime, with polynomial preparation and polynomial `M`, `1/σ₀`
  and `log(1/m)`, would therefore yield a polynomial SAT procedure. The implication is
  conditional on the evaluator (#99), which is not built.
- No such device is known. The repository's SAT-correct devices need exponential resources or
  precomputed preparations. So the framework turns a `P = NP` construction into a device-design
  problem at least as hard as the original.

**Barriers.**
- **Relativization.** The simulation argument relativizes. An oracle in the preparation passes
  through unchanged. It is consistent with either answer and cannot separate.
- **Natural proofs and algebrization.** As analyzed in `phase-xxxi-detector-division.md` §5.

`CrossingSAT.SATLowerBound` is preserved unchanged, neither proved nor refuted. **Classical P
versus NP remains unresolved.**

## 7. Progress, computed from obligations

`python3 pvnp/phase_xxxi/progress.py --check` recomputes these bars from the repository. The
counting rule is unchanged.

```
PVNP Phase XXXI | bars computed from obligations; subjective estimates labelled separately
     category                                                                                           computed   subjective (not computed)
C1   Detector-specific bound, static truncation                                   [####################] 100% (5/5)   100%
C2   Detector-specific bound, Galerkin dynamics                                   [################....]  80% (4/5)    80%
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
C12 is the only bar that measures classical P versus NP. It is 0: the problem is unresolved.
```

## Verification

Local, Lean 4.23.0, on the Lean tree of commit `ad0f992`:
- `lake build PVNP` passed (7,436 jobs). `PVNP.DetectorDynamic` builds without warnings.
- The 39 new declarations are registered in `lean/audit/AxiomAudit.lean`, which now lists 1,308
  declarations. The hosted workflow audits all of them at the pull-request head, accepting only
  `propext`, `Classical.choice` and `Quot.sound`. The local full-audit result is recorded on the
  pull request.

Later commits change documentation, the obligation registry, and generated dashboard data only.
The dashboard, status registry, manuscript-alignment and release-document checks pass, as do the
Python suite, the progress check and `git diff --check`. Hosted CI is recorded on the pull
request.
