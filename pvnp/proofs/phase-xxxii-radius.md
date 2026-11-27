# Phase XXXII: almost conservation of analytic energies and a polynomial analyticity radius (27 November 2026)

New Lean module: `lean/PVNP/AnalyticAlmostConservation.lean`, with 50 registered theorems.

## Outcome

- **Proved (kernel-checked), registry C3.5.** A polynomial lower bound on the analyticity radius
  over polynomial horizons, uniformly in the Galerkin set (`galerkin_radius_poly`).
  - *Setting:* analytic data and `γ > 0`.
  - *Statement:* for every horizon `T ≥ 0`, the cutoff-independent analytic bound
    `A_{σ_T}(W(t)) ≤ B` holds on `[0, T]` at the radius
    `σ_T = min(σ₀, (1 + K T)^{−2})`.
  - *Constants:* `B` and `K` depend only on `L, κ, β, γ` and the initial analytic norm.
  - The previous bound, `σ₀ 4^{−⌊T/τ⌋}` (C3.1), decays exponentially in `T`.
- **Proved: the detector bound for the actual PDE solution at the polynomial radius**
  (`pde_detector_poly`, and `galerkin_detector_poly` for two Galerkin trajectories).
  - **Bound.** The coarse Galerkin readout error is at most
    `2 C_A A_{σ_T}(χ) B e^{−2σ_T N} ((A_{σ_T}(w(0))² + G(B)²T) e^{(2K_F(B)+1)T})^{1/2}`.
  - **Cutoff for a margin-`m` readout:** it suffices that
    `N ≥ [(K_F(B) + 1/2)T + log(2C_A A_{σ₀}(χ) B (A_{σ₀}(w(0))² + G(B)²T)^{1/2}/m)] / (2σ_T)`.
    That is `O((1 + K T)²(T + log(1/m)))`.
  - **Consequence: polynomially many Fourier modes suffice over polynomial horizons**, for the
    continuum PDE in the restricted analytic regime.
- **Registry C3.6 is refuted.** C3.6 states that the radius decays exponentially for some
  admissible datum, so that the obstruction is real. In the restricted analytic regime no such
  datum exists: the cutoff-independent analytic bound holds at radius `σ_T ≥ min(σ₀, (1+KT)^{−2})`
  for every analytic datum, and the detector cutoff for the PDE is polynomial in `T`. The general
  `H²`-admissible class has no analyticity radius, and still no uniform cutoff
  (`no_uniform_H2_cutoff`).
- **Unchanged.**
  - The Turing-machine evaluator (#99, C7.5–C7.7) is not built. The mathematical ingredients of a
    polynomial-time simulation are now complete in this regime:
    - mode count (this note);
    - step count (`certified_integrator`, Phase XXVIII);
    - readout robustness (`decision_robust`).
  - I-2, I-16 and I-32 are open.
  - **Classical P versus NP remains unresolved.** This is a statement about simulating one
    restricted physical model, not a lower or upper bound for SAT.

## 1. The mechanism

The analytic weight `e^{σ|k|}`, with `|k| = |k₁| + |k₂|`, almost commutes with products.

**Weight defect** (`aw_defect_le`). Since `|k| ≤ |k − j| + |j|`,

`0 ≤ e^{σ|k−j|}e^{σ|j|} − e^{σ|k|} = e^{σ|k−j|}e^{σ|j|}(1 − e^{−σΔ}) ≤ e^{σ|k−j|}e^{σ|j|}√(2σ)√min(|k−j|, |j|)`.

Here `Δ = |k−j| + |j| − |k| ≤ 2 min(|k−j|, |j|)` and `1 − e^{−x} ≤ √x`. The half derivative falls
on the factor that does **not** carry the `H²` weight.

**Half a derivative in `ℓ¹`** (`summable_size_wt`, `tsum_sqrt_size_co_le`). On `T²_L`,
`Σ_j √|j| |ψ̂_j| ≤ √(SB) ‖ψ‖_{H²}`, with `SB = Σ_k |k|/w_k² < ∞`. The lattice sum converges because
`|k|/w_k² ≤ (2/c)(1 + c²k₁²)^{−3/4}(1 + c²k₂²)^{−3/4}`, `c = 2π/L`. This is where two dimensions
and `H²` control are used. A full derivative would give a divergent sum.

**Commutator** (`comm_mulH_le`). For the complex lift `ṽ = (e^{σ|k|}v_k)_k`,

`‖(vw)~ − ṽ w̃‖_{H²} ≤ C_B √σ A_σ(v) A_σ(w)`, with `C_B = 4√2 √(SB)/L`.

The proof mirrors the `H²` algebra estimate: split `w_k ≤ 2w_{k−j} + 2w_j`, then apply Young's
inequality with the half-derivative `ℓ¹` bound.

**The nonlinearity** (`comm_step`, `comm_Fnl_le`). Telescoping over the nested products of
`F(ψ) = −β|ψ|²ψ + γ|ψ|⁴ψ` gives `‖(F(u))~ − F(ũ)‖ ≤ √σ Q(A_σ(u))`, with
`Q(A) = C_B(2|β| C_A A³ + 4|γ| C_A³ A⁵)`.

## 2. Almost conservation along the Galerkin flow

**Lifted state.** `E_σ` is the analytic lift on `S`, a bounded diagonal operator (`EL`). For
`S`-supported states it agrees with the complex lift.

**Lifted field** (`lift_galerkin_err`). The lift of the Galerkin field differs from the Galerkin
field of the lift by at most `√σ Q(A_σ)`.

**Rates** (`lifted_rates`). The Galerkin field conserves mass and Hamiltonian
(`inner_Lc_galerkin`, `ham_galerkin_zero`, extracted from the conservation proofs). So along an
actual Galerkin trajectory:
- `|d/dt mass(E_σ W)| ≤ 2A·√σ Q(A)`;
- `|d/dt ham(U(t) E_σ W)| ≤ (2(|κ|+1)² A + 2 L_F(A) A)·√σ Q(A)`;

where `A = A_σ(W(t))`.

**Coercivity.** `TorusGlobal.norm_le_apriori` (`γ > 0`) bounds the `H²` norm by mass and
Hamiltonian: `A_σ(W(t)) = ‖E_σ W(t)‖ ≤ Rap(mass, ham)`.

**Continuity argument** (`bootstrap_le`, `galerkin_radius_bound`).
- *Hypotheses:* `A_σ ≤ 2B` on `[0, t)` and `T√σ K_R(B) ≤ 1`.
- *Rates:* the mass and the Hamiltonian of the lifted state change by at most 1 on `[0, t]`.
- *Conclusion:* `A_σ(W(t)) ≤ Rap(A₀² + 1, E(A₀) + 1) ≤ B`.
- The argument takes the first time the norm reaches `2B` (an infimum of a closed set) and
  derives a contradiction.

**Polynomial radius** (`σpoly`, `galerkin_radius_poly`). `σ_T = min(σ₀, (1 + K T)^{−2})`
satisfies `T√σ_T K ≤ 1`.

**Why no Bourgain spaces are needed.** The Phase XXIX note expected that polynomial radius bounds
would need dispersive smoothing. Here the conserved Hamiltonian already controls `H²`, and in two
dimensions `H²` controls half a derivative in `ℓ¹`. That is enough for the `√σ` commutator with
plain energy estimates.

## 3. Theorems

| Theorem | Statement |
|---|---|
| `one_sub_exp_neg_le_sqrt`, `aw_defect_le`, `aw_defect_le_left` | the weight defect bound |
| `summable_fq`, `size_div_wt_sq_le`, `summable_size_wt`, `tsum_sqrt_size_co_le` | `SB < ∞`; half a derivative in `ℓ¹` |
| `elift` and its algebra (`elift_add`, `elift_sub`, `elift_smul`, `elift_conjH`, `norm_elift`, `co_elift`) | the complex analytic lift |
| `comm_mulH_le` | the `O(√σ)` commutator with the `H²` product |
| `comm_step`, `comm_Fnl_le` | the remainder of the nonlinearity |
| `EL`, `EL_eq_elift`, `EL_U`, `EL_trunc`, `EL_trunc_elift`, `lift_galerkin_err` | the lifted Galerkin field |
| `inner_Lc_galerkin`, `ham_galerkin_zero`, `lifted_rates` | `O(√σ)` rates of the lifted mass and Hamiltonian |
| `bootstrap_le`, `galerkin_radius_bound` | almost conservation: `A_σ ≤ B` on `[0, T]` when `T√σ K ≤ 1` |
| `σpoly_spec`, `galerkin_radius_poly` | the polynomial radius `σ_T = min(σ₀, (1+KT)^{−2})` |
| `BR_mono`, `energyBudget_mono`, `potBudget_mono`, `anorm_trunc_le` | monotonicity of the constants |
| `galerkin_detector_poly` | the Galerkin–Galerkin detector bound at the polynomial radius |
| `pde_detector_poly` | the continuum detector bound at the polynomial radius |

## 4. What the result does and does not say

- **It is an upper bound on simulation cost** for Fourier truncation in the restricted analytic
  regime (`γ > 0`, analytic data). It is not a lower bound for anything.
- **The constants are large but polynomial.** `K = K_R(B)` is a polynomial of degree 10 in `B`,
  with factors up to `C_A⁷ C_B`. The bound is therefore far below the numerical radii of the Phase XXIX
  probe at moderate times. That probe saw σ ≈ 0.3–0.7 for `t ≤ 40` and log–log slopes up to 1.26,
  below the proved asymptotic exponent 2.
- **The general `H²`-admissible class is unchanged.** It has no analyticity radius, and Phase XXIII
  shows it admits no uniform cutoff.
- **The remaining work for `P_phys ⊆ P_TM` in this regime is machine-side:**
  - the arithmetic library (C5, C6);
  - the uniform Turing-machine evaluator and its runtime (C7.5–C7.7, #99).
- **Separation is unaffected.** `CrossingSAT.SATLowerBound` is neither proved nor refuted.
  **Classical P versus NP remains unresolved.**

## 5. Progress (registry)

```
C3   Spatial complexity and the analyticity radius                                [####################] 100% (6/6)    90%
C7   End-to-end continuum evaluator, P_phys in P_TM (#99, I-11)                   [#############.......]  67% (6/9)    70%
C12  Classical P versus NP                                                        [....................]   0% (0/1)     0%
```

- C3.5 is proved and C3.6 is refuted, so C3 moves from 4/6 to 6/6.
- C7.4 also cites `pde_detector_poly`.
- The ledger is unchanged. I-11 stays Restricted, and its subjective estimate moves from 84% to
  88%.

## Verification

Local, Lean 4.23.0, on the Lean tree of this branch:
- `lake build PVNP` passed (7,441 jobs). `PVNP.AnalyticAlmostConservation` builds without warnings
  and uses no `sorry`, `admit`, `native_decide` or custom axiom. One theorem (`comm_mulH_le`) sets
  `maxHeartbeats 400000`; `CookLevinMain` already does the same.
- The full transitive axiom audit (`audit/check_axioms.py`) runs over all 1,433 registered
  declarations: the 1,383 earlier ones and the 50 new theorems. The result is recorded on the
  pull request.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head.
