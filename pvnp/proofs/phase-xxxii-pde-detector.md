# Phase XXXII: the dynamic detector theorem for the continuum PDE (27 November 2026)

Base: `main` at `fc143c1` (PR #115 merged). New Lean module: `lean/PVNP/DetectorPDE.lean`.

## Outcome

- **Proved (kernel-checked), registry C2.5.** The detector-specific bound holds for the actual
  frozen PDE solution, not only between Galerkin trajectories. The doubled exponent
  `e^{−2σ_T N}` survives the continuum limit. All hypotheses are explicit.
- With C2.5 discharged, the detector category C2 is complete: 5/5.
- **Unchanged.**
  - The spatial obstruction is the analyticity radius `σ_T = σ₀4^{−⌊T/τ⌋}`. A polynomial lower
    bound on it is open (C3.5).
  - The composable Turing-machine infrastructure and the evaluator (#99) are not built (§3).
  - I-2, I-16 and I-32 are open.
  - **Classical P versus NP remains unresolved.**

## 1. The theorem (`DetectorPDE.pde_detector_dynamic`)

**Hypotheses:**
- `L > 0` and `γ > 0`;
- `χ` is real with `A_{σ₀}(χ) < ∞`;
- `w` is the interaction-picture frozen PDE solution, with `‖w(t)‖_{H²} ≤ R` and `‖w(0)‖ ≤ B`;
- `uniformRadius(B) ≤ R`, `2R ≤ M`, and `A_{σ₀}(w(0)) ≤ M`;
- `W` is the coarse Galerkin trajectory on `S` with `W(0) = P_S w(0)` and `‖W(t)‖ ≤ R`;
- every mode outside `S` has size `≥ N`.

**Conclusion.** With `τ = tstep(M)` and `σ_T = σ₀4^{−⌊T/τ⌋}`, the physical readouts satisfy

`|J(U(T)w(T)) − J(U(T)W(T))| ≤ 4 C_A A_{σ_T}(χ) M e^{−2σ_T N} ((A_{σ_T}(w(0))² + G(2M)²T) e^{(2K_F(2M)+1)T})^{1/2}`.

**Proof.** Fix `ε > 0`.
1. **Finer mode set** (`cutoffBox`, `exists_finer_set`). Let `S' = S ∪ {|k₁|, |k₂| ≤ ⌈N'⌉}`,
   where `N'` meets the cutoff condition of `Analytic.analytic_galerkin_pde_error` for `ε`.
2. **Global fine trajectory** (`TorusGalerkin.exists_uniform_galerkin`). It exists on `S'` with
   `W'(0) = P_{S'}w(0)`. Its `H²` bound `uniformRadius(B) ≤ R` does not depend on `S'`.
3. **Analytic bounds.** `Analytic.galerkin_analytic`, `radius_mono` and `asq_mono` give
   `A_{σ_T}(U(t)V(t)) ≤ 2M` on `[0, T]` for `V = W` and `V = W'`.
4. **Coarse versus fine** (`DetectorDynamic.galerkin_detector_dynamic_data`). This bounds the
   detector difference by the right-hand side, independently of `S'`.
5. **Fine versus PDE.** By `analytic_galerkin_pde_error`, `‖Lc(W'(T) − w(T))‖ ≤ ε`. With
   `Lc_U`, `norm_U` and `weak_detector_lipschitz`, the detector gap is `≤ C_det·2R·ε`.
6. **Limit.** The bound holds with an extra `+ C_det·2R·ε` for every `ε > 0`. Then
   `le_of_forall_pos_le_add` removes it.

**Mode count.** Unchanged from the Galerkin version: polynomially many Fourier modes suffice for
a margin-`m` readout of the actual PDE when `T = O(τ log n)`. Beyond that horizon, the proved
cutoff is exponential because of the radius bound.

## 2. Hypotheses, stated plainly

- **`γ > 0`** (defocusing quintic term). It gives global Galerkin existence with a
  cutoff-independent `H²` bound.
- **Analytic initial data.** This is the restricted analytic regime of Phase XXIX.
- **The PDE solution's `H²` bound `R`.** For actual solutions it follows from conservation
  (`apriori`).
- **No hypothesis on the fine trajectories.** They are constructed inside the proof.

## 3. Composable Turing-machine programs (status and design)

The sweep-program model (`PVNP.Discrete.Sweep.Prog`) bundles its data alphabet `D`. Composing two
verified programs therefore needs three things:
- an **alphabet-parametrized program type** `ProgOn D`, with `Prog = Σ D, ProgOn D`;
- **sequential composition** `seq A B e` with instruction set `A.I ⊕ B.I` and buffers
  `A.B ⊕ B.B`. A's transition into its exit instruction `e` is redirected to B's start;
- **first-arrival reachability.** The existing programs end in a `done` instruction that loops
  with identity trips. A `Reach` proof may include such loops, which would break exact cost
  addition. A composition theorem with exact charged costs needs arrival at the exit for the
  first time, `ReachFirst`.

**Composition theorem to prove.**
- *Hypotheses:* A first-arrives at `e` from `(a, l)` with output `l₁` and cost `c₁`, and B reaches
  `(e_B, l₂)` from `(B.start, l₁)` with cost `c₂`.
- *Conclusion:* `seq A B e` reaches `(inr e_B, l₂)` from `(inl a, l)` with cost exactly `c₁ + c₂`.
  The compiled machine follows by `Prog.reach_run`.

The existing primitives (`div_loop`, `mul_loop`, the adders) construct first-arrival paths. They
must be restated in `ReachFirst` form; the change is mechanical.

None of this is built in this phase. Signed, rational, fixed-point and complex arithmetic, the
constants, convolution, the Taylor recurrence and the evaluator all depend on it. Issue #99 stays
open.

## 4. The spatial barrier and separation

No new result.
- **Spatial.** The polynomial radius question is unchanged. The detector theorems show it is the
  only remaining spatial obstruction in the restricted analytic regime. This is a sufficient
  condition, not a lower bound on simulation cost.
- **Separation.** `CrossingSAT.SATLowerBound` is unchanged: neither proved nor refuted, and no
  polynomial-time SAT algorithm. **Classical P versus NP remains unresolved.**

## 5. Progress, computed from obligations

```
PVNP Phase XXXI | bars computed from obligations; subjective estimates labelled separately
     category                                                                                           computed   subjective (not computed)
C1   Detector-specific bound, static truncation                                   [####################] 100% (5/5)   100%
C2   Detector-specific bound, Galerkin dynamics                                   [####################] 100% (5/5)   100%
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

Local, Lean 4.23.0, on the Lean tree of commit `af51127`:
- `lake build PVNP` and the full transitive axiom audit (`audit/check_axioms.py`) are run on this
  tree. The four new declarations of `DetectorPDE` are registered, bringing the total to 1,312.
- The hosted workflow builds the modules and audits all registered declarations at the
  pull-request head. The local results are recorded on the pull request.

Later commits change documentation, the obligation registry, and generated dashboard data only.
The dashboard, status registry, manuscript-alignment and release-document checks pass, as do the
Python suite, the progress check and `git diff --check`.
