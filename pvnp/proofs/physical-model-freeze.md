# Frozen physical computational model `WCT-Phys` and the status of every resource (issue #10, O4–O8)

**ASTRA, 2 November 2026.** This document fixes one physical computational model so that every resource is an explicit function of the input length `n`, and records — resource by resource — what is a kernel-checked theorem, what is an analytic theorem, what is refuted, and what is open. It does **not** claim any physical or classical separation.

## 1. The model `WCT-Phys`

| Component | Frozen specification |
|---|---|
| Input / output | Input `x ∈ {0,1}ⁿ`; output one bit, read once at a declared readout time `t_*(n)`. |
| Geometry | Periodic square `Ω_n = [0, L_n)²` (2-D torus) with side `L_n ≥ 1`; `L_n` is a declared function of `n`. |
| Evolution | Projection-free WCT Hamiltonian `i ∂_t ψ = (Δ+κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ` (source: `wct-pde`, `projection_free.py`), smooth solutions; no forcing during the run. |
| Admissible initial data | `ψ(0) = E_n(x)` where the encoder `E_n` is computed by a uniform polynomial-time TM that outputs a finite Fourier description (frequencies with `|k| ≤ K_n`, coefficients to precision `2^{-b_n}`). |
| Mass / energy | `M_n = ‖ψ(0)‖²₂` and Hamiltonian `H_n`, both charged. |
| Bandwidth | Receiver observes the orthogonal projection onto the `D_n` lattice modes with `|k| ≤ K_n`. |
| Noise / precision | Adversarial receiver error of Euclidean norm `< η_n`; decoder is any function of the noisy projection. |
| Time / latency | `t_*(n)` (physical time) and number of switching events, both charged. |
| Parallelism | One field, one receiver; no external advice. |
| Initialization / preprocessing | Charged as the TM running time of `E_n` plus the bits `b_n · #modes` written into the source. |
| Algorithms | All uniform families `(E_n, t_*(n), K_n, D_n, decoder)` with every resource above bounded by a polynomial in `n`. |

**Resource vector:** `R(n) = (L_n, M_n, H_n, K_n, D_n, 1/η_n, b_n, t_*(n), T_enc(n))`. A language is in `P^{phys}_{WCT}` if some admissible family decides it with every component of `R(n)` polynomially bounded. `NP^{phys}_{WCT}` uses the same rails for a verifier with polynomial-length witnesses.

## 2. Status of each resource inequality

| Resource relation | Status | Evidence |
|---|---|---|
| Finite-radius causality: `R = m + Σᵢ tᵢ rᵢ` cells of causal coverage needed to read a distal bit | **Lean, unconditional (discrete locality model)** | `MultiStageCausality.multistage_required_causal_coverage`, `no_multistage_prefix_last_bit` (PR #14) |
| Receiver packing `N ≤ (1+√M/η)^{2D}` for `N` robustly distinguishable readouts | **Lean, unconditional** for the declared receiver class | `Packing.complex_receiver_packing`, `Packing.subspace_receiver_packing` |
| Mode count `D ≤ (2⌊LK/2π⌋+1)²` | **Lean** | `FourierReceiver.receiver_mode_count` |
| Receiver bandwidth = dynamical bandwidth | **Refuted** (the nonlinearity creates modes outside any finite support) | `FourierReceiver.cubic_quintic_generates_new_modes` |
| Packing ⇒ decision lower bound | **Refuted** (one mode, mass `η²` suffices for every language) | `DecisionVsEncoding.promoted_bound_false`, `robust_decision_readout` |
| `C_{Θ,ε} ≤ ‖Δψ‖²/(4ε²)` | **Lean, unconditional** (Lebesgue integral, any measure) | `PartIIIAnalytic.curvature_cost_le` |
| Energy (first derivatives) controls curvature | **Refuted** | `PartIIIAnalytic.no_gradient_energy_control`, `highfreq_curvature_lower` |
| Distinguishability ⇒ positive curvature cost | **Refuted** | `PartIIIAnalytic.zero_cost_counterexample` |
| Volume-uniform density/curvature floor | **Refuted** (expanding-domain plane waves) | `ExpandingDomain.no_positive_uniform_density_ratio` |
| Static storage needs exponential curvature | **Refuted** (O(n) storage) | `CurvatureBarrier.localStorageCost_le_n`, `graphStorageCost_le_n_mul_d_sq` |
| Expander/Tseitin hardness for every algorithm | **Refuted as stated** (GF(2) elimination) | `Tseitin.parity_sum_zero`, `odd_charge_unsatisfiable`; analytic Gaussian-elimination bypass |
| Curvature as a discrete resource beyond time | **Lean, refuted**: every poly-time discrete run has poly curvature for every embedding | `Discrete.P_TM_eq_curvature_rail` |
| Curvature is a representation-invariant cost | **Lean, refuted** | `Discrete.curvature_not_representation_invariant` (time *is* invariant: `WCC.relabel_decides`) |
| Existence/conservation for the frozen PDE (well-posedness) | **Open in Lean**; analytic for smooth periodic solutions (mass/Hamiltonian conservation) | `pvnp/proofs/wct-pde-transport-bound.md` |
| Nodal/phase coercivity with uniform constants as `L_n → ∞` | **Open** (fixed-domain version only) | `FixedMassNodal`, `PhaseObservability` |
| Simulation `P^{phys}_{WCT} ⊆ P_TM` (physical runs simulable in poly time) | **Open** (needs PDE numerical analysis with certified error at precision `η_n`) | — |
| Simulation `P_TM ⊆ P^{phys}_{WCT}` (realize any TM in the PDE within rails) | **Open** | — |

## 3. The universal resource statement (#10 D)

**Question.** Is there a resource bound that every correct decider for an NP-complete language must obey within `WCT-Phys`?

**What is proved.**

1. *Discrete shadow is exactly classical.* For the discrete WCC model, any universal superpolynomial lower bound on time **or** on discrete curvature for an NP language is equivalent to a classical lower bound: `Discrete.lower_bound_transfer`, `Discrete.curvature_lower_bound_is_classical`, `Discrete.p_vs_np_discrete_transfer`. So no discrete-WCC argument can yield the universal statement without proving `P ≠ NP`.
2. *Every currently proposed physical resource bound fails as a decision bound.* The packing bound is universal over codebooks but provably not over deciders (`promoted_bound_false`); curvature is neither energy-controlled nor representation invariant; the density floor fails on expanding domains.

**What is open (exact missing implications).**

- (M1) A two-way polynomial simulation between `WCT-Phys` and `TM` *with all rails preserved*. Without it, a physical separation (if one were proved) does not transfer to `P_TM ≠ NP_TM` (O9).
- (M2) A theorem forcing every admissible correct decider to create `2^{Ω(n)}` robustly distinguishable intermediate receiver states at a charged cut. Only then does the packing theorem give `M_n` or `D_n` superpolynomial. No such theorem exists, and `robust_decision_readout` shows the *output* cut never forces it.
- (M3) Global well-posedness and uniform-in-`L_n` coercivity constants for the frozen PDE.

**Classification:** the universal statement is **OPEN**; every concrete universal candidate tested here is **REFUTED** at its stated scope; the discrete version is **PROVED equivalent to classical P ≠ NP**.
