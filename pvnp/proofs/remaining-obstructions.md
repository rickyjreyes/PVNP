# Remaining obstructions and obligations (updated November 6, 2026; Phases VI, VIII, IX and X integrated)

Each item gives the precise missing statement, what has already been proved around it, and why it
is not closed. None of these items is assumed by any kernel-checked PVNP theorem. Each appears
either as an explicit premise of a conditional theorem or not at all.

## Part II: generality of the discrete equivalence

**D-1. Multidimensional converse — CLOSED (kernel-checked, 5 November 2026).**
`P_WCCD d = P_TM` and `NPOf (P_WCCD d) = NP_TM` for **every** `d`
(`PVNP.Discrete.P_WCCD_subset_P_TM`, `P_WCCD_eq_P_TM`, `NP_WCCD_eq_NP_TM`, in
`lean/PVNP/WCCDSweepMain.lean`).
- *Machine.* `WCCDSweep.toTM A` is an ordinary `PVNP.Discrete.TM`: a finite state set, a finite tape
  alphabet, one head with moves `L/S/R`, and the shared `FirstAnswer`/`DecidesAt` semantics. It is
  obtained by compiling an explicit 23-instruction round-trip sweep program (`WCCDSweep.prog`) with
  the generic compiler `Sweep.Prog.toTM` (`SweepTM.lean`). Each instruction is one left-to-right
  finite-state transduction, an optional one-cell extension, and one right-to-left transduction. The
  compiler's step count is exact (`reach_run`, `halts_run`, `toTM_firstAnswer`), so every head move is
  charged.
  - There is no random access, no unbounded register and no oracle.
  - Every coordinate operation is done by unary markers that move one cell per pass.
- *Simulation.*
  - The `(1+d)`-dimensional configuration is flattened to a cyclic array on `ℤ/Nℤ` with
    `N = M^(d+1) + 1` and `M = n + 2G + 3`. This is exact for rounds `≤ G` (`WCCDCyclic.lean`:
    `flat_inj`, `cyclic_exact`, `cyclic_out`).
  - One round rotates the `3^(d+1)` window tracks by `±M^k` with count-down markers started at
    reference cells `M^k` (`loopL`, `loopR`, `axis_step`, `axes_run`, `round`), then applies the local
    rule.
  - The reference cells are built by unary loops (`inner_loop`, `outer_loop`, `build_axes`,
    `xfin_inv`).
  - Horizons `G = 0, 1, 2, …` are tried in turn (`restart`, `enter`, `guesses`).
- *Decision semantics.*
  - At every check, the tape answer equals the WCCD output `A.out x t` exactly. This includes
    accepting or rejecting blank exteriors and acceptance precedence (`arrAns_eq`).
  - The TM's first answer is the WCCD's first answer (`halts_of_first`).
- *Explicit polynomial.* If `A` decides `L` in time `T`, then `toTM A` decides `L` within
  `(128 d + 421)·(n + 2T(n) + 3)^(2d+3)` steps (`toTM_decides`). The class theorem uses the witness
  `C(128d+421)·(X + 2p + 3)^(2d+3)`.
- *Axioms:* `propext`, `Classical.choice`, `Quot.sound` only.
- *Scope.* This is the discrete model equivalence for the frozen WCCD model: radius-one Moore
  neighbourhood, origin-marked input on the first axis, and existential output with acceptance
  precedence. It gives no information about classical `P` vs `NP`, the continuum PDE or physical
  devices.
- *Superseded groundwork* (still valid, no longer the frontier): `WCCDFiniteSupport`,
  `WCCDFiniteSnapshot`, `WCCDFiniteWork` and `TMStackScan` (PRs #21, #23, #24).

**E-1. Encoders.** No obligation. With polynomial-time encoders the class equality is trivially true,
because the encoder can compute the answer. With unrestricted encoders, or with one advice bit, it is
false (`unrestricted_encoder_trivializes_WCC`, `advice_bit_trivializes`). The meaningful theorem is
the fixed-encoding one, which is proved (`P_WCC_enc_id`).

## Phase 7: Cook–Levin (decision: **not necessary; isolated as CL-1**)

**CL-1.** Missing:
- every `L ∈ NP_TM` many-one reduces in polynomial time to `SATV.SAT_dense`;
- `P_TM` is closed under such reductions, which requires composing TMs.

No current claim needs CL-1:
- `curvature_lower_bound_is_classical`, `SAT_curvature_transfer`,
  `physical_SAT_lower_bound_is_classical` and `p_vs_np_discrete_transfer` use only
  `SAT_dense ∈ NP_TM`, which is proved (`SAT_dense_mem_NP_TM`).
- CL-1 would only add *converse* statements such as `P_TM ≠ NP_TM → SAT_dense ∉ P_TM`, or "the
  conjecture `conj:wcc_depth` is equivalent to `P ≠ NP`".

Formalizing CL-1 needs a TM-composition library and a tableau encoding of TM runs into the dense CNF
format. It is a large, self-contained project.

**CL-1, Phase X update (6 November 2026): the non-uniform part is CLOSED.**
- `CircuitCookLevin.SAT_dense_mem_Ppoly_iff` proves `SAT_dense ∈ Ppoly ↔ NP_TM ⊆ Ppoly`. Every
  `NP_TM` language reduces to `SAT_dense` by explicit projections of polynomial length:
  - verifier tableau circuits (`TMCircuit.tableau`);
  - the Tseitin transformation (`tseitin_sat_iff`);
  - the dense encoding as a projection (`encDense_full`).
- **Still open: the uniform part.** It needs a polynomial-time TM that computes the reduction, and
  closure of `P_TM` under it. Only the uniform part would give `P_TM ≠ NP_TM → SATLowerBound` and
  II-24. See `phase-x-circuit-route-status.md`.

## M1: two-way physical ⇄ TM simulation

- *Proved:* without charged encoders or decoders the physical class is trivial
  (`PhysicalAudit.unrestricted_encoder_trivializes`, `unrestricted_decoder_trivializes`).
- *Proved:* with polynomial-time indicator encoders it contains, and for that encoder class equals,
  `P_TM` at constant mass, zero curvature energy and two final states
  (`P_TM_subset_PhysConst`, `PhysConst_polyEnc_eq_P_TM`).
- *Missing (M1-a):* `P^phys_WCT ⊆ P_TM` for general rail-bounded devices. That is, for every admissible
  device family with polynomial rails `(L_n, M_n, H_n, K_n, D_n, 1/η_n, b_n, t_*(n))`, a TM must
  compute the receiver output to accuracy `η_n/3` in time `poly(n)`. This requires certified
  numerical analysis of the frozen PDE: stability plus error bounds for a discretization. The
  lattice model (`WCTLattice`) supplies the conservation and coercivity estimates such an argument
  would use, but no convergence or error theorem is proved.
- *Missing (M1-b):* `P_TM ⊆ P^phys_WCT` with a **language-independent** encoder. That is, a physical
  realization of TM computation inside the PDE evolution itself, rather than in the encoder. No
  construction exists.

## M2: universal physical lower bound

- *Proved obstruction:* for any encoder class containing polynomial-time indicator encoders, a
  physical lower bound for dense SAT implies `P_TM ≠ NP_TM` (`physical_SAT_lower_bound_is_classical`).
  M2 is therefore at least as hard as the classical problem.
- *Proved obstruction:* at the output cut, packing never forces large resources
  (`DecisionVsEncoding.robust_decision_readout`, `promoted_bound_false`).
- *Proved obstruction:* a fixed sign code stores `2ⁿ` labels at mass `n`
  (`DecoderUniformity.number_of_labels`, `signCode_mass`).
- *Strongest restricted theorems:*
  - the receiver packing bounds (`FourierTorus.torus2_bandlimited_packing`);
  - the split-input transcript bounds `2ⁿ ≤ (1 + A/η)ᵐ` (`AnalogSplitSAT.analog_split_sat_capacity`,
    under rectangle and robust-decoding premises);
  - the transport bound `∫‖Az‖² ≥ δ⁴/(Γ⁴T³)` (`WCTLattice.lattice_curvature_time_bound`; continuum
    form `TransportCalculus.curvature_time_lower_bound` with the flux premise).
- *Precise missing implication:* every admissible correct decider for an NP-complete language must
  create `2^{Ω(n)}` robustly distinguishable intermediate states at a *charged* cut, or a detected-mass
  change `δ_n` with `δ_n⁴/(Γ_n⁴ T_n³)` superpolynomial. Neither is known, and by the obstruction above
  either would imply `P ≠ NP` once the encoder is polynomial time.

### M2, Phase VIII update (6 November 2026)

The crossing-sequence route is now fully formalized for the ordinary single-tape `Discrete.TM`.

- `CrossingHennie` proves the complete splicing theorem.
- `CrossingSAT` and `CrossingSATSets` derive SAT mixed acceptance and the time lower bounds
  `T(N) = Ω(N^{3/2}/log|Λ|)` (split family) and `T(N) = Ω(N²/(log N · log|Λ|))` (set family).
- `sat_not_linear_time` rules out linear-time single-tape SAT deciders.

This is the ceiling of crossing-sequence counting: at most `N` bits cross a cut, and there are at
most `N + 1` cuts. Both hard families are decidable in polynomial time. The precise missing
implication is `CrossingSAT.SATLowerBound` (`SAT_dense ∉ P_TM`), which would give `P_TM ≠ NP_TM`
(`P_ne_NP_of_satLowerBound`). It is open; see `phase-viii-separation-status.md`.

### M2, Phase IX update (6 November 2026)

- **The target is fixed exactly.** The per-input statement is: every correct `SAT_dense` decider
  exceeds `C·|x|^k` first-answer steps on arbitrarily long inputs, for every `k` and every `C > 0`.
  - `SATTarget.satLowerBound_iff_superpolynomial` and `satLowerBound_iff_superpolynomialReal`
    prove it equivalent to `SATLowerBound`.
  - `satLowerBound_iff_wccDepth` and `satLowerBound_iff_wccdDepth` prove it equivalent to Part I
    `conj:wcc_depth` for `SAT_dense`.
- **Candidate invariants tested.** Each fails one of the two required implications: (A) every
  decider incurs it; (B) incurring it forces superpolynomial time.
  - *Constraint dependencies and global consistency* (resolution cost, expansion): (A) fails.
    Tseitin instances of `SAT_dense` are decided by component parity
    (`TseitinSAT.tseitin_mem_SAT_dense_iff_comp`, `tseitin_connected_iff`), although resolution
    needs `2^{Ω(m)}` on expanders (literature, not formalized).
  - *Crossing information* ("many distinguishable states"): (B) fails. `V_SAT ∈ P_TM` carries
    quadratic crossing information (`VerifierCrossing.crossingInfo_not_superpolynomial`).
  - *Circuit size*: (A) holds by the standard tableau simulation, but (B) is open and strictly
    stronger than the target (`SAT ∉ P/poly`).
  - *Curvature*: equivalent to the classical statement (`curvature_lower_bound_is_classical`).
- **Precise missing implication: unchanged.** It is `SATLowerBound`, in any of its proved-equivalent
  forms. It is open. See `phase-ix-universal-lower-bound-status.md`.

### M2, Phase X update (6 November 2026)

- **Proved: every algorithm incurs circuit size.** `TMCircuit.P_TM_subset_Ppoly`: every
  single-tape decider running in time `T` yields circuits of size `(T+1)(2T+3)·c_M`.
- **Proved: the circuit route reaches the premise.** By
  `CircuitCookLevin.satLowerBound_of_NP_not_Ppoly`, if any language in `NP_TM` requires
  superpolynomial circuits, then `SATLowerBound`, and hence `P_TM ≠ NP_TM`.
- **Open: the lower-bound half.** It requires a superpolynomial circuit lower bound for an NP
  language. The best known general lower bounds for explicit functions are linear.
- **Decisive premise: unchanged.** It is still `SATLowerBound`. See
  `phase-x-circuit-route-status.md`.

## M3: the frozen PDE `i∂ₜψ = (Δ+κ)²ψ − β|ψ|²ψ + γ|ψ|⁴ψ`

| Item | Status |
|---|---|
| Whole plane `ℝ²`, data in `H²` (`γ > 0`): global existence, uniqueness, continuous dependence, mass and Hamiltonian conservation, a priori bound `‖u‖²_{H²} ≤ 3(E + 3β²M/16γ) + (2+3k⁴)M` | **Proved externally**, `rickyjreyes/math@30a5ddc` (`ReyesMath.Sobolev.global_wellposed`, `continuous_dependence`, `conservation`, `norm_toSp_sq_le`). Built locally against the pinned Mathlib; only standard axioms. Definition match proved in `lean/bridge/MathBridge.lean`. |
| Lattice system on `ℤ/Nℤ`: local existence, exact conservation, uniform coercivity, flux inequality | **Proved in PVNP** (`WCTLattice`) |
| **M3-T** Periodic torus `T²_L`: global `H²` well-posedness | **CLOSED in Lean (PR #40).** `PVNP.Torus.global_wellposed`, `conservation`, `apriori`, `continuous_dependence` for `L > 0`, `γ > 0`, for the specified Fourier-coefficient `IsSolution` of the frozen PDE. The a priori H² bound is uniform in `L`; this does not prove uniform spectral gap, detector efficiency or M3-C convergence. See [Phase VI scope](phase-vi-torus-flux-status.md). |
| **M3-U** Constants uniform in `L` | Bandpass coercivity `‖(Δ+κ)ψ‖² ≤ H + (3β²/16γ)M` is uniform: **proved**, in integrated form (`TransportCalculus.hamiltonian_controls_bandpass`) and on the lattice for every `N` (`WCTLattice.bandpass_le_ham`). Poincaré/spectral-gap coercivity is **false** uniformly in `L`, with sharp constant `(2π/L)²` (`SpectralGap.no_uniform_poincare`, `wirtinger_sharp`). The density floor fails on expanding tori (`WCTPlaneWave.expanding_domain_countermodel`). |
| **M3-G** Global existence for the lattice ODE | **PROVED in Lean** (`WCTLattice.global_wellposed`, `exists_global_solution`, `global_solution_unique`, `exists_global_conserved_bounded`), merged PR #22 at `4acb9d8`; global flow for every finite nonempty lattice and arbitrary real coefficients. |
| **M3-C** Lattice → continuum convergence with certified error bounds | **Open.** This is also the missing piece for M1-a. |
| Stability of plane waves / orbital stability on tori | **Open.** External orbital-stability work in `rickyjreyes/math` (`OrbitalStability.lean`) concerns `ℝ²` minimizers and was not audited here. |

## Phase 3: the flux inequality `|J'(t)| ≤ Γ√D(t)`

- **Lattice: derived in Lean** (`WCTLattice.hasDerivAt_flux`, `flux_bound`,
  `lattice_flux_inequality`):
  - `J' = 2 Im⟨[A,w]z, Az⟩` exactly, because the cubic–quintic term is a real multiple of `z` and
    drops out;
  - `|J'| ≤ 4|a| ω √M ‖Az‖`;
  - hence `|J'| ≤ Γ√‖Az‖` with `Γ = 4|a|ω√M₀ (H₀ + 3β²M₀/16γ)^{1/4}`.
- **F-1 (continuum, CLOSED for the specified periodic-torus model; PR #40).** `PVNP.Torus.flux_identity` derives the localized-mass derivative along a PDE solution, and `flux_inequality` / `flux_inequality_explicit` bound it by `Gam … * sqrt (‖Dc L (u t)‖)`. `curvature_time_bound` integrates this estimate under explicit `L > 0`, `γ > 0`, real regular detector, derivative bounds, `T > 0`, and `Γ > 0` assumptions. The earlier `TransportCalculus` theorem remains conditional on its abstract flux premise; it is now instantiated by the torus PDE proof, not promoted to arbitrary detectors or continuum models. See [Phase VI scope](phase-vi-torus-flux-status.md).
- **Why the inequality has the `√D` form.** In the continuum derivation, `D = ‖Δψ‖₂` is the norm.
  The `κ`-term of the flux contributes `4κ a P ‖∇ψ‖ ≤ 4κ a P^{3/2} √D`. That term is what forces the
  `√D` form. The stronger form `|J'| ≤ Γ D` does not follow from this argument, and it is not
  claimed.

## Not claimed

Classical `P ≠ NP`. A physical `P ≠ NP`. Any universal SAT or curvature lower bound. Any physical
realization of discrete WCC with curvature preserved.
