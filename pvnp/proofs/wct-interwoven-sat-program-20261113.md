# Interwoven-Ψ SAT on the frozen WCT torus: energy model, device bound, countermodel, resource barrier

**Date:** 13 November 2026
**Base:** `main` after PR #89 (merge `0e77ba1`)
**Lean:** `lean/PVNP/InterwovenSAT.lean`, `lean/PVNP/WCTSATDevice.lean`, `lean/PVNP/WCTSATScaling.lean`
**Status:** kernel-checked with the pinned Lean 4.23.0 (see Verification). No `sorry`, `admit`,
`native_decide` or new axiom.

This note answers four questions in order.

1. Does SAT correspond to the ground states of an interwoven wavefield once coupling and
   curvature energies are added to the logical penalty? (Phase B)
2. On the actual frozen torus equation, what must a SAT-correct physical readout pay, and which
   of the assumptions behind that bound are necessary? (Phase C)
3. Can SAT force superpolynomial physical resources on every admissible uniformly encoded
   frozen-WCT solver? (Phase D)
4. Would such a physical bound transfer to classical Turing machines? (Phase F)

Nothing here proves `P_TM ≠ NP_TM` or `P_TM = NP_TM`.

## Summary

| Question | Outcome | Lean |
|---|---|---|
| SAT ⟺ zero ground energy, with coupling and curvature | **False** for sign-sensitive (naive) coupling or curvature; **true** for sign-blind terms; the exact criterion for any added energy `C ≥ 0` is proved | `naive_Emin`, `satisfying_not_ground`, `sat_iff_EminSB_eq_zero`, `locks_iff_sat_iff` |
| "SAT ⟺ ∃Ψ, E_F[Ψ] = E_min(F)" | **False** (every formula, satisfiable or not, attains its minimum); repaired as `SAT ⟺ E_min(F) = 0`, `UNSAT ⟺ E_min(F) ≥ 1/8` | `min_formulation_vacuous`, `sat_iff_EminSB_eq_zero`, `unsat_iff_EminSB_ge` |
| I-37 with the locking constraints defined | **Holds** for sign-blind flux terms, **fails** for sign-sensitive ones | `toroidal_locking_iff_unsat`, `naive_toroidal_locking_fails` |
| Device-form readout bound `d⁴ ≤ G⁴T³(B_SAT + B_UNSAT)`, `d = m − ρ − ε/2` | **Proved**, without the earlier hypothesis `Γ > 0`, with `G` bounded by the prepared mass and energy | `device_pair_budget`, `device_pair_budget_of_preparation` |
| Can the encoder bypass the transport cost? | **Yes.** Exact frozen-torus solutions read the correct answer at time zero with zero curvature budget | `preloaded_device`, `zeroMode_isSolution` |
| Is the initial-blindness hypothesis necessary? | **Yes.** Without it the bound is false | `blindness_necessary` |
| Superpolynomial resources for SAT over every admissible solver | Proving it, for any class containing the charged zero-mode devices, **proves `P_TM ≠ NP_TM`**; in the zero-mode class it is **equivalent** to `P_TM ≠ NP_TM` | `superpoly_SAT_implies_P_ne_NP`, `zeroSuperpoly_SAT_iff` |

## Phase B: the interwoven-Ψ model (`PVNP.InterwovenSAT`)

### Definitions

A 3-CNF formula `F` (`PartIPsiSat.CNF3`) over variables `0, 1, 2, …` is encoded by one complex
amplitude `ψᵢ = Aᵢ e^{iθᵢ}` per variable.

| Ingredient | Lean | Definition |
|---|---|---|
| Binary phase encoding | `PartIPsiSat.fieldOf`, `phaseOf` | `xᵢ = 1 ↦ ψᵢ = 1` (phase `0`), `xᵢ = 0 ↦ ψᵢ = −1` (phase `π`) |
| Variable-to-field map, shared-variable consistency | `fieldOf` | a variable occurring in several clauses is one field `ψᵢ` |
| Clause-to-coupling map, logical penalty | `Elog F Ψ = Elogic (arg ∘ Ψ) F` | `Σ_c Π_k (1 − s(ℓ_k; θ))`, `s = (1 + η cos θ)/2` |
| Interaction hypergraph / graph | `hyperedges`, `edges`, `vars` | one hyperedge per clause; one edge per pair of literal slots |
| Coupling energy | `Ecoup F Ψ` | `Σ_{(a,b) ∈ edges} (1 − Re ψₐ ψ̄_b)` |
| Geometric curvature energy | `Ecurv F Ψ` | `Σ_edges |ψₐ − ψ_b|² + Σ_v |(ΔΨ)_v|²` (graph gradient and Laplacian) |
| Admissible fields `𝒜` | `Admissible` | `|ψᵢ| = 1` for every `i`: the configuration space is the phase torus |
| Naive total energy | `energy F λ μ` | `E_logic + λ E_coupling + μ E_curv` |
| Sign-blind total energy | `energySB F λ μ` | coupling and curvature applied to `Ψ² = (ψᵢ²)ᵢ` |
| Ground energy | `Emin`, `EminSB` | `inf_{Ψ ∈ 𝒜} E_F[Ψ]` |
| Locking configuration | `Locks C F Ψ` | `Ψ ∈ 𝒜` and `E_logic(Ψ) + C(F, Ψ) = 0` |
| Measurement | `measure_satisfies` | read the signs `[Re ψᵢ ≥ 0]` |

### The naive model fails (phase frustration)

`F_xor = (x₀ ∨ x₁ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁ ∨ ¬x₁)` is satisfiable, and every solution has `x₀ ≠ x₁`,
i.e. opposite phases across the coupled pair. `G = (x₀ ∨ x₀ ∨ x₀) ∧ (¬x₀ ∨ ¬x₀ ∨ ¬x₀)` is
unsatisfiable. For every `λ, μ ≥ 0`:

* `xor_energy_pos`: if `4μ + 2λ > 0`, every admissible field has `E_{F_xor} > 0`.
* `xor_energy_ge_quarter`, `xor_energy_at_I`: if `4μ + 2λ ≥ 1/12`, `E_{F_xor} ≥ 1/4` on `𝒜`,
  attained at `ψ ≡ i`.
* `single_var_energy`: `E_G ≥ 1/4` on `𝒜`, attained at `ψ ≡ i`.
* `naive_Emin`: `E_min(F_xor) = E_min(G) = 1/4` once `4μ + 2λ ≥ 1/12`. The ground energy does not
  distinguish a satisfiable from an unsatisfiable formula.
* `satisfying_not_ground`: if `4μ + 2λ > 1/16`, every satisfying assignment of `F_xor` has more
  energy than the non-binary field `ψ ≡ i`. **A satisfying assignment need not minimise the total
  physical energy.**
* `naive_zero_energy_fails`, `naive_threshold_fails`: `SAT ⟺ ∃Ψ ∈ 𝒜, E = 0` and
  `SAT ⟺ ∃Ψ ∈ 𝒜, E < 1/8` are false.
* `min_formulation_vacuous`: `G` attains its minimum, so "`∃Ψ ∈ 𝒜, E_F[Ψ] = E_min(F)`" holds for
  an unsatisfiable formula. The target statement in that form is false for every energy with a
  minimiser; the reference value must be independent of `F`.

### When does the correspondence survive added terms?

`locks_iff_sat_iff`: let `C(F, Ψ) ≥ 0` on admissible fields. Then

  `(∀F, SAT(F) ⟺ ∃Ψ ∈ 𝒜, E_logic(Ψ) + C(F, Ψ) = 0)`
  `⟺ (∀F, SAT(F) ⟹ ∃Ψ ∈ 𝒜, E_logic(Ψ) = 0 ∧ C(F, Ψ) = 0)`.

So the correspondence survives exactly when the added terms vanish on some satisfying
configuration of every satisfiable formula. The UNSAT side never breaks: `E_logic + C ≥ 1/8` on
`𝒜` for every unsatisfiable `F` and every `C ≥ 0` (`unsat_gap_general`), and any zero is a
satisfiability certificate (`sat_of_locks`). The failure is always on the SAT side, and it is
caused by frustration: a sign-sensitive term charges the opposite phases that some clauses
require.

### The repaired model

With coupling and curvature applied to `Ψ²`, binary phases cost nothing and, for all `λ, μ ≥ 0`:

* `sat_iff_zero_energySB`: `SAT(F) ⟺ ∃Ψ ∈ 𝒜, E^{sb}_F[Ψ] = 0`;
* `sat_iff_EminSB_eq_zero`: `SAT(F) ⟺ E_min(F) = 0`;
* `unsat_iff_EminSB_ge`, `unsat_energySB_gap`: `F` unsatisfiable `⟺ E_min(F) ≥ 1/8`;
* `sat_iff_energySB_lt_eighth`: `SAT(F) ⟺ ∃Ψ ∈ 𝒜, E^{sb}_F[Ψ] < 1/8`;
* `measure_satisfies`: the sign readout of any admissible field with `E^{sb} < 1/8` satisfies `F`.

### I-37 with the locking constraints defined

Part I, §12.3: "a toroidal ψ–electron structure whose phase-locking and flux constraints
correspond to the satisfaction of all clauses. Nonexistence of such a locking configuration is
equivalent to unsatisfiability." With the configuration torus `|ψᵢ| = 1`, clause penalties as the
phase-locking constraints and coupling/curvature as the flux constraints:

* `toroidal_locking_iff_unsat`: with sign-blind flux constraints, no locking configuration
  `⟺` unsatisfiable, for every formula and every `λ, μ ≥ 0`;
* `naive_toroidal_locking_fails`: with sign-sensitive flux constraints (`4μ + 2λ > 0`), the
  satisfiable `F_xor` has no locking configuration.

The gap to the manuscript: its "ψ–electron structure" is a physical field on a spatial torus and
its constraints are not defined; here the structure is the configuration torus of the interwoven
field. The frozen torus dynamics cannot drive a field into a stable lock from outside it
(`Torus.no_locking`, Phase XVIII), so the theorem concerns existence, not reachability.

These are statements about an energy landscape. They give no bound on how long any algorithm or
physical process needs to find a low-energy field.

## Phase C: the frozen torus device (`PVNP.WCTSATDevice`)

### The device form of the bound

A uniform device fixes the torus side `L`, the parameters `κ, β, γ` (`γ > 0`), one real detector
`χ` (`L1q` coefficients), one threshold `τ`, one time `T > 0` and one readout error `ρ`; it maps
each formula to an exact solution of the frozen equation. If it reads every satisfiable formula
at least `m` above `τ` and every unsatisfiable one at least `m` below `τ` after an observation
error at most `ρ`, the two prepared states of a SAT/UNSAT pair differ in reading by at most `ε`,
and both flux constants are at most `G`, then with `d = m − ρ − ε/2 ≥ 0`

  `d⁴ ≤ G⁴ T³ (∫₀ᵀ ‖Δψ_SAT‖² + ∫₀ᵀ ‖Δψ_UNSAT‖²)`  (`device_pair_budget`).

Changes with respect to `PhysicalSATReadout`:

* **`Γ > 0` is not needed.** A zero flux constant freezes the reading (`Jdet_const_of_Gam_eq_zero`,
  from the flux identity and the flux inequality), and `change_budget` handles both cases.
* **`G` is a charged preparation quantity.** `Gam_le_of_bounds`: if the prepared state has mass at
  most `M` and Hamiltonian at most `H`, its flux constant is at most
  `budget a b κ √M (√(H + 3β²M/16γ) + |κ|√M)`, where `a, b` depend only on the detector.
  `device_pair_budget_of_preparation` states the bound with this explicit `G`.

### The preloaded-answer countermodel

`zeroMode_isSolution`: for every `L > 0` and all `κ, β, γ`, the zero-mode state
`ψ(t, x) = L⁻¹ c e^{−iΩt}`, `Ω = κ² − β|c|²/L² + γ|c|⁴/L⁴`, is an exact solution in the
repository's formulation `Torus.IsSolution`. It has zero curvature (`Dc_zeroMode`), mass `|c|²`
(`mass_zeroMode`), and the detector `χ(x) = L⁻¹(1 + cos(2πx₁/L))` reads it as `|c|²/L` at every
time (`Jdet_zeroMode_detector`).

`preloaded_device`: encode the SAT bit in the amplitude (`|c| = 2` if satisfiable, `1` otherwise).
For every `L > 0`, `κ ≠ 0` and all `β, γ`:

* every trajectory is an exact solution, the detector is real with `L1q` coefficients, and every
  flux constant is positive (`Gam_zeroMode_pos`);
* with threshold `5/(2L)` and margin `3/(2L)`, every satisfiable formula reads `4/L` and every
  unsatisfiable one `1/L`, **at every time**;
* the curvature budget is zero on every interval.

`preloaded_skew_eq_contrast`: the initial skew equals the final contrast `2m = 3/L`. The answer is
prepared at time zero and nothing is transported.

`blindness_necessary`: the statement obtained from
`PhysicalSATReadout.sat_pair_readout_resource_disjunction` by dropping the initial-skew hypothesis
(and taking `ε = 0`, its strongest conclusion) is **false**: the preloaded device on the unit
torus with `κ = γ = 1`, `β = 0` satisfies every other hypothesis with zero budgets, and the
conclusion `m⁴ ≤ 0` fails.

**What the countermodel means.** SAT correctness does not force two trajectories with nearly
equal initial readings. The encoder `F ↦ c_F` is a SAT decider, so the countermodel does not make
SAT easy; it shows that a transport lower bound has to charge the encoder or assume blindness.

### Which assumptions are necessary

| Assumption of the device bound | Necessary? | Evidence |
|---|---|---|
| Initial blindness `ε ≤ 2(m − ρ)` with `d > 0` | Yes | `blindness_necessary` |
| One detector and one threshold for all inputs | Yes for any nontrivial bound | with input-dependent decoders every language is decided at constant cost (`PhysicalAudit.unrestricted_decoder_trivializes`) |
| `Γ > 0` | No | removed (`change_budget`) |
| A uniform bound `G` on the flux constants | Only for the combined form; it follows from charged mass and energy bounds | `Gam_le_of_bounds` |
| `γ > 0` | Used by the flux inequality (a priori `H²` bound) | `TorusFlux.flux_inequality` |
| Charging the encoder | Yes for any lower bound on SAT devices | `preloaded_device`, Phase D |

**Scaling.** Even with blindness the bound gives `B_SAT + B_UNSAT ≥ d⁴/(G⁴T³)`. When `d` is at
least an inverse polynomial and `G`, `T` are polynomially bounded, this is an inverse-polynomial
lower bound; it never grows with the formula size by itself.

**Missing lemma (not formalized).** A blind SAT-correct device with constant budget: one exact
solution whose reading changes, `J(ψ(T)) ≠ J(ψ(0))`, paired with a zero-mode state of the same
initial reading. For a two-mode state `a e₀ + b e_{e₁}` the flux identity gives
`J'(0) = (κ² − (κ − q)²) Im(a b̄)/L` with `q = (2π/L)²` (hand computation; the nonlinearity drops
out of the flux identity), which is nonzero for suitable `a, b`; the regression
`test_wct_sat_device.py` checks the non-constancy numerically. With a SAT-deciding encoder this
device uses the same two trajectories for every formula, so its budget does not grow at all.

## Phase D: superpolynomial resources (`PVNP.WCTSATScaling`)

**Target statement** (`SuperpolyResources`): for a device class `𝓜` with charged resource `𝓡`,

  `∀ M ∈ 𝓜 deciding SAT, ∀ k, ∀ N, ∃ x, |x| ≥ N ∧ 𝓡_M(x) > |x|^k`,

i.e. for every `k`, `𝓡_M > n^k` on inputs of infinitely many lengths.

**The charged zero-mode class** (`ZeroDev`): a Turing machine `M` with polynomial time bound `p`
decides an amplitude-bit language `A`; input `x` is prepared as the zero-mode state of amplitude
`2` (`x ∈ A`) or `1`, evolved by the frozen equation and read at time `1` by the fixed detector
and threshold. Its charged resource (`ZeroDev.res`) is
`p(|x|) + T + ∫₀ᵀ ‖Δψ‖² + mass + 1/margin`.

| Theorem | Statement |
|---|---|
| `zdecides_iff` | a zero-mode device decides exactly its amplitude-bit language |
| `ZeroDev.res_le` | its resource is at most `p(|x|) + ⌈2L/3⌉ + 5` |
| `zero_charges_P` | every language of `P_TM`, whatever its configuration space, has a zero-mode device with polynomial resources |
| `zeroSuperpoly_iff` | in the zero-mode class, `SuperpolyResources Lang ⟺ Lang ∉ P_TM` |
| `zeroSuperpoly_SAT_iff` | for dense SAT, `SuperpolyResources ⟺ P_TM ≠ NP_TM` |
| `superpoly_SAT_implies_P_ne_NP` | in **every** class that has, for each language of `P_TM`, a device with polynomially bounded resource, `SuperpolyResources SAT_dense ⟹ P_TM ≠ NP_TM` |
| `torus_superpoly_implies_P_ne_NP` | the same for every class into which the zero-mode devices embed with polynomial resources |

**Answer to the question.** A theorem "interwoven SAT constraints force superpolynomial physical
resources on every admissible uniformly encoded frozen-WCT solver" would prove `P_TM ≠ NP_TM` for
every admissible class that contains the charged zero-mode devices. In the zero-mode class it is
exactly `P_TM ≠ NP_TM`. It is therefore Open, and it cannot be settled by an argument about the
PDE alone.

**Adversarial examples.**

* *Preloading* (`preloaded_device`): physical resources `O(1)`, all cost in the encoder.
* *Polynomial languages with exponentially many configurations* (`zero_charges_P`): `2ⁿ` binary
  field configurations do not imply exponential time. For example, satisfiability of Tseitin
  formulas reduces to component parities (`TseitinSAT.tseitin_mem_SAT_dense_iff_comp`), although
  on bounded-degree expanders with odd charge every resolution refutation has size `2^{Ω(m)}`
  (Urquhart 1987; Ben-Sasson–Wigderson 2001). Expansion, frustration and a large configuration
  space are compatible with polynomial-time decision.
* *Transport* (Phase C): the readout bound is at best inverse-polynomial.

## Phase F: transfer to classical computation

* **Physical ⟹ classical needs no simulation theorem** in any class that contains the charged
  zero-mode devices: `superpoly_SAT_implies_P_ne_NP` and `torus_superpoly_implies_P_ne_NP`.
* **Classical ⟹ physical** for a larger class needs a resource-preserving simulation of the PDE
  devices by Turing machines with charged encoders, robust measurement and polynomial numerical
  simulation of the nonlinear equation (I-11). That simulation is not available; I-11 stays
  Restricted.
* **Barriers.** Since any proof of `SuperpolyResources SAT_dense` over such a class proves
  `P_TM ≠ NP_TM`, it must avoid the relativization (Baker–Gill–Solovay), natural-proofs
  (Razborov–Rudich, under standard cryptographic assumptions) and algebrization
  (Aaronson–Wigderson) barriers. The theorems here are reductions; they relativize and do not
  attempt that.

## Claim-by-claim dependency graph

```text
PartIPsiSat.psi_sat_completeness ─┬─> InterwovenSAT.sat_of_locks ─> locks_iff_sat_iff ─> toroidal_locking_iff_unsat (I-37)
PhasePenaltyGap.unsat_logical_energy_gap ─> unsat_gap_general, unsat_energySB_gap ─> sat_iff_EminSB_eq_zero, unsat_iff_EminSB_ge
PhasePenaltyMargin.roundPhase_satisfies ─> measure_satisfies (I-3 readout)
Elogic + Ecoup + Ecurv algebra ─> xor_energy_pos / xor_energy_ge_quarter / single_var_energy ─> naive_Emin, satisfying_not_ground, naive_toroidal_locking_fails

TorusFlux.flux_identity + flux_inequality ─> Jdet_const_of_Gam_eq_zero ┐
PhysicalReadoutCapacity.detector_contrast_budget ──────────────────────┴─> change_budget ─> device_pair_budget ─> device_pair_budget_of_preparation
TorusWellPosed.IsSolution, TorusSeries.fc_field, integral_field ─> zeroMode_isSolution, Jdet_mode_zero ─> preloaded_device ─> blindness_necessary
PhysicalSATReadout.sat_pair_readout_resource_disjunction ─(hypothesis dropped)─> blindness_necessary

preloaded_device + DiscreteMachines.P_TM ─> zdecides_iff, ZeroDev.res_le ─> zero_charges_P
SATTarget.eval_le_pow_succ ─> not_superpoly_of_poly ─> superpoly_implies_not_mem_P
CookLevin.Gen.satLowerBound_iff_P_ne_NP ─> superpoly_SAT_implies_P_ne_NP, zeroSuperpoly_SAT_iff, torus_superpoly_implies_P_ne_NP
```

## Smallest remaining obligations

The inventory is not changed by the results PR. The proposed classification (I-37 from Open to
Restricted) is made, with its tooling, in a separate classification PR.

| Claim | Proposed status | Smallest missing obligation |
|---|---|---|
| I-37 | Restricted | a physical (spatial-torus) ψ–electron realization of the flux constraints, with dynamics that reach the locks; the frozen dynamics cannot (`Torus.no_locking`) |
| I-3 | Open | a formula-dependent, non-conservative dynamics that drives `E^{sb}` below `1/8` from a state prepared by an encoder that does not itself decide SAT, with charged time; the static criterion and the readout are proved |
| I-32, I-16 | Open | `P_TM ≠ NP_TM` (each is equivalent to it in its class) |
| I-11 | Restricted | resource-preserving TM simulation of the nonlinear PDE devices with charged encoders and robust measurement |
| I-2 | Open | a state notion (input-indexed or physical families with a preparation model) under which the conjecture has complexity content |
| Phase D target | Open | equivalent to `P_TM ≠ NP_TM` in the zero-mode class |

## Verification

Run on the branch head (13 November 2026, Lean 4.23.0, pinned Mathlib):

* `lake build PVNP.InterwovenSAT PVNP.WCTSATDevice PVNP.WCTSATScaling`: success, no warnings.
* `lake build PVNP`: 7,395 jobs, success.
* Axiom audit: 742 declarations (53 new), each depending only on `propext`, `Classical.choice`,
  `Quot.sound`.
* Python regressions `pvnp/tests/test_interwoven_sat_energy.py` and
  `pvnp/tests/test_wct_sat_device.py` (finite and numerical checks; they do not verify the Lean
  proofs).
