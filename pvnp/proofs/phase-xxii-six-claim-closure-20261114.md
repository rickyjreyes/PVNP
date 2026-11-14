# Phase XXII: final six-claim mathematical closure (14 November 2026)

**Baseline:** `main` after PRs #88–#94, ledger 79 Exact / 2 Restricted / 5 Refuted / 4 Open /
1 Interpretive (91 entries). The six claims below were the only mathematical entries not settled
by a proof or a counterexample.

**New Lean modules** (all in `lean/PVNP/`, imported by `PVNP.lean`, every principal theorem in
`lean/audit/AxiomAudit.lean`):

| Module | Claim | Principal theorems |
|---|---|---|
| `SpatialToroidalLocking.lean` | I-37 | `SpatialLocking.sat_iff_locked`, `no_locked_iff_unsat`, `locked_iff`, `locked_frozen_flow`, `frozen_flow_preserves_locks`, `ham_ge`, `eq_mode_of_ham_eq`, `no_attracting_locks` |
| `SATDynamicsObstruction.lean` | I-3 | `SATDynamics.energy_monotone_trapped`, `energySB_flip`, `sat_flipF`, `corner_trapped`, `no_corner_preparation_decides`, `sat_iff_corner_sweep`, `corner_sweep_card`, `efficient_device_and_simulation_imply_P_eq_NP` |
| `NonconstructibleFamily.lean` | I-2 (with I-16, I-32 links) | `NonconstructibleFamily.familyModel_Pst`, `unrestricted_family_separation`, `npFamily_separation_iff`, `npFamily_SAT_iff`, `wavefield_constructible_iff`, `wavefield_separation_iff`, `npFamily_iff_wccDepth`, `npFamily_iff_expanderGrowth` |
| `ContinuumPrecision.lean` | I-11 | `ContinuumPrecision.zeroDev_languages_eq_P_TM`, `Jdet_lipschitz`, `readout_precision`, `decision_robust`, `precision_suffices`, `approx_trajectory_close`, `approx_readout` |

No `sorry`, `admit`, `native_decide` or new axiom is used; the axiom audit allows only
`propext`, `Classical.choice` and `Quot.sound`.

## Outcome

| Claim | Before | After | Decisive new result |
|---|---|---|---|
| I-37 | Restricted (70%) | **Exact** | Realized on the spatial torus `T_L²` with frozen-WCT fields; SAT ⟺ a locking configuration exists; locks are exact, curvature-free solutions of the frozen flow and are never approached from outside. |
| I-3 | Open (45%) | **Restricted** | The static criterion holds (sign-blind encoding); as a dynamical test it is refuted for every energy-nonincreasing evolution from every formula-independent corner; an exhaustive (exponential) device is correct; an efficient one is the P vs NP question. |
| I-11 | Restricted (45%) | Restricted | The charged zero-mode torus class decides exactly `P_TM`; the readout decision is robust at precision `δ` with `log(1/δ) = LF·T + O(1)`; any approximate trajectory with certified residual `ε` gives the readout to within a Gronwall bound. A polynomial-time scheme with certified residual remains the gap. |
| I-2 | Open (15%) | Open | Every reading is false (explicit states), vacuous (unrestricted verification) or *exactly* `P_TM ≠ NP_TM` (NP-verified families, also physical wavefield families on the frozen torus). |
| I-32 | Open (20%) | Open | Equivalent to I-2 (reading C) and to I-16 for dense SAT in the charged constant class; its manuscript consequence via I-31 is broken because I-31 is refuted. |
| I-16 | Open (15%) | Open | For dense SAT it is exactly `P_TM ≠ NP_TM`, equivalent to I-2 (reading C). No strategy available here overcomes the known barriers. |

The classification changes (I-37, I-3) are applied in the companion classification PR, after
this module PR is merged at a verified head. The ledger becomes **80 Exact, 2 Restricted,
5 Refuted, 3 Open, 1 Interpretive** (91). Classical `P ≠ NP` is not proved, and no statement
here is a lower bound for all physical or classical SAT algorithms.

---

## I-37: toroidal locking

**Original statement** (Part I, §12.3). "A toroidal locking witness for a 3-SAT instance is a
curvature-locked configuration encoding a toroidal ψ–electron structure whose phase-locking and
flux constraints correspond to the satisfaction of all clauses. Nonexistence of such a locking
configuration is equivalent to unsatisfiability."

**Previous result** (Phase XX). Proved on the *configuration* torus `|ψᵢ| = 1`
(`InterwovenSAT.toroidal_locking_iff_unsat`); fails for sign-sensitive flux terms
(`InterwovenSAT.naive_toroidal_locking_fails`); for any added energy `C ≥ 0` it holds iff `C`
vanishes on some satisfying configuration of every satisfiable formula
(`InterwovenSAT.locks_iff_sat_iff`). Gap: no spatial field, and the frozen flow cannot reach a
stable lock from outside (`Torus.no_locking`).

**New result.** The structure is realized on the **spatial torus** `T_L² = (ℝ/Lℤ)²` of the
frozen WCT equation, with the repository's own torus field (`Torus.field`), not on a configuration
space.

* *Field.* `Ψ : ℕ → ℓ2`, a family of frozen-torus `H²` states; component `0` is the reference
  (ψ–electron) field and component `i + 1` carries variable `i`. Its value at `x` is
  `ψᵢ(x) = Torus.field L (co L (Ψ i)) x`.
* *Local constraints.* (a) `|ψᵢ(x)| = 1` everywhere; (b) the local density
  `dens(x) = E^{sb}_F(ψ_{i+1}(x)·conj ψ₀(x))` — the clause penalties plus the sign-blind coupling and
  curvature of the gauge-invariant relative field — vanishes at every point; (c) every component
  has zero gradient energy `Σ_k |ξ_k|² |ψ̂ᵢ,k|² = 0` (curvature-locked).
* `SpatialLocking.sat_iff_locked`: **`Sat F ⟺ ∃ Ψ, Locked F λ μ L Ψ`** for every formula, every
  `L > 0` and all `λ, μ ≥ 0`; `no_locked_iff_unsat` is the sentence of §12.3 verbatim.
* `locked_iff`: the locks are exactly the constant fields `ψᵢ ≡ cᵢ/L`, `|cᵢ| = L`, whose relative
  phases have zero clause energy (the gradient term forces constancy,
  `eq_mode_of_grad2_eq_zero`).

**Dynamical obstruction, resolved.** Two theorems settle what the frozen evolution does with locks:

1. *Conservative locking* (`locked_frozen_flow`, `frozen_flow_preserves_locks`, `γ > 0`). Every
   component of a lock evolves by the exact frozen solution `cᵢ e^{−iΩt}/L` with one common
   frequency `Ω`; the configuration stays locked for all `t`, and the Laplacian (`Dc`) vanishes
   identically, so the curvature functional is zero along the evolution. Locks are exact
   stationary states of the frozen PDE up to a global phase.
2. *No attracting locks* (`no_attracting_locks`, `κ ≤ 0`, `β ≤ 0`, `γ > 0`). If frozen
   solutions `Uᵢ` satisfy `Uᵢ(tₙ) → Φᵢ` along **any** time sequence and `Φ` is a lock, then
   `U(0)` is already a lock. Proof: at fixed mass the zero mode is the unique minimizer of the
   Hamiltonian (`ham_ge`, `eq_mode_of_ham_eq`, from the kinetic bound `kin_ge` and the
   tangent-line bound `pot_ge` integrated over the box of area `L²`); mass and Hamiltonian are
   conserved and continuous, so `U(0)` has the minimal energy at its mass and is a zero mode
   with the limit's modulus (`approach_zeroMode`); the common phase rotation preserves the
   relative phases, which therefore equal those of `Φ`.

So the frozen dynamics neither destroys a lock nor creates one; a lock can only be prepared.
Dissipative extensions do not help in general: the false well of I-3 traps every
energy-nonincreasing evolution (below).

**Closure status: PROVED (Exact).** The claim is a static existential equivalence. The
manuscript requires the phase-locking and flux constraints to "correspond to the satisfaction of
all clauses", and `locks_iff_sat_iff` shows the equivalence holds exactly for flux terms
compatible with satisfaction; the sign-sensitive terms that fail are not such constraints. The
spatial realization satisfies every requirement of the sentence: a field on a torus, local
constraints, Boolean phase consistency, sign-blind coupling and curvature, curvature-locked
configurations. The only interpretive element is the name "ψ–electron", which the manuscript
uses once and does not define; it is read as the reference component of the unit-modulus field.

**Remaining obstruction:** none mathematical. Reaching a lock is not part of the claim and is
settled negatively for the frozen flow (2.) and for energy descent from formula-independent
preparations (I-3).

---

## I-3: physical SAT dynamics and readout

**Original statement** (Part I, §2.3/§4.1): "The proposed physical lock tests whether local phase
gradients decay and intensity reaches a local maximum", with "SAT ⟺ ∃xᵢ : ∇φ → 0, |ψ|² → max";
the encoding is not fixed.

**Previous result.** The bare lock (gradient and intensity only) does not detect SAT
(`PhaseLockScope.bare_phase_lock_not_sat`). With the sign-blind interwoven energy, SAT ⟺ ground
energy `0`, UNSAT ⟺ ground energy `≥ 1/8`, and the sign readout below `1/8` is a satisfying
assignment (`InterwovenSAT.sat_iff_EminSB_eq_zero`, `unsat_iff_EminSB_ge`, `measure_satisfies`);
with the literal sign-sensitive gradient the criterion fails. PR #94 gave a satisfiable formula
with a nonglobal local well (`SATFalseWell.signblind_false_local_well`). Missing: a dynamics that
drives the energy below `1/8` from a state prepared without deciding SAT.

**New results.**

1. *The false well is an invariant trap for every energy-nonincreasing evolution*
   (`SATDynamics.energy_monotone_trapped`). Let `Ψ : ℝ → (ℕ → ℂ)` be any evolution of unit fields
   with continuous components along which `E^{sb}_{trap}` is non-increasing on `t ≥ 0`. If `Ψ(0)`
   lies in the box `sᵢ ≤ 1/8` (`i = 0, 1, 2`) with energy `< 17/16`, then for all `t ≥ 0` it stays
   in the box with energy `≥ 1`. Proof: on the box the energy is `≥ 1 + (s₀+s₁+s₂)/2`
   (`trapEnergy_local_lower`); leaving the box requires (intermediate value theorem on the largest
   score) a time at which the largest score equals `1/8`, where the energy is `≥ 17/16`, which
   monotonicity forbids. This covers every gradient flow, damped or dissipative evolution with
   Lyapunov function `E^{sb}`, at any speed. It is a **trap, not metastability**: there is no
   escape at any time.
2. *Every formula-independent corner preparation fails* (`corner_trapped`,
   `no_corner_preparation_decides`). Polarity flips preserve energy and satisfiability
   (`energySB_flip`, `sat_flipF`), so for every corner `a` the satisfiable formula
   `flipF a trapFormula` has its false well at `fieldOf a`.
3. *A correct end-to-end device exists at exponential cost* (`sat_iff_corner_sweep`,
   `corner_sweep_card`): preparing each of the `2^{nvar F}` corner fields and reading `E^{sb} < 1/8` decides SAT for every formula; the encoder reads `F` and presupposes
   nothing about its satisfiability.
4. *Efficiency is the classical question* (`efficient_device_and_simulation_imply_P_eq_NP`): a
   polynomial-resource physical SAT decider in any class with a resource-preserving Turing
   simulation (I-11) gives `P_TM = NP_TM`.

**Local / global / efficiency, separated.**
*Global:* the zero-energy (ground-state) criterion is exact in the sign-blind encoding.
*Local:* local energy minima and local descent do not detect SAT (1., 2.).
*Efficiency:* any efficient realization is a polynomial SAT algorithm modulo simulation (4.).

**Closure status: RESTRICTED.** The criterion holds in the sign-blind encoding as a static
(global) criterion and with an exhaustive preparation (3.); it is refuted literally (bare lock,
sign-sensitive gradient) and as a convergence test for energy descent from formula-independent
preparations (1., 2.). The obligation recorded before this phase — a non-conservative dynamics
reaching the readout region from a SAT-agnostic preparation — is now decided: impossible for
energy-nonincreasing dynamics from corners, possible with exponential resources.

**Remaining obstruction.** Non-monotone (e.g. stochastic) dynamics from non-corner, formula-
dependent polynomial-time preparations are not excluded; with polynomial resources and a
resource-preserving simulation they would decide SAT in polynomial time (4.), so they are not a
proof obligation of I-3 but of P vs NP.

---

## I-11: continuum computation equivalence

**Original statement** (Remark `rem:infinite-compute`): within the rail, `P_WCC = P_Turing`.

**Previous result.** `PartIIUniform.P_disc_eq_P_TM` (discrete, exact);
`PhysicalAudit.unrestricted_phys_ne_P_TM` (arbitrary encoders give a diagonal language outside
`P_TM`); physical lower bounds transfer to classical ones in any class containing the charged
zero-mode torus devices (`WCTSATScaling.superpoly_SAT_implies_P_ne_NP`).

**New results.**

1. *Exact equality on a continuum subclass* (`ContinuumPrecision.zeroDev_languages_eq_P_TM`):
   the languages decided by the charged zero-mode devices of the frozen torus PDE (polynomial-time
   encoder, exact frozen evolution, fixed detector and margin, every resource charged) are exactly
   `P_TM`. This gives `P_TM ⊆ P_phys` without advice or a preloaded answer beyond a
   polynomial-time encoder.
2. *Readout robustness* (`Jdet_lipschitz`, `readout_precision`, `decision_robust`,
   `precision_suffices`). The detector is Lipschitz on bounded sets,
   `|J(v) − J(w)| ≤ C_χ (‖v‖ + ‖w‖) ‖v − w‖` with `C_χ = L⁻¹ Σ_k |χ̂_k|`. With the a-priori bound
   and Lipschitz dependence of frozen solutions on their data,
   `|J(v(T)) − J(u(T))| ≤ 2 R C_χ e^{LF·T} ‖v(0) − u(0)‖`. Hence data known to precision
   `δ = m / (4 R C_χ e^{LF·T})` fix the decision of a device with margin `m`, and
   `log(1/δ) = LF·T + log(4 R C_χ / m)`: the number of bits grows linearly in the evolution time.

3. *Stability of approximate trajectories* (`approx_trajectory_close`, `approx_readout`). Let
   `W` be any approximate trajectory in the interaction picture (`W' = G(t, W)` is the frozen
   equation) with residual `‖W'(t) − G(t, W(t))‖ ≤ ε`, initial error `‖W(0) − u(0)‖ ≤ δ`, and
   `‖W(t)‖ ≤ R` on `[0, T)`. Then `‖e^{tA}W(t) − u(t)‖ ≤ δ e^{LF·t} + (ε/LF)(e^{LF·t} − 1)` (Mathlib's
   approximate-trajectory Gronwall inequality with the Lipschitz bound of `G` on the ball), and
   the detector reading is accurate to `C_χ (‖W(T)‖ + R)` times that bound. This is the stability
   half of a certified simulation: any scheme whose residual is certified below the margin's
   threshold decides correctly.

**Closure status: RESTRICTED** (unchanged). Robust measurement — one of the three missing
ingredients recorded before this phase — is now a theorem, the charged encoder ingredient is
exact on the zero-mode class, and stability of approximate trajectories is proved.

**Remaining obstruction.** `P_phys ⊆ P_TM` for the full frozen-PDE class needs consistency with
polynomial cost: a finite-dimensional scheme (a Galerkin truncation of the *solution*, not only of
the data, and a time discretization) whose residual `‖W' − G(t, W)‖` is certified small in the norm
in which the detector is Lipschitz, computed with exact-arithmetic bit costs polynomial in the
input length. By 3. nothing else is needed. The results here do not control the tail of the nonlinearity in the `H²`-weighted space
beyond the conserved quantities; such control needs propagation of higher (for example analytic)
regularity, which is not proved. No countermodel is known either; the zero-mode class is
contained in `P_TM` (`WCTSATScaling.zdecides_mem_P`).

---

## I-2: verifiable, non-constructible wavefield family

**Original statement** (Part I, "Symbolic Separation Program"): under one fixed preparation,
verification and resource model, there is a coherent target state in `NP_st \ P_st`.

**Previous result.** Explicit finite states: false (`DepthBarrier.explicit_no_separation`).

**New result: every reading is settled or is exactly `P ≠ NP`.**

* *Reading A, explicit states:* false (Phase XVIII).
* *Reading B, input-indexed families `x ↦ ψ_x ∈ {0,1}` with unrestricted verification*
  (`familyModel`): constructible families are exactly `P_TM` (`familyModel_Pst`), and the
  separation holds for the vacuous reason that a diagonal language outside `P_TM` is "verified" by
  the trivial predicate (`unrestricted_family_separation`).
* *Reading C, NP-verified families* (`npFamilyModel`): `NPst \ Pst ≠ ∅ ⟺ P_TM ≠ NP_TM`
  (`npFamily_separation_iff`); dense SAT is a witness iff `P_TM ≠ NP_TM` (`npFamily_SAT_iff`).
* *Reading C on the frozen torus, physical wavefield families* (`wavefieldModel`): states are
  families of frozen-torus fields, constructors are charged zero-mode devices, verification is
  NP-membership of the amplitude-bit language. A wavefield family is constructible iff its
  language is in `P_TM` (`wavefield_constructible_iff`), and the separation holds iff
  `P_TM ≠ NP_TM` (`wavefield_separation_iff`).

**Closure status: OPEN**, with the reduction proved. The original claim is not promoted by
proving the weaker readings: A is false, B has no complexity content, and C is the classical
separation. **Remaining obstruction:** `P_TM ≠ NP_TM`.

---

## I-32: encoding-independent interface growth

**Original statement** (Hypothesis `prop:locked-expander-full`): every decider of the language has,
beyond every length, an input and a time at which its decision interface has measure at least
`c₀ 2^{γ n}`.

**Results.** In the charged constant-device class, for dense SAT it is equivalent to
`P_TM ≠ NP_TM` (`ExpanderInterface.expanderGrowth_SAT_iff`), and therefore to reading C of I-2
(`NonconstructibleFamily.npFamily_iff_expanderGrowth`); in any class containing those devices it
implies `P_TM ≠ NP_TM`. It is false for every language in `P_TM`. The unconditional bounds that do
hold are linear: under charged finite-radius local transport, a correct decoder of the distributed
SAT energy must have every decisive source position in its causal cone
(`WCTDistributedSAT.distributed_energy_requires_causal_coverage`).

**I-31/I-32 audit (cross-connection 5).** The manuscript turns interface growth into a resource
lower bound through the separator price `lem:separator-price` (I-31). I-31 is refuted for the frozen
trajectory class: plane waves of fixed amplitude keep the curvature functional bounded while their
interface measure grows with the torus side (`SeparatorFrozen.no_uniform_separator_price`). So even
a proof of I-32 would not yield the manuscript's energy lower bound without a replacement for I-31;
the corrected `SeparatorFrozen.layer_price` (width-`w` transition costs at least `4η²/w` per unit
length) applies only to sharp interfaces.

**Closure status: OPEN.** **Remaining obstruction:** cannot be proved without `P_TM ≠ NP_TM`; in
the constant class cannot be refuted without `P_TM = NP_TM`.

---

## I-16: universal SAT lower bound

**Original statement** (Conjecture `conj:wcc_depth`): every uniform discrete WCC decider of 3-SAT is
superpolynomial infinitely often.

**Results.** For dense SAT it is exactly `P_TM ≠ NP_TM` in the radius-one, `ℤ^(1+d)` and uniform
models (`DepthBarrier.wccDepth_SAT_iff`, `wccdDepth_SAT_iff`, `uniform_depth_SAT_iff`) and for the
charged zero-mode torus devices (`WCTSATScaling.zeroSuperpoly_SAT_iff`); it is equivalent to
reading C of I-2 (`NonconstructibleFamily.npFamily_iff_wccDepth`). The strongest unconditional
lower bound in the repository is quadratic, for one-tape deciders
(`CrossingSATMatrix.quadratic_every_budget`).

**Strategy audit.** (A) Diagonalization separates `P_TM` from *some* language
(`PhysicalAudit.diagonal_not_mem_P_TM`) but says nothing about SAT unless combined with
NP-hardness, i.e. it needs the separation itself. (B) Crossing sequences give `Ω(n²)` for one-tape
machines and do not transfer to multi-tape or lattice models with polynomial overhead. (C) Locality
and causal-cone arguments give linear bounds only (`WCTDistributedSAT`). (D) Physical-resource
arguments reduce to I-31 (refuted) or to the zero-mode class (equivalent to `P ≠ NP`).
(E) Known barriers: diagonalization relativizes (Baker–Gill–Solovay), so it cannot separate `P` from
`NP` on its own; natural circuit lower-bound arguments are blocked by Razborov–Rudich under standard
cryptographic assumptions; arithmetized extensions are blocked by algebrization
(Aaronson–Wigderson). No argument here is shown to avoid these barriers. They are cited, not
formalized.

**Closure status: OPEN.** **Remaining obstruction:** classical `P_TM ≠ NP_TM`.

---

## Cross-connections

1. **I-37 / I-3.** Both rest on the same static fact (zero sign-blind energy ⟺ SAT). Their common
   obstruction is dynamical: the frozen flow preserves locks and never approaches one
   (`no_attracting_locks`), and energy descent is trapped by false wells
   (`energy_monotone_trapped`). Existence (I-37) is exact; detection by dynamics (I-3) is not.
2. **I-3 / I-11.** An efficient physical SAT decider plus a resource-preserving simulation gives
   `P_TM = NP_TM` (`efficient_device_and_simulation_imply_P_eq_NP`); the precision half of that
   simulation is proved (`precision_suffices`).
3. **I-11 / I-32.** In any class containing the charged zero-mode devices, a physical lower bound
   transfers to a classical one without simulation; the zero-mode class equals `P_TM`
   (`zeroDev_languages_eq_P_TM`), so I-32 restricted to it is false for every language in `P_TM`.
4. **I-2 / I-16 (exact equivalence).** `npFamily_iff_wccDepth`: reading C of I-2 holds iff
   `conj:wcc_depth` holds for dense SAT; with `npFamily_iff_expanderGrowth` the three open claims
   coincide for dense SAT in the charged constant class.
5. **I-31 / I-32.** The interface-to-resource step uses I-31, which is refuted; see above.

## Verification

* `lake build PVNP` (Lean 4.23.0, pinned Mathlib): 7,405 jobs, success; the four new modules build
  without warnings.
* Axiom audit (`lean/audit/AxiomAudit.lean` + `audit/check_axioms.py`): 868 declarations, only
  `propext`, `Classical.choice`, `Quot.sound`.
* Python regressions (`pvnp/tests`, 76 tests), `pvnp/phase_xvi/status.py --check`,
  `scripts/check_manuscript_alignment.py`, `scripts/check_public_release_docs.py`: pass.
* CI: a dedicated build step and closure guard for the four modules in `.github/workflows/lean.yml`.
