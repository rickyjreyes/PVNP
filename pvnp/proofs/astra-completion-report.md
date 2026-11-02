# ASTRA completion report — PVNP mathematical and Lean program (2 November 2026)

Author of the research program: **Richard J. Reyes**. Original publications (Zenodo releases 03, 12, 13 and the May/November/December 2025 versions) are preserved unchanged; this report records the current, revised state of the mathematics.

Branch: `astra/complete-program-20261102`, built on PR #14 head `98d0ac20` (which itself extends `main`). Every result below was checked locally with the pinned toolchain (`leanprover/lean4:v4.23.0`, Mathlib `v4.23.0`) via `lake build PVNP`, and the axiom audit `lean/audit/AxiomAudit.lean` reports only `propext`, `Classical.choice`, `Quot.sound` for all 61 principal declarations. GitHub Actions on the branch head is the authoritative CI record.

---

## A. GitHub issue status

### #11 — discrete WCC ↔ Turing equivalence

- **Starting status:** OPEN. PR #14 had one-step head motion, safe moving-head traces (left/right only), stationary-head traces, bit-grid machine tables with strict one-hot decoding; no stay/halt in traces, no reverse interpreter, no class theorems.
- **Work performed:** froze one discrete model pair and proved both simulations end-to-end, the class equalities, and a flat binary serialization.
- **New Lean files:** `DiscreteMachines.lean`, `TMtoWCC.lean`, `WCCtoTM.lean`, `ComplexityEquivalence.lean`, `MachineSerialization.lean`, `WitnessSizeUniformity.lean` (the issue's requested `UniformSimulationBridge` content is `ComplexityEquivalence.explicit_simulations`).
- **New theorems (qualified names, namespace `PVNP.Discrete`):**
  - `TM.toWCC_step_encode` — `M.toWCC.step (M.encode c) = M.encode (M.next c)` for **every** configuration (left, right, stay, halt).
  - `TM.toWCC_run_encode`, `TM.encode_injective`, `TM.encode_head_unique` — all finite executions; exactly one head marker at every step.
  - `TM.toWCC_decides` — real-time: same language, same time bound `T`.
  - `WCC.rsweep_run`, `WCC.lsweep_run`, `WCC.phase_step`, `WCC.global` — exact invariants of an explicit ordinary single-tape TM (`WCC.toTM`) that simulates the WCC by alternating shifted sweeps (one TM step per simulated cell, no return sweep).
  - `WCC.toTM_decides` — the TM decides `L` within `1 + (T n + 1)(n + 2 T n + 5)` steps.
  - `P_TM_subset_P_WCC`, `P_WCC_subset_P_TM`, **`P_WCC_eq_P_TM`**, **`NP_WCC_eq_NP_TM`**.
  - `p_vs_np_discrete_transfer : (P_WCC = NP_WCC) ↔ (P_TM = NP_TM)`, `lower_bound_transfer`.
  - Witness quantifiers: `pair_length` (`|pair x w| = 2|x|+1+|w|`), `NP_TM_verifier_to_WCC` (same language, same witness polynomial `q`, same time `p`, verifier time in `|x|` at most `p ∘ (2X+1+q)`), `NP_WCC_verifier_to_TM`.
  - Serialization: `Codec` laws, `encodeTable_decodeTable`, `decodeTable_sound`, `decodeTable_rejects`, `encodeTable_injective`, `encodeTable_length_le` (`|code| ≤ 4 + 6k + 4m + km(k+m+4)`), `TM.normalize_decides`, `P_TM_eq_tables`.
- **Exact definitions used (no hypothesis restates the conclusion):** `P_TM = {L | ∃ M p, M.Decides L (p.eval ·)}`, `P_WCC` likewise; `NP_X = NPOf P_X` with `x ∈ L ↔ ∃ w, |w| ≤ q(|x|) ∧ pair x w ∈ V`. `Decides` = for every input, the first non-`none` output occurs by step `T |x|` and equals the membership bit. Both alphabets/state sets are `Fintype`.
- **Readout convention:** a WCC answers when *some* cell carries an accepting/rejecting symbol (acceptance takes precedence). The TM→WCC compiler only ever produces such symbols in the single head cell, and the WCC→TM simulator handles the global readout explicitly, so the class is the same under the local head-cell readout; no non-local readout power is hidden in `P_WCC`.
- **Reused:** the head-marker idea and `OracleObstruction` motivation from PR #14 (the new modules are self-contained and do not modify PR #14 files).
- **Counterexamples:** none needed — the exact formulation holds.
  - **`P ⊆ NP`, unconditionally** (`PSubsetNP.lean`): `TM.unpair_decides` builds an explicit ordinary TM that parses `pair x w` (rejecting every malformed string), erases the witness, returns, and simulates `M` on odd cells, deciding `{pair x w | x ∈ L}` within `2N + 3 + 2p(N)` steps; hence **`P_TM_subset_NP_TM`** and **`P_WCC_subset_NP_WCC`**.
- **Remaining scope limits (not mathematical obstructions):** radius-`r`/`d`-dimensional lattices and polynomial-time non-local encoders from the manuscript's general definition (standard block/encoder composition, not formalized); a universal TM executing serialized descriptions and a TM-step bound for the parser (not needed for the class equalities, since the classes quantify over machines).
- **Classification: PROVED** for the frozen 1-D radius-one finite quiescent model — the project's declared Part II Lean semantics.

### #15 — noise-robust bandlimited packing

- **Starting status:** OPEN; analytic proof only.
- **New Lean files:** `BandlimitedNoisyPacking.lean`, `FourierReceiverProjection.lean`, `DecisionVsEncodingCounterexample.lean`, `FourierTorusReceiver.lean`.
- **New theorems:** `Packing.packing_card_le` (Haar-measure volume argument, any finite-dimensional real normed space); `Packing.finrank_real_euclideanSpace_complex` (`dim_ℝ ℂ^D = 2D`); `Packing.complex_receiver_packing` / `_strict` (**`N ≤ (1+√M/η)^{2D}`**, under `≥ 2η` and the supplement's `> 2η`); `Packing.receiver_projection_norm_le`; `Packing.subspace_receiver_packing` (any complex `D`-dimensional receiver subspace, states of mass `≤ M`); `Packing.capacity_bits_le`; `Packing.mass_lower_bound`; `FourierReceiver.mode_count_le`, `receiver_mode_count`; and on the **genuine `L²` torus** (`FourierTorusReceiver.lean`): `FourierTorus.receiver_bessel` (Parseval ⇒ Bessel for the observed Fourier coefficients), `torus_receiver_packing` (`N ≤ (1+√M/η)^{2|S|}` for fields in `L²(𝕋^d)`), `torus2_bandlimited_packing` (2-torus receiver observing all modes with `|2πk/L| ≤ K`: `N ≤ (1+√M/η)^{2(2⌊LK/2π⌋+1)²}`). The receiver is now literally the list of Fourier coefficients of an `L²` field, not an abstract projection.
- **New counterexamples:** `FourierReceiver.cubic_quintic_generates_new_modes` (the WCT nonlinearity leaves the finite support `{1,2}` for every `(β,γ) ≠ 0`; algebraic Fourier-coefficient model); `DecisionVsEncoding.promoted_bound_false` (storage bound ≠ decision bound; one mode and mass `η²` give an η-robust readout of **every** language: `robust_decision_readout`); `decision_forgets_witnesses`.
- **Assumptions match the supplement:** adversarial error radius `η > 0`, codeword norm `≤ √M`, pairwise separation (we prove the stronger `≥ 2η` version), finite complex receiver dimension `D`.
- **Classification: PROVED** (packing theorem and receiver lemmas); promotion to a SAT/decision lower bound **REFUTED**.

### #10 — Part I resource lower bounds

- **Starting status:** OPEN; PR #14 proved the unconditional finite-radius causality family (`R = m + Σ tᵢ rᵢ`, `MultiStageCausality`), preserved here unchanged.
- **Work performed:** froze the physical model (`pvnp/proofs/physical-model-freeze.md`), classified every resource inequality, proved the discrete curvature-rail theorems, and ran the adversarial suite against each universal candidate.
- **New Lean files:** `DiscreteCurvatureRail.lean`, `CircleSpectralGap.lean`, `WCTPlaneWave.lean` (+ #12 modules used here).
- **Genuine function-space / PDE results (new):**
  - `SpectralGap.wirtinger`: for a continuous periodic field `f` on the circle of length `L` with continuous derivative `g`, `(2π/L)²(∫‖f‖² − ‖f̂(0)‖²) ≤ ∫‖g‖²` (normalized Haar measure); `wirtinger_sharp` (equality for `e^{2πix/L}`); `no_uniform_poincare` (for every `c > 0` some domain length defeats the constant `c`). Proved from Mathlib's Parseval identity and Fourier coefficients of derivatives.
  - `WCTPlaneWave.plane_wave_solves` + `classical_derivatives`: `u = A e^{i(kx₁−ωt)}`, `ω = (κ−k²)² − β|A|² + γ|A|⁴`, is an exact classical solution of the frozen PDE `i∂ₜu = (Δ+κ)²u − β|u|²u + γ|u|⁴u` (genuine partial derivatives); `expanding_domain_countermodel`: on the torus of side `L` with fixed mass `M`, exact solutions have mass exactly `M`, curvature energy `(2π/L)⁴M → 0` (`curvature_energy_vanishes`), and Hamiltonian `M(κ−(2π/L)²)² − βM²/(2L²) + γM³/(3L⁴)`.
- **New theorems:** `WCC.run_blank_outside` (light cone), `WCC.lap_zero_outside`, `WCC.curvature_le` (`curv ≤ 16K²(n+2t+3)` for *every* amplitude embedding), **`P_TM_eq_curvature_rail`**, **`curvature_lower_bound_is_classical`**, `no_curvature_lower_bound_in_P`.
- **Counterexamples (new):** `promoted_bound_false`, `no_gradient_energy_control`, `zero_cost_counterexample`, `curvature_not_representation_invariant`, `cubic_quintic_generates_new_modes`. **Preserved:** polynomial static storage, bounded-degree expanders, GF(2)/Tseitin bypass, affine/zero-curvature channels, phase-only and nodal obstructions, expanding-domain plane waves, nonlocal readout (`RadiusCausality.shortcut_encoding_reads_far_at_zero`), uncharged preprocessing.
- **Universal resource statement:** within the discrete model it is **proved equivalent to classical P ≠ NP**; within `WCT-Phys` it is **OPEN**, with missing implications M1 (rail-preserving two-way simulation), M2 (forced `2^{Ω(n)}` distinguishable intermediate states for every decider), M3 (PDE well-posedness and `L_n`-uniform coercivity).
- **Classification: PARTIAL.** The original claim (exponential curvature barrier for all SAT deciders) is **REFUTED as stated**; no universal lower bound is proved; the central obligation remains open, so the issue must not be closed as proved.

### #12 — Part III reassessment

- **Starting status:** OPEN; mostly symbolic Lean (e.g. `zeroLaplacian _ = 0`).
- **New Lean files:** `PartIIIAnalytic.lean`, `PartIIIHighFreq3D.lean`, `PhysicalComplexityClasses.lean`, `SATVerifier.lean` (plus `DiscreteCurvatureRail`, `ComplexityEquivalence`, `PSubsetNP`).
- **Classification: PROVED at the stated scope** — every principal mathematical statement of Part III now has a Lean declaration: a proved theorem, a proved counterexample, or a statement formalized *as conditional* with its premises explicit (map below). Part III itself claims no physical class separation; that question is recorded as OPEN (O8) and is not part of this classification.

#### Part III statement map

| Part III statement | Status | Lean / evidence |
|---|---|---|
| Def. `def:regularized`, Prop. `prop:zero_cost` | Lean, counterexample (genuine Laplacian) | `PartIIIAnalytic.theta`, `curvatureCost`, `laplacian_const`, `zero_cost_counterexample` |
| Prop. conditional additive storage | Lean, **conditional** (sums `n` assumed cellwise premises) | `Discrete.conditional_additive_storage`; positive `c₀` is *not* provided by `C_Θ` (`zero_cost_counterexample`) |
| Def. physical complexity classes | Definitions; machine-relative | `Discrete.NPOf`, `P_curvRail`, freeze doc |
| Lem. `lem:h2bound` | Lean, unconditional | `PartIIIAnalytic.curvature_cost_le`, `theta_pointwise_le` |
| WIN-13 shifted denominator | Lean, counterexample | `PartIII.shifted_denominator_no_uniform_gap` |
| Thm. `thm:disc-equiv` | **Lean, proved** (1-D radius-one) | `Discrete.P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM` |
| Thm. `thm:p-in-np` | **Lean, unconditional for the discrete classes** (`P_TM ⊆ NP_TM`, `P_WCC ⊆ NP_WCC`); physical version conditional on its closure premise | `Discrete.P_TM_subset_NP_TM`, `P_WCC_subset_NP_WCC`, `TM.unpair_decides`; `Discrete.P_subset_NPOf` |
| Prop. "no logical conflict" | Lean | `Discrete.inclusions_do_not_determine` |
| WIN-17 well-posedness | Lean (definitional) | `Discrete.classical_question_well_posed`, `p_vs_np_discrete_transfer` |
| Prop. `prop:interface` | Lean, **conditional** | `Discrete.conditional_interface_bound` |
| Prop. `prop:assignment-P` (`L_check ∈ P`) | **Lean, proved** (dense CNF encoding, pair-encoded instance/assignment) | `Discrete.SATV.satTM_decides`, `V_SAT_mem_P_TM`; semantics `encDense_mem_SAT_iff` against `PVNP.PartI.satisfiable` |
| Thm. `thm:constructibility` | Lean, conditional premise explicit | `Discrete.telescoping_bound` |
| Prop. `prop:highfreq` | **Lean, on the 3-D periodic cube with the manuscript's constants** (`4π³`, `(16/25)π³N²`), and in 1-D | `PartIIIHighFreq3D.cube_gradient_energy`, `cube_curvature_lower`, `lap3_psi`; `PartIIIAnalytic.highfreq_*`, `no_gradient_energy_control` |
| Thm. `thm:capacity` | Lean, conditional premise explicit | `PartIIIAnalytic.capacity_law` |
| Lem. `lem:boundary_variation` | Lean, exact | `PartIII.directed_boundary_eq` |
| Thm. `thm:influence` | Lean | `PartIII.normalized_total_influence_le_n` |
| Cor. `cor:var` | Lean | `PartIII.variation_class_vacuous` |
| WIN-21 parity | Lean | `PartIII.parity_total_influence`, `parity_directed_boundary` |
| Representation invariance (#12) | Lean: time **invariant**, curvature **not** | `WCC.relabel_decides`, `curvature_not_representation_invariant` |
| Locality/GR/Lieb–Robinson remarks; arrow of time | Non-mathematical scope remarks; no theorem claimed | — |

---

## B. Mathematical accomplishments, ranked

1. **`P_WCC = P_TM` and `NP_WCC = NP_TM`, kernel-checked** with explicit simulations in both directions (real-time TM→WCC; `1 + (T+1)(n+2T+5)` WCC→TM). *Formal model equivalence; formalization of an existing analytic claim, now with a fully explicit sweep simulator.*
2. **Obstruction theorems for the program's lower-bound strategy:** `p_vs_np_discrete_transfer`, `P_TM_eq_curvature_rail`, `curvature_lower_bound_is_classical`. Any discrete time **or curvature** lower bound for an NP language is exactly a classical `P ≠ NP` proof; curvature rails add no power in the discrete model. *New theorems (no-go).*
3. **Noise-robust receiver packing `N ≤ (1+√M/η)^{2D}`**, including the projected-subspace form, the genuine `L²`-torus Fourier receiver (Parseval/Bessel), the bandlimited 2-torus bound, and mass/capacity corollaries. *Formalization of an existing analytic proof, strengthened (`≥ 2η`) and made concrete on `L²(𝕋^d)`.*
3a. **Sharp spectral gap and its collapse on expanding domains** (`SpectralGap.wirtinger`, `wirtinger_sharp`, `no_uniform_poincare`) and **exact classical solutions of the frozen WCT PDE** with fixed mass and vanishing curvature energy (`WCTPlaneWave.expanding_domain_countermodel`). *Formalization of the analytic core of the expanding-domain countermodel; converts O4/O5 "analytic only" items into kernel-checked statements.*
3b. **`P ⊆ NP` for TMs and discrete WCCs** with an explicit pair-parsing verifier. *Formal model infrastructure.*
3c. **CNF-SAT ∈ NP_TM with an explicit verified verifier TM** (`SATVerifier.lean`, ~1100 lines): dense CNF encoding, zig-zag witness marking machine, exact round invariants, time `2(N+3)²`, and agreement with Part I CNF semantics. Closes O2 and Part III `prop:assignment-P`; yields `SAT_curvature_transfer` (a discrete curvature lower bound for SAT would prove `P_TM ≠ NP_TM`). *Formalization of classical facts in the project's own machine model.*
4. **Refutation of storage-to-decision promotion** (`promoted_bound_false`) and of finite-Fourier-support preservation by the WCT nonlinearity. *Counterexamples / no-go.*
5. **Function-space Part III theorems:** Lebesgue-integral curvature bound; zero-cost counterexample with Mathlib's Laplacian; high-frequency counterexample with genuine derivatives and integrals. *Formalizations of existing analytic proofs (1-D for `prop:highfreq`).*
6. **Representation (non)invariance:** time classes invariant under alphabet relabelling; curvature not. *New theorem + counterexample.*
7. **Flat binary machine serialization** with verified prefix-codec combinators and normalization of every TM. *Supporting infrastructure.*
8. Exact Boolean identities (boundary = `2ⁿ`·Var, parity `Var = n`), telescoping and interface conditionals. *Supporting lemmas.*

**Requires physical/empirical validation (not proved here):** that any physical device realizes the frozen `WCT-Phys` model; well-posedness of the frozen PDE in Lean; noise models of real receivers.

---

## C. O1–O10 formal completion ledger

No percentages are used. Status words follow the charter's labels.

| ID | Status after ASTRA | Evidence / outstanding dependency |
|---|---|---|
| O1 | **Maintained.** Original releases and titles untouched; revisions recorded in manuscripts' revision registers and this report. | Ongoing: keep original-vs-revised ledger with source anchors. |
| O2 | **Complete for the dense CNF encoding.** One uniform instance/witness language (`SATV.encDense`, assignment witness, `|w| ≤ |x|`); an explicit verifier TM with yes/no correctness and time `2(N+3)²` (`satTM_decides`, `V_SAT_mem_P_TM`); `SAT_dense_mem_NP_TM`, `SAT_dense_mem_NP_WCC`; semantic agreement with Part I CNF satisfiability (`encDense_mem_SAT_iff`). "Physical admissibility" of the encoding is a separate O4–O6 question. | NP-completeness (Cook–Levin) of the dense encoding is classical but not formalized; the sparse/binary-index encoding is not formalized. |
| O3 | **Complete for the frozen discrete model** (1-D, radius one, quiescent, finite). | Optional generalizations: radius-`r`, `d`-dim, poly-time encoders, universal TM. |
| O4 | **Frozen** (`physical-model-freeze.md`). Lean: explicit exact classical solution family of the frozen PDE (`WCTPlaneWave.plane_wave_solves`), with exact mass and Hamiltonian on every torus. | General well-posedness and conservation for arbitrary admissible data (open). |
| O5 | **Partial.** Packing (abstract and genuine `L²`-torus Fourier receiver), mode count, `C_Θ ≤ ‖Δψ‖²/4ε²`, sharp circle spectral gap proved; energy→curvature, distinguishability→curvature, bandwidth-preservation, and domain-uniform Poincaré constants refuted. | Uniform-in-`L_n` nodal/phase coercivity (now known to be impossible for the plain Poincaré constant: `no_uniform_poincare`). |
| O6 | **Partial.** All resources specified as functions of `n`; discrete curvature polynomially accounted. | Hidden-resource accounting for continuum devices (precision/switching), M3. |
| O7 | **Open;** every tested universal statement refuted at stated scope; discrete version proved equivalent to classical P ≠ NP. | M2. |
| O8 | **Open.** No candidate language with a physical verifier and a proved all-decider lower bound. | M1 + M2. |
| O9 | **Reduced to classical P vs NP** for the discrete model (`p_vs_np_discrete_transfer`); for the physical model blocked on M1. | Classical P ≠ NP itself (unresolved). |
| O10 | **Advanced.** 61 principal declarations axiom-audited; CI enforces the audit; Python cross-checks added (`pvnp/tests/test_astra_discrete.py`). | Independent adversarial review; manuscript text alignment (section D). |

---

## D. Manuscript consistency

Claims that remain **unsupported** by the verified mathematics, and must stay marked historical / conditional:

1. Any statement (including the historical Part I title and abstract framing) that P ≠ NP has been proved. *Unsupported.* `p_vs_np_discrete_transfer` shows the discrete WCC question **is** the classical one.
2. An exponential curvature/energy barrier for every SAT decider. *Refuted as stated* (static storage, expanders, GF(2) bypass, expanding domain, `P_TM_eq_curvature_rail`).
3. "Physical distinguishability forces positive curvature cost." *Refuted* (`zero_cost_counterexample`).
4. "Finite energy bounds curvature." *Refuted* (`no_gradient_energy_control`).
5. "Storage capacity bounds imply decision-time bounds." *Refuted* (`promoted_bound_false`).
6. "Bandlimited receivers reflect a bandlimited evolution." *Refuted* (`cubic_quintic_generates_new_modes`).
7. Part II Theorem `thm:tm_to_wcc` states a factor-2 overhead; the Lean construction achieves factor 1 — consistent (stronger). Part II Theorem `thm:wcc_to_tm` is stated for general `d`, `r`, and lattice size; Lean covers `d = 1`, `r = 1`. Part III `prop:highfreq` is now checked in 3-D with the stated constants.
8. `NP^{phys}_{WCC} = ∅` (WIN-16) remains withdrawn; P ⊆ NP holds under the explicit closure premise.

The classical P versus NP problem remains a well-defined, open mathematical question; nothing here proves or disproves it.
