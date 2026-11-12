# Formalization report — revision 2 (2 November 2026)

**Starting point:** merge commit `614dc1c9894d7384e46d6c0cb95310ecfc88c201`. **Toolchain:** Lean
v4.23.0 with Mathlib v4.23.0 (`37df177`).

**Verification standard.** No `sorry`, `admit` or custom `axiom` anywhere. Every audited
declaration uses only `propext`, `Classical.choice` or `Quot.sound`. The full axiom audit covers
**111 declarations**. Classical `P ≠ NP` is **not** claimed, and neither is any physical separation.

**Post-report verification update (6 November 2026):** The November 2 tables and open-item descriptions below are historical snapshots, not the current status. **M3-T and F-1 are now CLOSED** for the specified torus model by `PVNP.Torus.global_wellposed`, `flux_identity`, `flux_inequality` and `curvature_time_bound` in [Phase VI PR #40](https://github.com/rickyjreyes/PVNP/pull/40), with all three PR-head CI checks passed. **Phase VIII** additionally proves the complete ordinary single-tape TM crossing-sequence splicing theorem and a near-quadratic SAT time lower bound in [PR #38](https://github.com/rickyjreyes/PVNP/pull/38). Classical `P ≠ NP`, M2 and lattice-to-continuum convergence M3-C remain open. The authoritative status is [`lean/formalization.yaml`](../../lean/formalization.yaml); see [Phase VI](phase-vi-torus-flux-status.md) and [Phase VIII](phase-viii-separation-status.md) scope notes. The manuscript claim ledger remains 70 Exact, 2 Restricted, 11 Refuted, 8 Open.

## Summary

| Paper | Main theorem proved? | Lean verified? | Remaining gap | Publication readiness |
|---|---|---|---|---|
| **Part I**: curvature-bounded wave computation | **No.** The physical/curvature separation is conditional and open. Its discrete form is proved equivalent to classical `P ≠ NP` (`p_vs_np_discrete_transfer`, `curvature_lower_bound_is_classical`), and its physical form is proved at least as hard (`physical_SAT_lower_bound_is_classical`). | The supporting discrete and conditional statements are verified; the separation is not. | M2 (universal lower bound); the dimensional-lock hypothesis; F-1; CL-1 (converse transfers only) | **Not ready** as a separation paper. It could be submitted as a conditional framework plus obstruction analysis after the title, abstract and claims are rescoped. |
| **Part II**: discrete WCC ⇄ Turing equivalence | **Yes, in dimension 1 for every fixed radius and on `ℤ^(1+d)` for every `d`** (radius-one Moore neighbourhood) with the fixed origin-marked encoding. | Yes: `P_WCC_eq_P_TM`, `NP_WCC_eq_NP_TM`, `P_WCCR_eq_P_TM`, `NP_WCCR_eq_NP_TM`, `P_WCCD_eq_P_TM`, `NP_WCCD_eq_NP_TM` (D-1 closed 2026-11-05 by an explicit single-tape TM, `WCCDSweep.toTM_decides`) | none for the discrete equivalence. The physical capacity sections are conditional. | **Near-ready** for the discrete part with the restricted scope now stated in the text (Remark `rem:verified-scope`). The physical sections need their conditional status kept explicit. |
| **Part III**: physical complexity reassessment | **Yes** for its corrective content: counterexamples, corrected conditional bounds, Boolean-influence results and `P ⊆ NP`. **No** for M1–M3 on tori. | All 14 numbered statements have kernel-checked counterparts: 9 proved, 1 proved for a restricted scope, 4 conditional with explicit premises. The continuum flux inequality stays a premise. | F-1 (continuum flux inequality), M3-T (torus well-posedness), M1-a (certified simulation), M2 | **Ready** as a reassessment note after copy-editing. Every claim is classified. |

Every numbered statement is classified in `theorem-manuscript-map.md`, and every open item in
`remaining-obstructions.md`. These classifications do **not** mean that the papers' physical
programs are proved.

## 1. Newly completed theorems (this program)

**Radius-r discrete equivalence** (`lean/PVNP/WCCRadius.lean`).
- `WCCR.toTM` is an explicit one-tape TM:
  - it buffers `2r` symbols in the control state;
  - each sweep shifts the frame by `r` and grows the region by `2r`.
- `WCCR.rsweep_run`, `lsweep_run`, `phase_step` and `global` are the exact invariants.
- `WCCR.toTM_decides` bounds the running time by `1+(T+1)(n+2r(T+1)+2r+1)`.
- `WCC.toR_decides` embeds radius one.
- Class results: `P_WCCR_eq_P_TM`, `NP_WCCR_eq_NP_TM`, `P_WCCR_radius_invariant`,
  `p_vs_np_radius_transfer`, `explicit_radius_simulations`.

**Lattices `ℤ^(1+d)`** (`WCCGenerality.lean`). `WCC.toD_run` is an exact axis embedding: the run is
blank off the axis. It gives `P_TM_subset_P_WCCD` and `NP_TM_subset_NP_WCCD`.

**Physical-model audit** (`PhysicalModelAudit.lean`), using exact classical PDE solutions:
- `device_physics`;
- `P_TM_subset_PhysConst`;
- `PhysConst_polyEnc_eq_P_TM`, a restricted two-way equivalence;
- `physical_SAT_lower_bound_is_classical`;
- `two_states_suffice`.

**Lattice WCT system** (`WCTLattice.lean`):
- `ip_Aop`: self-adjointness of the discrete operator.
- `hasDerivAt_mass`, `mass_conserved`, `hasDerivAt_ham`, `ham_conserved`: exact conservation.
- `exists_local_solution` (Picard–Lindelöf) and `local_conservation`.
- `bandpass_le_ham`: coercivity uniform in `N`.
- `hasDerivAt_flux`: the exact flux identity.
- `flux_bound` and **`lattice_flux_inequality`**: the flux inequality is **derived** from the
  equation, with an explicit `Γ`.
- `lattice_curvature_time_bound`: the curvature–time bound on the lattice.

**Definition-match bridge** (`lean/bridge/MathBridge.lean`, optional; it imports
`rickyjreyes/math@30a5ddc`):
- `opK_comp`: `(Δ+κ)² = AS k ∘ AS k` for `κ = k²`.
- `lap_comp_mathlib`: PVNP's coordinate Laplacian equals Mathlib's `Δ`.
- `fnl_eq_pvnp` and `fnl_eq_lattice`: the nonlinearities agree.
- `hamDensity_comp`: the Hamiltonian densities agree.

**External verification.**
- `ReyesMath.Sobolev.global_wellposed`, `continuous_dependence`, `conservation` and
  `norm_toSp_sq_le` were built from source against the same pinned Mathlib.
- That build covers 11 modules and 11,890 lines.
- These theorems give global `H²(ℝ²)` well-posedness for the same PDE.

## 2. Counterexamples (kernel-checked)

**New in this program:**
- `PhysicalAudit.unrestricted_encoder_trivializes`: with unrestricted encoders, every language is
  decided by a constant-cost exact PDE solution.
- `PhysicalAudit.unrestricted_decoder_trivializes`: the same holds for unrestricted decoders after
  a fixed injective encoder.
- `Discrete.unrestricted_encoder_trivializes_WCC`: with an unrestricted encoder, every language is
  decided in time 0 by a fixed one-cell WCC.
- `Discrete.advice_bit_trivializes`: one advice bit decides every length-determined language.

**From earlier programs, still in force:**
- `DecisionVsEncoding.promoted_bound_false`;
- `DecoderUniformity.arbitrary_predicate_has_robust_decoder` (merged from main);
- `SpectralGap.no_uniform_poincare`, the sharp uniform-coercivity counterexample, with constant
  `(2π/L)²`;
- `WCTPlaneWave.expanding_domain_countermodel`;
- `FourierReceiver.cubic_quintic_generates_new_modes`;
- `PartIIIAnalytic.zero_cost_counterexample`;
- `PartIIIAnalytic.no_gradient_energy_control`;
- `Discrete.curvature_not_representation_invariant`.

## 3. Strengthened scopes

- **Radius.** Part II's equivalence went from radius one to every fixed radius `r ≥ 1`.
- **Dimension.** Part II's `P_TM ⊆ P_WCC` inclusion went from 1-D to `ℤ^(1+d)`.
- **Encoder class.** The class equality is now pinned to the fixed origin-marked encoding
  (`P_WCC_enc_id`). The manuscript now records that, for polynomial-time encoders, the `⊇`
  inclusion is trivial.
- **Flux inequality.** It went from an assumed premise to a derived theorem on the lattice, with a
  constant `Γ` that is uniform in the domain size.
- **Well-posedness.** It went from open to proved for the whole-plane variant (externally, with the
  definition match proved). It remains open on tori.

## 4. Conditional assumptions eliminated

- On the lattice, the flux inequality premise of the transport theorem is eliminated: it is derived
  in `lattice_flux_inequality`, and `lattice_curvature_time_bound` has no flux premise.
- In the conservation laws, the a priori bound `D(t) ≤ D₀` is no longer assumed. It is derived from
  conservation plus `bandpass_le_ham`.
- The existence premise is discharged at the local level (`exists_local_solution`,
  `local_conservation`).
- The stale "unproved" ledger entries were corrected in `formalization.yaml`, in the
  `superseded_statements` and `current_status` sections.

## 5. Unresolved theorems and their obstructions

Full statements are in `remaining-obstructions.md`.

| Item | Missing statement |
|---|---|
| ~~**D-1**~~ | **CLOSED 2026-11-05**: `P_WCCD_eq_P_TM`, `NP_WCCD_eq_NP_TM` (explicit single-tape TM `WCCDSweep.toTM`, bound `(128d+421)(n+2T+3)^(2d+3)`). |
| **CL-1** | Cook–Levin for `SAT_dense`. Decision: **not necessary** for any current claim, which uses only `SAT_dense ∈ NP_TM`; isolated as an obligation. |
| **M1-a** | Certified simulation `P^phys ⊆ P_TM`. Needs PDE error bounds at precision `η_n`. |
| **M1-b** | Physical realization of TM computation with a language-independent encoder. |
| **M2** | A universal lower bound. Proved to be at least as hard as `P ≠ NP`. |
| **M3-T** | Torus well-posedness. |
| **M3-G** | Global lattice existence. |
| **M3-C** | Lattice → continuum convergence. |
| **F-1** | Continuum flux inequality in Lean. |

## 6. Files

**Lean (new):**
- `lean/PVNP/WCCRadius.lean`
- `lean/PVNP/WCCGenerality.lean`
- `lean/PVNP/PhysicalModelAudit.lean`
- `lean/PVNP/WCTLattice.lean`
- `lean/bridge/MathBridge.lean` and `lean/bridge/README.md`

**Lean (updated):**
- `lean/PVNP.lean`
- `lean/audit/AxiomAudit.lean`
- `.github/workflows/lean.yml` (module list)
- `lean/formalization.yaml`
- `lean/README.md`

**Manuscripts:** the three `main.tex` files (formal-verification paragraphs; Part II gains Remark
`rem:verified-scope` and label `sec:uniform-bridge`). PDFs were rebuilt locally: Part I 63 pages,
Part II 35 pages, Part III 11 pages, with no undefined references.

**Reports:**
- `pvnp/proofs/final-formalization-report.md`
- `pvnp/proofs/theorem-manuscript-map.md`
- `pvnp/proofs/remaining-obstructions.md`

## 7. Test and audit results

| Check | Result |
|---|---|
| `lake build PVNP` | passes (7280 jobs) |
| `lake env lean audit/AxiomAudit.lean` with `check_axioms.py` | OK, 111 declarations |
| External `MathProofs.CubicQuinticFlow` | built (10.5 min); its six principal theorems use only standard axioms |
| `MathBridge.lean` | compiles; only standard axioms |
| Python regression tests (`unittest`) | 9/9 pass |
| Non-vacuity checks | pass: `P_WCCR 3 = P_TM`; `P_WCCR 0 = ∅`; the flux weight hypothesis is satisfiable; local lattice solutions exist; the physical encoder class contains the `P_TM` indicators |
| Adversarial review | no hypothesis restates its conclusion. Every conditional premise is either named in `conditional_premises_explicit` or discharged (lattice flux). Degenerate cases checked: radius 0 (excluded, `P_WCCR_zero`); `N = 1` lattice (formulas valid); `Γ = 0` (excluded by `hΓ`). |

## 8. PR links and SHAs

**PR #17** (integration; merged by the owner into the PR #14 branch):
- head `fb4852ef`;
- CI green (lean, build, semantic-test).

**PR #14:** merged by the owner into `main` as `a1293dc`.

**PR #19** (this program's Lean modules), <https://github.com/rickyjreyes/PVNP/pull/19>:
- base `main`; original development commits are recorded below;
- commits `522db46` (physical audit), `210ef45` (radius-r), `5c29bda` (merge main), `2bd6ba8`
  (generality), `82987fd` (lattice and bridge), `d2b019a` (ledger);
- CI on `2bd6ba8`: Lean run 41529538065 ✓, PDFs run 41529538053 ✓;
- CI on `82987fd` (lattice and bridge, 111-declaration audit): Lean run 41532337480 ✓, PDFs ✓;
- CI on `d2b019a` (ledger only): see the PR checks.

**Docs/manuscripts PR** (stacked on #19): consult the historical PR description and commit record.

## 9. Next highest-value task

**M3-T + F-1 on the 1-D/2-D torus.**
- Port the external interaction-picture proof (`CubicQuinticFlow`) from `H²(ℝ²)` to `H²(T²_L)` using
  Fourier series.
- In the same framework, derive the continuum flux identity `J' = 2 Im⟨[A,χ]ψ, Aψ⟩`.

This would replace the last analytic premise of the continuum transport theorem with a derived
statement, and it would give the frozen model's own geometry a well-posedness theorem. It still
proves no lower bound against all deciders, because M2 is provably as hard as `P ≠ NP`.
