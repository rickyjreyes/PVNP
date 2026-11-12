# Phase XVIII: exact barriers for the claims that stay open

**Date:** 12 November 2026
**Claims:** I-32, I-37, I-3, I-16, I-2, III-22
**Outcome:** no status changes. Each claim stays Open, now with a kernel-checked statement of
what deciding it would take, or of what the frozen model cannot do.
**Lean:** `lean/PVNP/ExpanderInterfaceBarrier.lean`, `lean/PVNP/TorusNoLocking.lean`,
`lean/PVNP/DepthBarrier.lean`

## I-32: expander interface growth is as hard as `P_TM ≠ NP_TM`

Hypothesis `prop:locked-expander-full`: every permitted decider of a hard-instance family has a
worst-case input whose field trajectory has separator measure at least `c₀ 2^{γn}`.

`ExpanderGrowth` states it for a device class in its weakest form (the bound only for infinitely
many lengths); the every-length form implies it (`expanderGrowth_of_every_length`). The separator
measure is the Euclidean length of the decision interface `∂{Re ψ > 0}`, as for I-31.

The frozen model contains the charged constant devices of `PhysicalAudit` (polynomial-time
indicator amplitude, exact solution `A e^{−iωt}`). Their fields are constant in space, so their
separator measure is `0` at every time (`sep_const`). Therefore:

| Theorem | Statement |
|---|---|
| `expanderGrowth_const_iff` | in the charged constant class, the hypothesis for `Lang` holds iff `Lang ∉ P_TM` |
| `expanderGrowth_SAT_iff` | for dense SAT: hypothesis ⟺ `P_TM ≠ NP_TM` |
| `expanderGrowth_implies_P_ne_NP` | in any device class containing the charged constant devices, hypothesis for dense SAT ⟹ `P_TM ≠ NP_TM` |
| `expanderGrowth_false_of_mem_P` | for every language in `P_TM` the hypothesis fails |

So it cannot be proved without proving `P_TM ≠ NP_TM`, and in the constant class it cannot be
refuted without proving `P_TM = NP_TM`. A "hard-instance family" whose language is decidable in
polynomial time (for example Tseitin formulas, `TseitinSAT.tseitin_mem_SAT_dense_iff_comp`)
cannot satisfy it.

## I-37 and I-3: the frozen dynamics cannot lock

Part I defines a curvature-locked state through the evolution (`dS/dt → 0`, `∇W_ψ → 0` "under the
WCT/WCC evolution rules"), and I-3's criterion asks for `∇φ → 0`. A physical realization needs
convergence to the set `Λ` of locked states, and a readout that tolerates preparation and noise
errors, i.e. Lyapunov stability of `Λ`.

**Time reversal** (`isSolution_reverse`). With `conjH v = (conj v_{−k})_k`, complex conjugation in
Fourier coefficients, `t ↦ conjH (u (−t))` solves the frozen equation whenever `u` does. The proof
works in the repository's own formulation `Torus.IsSolution` (coefficientwise ODE in `H²(T_L²)`),
using `om L κ (−k) = om L κ k`, `fnl(z̄) = conj fnl(z)` and the conjugation rule for Fourier
coefficients (`fc_conj`).

**No locking** (`no_locking`). Let `Λ` be nonempty, Lyapunov stable for the frozen dynamics
(`StableLock`) and invariant under `conjH`. If a solution converges to `Λ`, its initial state lies
in the closure of `Λ`.

*Proof.* Given `ε`, take `δ` from stability and `T` with `dist(u T, Λ) < δ`. The reversed and
shifted trajectory `v t = conjH (u (T − t))` is a solution starting within `δ` of `Λ` (`conjH` is an
isometric involution preserving `Λ`), so it stays within `ε` of `Λ`; at `t = T` it equals
`conjH (u 0)`, so `dist(u 0, Λ) < ε`. ∎

`Λ` may be the phase orbit `{e^{iθ} v}` of any state with a real field (`phaseOrbit_conj`) — the
shape of a standing-wave lock of a binary-phase (`0`/`π`) ψ-SAT encoding — or the set of all
real-field states (`realStates_conj`).

**Consequence.** In the frozen model a toroidal locking scheme is either not robust (its lock set
is unstable) or trivial (the encoder already prepares a locked state and the dynamics computes
nothing) (`unstable_or_unreachable`). A realization of §12.3 or of I-3's criterion needs dissipative
or forced dynamics, which the frozen model ("no forcing during the run") excludes.

**Why I-37 stays Open.** The manuscript never defines the "phase-locking and flux constraints
corresponding to the satisfaction of all clauses", so the equivalence is not a well-posed
statement. The obstruction applies to every definition whose locks are approached by the frozen
evolution and are stable.

## I-16: `conj:wcc_depth` for dense SAT is `P_TM ≠ NP_TM`

`PartISeparation.WCCDepth_iff_not_P_TM` gave `WCCDepth L ↔ L ∉ P_TM`. Composing with the uniform
Cook–Levin theorem:

* `wccDepth_SAT_iff`: `WCCDepth SAT_dense ↔ P_TM ≠ NP_TM`;
* `wccdDepth_SAT_iff`: the same on `ℤ^(1+d)`;
* `uniform_depth_SAT_iff`: `SAT_dense ∉ P_disc ↔ P_TM ≠ NP_TM` in the uniform model.

I-16 is the classical question; it is not resolved here. The barrier list in
`phase-xvii-math-frontier.md` (relativization, natural proofs, algebrization) applies to any
attempt.

## I-2: the explicit-state reading is false

"Under one fixed preparation, verification and resource model, there exists a coherent target
state in `NP_st \ P_st`." If a state is an explicit finite description and constructors are
machines of `def:tm` started on a trivial input, `TwoPhaseFixedWord.literalMTM s` writes `s` in
`|s| + 1` transitions on every input (`explicit_state_constructible`). In the construction model
`explicitModel V`, every state is constructible and `NPst \ Pst = ∅` for every verifier `V`
(`explicit_no_separation`). This is the construction-side companion of I-20's size obstruction.

A non-trivial reading needs a different notion of state: families indexed by the input length,
or physical fields with a specified preparation model. The manuscript fixes neither, so I-2 stays
Open. (Informal remarks, not formalized here: for families with several verified states per
length a counting argument gives a verified non-constructible family with no complexity content;
for verifiers with a unique accepted state per length, prefix search shows that the conjecture
would imply `P_TM ≠ NP_TM`.)

## III-22: the remark and its physical sentence

§8 states that no equivalence `P^phys = NP^phys ⟺ retrocausality` is proved; that is a correct
statement about the absence of a proof, not a mathematical claim. Its sentence "inverse dynamics
need not efficiently solve SAT" has an exact form for the frozen model:

* `backward_eq_forward_conj`: if `u, v` are solutions with `v 0 = conjH (u 0)`, then
  `u (−t) = conjH (v t)` for every `t` (uniqueness from `global_wellposed`);
* `flow_neg`: `Φ_{−t} = conjH ∘ Φ_t ∘ conjH` for the flow map.

Running the frozen dynamics backward is forward computation with the encoder and decoder composed
with `conjH`, which is a reindexing and conjugation of Fourier coefficients. III-22 stays Open
(interpretive); this result is recorded as supporting material, not as a proof of the remark.

## Verification

Local, Lean 4.23.0, on the branch head: `lake build PVNP` 7,390 jobs; axiom audit 678 declarations
(30 new), only `propext`, `Classical.choice` and `Quot.sound`.
