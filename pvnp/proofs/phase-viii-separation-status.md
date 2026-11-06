# Phase VIII: the crossing-sequence route to the separation — what is proved and what remains

**Date:** 6 November 2026. **Lean modules:** `CrossingHennie.lean`, `CrossingSAT.lean`,
`CrossingSATSets.lean` (built on the Phase VII modules `CrossingTrace`, `CrossingSplice`,
`CrossingDiagonal`). **Result in one line:** the complete crossing-sequence splicing theorem and its
SAT application are kernel-checked, and they give the strongest lower bound this method can give
(near-quadratic, for single-tape machines). `SAT_dense ∉ P_TM` — hence `P_TM ≠ NP_TM` — is **not**
proved, and the method provably cannot prove it. Classical P versus NP remains open.

## 0. Phase VII verification

The full Lean CI run on `main` after PR #36 (`cbd9d2a`, run 42131080299) failed.

- `PVNP.CrossingTrace` did not compile: `CrossRight` and `CrossLeft` are `Prop` definitions with no
  `Decidable` instance, so the `if` in `event` could not be elaborated.
- `PVNP.CrossingSplice` had structure-update continuation lines that the parser rejects.

PR #37 repairs both. No statement changed.

## 1. The complete crossing-sequence splicing theorem (proved)

Fix a cut `κ`: the left half is cells `i < κ`, the right half is cells `i ≥ κ`. The crossing trace
`trace M κ c t` lists, in order, the post-transition state and direction of every step that moves
the head across the cut.

**`CrossingHennie.splice_core`.** Assume:

- the *active* run `A` and the *passive* run `P` start on the same side `s`;
- they have equal crossing traces over windows `ta` and `tp`;
- neither displays an answer before the end of its window.

Run the machine from the *mixed* configuration. It takes `A`'s control state and head, `A`'s tape on
side `s`, and `P`'s tape on the other side. Then for some `tz ≤ ta + tp`:

- the mixed run displays no answer before `tz`;
- at `tz` it displays `A`'s final answer if the common trace has even length, and `P`'s otherwise.

The proof is an induction over the list of crossing events. At each crossing the two runs exchange
roles. The invariant records each of the following.

- **Side.** Which side is currently scanned (`OnSide`, `stays_side`).
- **Control state.** The post-crossing states agree because the traces agree (`cross_of_event`).
- **Boundary position.** Both runs land on the cell adjacent to the cut (`cross_of_event`).
- **Tape writes on both halves.** The half away from the head is frozen (`run_offSide_tape`).
- **Segment lengths.** Variable lengths come from decomposing the trace (`trace_cons_events`).
- **First-answer semantics.** These are carried through every segment.

Everything is derived from `TM.next`. No rectangularity of crossing records is assumed.

**`CrossingHennie.hennie`** applies this to inputs. Take `|u| = |u'| ≥ 1` and the cut at `|u|`.
Suppose `u ++ v` and `u' ++ v'` have equal traces up to their first answers. Then `u ++ v'` gives its
first answer within `sx + sy` steps. That answer comes from the side on which the last segment runs.

**`splice_mem`** and **`CrossingSATSets.splice_nmem`** are the decision corollaries, for two members
and for two non-members of a decided language.

## 2. The SAT application (proved)

**Encoding.** `CrossingSAT.encSplit n g a b` is the dense encoding (`SATV.encDense`, `3n` bits per
clause) of a padded split 3-CNF. It has three blocks:

- an `a`-block, `(zᵢ ∨ zᵢ ∨ zᵢ)` if `aᵢ = 1` and the tautology `(zᵢ ∨ ¬zᵢ ∨ ¬zᵢ)` otherwise;
- `g` padding tautologies;
- a `b`-block, `(¬zᵢ ∨ ¬zᵢ ∨ ¬zᵢ)` or the tautology.

Its key facts:

- **Relation to the SAT language** (`encSplit_mem_iff`): `encSplit n g a b ∈ SAT_dense` holds iff
  `splitThreeSat` is satisfiable, iff `a ∩ b = ∅`. Here `SAT_dense` is the repository's ordinary
  CNF-SAT language, already shown to be in `NP_TM`.
- **Spatial separation** (`encSplit_layout`, `length_encSplit`): the input is
  `partA a ++ partP g ++ partB b`, of lengths `3n²`, `3ng` and `3n²`. Any cut `3n² + j` with
  `j ≤ 3ng` therefore splits the input into an `a`-part and a `b`-part.

The lower bound concerns an ordinary single-tape machine deciding `SAT_dense` on actual input
strings. No two-party protocol is assumed.

**Mixed acceptance.** `diag_mixed` is derived from `splice_mem`. Equal decision traces of the
diagonal instances `(a, ¬a)` and `(a', ¬a')`, at a cut in the padding, force `(a, ¬a')` to be
satisfiable. Applying this in both orders, `dtrace_injective` makes the decision traces injective on
the `2ⁿ` diagonal instances.

**The Phase VII premise is now derived.** `hmixed_of_halting` proves the hypothesis `hmixed` of
`CrossingDiagonal.diagonal_trace_capacity` for every `SAT_dense` decider that halts when it answers.
`diagonal_capacity` covers every decider, using decision traces. Both give
`2ⁿ ≤ (|Λ×Dir| + 1)^{T(3n(2n+g))}`.

## 3. The strongest unconditional lower bounds (proved)

The two ingredients are:

- `sum_trace_length_le`: across all cuts together there are at most `t` crossing events in `t`
  steps;
- double counting over cuts and inputs.

| Theorem | Statement (every single-tape `M` deciding `SAT_dense` within `T`) |
|---|---|
| `CrossingSAT.sat_time_lower_bound` | `(3ng + 1)·ℓ ≤ 2T(3n(2n+g))` whenever `2(\|Λ×Dir\|+1)^ℓ ≤ 2ⁿ` |
| `CrossingSAT.sat_time_lower_bound_sq` | `(3n²+1)⌊(n−1)/L⌋ ≤ 2T(9n²)`, `L = ⌊log₂(\|Λ×Dir\|+1)⌋+1`: `T(N) = Ω(N^{3/2}/log\|Λ\|)` |
| `CrossingSAT.sat_not_linear_time` | for every `C`, some `N` has `C·N < T(N)` |
| `CrossingSATSets.fooling_time_bound` | generic: injective decision traces on a family of size `F` at `G` distinct cuts give `Gℓ ≤ 2T` whenever `2(\|Λ×Dir\|+1)^ℓ ≤ F` |
| `CrossingSATSets.sat_time_lower_bound_sets` | `(3ng + 1)·ℓ ≤ 2T(3n(2·2ⁿ+g))` whenever `2(\|Λ×Dir\|+1)^ℓ ≤ 2^{2ⁿ}` |
| `CrossingSATSets.sat_time_lower_bound_near_sq` | `(3n2ⁿ+1)⌊(2ⁿ−1)/L⌋ ≤ 2T(9n2ⁿ)`: **`T(N) = Ω(N²/(log N · log\|Λ\|))`** |

The dependences are explicit:

- `n` is the number of information bits;
- `|Λ|` enters through `|Λ × Dir| = 3|Λ|`;
- `T` enters through the first-answer time `ftime ≤ T(N)`;
- crossing multiplicities enter through `Σ_cuts |dtrace| ≤ ftime`.

**The set family** (`CrossingSATSets`) gives the strongest bound. For `S, S' ⊆ {0,1}ⁿ`:

- `encSet n g S S'` excludes every point outside `S` in its first block and every point of `S'` in
  its last block;
- it is satisfiable iff `S ⊄ S'` (`encSet_mem_iff`);
- the diagonal instances `(S, S)` are **unsatisfiable**, so rejection splicing makes decision traces
  injective on `2^{2ⁿ}` instances (`dtraceSet_injective`);
- the information forced across every cut is therefore linear in the input length.

## 4. The ceiling: why this does not prove `SAT_dense ∉ P_TM`

1. **The bounds are fixed polynomials.** `SAT_dense ∉ P_TM` requires excluding *every* polynomial
   time bound. These theorems exclude only time `o(N²/(log N · log|Λ|))`.
2. **Crossing-sequence counting has a quadratic ceiling.** At one cut, injectivity on a family of
   inputs of length `N` can force at most `log_{3|Λ|+1} 2^N ≤ N` crossings, and there are at most
   `N + 1` cuts. So no counting argument of this kind certifies more than `O(N²)` single-tape steps.
   `sat_time_lower_bound_near_sq` reaches that ceiling up to logarithmic factors. Adding more cuts,
   repeated transport or interface geometry cannot go further: each is still bounded by the
   information carried across a cut, which is at most the input length.
3. **The hard families are easy.** Satisfiability of `encSplit` is disjointness, and satisfiability
   of `encSet` is non-inclusion. Both are decidable in polynomial time. Any lower bound obtained by
   looking only at such instances is at most their polynomial complexity. A superpolynomial bound
   needs instances on which SAT is hard. The crossing-trace information measure is blind to that
   hardness: it is bounded by input length either way.
4. **The bounds are model-specific.** A multi-tape machine decides both families in roughly linear
   time. A single-tape machine simulates `t` multi-tape steps in `O(t²)`, so a single-tape lower
   bound `L(N)` transfers to multi-tape machines only as `Ω(√L(N))`, which here is `Ω̃(N)`. That is
   nothing beyond reading the input. The class `P` is model-robust; these bounds are not.
5. **The curvature-confinement bridge (Part I) does not escape this.** Earlier phases proved, in
   Lean, that for NP languages every discrete curvature or depth lower bound is *equivalent* to the
   classical time lower bound (`Discrete.lower_bound_transfer`, `curvature_lower_bound_is_classical`,
   `P_TM_eq_curvature_rail`). So `conj:wcc_depth`, `lem:separator-price` and
   `prop:locked-expander-full` cannot be established by curvature reasoning without proving the
   classical statement itself. They remain **Open**.
6. **Known barriers.** Any proof of `SAT_dense ∉ P_TM` must avoid relativization (Baker–Gill–Solovay),
   natural proofs (Razborov–Rudich) and algebrization (Aaronson–Wigderson). Information-counting
   arguments of the kind formalized here do not address them.

No new mathematics establishing an algorithm-independent superpolynomial cost was found in this
phase. Nothing in this repository claims one.

## 5. The precise remaining theorem

```lean
-- PVNP.CrossingSAT
def SATLowerBound : Prop := SAT_dense ∉ P_TM
theorem satLowerBound_iff :
    SATLowerBound ↔ ∀ (M : TM) (p : Polynomial ℕ), ¬ M.Decides SAT_dense (fun n => p.eval n)
theorem P_ne_NP_of_satLowerBound (h : SATLowerBound) : P_TM ≠ NP_TM
```

`SATLowerBound` is the exact missing implication.

- It would give `P_TM ≠ NP_TM`, because `SAT_dense ∈ NP_TM` is proved.
- Through the Milestone 5 equalities `P_disc = P_TM` and `NP_disc = NP_TM`, it would also give the
  discrete WCC separation.

It is **unproved**. Classical P versus NP remains unresolved.

## 6. Ledger

No manuscript claim changes status: **70 Exact, 11 Refuted, 2 Restricted, 8 Open**. The Phase VIII
theorems are supporting results. They do not settle any of the open Part I claims.
