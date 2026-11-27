# Phase XXXII: composable verified Turing-machine programs (27 November 2026)

New Lean modules: `lean/PVNP/SweepCompose.lean` and `lean/PVNP/SweepLens.lean`. They are based on the
Phase XXXII PDE-detector branch.

## Outcome

- **Proved (kernel-checked).** A general sequential-composition theorem for the repository's
  sweep programs. Composition preserves the abstract semantics, the outputs and the exact charged
  transition counts. A compiled single-tape TM corollary follows.
- **Proved.** Long division in first-arrival form (`div_first`), the interface the composition
  theorem consumes.
- **Proved.** Verified alphabet translations through **track lenses** (`SweepLens`, §2a). A
  program over one alphabet runs on the chosen tracks of a common multi-track alphabet. Its
  first arrivals and exact costs transport, and independent tracks are left unchanged.
- **Not done.**
  - **Instantiation.** A common track alphabet, the concrete lenses for `MCell` and `DCell`, and
    multiplication in first-arrival form. With these, multiply-then-divide, which is certified
    fixed-point multiplication, follows by `seq_reach`.
  - **Downstream arithmetic.** Signed, rational, fixed-point multiplication and complex
    arithmetic.
  - **Numerical kernels.** Constants, convolution and the Taylor recurrence.
  - **The evaluator** (#99, which stays open).
- **Classical P versus NP remains unresolved.**

## 1. The obstruction and its resolution

A `Prog` bundles its data alphabet `D` as a field. Two verified programs cannot be chained
without casting along `P.D = Q.D`. Three pieces resolve this.

1. **`ProgOn D`.** A program over a fixed alphabet `D`, with translations `toProg : ProgOn D →
   Prog` and `ofProg : (P : Prog) → ProgOn P.D`. The identity `(ofProg P).toProg = P` holds by
   structure eta (`toProg_ofProg`, proved by `rfl`). Existing programs therefore enter the
   composition framework unchanged.
2. **`seq A B e`.** Instructions `A.I ⊕ B.I` and buffers `A.B ⊕ B.B`. The composite:
   - runs `A`;
   - turns `A`'s transition into its exit instruction `e` into a transition to `inr B.start`;
   - then runs `B`.
3. **`ReachFirst P e s l c`.** First arrival at `e` with exact cost `c`. The existing programs
   end in a `done` instruction that loops with identity trips. A plain `Reach` proof may
   therefore include loop trips, and exact cost addition requires the first arrival.
   `ReachFirst.reach` recovers `Reach`.

## 2. Theorems

| Theorem | Statement |
|---|---|
| `fscan_inl`, `fscan_inr`, `bscan_inl`, `bscan_inr` | the composite's scans are the component scans, with tagged buffers |
| `trip_inl`, `trip_inr` | the composite's trips are the component trips |
| `tripCost_inl`, `tripCost_inr` | the composite's trip costs are the component costs |
| `stepP_inl_ne`, `stepP_inl_exit`, `stepP_inr` | the composite's steps: `A`'s steps; the exit step to `inr B.start`; `B`'s steps |
| `reachFirst_lift`, `reach_lift_inr` | lifting first arrivals of `A` and reaches of `B` into the composite |
| `seq_reach` | **composition theorem**: `ReachFirst A e (a, l) l₁ c₁` and `B.Reach (start, l₁) (e_B, l₂) c₂` imply `(seq A B e).Reach (inl a, l) (inr e_B, l₂) (c₁ + c₂)` |
| `seq_tm` | the same on the compiled single-tape TM: the charged transition count is exactly `c₁ + c₂`, and the output tape represents `l₂` |
| `div_loop_first`, `div_reach_first`, `div_first` | long division first-arrives at `done` from `divInput W N D` in exactly `(W + 2)(4W + 2)` transitions, with quotient `N/D` and remainder `N mod D` |

Composition preserves:
- **machine semantics:** every composite step is a component step;
- **termination:** the composite reaches `B`'s exit;
- **output correctness:** the composite's final data is `B`'s output on `A`'s output;
- **intermediate representation:** `A`'s output is `B`'s input on the same tape alphabet;
- **charged costs:** exactly additive.

## 2a. Track lenses (`SweepLens`)

**Definitions.**
- A lens `ℓ : TrackLens E D` has `get : E → D` and `put : E → D → E`, with `get (put x d) = d`.
- `viaLens A ℓ z lift` runs `A` on `get` of each cell and writes the result back with `put`.
  Extension cells are written into `z`.
- `ℓ₂` is *independent* of `ℓ` (`Indep`) when `ℓ₂.get (ℓ.put x d) = ℓ₂.get x`.

| Theorem | Statement |
|---|---|
| `fscan_lens`, `bscan_lens`, `trip_lens`, `trip_lens_view`, `trip_lens_buf` | the lifted scans and trips are the original ones on the view |
| `tripCost_lens` | equal costs |
| `stepP_lens` | lifted steps are the original steps on the view |
| `reachFirst_lens` | **transport**: a first arrival of `A` from the view `l.map get` lifts to a first arrival from `l`, with the same cost and the same output view |
| `frame_trip`, `reachFirst_lens_frame` | **frame preservation**: if `A` never extends the tape, an independent lens sees no change |

**Consequence.** On a common alphabet, the division program can read its dividend directly from
the multiplication program's accumulator track. No copying program is needed. The other inputs of
division (the shifted divisor, the zero quotient and the marker) sit on tracks that the multiplier's
lens leaves unchanged.

## 3. What remains on the machine side

1. **Common alphabet.** The general transport is proved (`reachFirst_lens`,
   `reachFirst_lens_frame`). What remains is the concrete common alphabet with lenses for
   `Cell`, `MCell` and `DCell`, and multiplication and addition in first-arrival form.
2. **Layout conversion.** Where tracks cannot be shared, layout conversion is needed. Write programs that copy, shift and clear tracks, with first-arrival
   costs. One is needed between consecutive primitives, for example to move a product into a
   dividend track.
3. **Arithmetic.**
   - signed numbers as sign and magnitude over the verified unsigned operations;
   - fixed-point multiplication as multiply then shift by `p`, with the rounding certificate as
     in `fixdiv_certified`;
   - rationals as pairs reduced by Euclid's algorithm, built from verified division;
   - complex numbers as pairs.
4. **Numerical kernels and the evaluator.** Then constants (`C_A` through a certified tail sum),
   convolution and the Taylor recurrence. Finally the evaluator that composes them with the
   certified cutoff of `DetectorPDE.pde_detector_dynamic`.

## 4. Progress (registry)

The registry records the composition theorem as C7.8 and the track-lens transport as C7.9, both
in the evaluator category. That category moves from 4/7 to 6/9.

## Verification

Local, Lean 4.23.0, on the Lean tree of this pull request's head:
- `lake build PVNP` passed (7,439 jobs). `PVNP.SweepCompose` and `PVNP.SweepLens` build without
  warnings.
- Axiom audit:
  - The full transitive audit passed for all 1,334 declarations registered before `SweepLens`.
  - A targeted audit passed for the 15 `SweepLens` declarations.
  - Every audited declaration uses only `propext`, `Classical.choice` and `Quot.sound`, and no
    `sorryAx` occurs.
- The hosted workflow audits all 1,349 registered declarations at the pull-request head.

Later commits change documentation, the obligation registry and generated dashboard data only.
Hosted CI is recorded on the pull request.
