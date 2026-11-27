# Phase XXXII: composable verified Turing-machine programs (27 November 2026)

New Lean module: `lean/PVNP/SweepCompose.lean`. It is based on the Phase XXXII PDE-detector branch.

## Outcome

- **Proved (kernel-checked).** A general sequential-composition theorem for the repository's
  sweep programs. Composition preserves the abstract semantics, the outputs and the exact charged
  transition counts. A compiled single-tape TM corollary follows.
- **Proved.** Long division in first-arrival form (`div_first`), the interface the composition
  theorem consumes.
- **Not done.**
  - **Alphabet translations.** The verified primitives use different cell alphabets: `Cell` for
    addition, `MCell` for multiplication, `DCell` for division. Composing different primitives
    needs verified alphabet embeddings or a common track alphabet, and layout-conversion
    programs.
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

## 3. What remains on the machine side

1. **Common alphabet.** Embed `Cell`, `MCell` and `DCell` into one track alphabet. Prove that
   each primitive transports along the embedding, preserving its `ReachFirst` statement.
2. **Layout conversion.** Write programs that copy, shift and clear tracks, with first-arrival
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

The registry records the composition theorem as C7.8 in the evaluator category. That category
moves from 4/7 to 5/8.

## Verification

VERIFICATION
