# Part I: bounded crossing-record capacity

**Repository scope:** `lean/PVNP/CrossingCapacity.lean`, built upon `Communication.lean` and `SplitSATCapacity.lean`.

## Established statement

For the indexed split 3-CNF SAT family on two private (n)-bit inputs, let a
deterministic protocol produce a cut record in

[
  R_m(Q)=(\operatorname{Option}(Q))^{\{0,\ldots,m-1\}},
]

where (Q) is finite. `none` records the end of a shorter crossing record.

Assume (a) correctness for the same split-SAT language, and (b) **rectangular
splicing** for the complete record, so equal records on ((a,b)) and
((a',b')) imply the same record on both crossed inputs.

The diagonal split-SAT inputs ((a,\neg a)) form a fooling family with
(2^n) members. By the proved injectivity theorem in `Communication.lean`,
their complete records are distinct. As a record has ((|Q|+1)^m) potential
values, the new theorem gives

[
  \boxed{2^n\le (|Q|+1)^m}.
]

`bounded_crossing_record_capacity` implements the conclusion, and
`no_short_crossing_record` states the equivalent contradiction when the
record alphabet is too small.

This extends the prior fixed-length transcript result to bounded
option-state records. The count is conservative: it allows arbitrary
`none` placements, not only trailing `none`, so it is not assuming free
variable-length signaling.

## Actual single-tape machine facts

The same module uses the repository's ordinary finite-state, bi-infinite
tape `Discrete.TM`, not an oracle machine:

- `same_scanned_symbol_same_instruction`: two configurations with equal
  control state and equal currently scanned symbol use the same instruction.
- `one_tape_head_speed`: the head moves at most one cell per step.
- `right_crossing_is_adjacent`: one rightward cut crossing ends immediately
  at the right-neighboring cell.

These are genuine machine transition facts, but **not** a complete
crossing-sequence splicing theorem for arbitrary executions.

## Next theorem for the original Part I proof

Define the actual crossing-record extraction on `TM.run`, including first
halting output, arbitrary tape reuse, and the two halves' input layout.
Prove rectangular splicing for this extracted record **from the TM transition
table**, or identify any extra information required by the correct
splicing invariant. Then combine it with this finite-state counting result
and convert crossing counts to machine steps.

The existing bound is information-theoretic and, for a fixed finite control
alphabet, only forces a lower bound linear in (n) for the length of one
record. It does **not** establish SAT outside P or a superpolynomial bound.
Any stronger claim requires an independent, all-algorithm theorem.

No change to the 70/91 manuscript Exact count is justified by this
supporting module. The original Part I `conj:wcc_depth`,
`lem:separator-price`, and `prop:locked-expander-full` remain open.
