# I-11 exact countermodel: unrestricted encoder class is not polynomial-time computation

**Date:** 6 November 2026. **Model:** the constant-amplitude classical WCT solution
already formalized in `PhysicalModelAudit.lean`.
**Lean:** `lean/PVNP/PhysicalDiagonal.lean`.

## Mathematical result

Every ordinary finite-state, finite-alphabet deterministic Turing machine in
`PVNP.Discrete.TM` can be normalized to a finite table `t`, with a canonical,
injective binary code `encodeTable t` and a strict decoder `decodeTable`.
The existing theorem `P_TM_eq_tables` guarantees that no polynomial-time
language is lost through this normalization.

For a table `t`, define `A_t(x)` to mean that `TM.ofTable t` produces
`true` at its **first** answer on `x`. Define a diagonal language

```text
D = { x | ∃ t, decodeTable x = some t ∧ ¬ A_t(x) }.
```

For each canonical code, the codec round-trip lemma proves

```text
encodeTable t ∈ D  ↔  ¬ A_t(encodeTable t).
```

If any polynomial-time table machine `t` decided `D`, its correctness
would imply `A_t(x) ↔ x ∈ D` for every `x`. Substitute `encodeTable t`
to obtain `A_t(encodeTable t) ↔ ¬ A_t(encodeTable t)`, a contradiction.

Thus the exact theorem `diagonal_not_mem_P_TM` states `D ∉ P_TM`.
This is the standard diagonal separation of decidable polynomial time from
**all** languages, not an NP-versus-P separation. No NP membership for `D`
is claimed or needed.

The existing `unrestricted_encoder_trivializes` theorem says that the
constant-amplitude physical model `PhysConst κ β γ Set.univ` contains
**all** languages when encoders are arbitrary. Combining both results gives

```lean
unrestricted_phys_ne_P_TM (κ β γ : ℝ) :
  PhysConst κ β γ Set.univ ≠ P_TM
```

for every real coefficient choice, independently of the truth of P versus NP.

## Status impact and non-claims

**I-11 remains Restricted:** the manuscript's original rail-based physical
computational class has not been identified with this unrestricted-encoder
class, nor has a certified continuum-PDE-to-single-tape-TM simulation for
charged polynomial resources been constructed. The new theorem disproves
a broader *uncharged* equivalence, and explicitly isolates the encoder
uniformity requirement. Existing exact `P_disc_eq_P_TM` remains unchanged.

**II-10 remains Restricted:** a uniform polynomial-time transducer for the
specific `PartIITwoPhase.W_M` encoder/lattice/decoder is still needed.
The existing one-cell `PartIIUniform.P_Turing_subset_P_disc` is a different
construction and is not a replacement.

**I-16, I-31, I-32:** no universal superpolynomial SAT lower bound is proved.
The expander/parity bypass established in Phase IX still applies to
unrestricted-algorithm claims.

**I-2, I-3, I-37, III-22:** no new resolution; phase-locking and toroidal
locking require frozen input-dependent logical penalties, solution semantics,
and quantifiers before an iff theorem can be checked, and the arrow-of-time
remark is not a mathematical equivalence claim.

**II-24:** already proved as a *conditional* theorem in merged PR #54. The
91-claim inventory must be updated only with a CI-verified, registered status
change; this PR does not modify the generated dashboard or fabricate new
completion counts.

## Verification

The module is imported by the root `PVNP` tree and individually built by
CI. Its five principal theorems appear in `audit/AxiomAudit.lean`.
Require all three exact-head GitHub checks to pass before merging.
