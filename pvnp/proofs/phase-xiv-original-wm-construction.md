# Phase XIV: original W_M lattice-word and state-bit construction

**Starting point:** merged Phase XIII PR #58 at `4b1b292`.
**Main problem:** The original II-10 theorem requires both unrestricted polynomial-radius
`FP (originalWindowCode p)` and `FP (originalInputCode M p)`, as well as the
complete round-by-round compilation proof. The former is known only in a
restricted constant-radius case here. The full II-10 manuscript claim is
**still Restricted**.

## Exact lattice word

`TwoPhaseWindowWord.lean` introduces

```lean
windowWord L :=
  replicate (L+1) true ++
  false :: (range (2*(L+1)+1)).map
    (fun j => decide (0<j ∧ j<2*(L+1)))
```

and derives:

- `bitmap_eq_interior`, the complete bitmap list, not merely a single bit;
- `windowWord_eq_latCode`, equality with the original manuscript encoding;
- `originalWindowCode_eq_windowWord`, for every natural polynomial `p` and input `x`;
- `windowWord_length`, exact length `3L+5`.

The crucial new fact is complete **output equality**, not an assumption about
the encoder's runtime.

## First explicit original-window MTM output witness

`TwoPhaseConstantWindow.lean` implements `zeroWindowMTM` with states `Fin 7`
and `Option Bool` symbols. Its six transitions write the literal full code
`[true, false, false, true, false]`, including a blank at the output end.

```lean
zeroWindowMTM_outputs (x : List Bool) :
  zeroWindowMTM.Outputs x [true,false,false,true,false] 6

zeroWindowCode_fp :
  FP (originalWindowCode (0 : Polynomial ℕ))
```

The proof follows the existing `PartIIUniform.latMTM_outputs` pattern:
explicit finite transition states, first-halt proof, output tape correctness,
constant polynomial bound. This is an actual restricted `FP` witness,
**not** a claim of `FP (originalWindowCode p)` for arbitrary polynomial `p`.

## Canonical original state-bit encoding

`pvnp/two_phase_state_serializer.py` writes the three fixed header bits
and the tagged `pack (identityBits M s)` tail from the actual
`TwoPhaseDecoder.stateBits` formula. A supplied enumeration of the finite
alphabet represents Lean's `Fintype.equivFin (S M)`; the Python ordering must
be chosen equal to that Lean order for bit-for-bit cross-language comparison.

The input encoder uses the original alphabet
`Γ × Option (Q ⊕ Q×Mv) × Bool`, preserves the initial head at cell zero,
writes input symbols inside the bounded lattice and blank symbols elsewhere,
and gives all other states phase false. Each state code is of width
`3+2*card(S M)`. These are explicit reference routines, not a formal Lean
TM or a claimed `FP` proof for the original encoder.

Five independently executed Python tests pass:
- every finite alphabet state has a distinct fixed-width code;
- the tag bits and acceptance/rejection headers are correct;
- the origin and empty input are covered;
- all Boolean inputs through length 4 and several radius polynomials
  agree with independent per-site serialization;
- malformed duplicate enumerations are rejected.

## Remaining mathematical obligations

1. Replace the restricted zero-radius writer with a parameterized finite
   `MTM` that consumes `p(|x|)` and emits the exact full lattice word.
   Reuse `CookLevin.Gen.HPar.horner_phase` and prove the output convention
   and polynomial transition count.
2. Construct the original input-code writer using the actual fixed finite
   `stateBits M` encoding and prove its polynomial-time `MTM.Outputs`.
3. Instantiate `TwoPhaseUniform.originalUniform M p` with **proved** FP
   witnesses. Do not add the FP premises as parameters to the final theorem.
4. Re-run the entire Lean kernel build and axiom audit.
5. Keep `I-16` Open: no universal superpolynomial SAT lower bound follows
   from these construction results.

## Verification

The Python serializer tests passed locally. No Lean toolchain is available
in this execution environment. GitHub Actions issue #59 has caused jobs to
fail before executing any steps on recent commits, including the previous
merged PR #58. The new Lean modules have been added to the audit and workflow,
but must **not** be described as kernel-checked until exact-head CI or an
independent local Lean build completes successfully. Do not merge this
branch while those verification gates remain unresolved.

The official 91-claim inventory is unchanged.
