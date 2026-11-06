# Part I I-12 and I-20: computational-model reformulation

This note records the 6 November 2026 amendment of the original Part I manuscript. The original counterarguments in Lean and Git history are preserved.

## I-12: a conditional compatibility result, not a physical P-vs-NP proof

**Superseded claim:** even if the classical classes P and NP coincided, every SAT algorithm would have to break the WCT curvature/energy rails. That universal assertion is not justified by the frozen model with polynomial-time charged encoders.

**Amended statement:** fix the frozen physical class `PhysicalAudit.PhysConst κ β γ polyEnc`. This restricts the input encoder to indicators of languages in `P_TM`, charging all work needed to calculate the decision bit, and leaves only the field evolution at constant cost. The kernel-checked equivalence

`PhysicalAudit.PhysConst_polyEnc_eq_P_TM`

means that *if hypothetically* `P_TM = NP_TM`, then dense SAT is physically implementable in the restricted model:

`PartISeparation.PNP_SAT_physically_constant`.

Therefore the hypothetical claim “SAT remains physically impossible in this model even if P=NP” *implies P!=NP*:

`PartISeparation.category_error_claim_implies_classical`.

**Interpretation:** these are conditional implications. Neither P=NP nor P!=NP is proved; constant field evolution does not imply zero encoder computation. An unconditional physical lower bound needs a precisely specified, more restrictive admissible device/encoder class, a proof it excludes *all* alternative implementations, and fully charged resources.

## I-20: do not use a high-complexity explicit state as a short NP witness

**Superseded conjecture:** a target state simultaneously satisfies superpolynomial description complexity and serves as an explicit polynomial-size NP witness. Under a decoder `D` that accepts literal descriptions with additive overhead `c`, these are incompatible.

**Amended proved obstruction:** for finite strings `s`,

`K_D(s) <= |s|+c`,

so `K_D(s_n) > q(n)+c` implies `|s_n| > q(n)`. The state itself cannot be an explicit witness of length at most `q(n)`. Already kernel-checked:

- `PartISeparation.Kc_le`
- `PartISeparation.high_K_not_poly_witness`

This does **not** exclude a different short certificate `w`. The logical witness statement is `x in L iff exists w of polynomial length with V(x,w)=1`. No rule requires the verifier to reconstruct `s_n` unless the physical computation model *specifically* imposes that requirement and charges it.

### Distinct resource obligations

For an instance `x` and a certificate `w`, specify separately:
1. `C_prep(x,w)`: cost to produce a designated target field from initialized data.
2. `C_ver(x,w)`: cost to check the supplied certificate, including encoding and any physically necessary state preparation.
3. `C_dec(x)`: cost to decide the language on `x` without a certificate.

A preparation lower bound for one target field **does not** prove a decision lower bound for all algorithms. To establish a physical NP/P separation, prove uniformly polynomial-size certificates and charged polynomial-resource verifier, *and* a superpolynomial worst-case lower bound against every admissible decider, with identical resource accounting. This open premise is also isolated in the existing conditional implication `PartISeparation.np_type_conditional`.

## Claim-inventory provenance

| Snapshot | Exact | Restricted | Refuted | Open | Total |
|---|---:|---:|---:|---:|---:|
| Original October 27 manuscript | 70 | 2 | 11 | 8 | 91 |
| After II-7, II-8, II-17 | 73 | 2 | 8 | 8 | 91 |
| After I-10, I-13 | 75 | 2 | 6 | 8 | 91 |
| Proposed I-12, I-20 amendments | 77 | 2 | 4 | 8 | 91 |

**Critical scope:** two previously refuted claims are replaced by *different, narrower, kernel-checked propositions*. This is a manuscript-alignment metric, **not** proof progress on `CrossingSAT.SATLowerBound`, proof of a physical separation, or evidence that WCT realizes the new open premises. The original invalid assertions remain invalid and documented.

Exact-head CI must confirm the Lean and PDF builds before those check results are called passed.
