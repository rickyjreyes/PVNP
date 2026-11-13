# Part I I-3: nonglobal local minimum in the sign-blind SAT energy

**Date:** 13 November 2026
**Base:** PVNP main, after merge PR #93.
**Code:** `lean/PVNP/SATFalseWell.lean`
**Status:** Pending exact-head Lean build and axiom audit. Do not count as verified until CI succeeds.

## Claim and direct calculation

For variables `x0,x1,x2`, set

```text
F = (x0 ∨ x1 ∨ x2)
    ∧ (¬x0 ∨ x1 ∨ x1)^2
    ∧ (¬x1 ∨ x2 ∨ x2)^2
    ∧ (¬x2 ∨ x0 ∨ x0)^2
```

The superscript denotes a duplicated clause, not exponentiation in CNF.
The all-true assignment satisfies `F`.

Put `s_i = (1+cos θ_i)/2`. The exact existing Part I logical
penalty `PartIPsiSat.Elogic θ F` is

```text
E(x,y,z) = (1-x)(1-y)(1-z)
           + 2 [x(1-y)^2 + y(1-z)^2 + z(1-x)^2]
```

with `x=s_0`, `y=s_1`, `z=s_2`. The proof uses this actual
formula's clause semantics, not a substitute model.

For `0 ≤ x,y,z ≤ 1/8`:

```text
(1-x)(1-y)(1-z) ≥ 1-x-y-z
(1-u)^2 ≥ 3/4                for 0 ≤ u ≤ 1/8
E(x,y,z) ≥ 1+(x+y+z)/2.
```

Thus `E(0,0,0)=1` is a strict minimum within the small nonnegative
score box, while `E(1,1,1)=0`. In particular, the all-false phase
`θ0=θ1=θ2=π` is a nonglobal local minimizer of the logical energy.

The sign-blind added coupling/curvature energies in
`InterwovenSAT.energySB` are nonnegative on admissible states and
vanish at both binary fields `ψ_i=-1` and `ψ_i=1`. Consequently
the false configuration is a nonglobal local minimum for every
`λ,μ≥0`. (The theorem proves the local-minimum inequality throughout
an explicit phase-score neighborhood; it does not prove a strictly
positive Hessian on every infinite-dimensional direction.)

## Mathematical significance

The original Part I conjecture I-3 asks for a field evolution from a
uniform SAT-independent initialization into an admissible satisfying
lock. The exact static energy equivalence already proved in Phase XX
does **not** imply that local energy-descent evolution finds it.
The falsifying example excludes a general claim that every local energy
minimum is a SAT certificate.

The theorem does not show all gradient trajectories get trapped,
does not compare with arbitrary noise/annealing/global methods, and
does not imply the frozen *Hamiltonian* WCT PDE is a gradient flow.

**Unresolved:** a uniform physical reduction and dynamics that reach
SAT solutions with charged preparation, energy, time and precision;
an all-decider resource lower bound; equivalence to classical P/NP.
The four Open manuscript claims remain Open.

## Verification gate

```bash
cd lean
lake build PVNP.SATFalseWell
lake build PVNP
lake env lean audit/AxiomAudit.lean > /tmp/pvnp-axioms.txt
```

The standard workflow must certify that no `sorry`, `admit` or
nonstandard axioms are needed. No manuscript status is changed merely
by adding the new restricted obstruction theorem.
