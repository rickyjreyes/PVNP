# Milestone 5: checkpoint of the uniform simulator infrastructure (5 November 2026)

This checkpoint preserves the **committed** code from the interrupted Milestone 5
development session. It is intentionally **not** a claim of completion of the
manuscript's discrete computational equivalence.

## Included in this checkpoint

- `lean/PVNP/UniformSimLib.lean`: reusable forward/backward scan lemmas,
  round-trip reachability and cost accounting, folded-tape representation,
  and `UniformSim.simTrip_spec` proving one round trip simulates one
  step of the manuscript's Turing machine.
- `lean/PVNP/UniformSimProg.lean`: the multi-track sweep-program structure,
  state definitions, transducers, and control flow for the intended uniform
  automaton simulation.
- Imports and CI compilation targets to check both modules, plus the axiom
  audit for selected proved lemmas.

## Explicitly not yet established

- The remaining *semantic* proof that each complete sweep-program
  automaton round computes `UWCC.step` for all dimensions and radii.
- The full polynomial overhead bound for the lattice generator,
  encoder, local evolution, and decoder.
- `PartIIUniform.P_disc ⊆ P_TM` and
  `PartIIUniform.P_disc = P_TM`.
- The uniform verifier-class equality for NP.

The interrupted agent's notes mentioned additional locally compiling phase
proofs (initialization, parse, grow, load, pack, rotations). Those proofs
were **not present in the committed branch** when this checkpoint was made
and therefore are not part of this merge. Recover them from the previous
workspace if possible; otherwise reimplement them on a successor branch.

The manuscript-to-Lean inventory is intentionally unchanged.
No Restricted claim is upgraded by merging this checkpoint.
