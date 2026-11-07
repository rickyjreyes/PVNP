# Independent supplement — fixed-mass nodal coercivity

> **Publication status:** Historical manuscript/supplement. The [consolidated PVNP volume](../consolidated-wave-computation/README.md) is the one current release. The separate PDF may be retired from the current tree after a successful consolidated build; this source and its original historical record are retained.


[LaTeX source](../../papers/supplement-fixed-mass-nodal-coercivity/main.tex) · [Primary consolidated PDF](../consolidated-wave-computation/paper.pdf) · [Lean proof](../../../lean/PVNP/FixedMassNodal.lean)

This note is preserved as an appendix in the [single consolidated PVNP volume](../consolidated-wave-computation/README.md). Its source and earlier compiled history are retained.

This is an **independent auxiliary research continuation**, not an amendment to the author's original P versus NP proof or the three PVNP manuscripts.

The analytical theorem proves density-weighted Laplacian coercivity on **fixed-domain, positive-mass, bounded-Hamiltonian H² sublevels**, even when fields have zeros, using compactness and periodic integration by parts. The result is conditional on the exact functional and domain assumptions. The Lean module proves an exact connected two-node version and an algebraic readout-cost transfer, **not** the continuum compactness argument or the Hamiltonian PDE itself.

No universal input-size-independent constant, full machine lower bound, or P-versus-NP separation is claimed.
