# Split 3-CNF SAT: all-protocol deterministic cut bound with noise-aware resource accounting

**Scope:** A model-wide lower bound for **exact deterministic two-party distributed SAT protocols**, not the unrestricted centralized SAT problem. This closes an explicit missing reduction in the PVNP communication argument: the actual 3-CNF satisfiability semantics, not just DISJ, are now mechanized in Lean.

## 1. Uniform 3-CNF reduction from disjointness

Alice has \(a\in\{0,1\}^n\); Bob has \(b\in\{0,1\}^n\). Both know public variable names \(z_1,\ldots,z_n\). Alice contributes the clause
\[
(z_i\lor z_i\lor z_i)
\quad\text{iff }a_i=1,
\]
and Bob contributes
\[
(\neg z_i\lor\neg z_i\lor\neg z_i)
\quad\text{iff }b_i=1.
\]
All other clauses are **omitted**; there is no signaled dummy constraint. This defines a standard 3-CNF with \(n\) variables and at most \(2n\) width-three clauses, generated from the two private inputs in \(O(n)\) local work.

The union \(F(a,b)\) is satisfiable if and only if no coordinate has both \(a_i=b_i=1\):
\[
\boxed{\quad F(a,b)\in3SAT
\iff \forall i,\neg(a_i\land b_i)
\iff \operatorname{DISJ}_n(a,b).\quad}
\]
For the forward direction, conflicting positive and negative unit clauses at any one coordinate contradict each other. For the reverse direction, choose \(z_i=a_i\). Each Alice clause is satisfied automatically, and a Bob clause forces \(a_i=0\) exactly when the two inputs are disjoint. Triplication preserves the truth of each unit clause.

**Lean:** [SplitSATCapacity.lean](../../lean/PVNP/SplitSATCapacity.lean) defines the *indexed satisfaction semantics* of these 3-clauses and proves the equivalence for **all** \(n,a,b\). The Lean object is not a serialized DIMACS or list CNF; those serialization and runtime details are a separate task in the O2 proof charter.

## 2. Deterministic all-protocol fooling-set theorem

Consider **any** correct deterministic two-party protocol deciding whether \(F(a,b)\) is satisfiable. Its complete transcript is a word of \(m\) symbols from an alphabet of size \(q\). The complete transcript must include any round-termination or final-output metadata that carries information; no uncharged length, timing, or analog metadata may serve as a side channel.

For the ordinary deterministic communication model, inputs generating one full transcript form a **combinatorial rectangle**. Formally, if the transcript at \((a,b)\) equals that at \((a',b')\), the two cross-inputs \((a,b')\) and \((a',b)\) yield that same transcript. A final answer is a function of that transcript (so acceptance is transcript-determined). These properties are *model assumptions*; they are standard for deterministic two-party protocols, but they do not describe arbitrary continuous coupled PDE evolution without a separate realization theorem.

Take the \(2^n\) accepting pairs \((x,\neg x)\). If two such pairs shared an accepting transcript, rectangularity and soundness would force both \((x,\neg y)\) and \((y,\neg x)\) to be disjoint. Hence \(x=y\). Therefore there must be at least \(2^n\) distinct full transcripts:
\[
\boxed{\qquad 2^n\le q^m.\qquad}
\]
For binary transcript symbols \(q=2\), **every** exact deterministic protocol in the split-input model uses \(m\ge n\) total message bits in the worst case (under fixed-length full-transcript accounting).

**Lean:** The new module specializes the existing kernel-checked fooling-set theorem in \`PVNP.Communication\` to the **actual 3-CNF encoding**, proves the required SAT correctness/diagonal acceptance, and obtains both \(2^n\le q^m\) and \(m\ge n\) for \(q=2\). This is a true **all-protocol lower bound within a declared distributed communication class**. It is *linear*, not exponential, in the required binary communication.

## 3. Deterministic bounded-noise physical channel packing

To translate abstract alphabet size to physical observability, state an additional **nontrivial instrumentation assumption**:

- Each transmitted scalar signal level lies in \([-A,A]\), with \(A>0\).
- An adversarial measurement error of magnitude at most \(\eta>0\) is possible.
- Every pair of *distinct decoded symbols* remains distinguishable for **all** allowed errors in that same slot. Thus code-level intervals of radius \(\eta\) must be nonoverlapping, requiring center separation \(>2\eta\). Exactly touching intervals can also be ambiguous, so a strict gap is appropriate.
- There is no uncharged phase, frequency, timing, spatial position, correlated-history, or other side channel.

Partition \([-A,A]\) into
\(Q=\lceil A/\eta\rceil\ge1\) contiguous intervals, each of length at most \(2\eta\). No two allowed distinct signal centers can lie in the same interval. Thus
\[
q\le Q=\left\lceil\frac A\eta\right\rceil.
\]
Combining this with the Lean-proved discrete transcript inequality gives the **analytic noise-aware corollary**:
\[
\boxed{\quad
2^n\le\left\lceil A/\eta\right\rceil^m,\qquad
n\le m\log_2\left\lceil A/\eta\right\rceil.
\quad}
\]
For \(Q=1\) and \(n>0\), no such exact protocol exists. If \(Q\ge2\), then
\[
\boxed{\quad m\ge\frac{n}{\log_2Q}.\quad}
\]

**Important scope:** The packing argument is a conventional mathematical derivation **not currently Lean-formalized**. The Lean module certifies the \(q^m\) part and does not import channel-amplitude or noise hypotheses as facts about the WCT PDE. The bound requires deterministic worst-case (adversarial) noise reliability, not merely small average error or statistical distinguishability. The received signal is scalar with an independently decoded level in every charged slot; a joint waveform decoder may be a different physical model.

## 4. Why this does not establish P != NP

This restricted instance family is *easy for a centralized machine*: simply scan \(i=1,\dots,n\) and reject if \(a_i=b_i=1\). The algorithm takes \(O(n)\) time with both inputs available. The communication lower bound reflects the **private partition**, not intrinsic SAT decision difficulty. It cannot be converted into an exponential SAT running-time lower bound by interpreting a message bit as a curvature unit.

Similarly, high-precision or high-amplitude coding can make \(Q\) grow with \(n\); charging only \(m\) and keeping \(A/\eta\) unconstrained invalidates any uniform throughput claim. A physical wave solver need not realize the abstract transcript rectangle property. Deriving **actual PDE bandwidth/precision/resource bounds** from the maintained Hamiltonian remains open.

This result advances O2 and O6 in the [full proof charter](../PROOF_COMPLETION_CHARTER.md) and isolates the still-decisive O7/O9 step: an unconditional hard-instance resource lower bound against *all permitted SAT deciders*, and the independent bridge to ordinary Turing computation.

## 5. Reproducibility and independent witnesses

- **Finite Lean semantics and capacity:** \`lean/PVNP/SplitSATCapacity.lean\`.
- **Exhaustive small-n testing:** \`pvnp/tests/test_split_three_sat.py\`; independently enumerates all pairs \(a,b\) and their possible assignments \(z\) for \(n\le4\), checking exact equivalence and verifying a centralized linear-scan witness.
- **Continuum WCT resource caveats:** [Hamiltonian phase-observability supplement](phase-sensitive-observability.md), [fixed-mass nodal supplement](../preprints/supplement-fixed-mass-nodal-coercivity/README.md), and [expanding-domain exact PDE countermodel](expanding-domain-hamiltonian-mode.md).

**Verdict:** Exact deterministic split-3SAT has a rigorous linear finite-alphabet communication lower bound. An amplitude/noise cap can turn that into a channel-use bound. No universal WCT SAT hardness or classical P≠NP theorem has been established.
