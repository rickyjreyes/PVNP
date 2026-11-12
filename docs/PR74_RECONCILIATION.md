# PR #74 versus merged Phase XVIII: reconciliation record

**Review date:** 12 November 2026. **Do not merge PR #74 wholesale.**

## Branch graph

- PR #68 (Phase XVI) → merged into \`main\`.
- PR #69 (Phase XVII) → merged into \`main\`.
- PR #73 (Phase XVIII original II-10 machine proof) → merged into \`main\`, including promotion commit \`417c2d4\`.
- PR #72 is a recovered writer-integration branch already represented by #73; merging separately risks duplicate or stale source.
- PR #70 carries superseded incomplete return-sweep proof candidates; **do not merge**.
- PR #74 (draft) is based on the pre-promotion Phase XVIII head and diverges from \`main\` after \`417c2d4\`. Its independent edits should not replace the author-verified promotion wholesale.

## Already present in main

The 91-row inventory and registry already read **79 Exact / 1 Restricted / 4 Refuted / 7 Open**. II-10 is Exact, Part II has 28/28 Exact, and the original unconditional two-phase machine/proof chain, including \`originalWM_first_answer\`, is integrated. The exact-head local gate is reported at \`df8824c\` and \`417c2d4\`, whereas hosted jobs fail before executing steps.

Do not perform a second reclassification, count change, or regeneration of the official proof tree simply to integrate PR #74.

## Safe portions transferred in Phase XIX

- Updated root README to link explicit public-release gates and current 91-claim inventory.
- Added 12 November II-10 historical addendum from PR #74 to \`pvnp/proofs/pdf-lean-reconciliation-20261107.md\`, retaining its original 7 November historical context.
- Corrected stale original-writer description in the consolidated-volume README.
- Added verification-provenance and corrected zero-input boundary notes to the dashboard README.

## Material still to review on PR #74

| Files | Question before integration |
| --- | --- |
| \`pvnp/dashboard/build.js\`, \`check.js\` | Distinguish author-reported exact-head proof source from hosted main CI and verify scope-change guards without breaking existing full-history validation |
| \`pvnp/dashboard/results.json\`, generated \`data.js\`, UI files | Preserve the established original 91-row history, PR #73 formalization attribution, static data regeneration and consistency |
| \`scripts/check_manuscript_alignment.py\` | Merge only stricter logically compatible manuscript checks; run against all five sources |
| \`pvnp/proofs/II10_VERIFICATION_LEDGER.md\`, manuscript text | Preserve the author-verified proof argument and original \`T_W=2 T_M\` statement, historical changes and local vs hosted verification distinction |
| \`pvnp/phase_xvi/targets.json\` | Both branches already classify II-10 Exact; merge wording only if better and not contradictory |

**Required exact-head test before any remaining code merges:** \`node pvnp/dashboard/build.js --check\`, \`node pvnp/dashboard/check.js\`, \`python3 scripts/check_manuscript_alignment.py\`, full release verification where source changes warrant it.

No such full-history test has executed in this integration environment. This branch leaves the conflicting source/generator portion of #74 unresolved rather than claiming it was tested.

## I-31 and other independent branches

The user's reported I-31 finite-torus counterexample work is a separate mathematical development and was not present as an identified I-31 branch or PR in the branch search at review time. It must be assessed against hypothesis \`lem:separator-price\` and its exact physical detector/trajectory assumptions before any classification change. The original I-31 remains Open.

PR #71's interpretive III-22 reclassification is similarly independent and has not altered the authoritative inventory.
