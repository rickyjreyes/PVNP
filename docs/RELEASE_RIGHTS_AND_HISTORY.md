# PVNP rights and Git-history release review

**Status: REVIEW IN PROGRESS, NOT CLEARED.** Documentation and scanners
cannot make a patent/licensing/legal determination.

## Inventory observed on 12 November 2026

- **319 tracked repository entries** (directories included in that count)
  in the reviewed Git tree; **5 tracked PDF binaries**, all within
  \`pvnp/preprints/\`; **5 LaTeX main sources** within \`pvnp/papers/\`.
- PDF set: three historic manuscripts, one fixed-mass supplement, and
  one consolidated volume. Each has an identified corresponding
  \`pvnp/papers/<slug>/main.tex\` source.
- All five maintained LaTeX sources were inspected for asset inclusion:
  there are **no external `\\includegraphics` files**, one inline
  `pgfplots` plot in Part I, and four `\\includepdf` references to
  internally rebuilt standalone manuscripts in the consolidated source.
  No externally tracked standalone image or dataset binary was identified
  in the complete 319-entry current tree. This does **not** establish sole
  authorship or clearance of prose, copied code, citations, or history.
- A preliminary sample of the most recent 300 GitHub commits includes
  multiple author display names. This is **not** proof of independent
  contributor rights but makes the authorship/chain-of-title audit important.
  The full local all-ref history review remains pending.
- Third-party runtime and build dependencies include Lean, Mathlib,
  Python dependencies, Node and TeX packages; these are not automatically
  redistributed under the proposed author-code or manuscript licenses.

Run \`python3 scripts/audit_release_assets.py --history\` in a **full clone**
to produce a local ignored inventory with hashes, TeX inclusions,
historical filenames and PDF metadata flags. Run
\`python3 scripts/audit_public_release.py --history\` separately to
perform full-ref Gitleaks scanning. Do not commit either report.

## Manual review matrix

| Material | Review requirement | Status |
| --- | --- | --- |
| Author-created Lean, Python, JavaScript, shell and HTML | Confirm exclusive copyright or contributor permission; inspect upstream-derived snippets | PENDING |
| LaTeX prose and equations | Compare historical Zenodo license and citations, borrowed quotations and illustrative material | PENDING |
| Five PDF binaries | Rebuild; inspect contents, embedded metadata, fonts and generated artifacts | PENDING |
| All history, tags and remote refs | Examine other contributors, potentially sensitive content and previously unfiled technical disclosures | PENDING |
| External third-party tools or packages | Preserve upstream notices if redistribution applies | PENDING |
| Ownership of source vs. license scope | Author selects license(s) and explicitly records applicable directories | PENDING |

### Useful commands (local only)

\`\`\`bash
git fetch --all --prune --tags
git rev-parse --is-shallow-repository
git log --all --format='%h %an <%ae>' | sort -u
git rev-list --objects --all
python3 scripts/audit_release_assets.py --history
python3 scripts/audit_public_release.py --history
bash scripts/verify_public_pdf_offline.sh
\`\`\`

The Git-author identity command is for private review. It may reveal private
emails; keep its output in ignored local evidence, not in public commits.
An absent scanner finding is **not** a rights or confidentiality clearance.
