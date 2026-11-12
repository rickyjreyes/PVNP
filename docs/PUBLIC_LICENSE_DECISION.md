# PVNP licensing decision record (pending)

**Status: PROPOSAL ONLY. No license has been selected or granted by this document.**

A publicly accessible repository without a license does not generally authorize others to copy, modify or redistribute its contents. Public GitHub visibility and a grant of copyright or patent rights are different decisions.

## Possible segmentation

| Material | Candidate | Important consideration |
| --- | --- | --- |
| Original Python, JavaScript and Lean source owned by the author | BSD-3-Clause or MIT | Permissive copyright terms; do not assume an express patent grant or immunity from patent infringement |
| Software intended for explicit contributor/patent licensing | Apache-2.0 | Includes an express contributor patent-license mechanism and termination conditions; review alongside patent strategy before adoption |
| Original manuscripts, author-created diagrams, research text | CC BY 4.0 | Attribution license for content; not a software-specific license, does not license patents |
| Third-party figures, datasets, Mathlib dependencies or excerpts | Original upstream terms | The author cannot license material whose rights are not held or granted; include provenance and required notices |
| Filed patent technical subject matter or new unfiled improvements | Separate patent/legal evaluation | No software or Creative Commons choice by itself solves patent, priority, or foreign-disclosure questions |

**Working recommendation for review:** BSD-3-Clause for author-owned code and CC BY 4.0 for author-owned text/figures, only after checking the actual chain of title, prior Zenodo publication terms, external contributor rights and patent implications. Apache-2.0 requires separate explicit approval for its patent-license terms. Do not add a root \`LICENSE\` or universal copyright claim yet.

## Pre-decision audit

1. Inventory authors and external contributions for all folders, generated assets, paper figures and embedded code.
2. Record license metadata and redistributability for dependencies and any borrowed figures/text.
3. Compare each existing Zenodo record's license with the proposed manuscript license; retain original DOI and dates.
4. Review source and **all reachable historical commits and branches** for technical disclosures not contained in relevant filed claims, including added matter after the filing dates.
5. Identify jurisdictions in which public disclosure may affect patent rights. Do not assume a US grace period applies abroad or to new subject matter.
6. Confirm notice/citation text, contributor policy and whether separate \`code/\` and \`manuscripts/\` license files or SPDX identifiers are needed.
7. Obtain the author's explicit licensing and visibility decisions. Obtain qualified patent advice for unresolved priority/claim-scope issues.

## Decision to be recorded

- Code license and exact directories: **PENDING**
- Manuscript/figure license and exact directories: **PENDING**
- Excluded third-party material: **PENDING**
- Patent disclosure sign-off: **PENDING**
- License-approved commit SHA: **PENDING**
- Visibility authorization: **NOT GIVEN**

This is a research-release checklist, not legal advice or a determination that any patent filing covers the full repository.
