#!/usr/bin/env python3
"""Cheap source-level PVNP/Lean manuscript alignment gate.

This does not replace compilation of either LaTeX or Lean. It guards the
specific historical mistakes resolved in the 7 Nov 2026 publication PR.
"""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "pvnp/papers"


def source(slug: str) -> str:
    return (PAPERS / slug / "main.tex").read_text(encoding="utf8")


def must(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def main() -> None:
    p1 = source("part-i-curvature-bounded-wave-computation")
    p2 = source("part-ii-discrete-wcc-turing-equivalence")
    p3 = source("part-iii-physical-complexity-reassessment")
    supplement = source("supplement-fixed-mass-nodal-coercivity")
    combined = source("consolidated-wave-computation")
    inventory = (ROOT / "pvnp/proofs/manuscript-lean-inventory.md").read_text(
        encoding="utf8"
    )

    must("| **Total** | **91** | **78** | **2** | **4** | **7** |" in inventory,
         "Canonical claim inventory unexpectedly changed")
    for number in (25, 26, 27, 28):
        must(re.search(r"Withdrawn[^\n]*I-" + str(number) + r"\b", p1) is not None,
             f"I-{number} historical inference not explicitly withdrawn")
    for disallowed in (
        r"\\begin\{proposition\}\[Model-Relative Separation in Ideal WCC",
        r"\\begin\{proposition\}\[Formal Model-Theoretic Separation in WCT",
        r"\\begin\{proposition\}\[Conditional Turing Reduction Template",
    ):
        must(re.search(disallowed, p1) is None,
             f"Superseded state-to-language proposition still present: {disallowed}")
    must("Original two-phase simulation: exact dynamics, conditional uniformity" in p2,
         "Original II-10 theorem still presented as full unconditional uniformity")
    must("PartIIUniform.P" in p2 and "original" in p2.lower(),
         "Generic uniform class theorem and original W_M not distinguished")
    must("Current formalization status (7 November 2026)" in p2,
         "Missing current Part II status section")
    must("Current Lean formalization status (7 November 2026)" in p1,
         "Missing current Part I status section")
    must("Current Lean formalization status (7 November 2026)" in p3,
         "Missing current Part III status section")
    for p, name in ((p1, "I"), (p2, "II"), (p3, "III")):
        must("Formal verification status (November 2, 2026)" not in p,
             f"Part {name} still has a superseded 2 Nov verification status")
        must("Uniform-model completion (repository addendum" not in p,
             f"Part {name} has contradictory postdating status addenda")
        must("kernel build" in p or "kernel" in p.lower(),
             f"Part {name} does not document the verification boundary")
    for f in (p1, p2, p3, supplement, combined):
        for env in ("document", "abstract", "theorem", "proof",
                    "proposition", "remark", "enumerate", "itemize", "equation"):
            must(f.count("\\begin{" + env + "}") == f.count("\\end{" + env + "}"),
                 f"Imbalanced LaTeX environment {env}")
        labels = re.findall(r"\\label\{([^}]*)\}", f)
        must(len(labels) == len(set(labels)), "Duplicate LaTeX labels in source")
        refs = re.findall(r"\\(?:eqref|autoref|ref)\{([^}]*)\}", f)
        must(set(refs).issubset(labels), "Unresolved internal LaTeX reference")
    must(combined.count("\\includepdf[") == 4, "Consolidated volume not binding four parts")
    for name in ("part-i", "part-ii", "part-iii", "supplement"):
        must("archive/" + name + ".pdf" in combined,
             f"Missing {name} PDF from consolidated volume")
    must("Unresolved original-claim register" in combined,
         "Consolidated volume missing the nine Restricted/Open entries")
    must("two-site" in supplement, "Missing supplement finite-model disclaimer")
    print("PASS: Part I-III historical corrections and 91-claim inventory are aligned")
    print("PASS: consolidated LaTeX sources and nine-claim register are structurally consistent")
    print("NOTE: these static checks DO NOT verify Lean or compiled PDF output")


if __name__ == "__main__":
    main()
