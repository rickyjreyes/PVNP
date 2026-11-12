#!/usr/bin/env python3
"""Read-only consistency checks for PVNP public-release-facing documentation.

This gate checks source-level claims only. It does not compile Lean, PDFs,
audit patent rights, scan history, or approve publication. No Python assertions
are used, so -O cannot disable the checks.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {"Exact": 79, "Restricted": 1, "Refuted": 5, "Open": 6, "total": 91}


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def require(ok: bool, why: str) -> None:
    if not ok:
        raise SystemExit(f"BLOCKED: {why}")


def main() -> None:
    inventory = read("pvnp/proofs/manuscript-lean-inventory.md")
    registry = json.loads(read("pvnp/phase_xvi/targets.json"))
    root_readme = read("README.md")
    preprint_readme = read("pvnp/preprints/consolidated-wave-computation/README.md")
    historical = read("pvnp/proofs/pdf-lean-reconciliation-20261107.md")
    release = read("PUBLIC_RELEASE_READINESS.md")
    license_note = read("docs/PUBLIC_LICENSE_DECISION.md")

    require(registry.get("baseline") == EXPECTED, "nine-claim registry totals diverge")
    actual = [t for t in registry.get("targets", []) if t.get("id") == "II-10"]
    require(len(actual) == 1 and actual[0].get("status") == "Exact",
            "original II-10 entry not uniquely Exact")
    require("| **Total** | **91** | **79** | **1** | **5** | **6** |" in inventory,
            "authoritative manuscript totals diverge")
    refuted = [t for t in registry.get("targets", []) if t.get("id") == "I-31"]
    require(len(refuted) == 1 and refuted[0].get("status") == "Refuted"
            and "no_uniform_separator_price" in inventory,
            "I-31 is not recorded as refuted with its counterexample")
    require("| I-31 |" in inventory and "| II-10 |" in inventory,
            "missing original claim record")
    require("originalWM_first_answer" in inventory, "missing original first-answer theorem")
    require("PUBLIC_RELEASE_READINESS.md" in root_readme, "README omits publication controls")
    require("docs/PUBLIC_LICENSE_DECISION.md" in release, "licensing review not linked")
    require("## 12 November 2026 addendum: II-10 original scope closed" in historical,
            "dated historical correction missing")
    require("The original uniform two-phase lattice/encoder cost proof," not in preprint_readme,
            "consolidated-volume README still describes II-10 as unresolved")
    require("original finite discrete two-phase" in preprint_readme.lower(),
            "consolidated-volume README lacks corrected II-10 scope")
    require("NO-GO" in release and "explicit approval" in release.lower(),
            "missing publication approval gates")
    require("PENDING" in license_note and "No license has been selected" in license_note,
            "licensing document may assert unauthorized permission")
    require("verify_public_pdf_offline.sh" in release,
            "release documentation must describe the offline PDF gate")
    require("docs/PATENT_PUBLIC_DISCLOSURE_REVIEW.md" in release,
            "patent disclosure hold point is not linked")
    print("PASS: release-facing documentation matches amended original II-10 scope")
    print("NOTE: source validation is not proof, legal approval, or visibility authorization")


if __name__ == "__main__":
    main()
