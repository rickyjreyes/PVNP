#!/usr/bin/env python3
"""Read-only consistency checks for PVNP public-release-facing documentation.

This gate checks source-level claims only. It does not compile Lean, PDFs,
audit patent rights, scan history, or approve publication.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def main() -> None:
    inventory = read("pvnp/proofs/manuscript-lean-inventory.md")
    registry = read("pvnp/phase_xvi/targets.json")
    root_readme = read("README.md")
    preprint_readme = read("pvnp/preprints/consolidated-wave-computation/README.md")
    historical = read("pvnp/proofs/pdf-lean-reconciliation-20261107.md")
    release = read("PUBLIC_RELEASE_READINESS.md")
    license_note = read("docs/PUBLIC_LICENSE_DECISION.md")

    assert "| **Total** | **91** | **79** | **1** | **4** | **7** |" in inventory
    assert "| I-31 |" in inventory and "| II-10 |" in inventory
    assert "originalWM_first_answer" in inventory
    assert '"Exact": 79' in registry and '"Restricted": 1' in registry
    assert '"id": "II-10"' in registry and '"status": "Exact"' in registry
    assert "PUBLIC_RELEASE_READINESS.md" in root_readme
    assert "docs/PUBLIC_LICENSE_DECISION.md" in release
    assert "## 12 November 2026 addendum: II-10 original scope closed" in historical
    assert "The original uniform two-phase lattice/encoder cost proof," not in preprint_readme
    assert "original finite discrete two-phase" in preprint_readme.lower()
    assert "NO-GO" in release and "explicit approval" in release.lower()
    assert "PENDING" in license_note and "No license has been selected" in license_note
    print("PASS: release-facing documents consistent with amended II-10 source status")
    print("NOTE: this is source validation only, not proof or public-release clearance")


if __name__ == "__main__":
    main()
