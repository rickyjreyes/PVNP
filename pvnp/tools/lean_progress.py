#!/usr/bin/env python3
"""Validate and display Lean progress using the canonical 91-claim inventory.

No percentage is assigned to an open or restricted proof: those cases have
named missing obligations, not a measurable fraction of a finished proof.
Refuted original statements are recorded as verified counterexamples,
not as completed proofs of the original assertion.

Run from anywhere:
  python3 pvnp/tools/lean_progress.py --check
  python3 pvnp/tools/lean_progress.py --markdown
  python3 pvnp/tools/lean_progress.py --json
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
INVENTORY = ROOT / "pvnp/proofs/manuscript-lean-inventory.md"
AUDIT = ROOT / "lean/audit/AxiomAudit.lean"
STATUS = ("Exact", "Restricted", "Refuted", "Open")

# Claim counts are compared against the inventory's own coverage table rather
# than hardcoded historical counts, since corrected manuscripts can change status.
PARTS = ("I", "II", "III")

PHASE_X_PREFIXES = (
    "PVNP.TMBooleanTableau.",
    "PVNP.CircuitCNF.",
    "PVNP.VerifierCircuits.",
    "PVNP.SATProjection.",
    "PVNP.CrossingSATMatrix.",
    "PVNP.PhaseXIQuadratic.",
)
PHASE_XI_THEOREM = "PVNP.PhaseXIQuadratic.sat_no_uniform_subquadratic"


def parse_coverage(text: str) -> dict:
    """Read the separate coverage summary and validate its arithmetic."""
    coverage: dict = {}
    pattern = re.compile(
        r"^\|\s*Part\s+(I|II|III)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|"
    )
    for line in text.splitlines():
        match = pattern.match(line)
        if match is None:
            continue
        part, total, exact, restricted, refuted, open_ = match.groups()
        counts = dict(
            total=int(total), Exact=int(exact), Restricted=int(restricted),
            Refuted=int(refuted), Open=int(open_),
        )
        if counts["total"] != sum(counts[k] for k in STATUS):
            raise ValueError(f"Coverage arithmetic mismatch in Part {part}")
        if part in coverage:
            raise ValueError(f"Duplicate coverage for Part {part}")
        coverage[part] = counts
    if set(coverage) != set(PARTS):
        raise ValueError(f"Missing manuscript coverage rows: {coverage}")
    return coverage


def parse_inventory(text: str) -> list[dict]:
    claims: list[dict] = []
    seen: set[str] = set()
    for line in text.splitlines():
        if not re.match(r"^\|\s*(?:I|II|III)-\d+\s*\|", line):
            continue
        # Markdown may contain escaped pipes inside LaTeX in earlier cells.
        cells = [c.strip() for c in re.split(r"(?<!\\)\|", line.strip().strip("|"))]
        if len(cells) < 5:
            raise ValueError(f"Invalid claim row: {line}")
        claim_id, label = cells[0], cells[1].replace("\\|", "|")
        match = re.match(r"^(Exact|Restricted|Refuted|Open)\b", cells[-1])
        if match is None:
            raise ValueError(f"Missing status for {claim_id}: {line}")
        if claim_id in seen:
            raise ValueError(f"Duplicate claim ID: {claim_id}")
        seen.add(claim_id)
        state = match.group(1)
        claims.append({
            "id": claim_id,
            "part": claim_id.split("-")[0],
            "label": label.replace("`", ""),
            "status": state,
            "exact_proof_percent": 100 if state == "Exact" else None,
            "verified_counterexample": state == "Refuted",
            "status_detail": cells[-1],
        })
    return claims


def summarize(claims: list[dict], expected: dict) -> dict:
    per_part = {}
    for part in PARTS:
        counts = Counter(row["status"] for row in claims if row["part"] == part)
        per_part[part] = {status: counts[status] for status in STATUS}
        expected_counts = {status: expected[part][status] for status in STATUS}
        if per_part[part] != expected_counts:
            raise ValueError(
                f"{part} inventory changed without updating the baseline: "
                f"{per_part[part]} != {expected_counts}"
            )
    if len(claims) != 91:
        raise ValueError(f"Expected exactly 91 unique claims, got {len(claims)}")
    counts = Counter(row["status"] for row in claims)
    return {
        "total": len(claims),
        "exact": counts["Exact"],
        "restricted": counts["Restricted"],
        "refuted": counts["Refuted"],
        "open": counts["Open"],
        "determined_by_proof_or_counterexample": counts["Exact"] + counts["Refuted"],
        "exact_percent": round(100 * counts["Exact"] / len(claims), 2),
        "per_part": per_part,
    }


def audited_support() -> list[str]:
    text = AUDIT.read_text(encoding="utf-8")
    all_names = re.findall(r"^\s*#print axioms\s+(\S+)\s*$", text, flags=re.MULTILINE)
    if PHASE_XI_THEOREM not in all_names:
        raise ValueError("Phase XI theorem is missing from the axiom audit")
    return [name for name in all_names if name.startswith(PHASE_X_PREFIXES)]


def markdown(data: dict) -> str:
    s = data["summary"]
    lines = [
        "# Lean proof progress (inventory-driven)",
        "",
        f"Exact: {s['exact']}/{s['total']} ({s['exact_percent']:.2f}%). "
        f"Determined, including refutations: "
        f"{s['determined_by_proof_or_counterexample']}/{s['total']}.",
        "",
        "A full bar means the original exact statement is kernel-verified "
        "on a green commit. A refutation verifies a counterexample instead.",
        "",
        "| Claim | Title | Outcome | Exact proof progress |",
        "|---|---|---|---|",
    ]
    for row in data["claims"]:
        progress = "██████████ 100%" if row["status"] == "Exact" else "not quantified"
        label = row["label"].replace("|", "\\|")
        lines.append(f"| {row['id']} | {label} | {row['status']} | {progress} |")
    lines.extend([
        "",
        f"Phase X/XI principal declarations listed in the axiom audit: "
        f"{len(data['supporting_axiom_audit_declarations'])}.",
        "",
        "**Open central target:** `SAT_dense ∉ P_TM`. "
        "The Phase XI quadratic theorem does not establish this target.",
    ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check", action="store_true")
    group.add_argument("--json", action="store_true")
    group.add_argument("--markdown", action="store_true")
    opts = parser.parse_args()

    inventory = INVENTORY.read_text(encoding="utf-8")
    claims = parse_inventory(inventory)
    data = {
        "summary": summarize(claims, parse_coverage(inventory)),
        "claims": claims,
        "supporting_axiom_audit_declarations": audited_support(),
        "validation_scope": "Source inventory and audit registry. Kernel verification requires a green exact-head CI run.",
    }
    if opts.json:
        print(json.dumps(data, indent=2, ensure_ascii=False))
    elif opts.markdown:
        print(markdown(data))
    else:
        s = data["summary"]
        print(
            f"OK: {s['exact']}/{s['total']} exact, "
            f"{s['refuted']} refuted, {s['restricted']} restricted, "
            f"{s['open']} open; {len(data['supporting_axiom_audit_declarations'])} "
            "Phase X/XI audit declarations registered"
        )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as exc:
        print(f"Proof progress audit failed: {exc}", file=sys.stderr)
        sys.exit(1)
