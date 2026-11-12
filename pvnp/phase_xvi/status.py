"""Cross-check the Phase XVI registry and print nine per-claim progress bars.

Estimates are not proof coverage, probabilities or machine-verified claims.
The original 91-claim inventory is the authoritative classification source.
"""
import argparse
import json
import pathlib
import re

TARGET_IDS = ("II-10", "I-31", "I-37", "I-32", "I-3", "I-11",
              "I-2", "I-16", "III-22")
COUNT_BASELINE = {"Exact": 79, "Restricted": 1, "Refuted": 4, "Open": 7}


def parse_inventory(path: pathlib.Path) -> dict[str, str]:
    claims = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        item = re.match(r"^[|][ ]*((?:I|II|III)-[0-9]+)[ ]*[|]", line)
        if not item:
            continue
        claim_id = item.group(1)
        # Do not split on every pipe: TeX math in the inventory includes
        # escaped vertical bars inside a status description.
        matches = re.findall(r"[|][ ]*(Exact|Restricted|Refuted|Open)(?![A-Za-z])", line)
        if not matches:
            raise ValueError(f"Missing status for {claim_id}")
        status = matches[-1]
        if claim_id in claims:
            raise ValueError(f"Duplicate claim {claim_id}")
        claims[claim_id] = status
    return claims


def validate(registry: dict, inventory: dict[str, str]) -> dict[str, int]:
    ids = tuple(item["id"] for item in registry["targets"])
    if ids != TARGET_IDS:
        raise ValueError(f"Wrong Phase XVI targets or ordering: {ids!r}")
    counts = {s: list(inventory.values()).count(s) for s in COUNT_BASELINE}
    if counts != COUNT_BASELINE or len(inventory) != 91:
        raise ValueError(f"Inventory changed: {counts!r}, total {len(inventory)}; review the proofs before changing the baseline")
    for item in registry["targets"]:
        if item["status"] != inventory[item["id"]]:
            raise ValueError(f"Stale classification {item['id']}: {item['status']} vs {inventory[item['id']]}")
        p = item["research_estimate_percent"]
        if type(p) is not int or not 0 <= p <= 100:
            raise ValueError(f"Invalid research estimate for {item['id']}")
        if item["id"] == "III-22" and item["metric"] != "editorial":
            raise ValueError("III-22 progress is strictly editorial")
        if not item["evidence"] or not item["remaining_obligation"]:
            raise ValueError(f"Missing evidence or proof obligation for {item['id']}")
    return counts


def render(registry: dict) -> str:
    lines = ["PVNP Phase XVI | estimated research progress, NOT verified claim completion"]
    for item in registry["targets"]:
        pct = item["research_estimate_percent"]
        filled = pct // 5
        bar = "█" * filled + "░" * (20 - filled)
        lines.append(f"{item['id']:6s} {bar} {pct:3d}% {item['status']} [{item['metric']}]")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--registry", type=pathlib.Path)
    parser.add_argument("--inventory", type=pathlib.Path)
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parents[2]
    registry_path = args.registry or root / "pvnp" / "phase_xvi" / "targets.json"
    inventory_path = args.inventory or root / "pvnp" / "proofs" / "manuscript-lean-inventory.md"
    registry = json.loads(registry_path.read_text(encoding="utf-8"))
    counts = validate(registry, parse_inventory(inventory_path))
    if args.check:
        print(f"PASS: nine claims agree with manuscript ledger {counts}")
    else:
        print(render(registry))


if __name__ == "__main__":
    main()
