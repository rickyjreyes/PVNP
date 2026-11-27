"""Phase XXXI progress bars, computed from the obligation registry `obligations.json`.

Each bar is discharged / total over the obligations of one category (the registry's "rule").
* A mathematical obligation counts only if its status is "proved" or "refuted" and every Lean
  declaration it cites is registered in `lean/audit/AxiomAudit.lean` and declared under
  `lean/PVNP`.
* A process obligation counts only if its status is "done" and its file check passes.
* "derived", "analyzed" and "open" never count.

The subjective estimates are printed in a separate, labelled column and are not computed from the
obligations. Only category C12 measures progress toward classical P versus NP; it is 0 while that
problem is open.

Usage: `python3 pvnp/phase_xxxi/progress.py [--check]`.
"""
import argparse
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REGISTRY = os.path.join(ROOT, "pvnp", "phase_xxxi", "obligations.json")
AUDIT = os.path.join(ROOT, "lean", "audit", "AxiomAudit.lean")
LEAN_DIR = os.path.join(ROOT, "lean", "PVNP")

MATH_STATUSES = {"proved", "refuted", "derived", "analyzed", "open"}
MATH_DISCHARGED = {"proved", "refuted"}
PROCESS_STATUSES = {"done", "open"}


def load_registry(path=REGISTRY):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def audited_names(path=AUDIT):
    names = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"#print axioms (\S+)", line.strip())
            if m:
                names.add(m.group(1))
    return names


def lean_sources(directory=LEAN_DIR):
    texts = []
    for name in sorted(os.listdir(directory)):
        if name.endswith(".lean"):
            with open(os.path.join(directory, name), encoding="utf-8") as f:
                texts.append(f.read())
    return "\n".join(texts)


def is_declared(name, sources):
    short = name.rsplit(".", 1)[-1]
    pattern = r"^(?:theorem|lemma|def|noncomputable def)\s+" + re.escape(short) + r"(?![\w'.])"
    return re.search(pattern, sources, re.M) is not None


def process_check(obligation, root=ROOT):
    check = obligation.get("check", {})
    if "file_contains" in check:
        path, needle = check["file_contains"]
        full = os.path.join(root, path)
        if not os.path.exists(full):
            return False
        with open(full, encoding="utf-8") as f:
            return needle in f.read()
    if "file_exists" in check:
        return os.path.exists(os.path.join(root, check["file_exists"]))
    return False


def evaluate(registry, audited, sources, root=ROOT):
    """Return (rows, errors). A row is (id, title, discharged, total, subjective_percent)."""
    rows, errors = [], []
    seen = set()
    for cat in registry["categories"]:
        discharged = 0
        for ob in cat["obligations"]:
            oid = ob["id"]
            if oid in seen:
                errors.append(f"{oid}: duplicate obligation id")
            seen.add(oid)
            status = ob["status"]
            if ob.get("kind", "math") == "process":
                if status not in PROCESS_STATUSES:
                    errors.append(f"{oid}: unknown process status {status!r}")
                elif status == "done":
                    if process_check(ob, root):
                        discharged += 1
                    else:
                        errors.append(f"{oid}: marked done but its file check fails")
                continue
            if status not in MATH_STATUSES:
                errors.append(f"{oid}: unknown status {status!r}")
                continue
            names = ob.get("lean", [])
            if status in MATH_DISCHARGED:
                if not names:
                    errors.append(f"{oid}: {status} without a cited Lean declaration")
                    continue
                missing = [n for n in names if n not in audited]
                undeclared = [n for n in names if not is_declared(n, sources)]
                if missing:
                    errors.append(f"{oid}: not registered in the axiom audit: {missing}")
                if undeclared:
                    errors.append(f"{oid}: no declaration found under lean/PVNP: {undeclared}")
                if not missing and not undeclared:
                    discharged += 1
        pct = cat["subjective_percent"]
        if not isinstance(pct, int) or not 0 <= pct <= 100:
            errors.append(f"{cat['id']}: subjective_percent must be an integer in [0, 100]")
        rows.append((cat["id"], cat["title"], discharged, len(cat["obligations"]), pct))
    by_id = {r[0]: r for r in rows}
    if len(rows) != 12:
        errors.append(f"expected 12 categories, found {len(rows)}")
    for guarded in ("C9", "C12"):
        if guarded in by_id and by_id[guarded][2] == 0 and by_id[guarded][4] != 0:
            errors.append(f"{guarded}: nonzero subjective estimate while nothing is discharged")
    return rows, errors


def bar(done, total, width=20):
    filled = round(width * done / total) if total else 0
    return "[" + "#" * filled + "." * (width - filled) + "]"


def render(rows):
    lines = ["PVNP Phase XXXI | bars computed from obligations; subjective estimates labelled separately",
             f"{'':4} {'category':76} {'computed':>30}   subjective (not computed)"]
    for cid, title, done, total, pct in rows:
        computed = f"{bar(done, total)} {round(100 * done / total):3d}% ({done}/{total})"
        lines.append(f"{cid:4} {title[:76]:76} {computed:>30}   {pct:3d}%")
    lines.append("C12 is the only bar that measures classical P versus NP. It is 0: the problem is unresolved.")
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="exit nonzero on any registry error")
    args = parser.parse_args(argv)
    rows, errors = evaluate(load_registry(), audited_names(), lean_sources())
    print(render(rows))
    for e in errors:
        print("ERROR:", e, file=sys.stderr)
    return 1 if (args.check and errors) else 0


if __name__ == "__main__":
    sys.exit(main())
