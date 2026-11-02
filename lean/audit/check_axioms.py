"""Fail unless every `#print axioms` line in AxiomAudit.lean reports only
standard Lean axioms (propext, Classical.choice, Quot.sound)."""
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

audit_src = open(sys.argv[1]).read()
output = open(sys.argv[2]).read()
expected = len(re.findall(r"^#print axioms", audit_src, flags=re.M))
reports = re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
if len(reports) != expected:
    print(f"expected {expected} axiom reports, found {len(reports)}")
    sys.exit(1)
bad = []
for name, _, axioms in reports:
    used = {a.strip() for a in axioms.split(",") if a.strip()}
    if not used <= ALLOWED:
        bad.append((name, sorted(used - ALLOWED)))
if bad or "sorryAx" in output:
    for name, extra in bad:
        print(f"non-standard axioms in {name}: {extra}")
    sys.exit(1)
print(f"axiom audit OK: {expected} declarations, only {sorted(ALLOWED)} (or subsets)")
