#!/usr/bin/env bash
# Run from any working directory, including inside the lean/ subfolder.
# Does not update dependencies or mutate the proof ledger.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

printf '\n=== Phase XVII | exact commit ===\n'
git rev-parse HEAD
printf '\n=== Python regressions from repo root ===\n'
python -m unittest discover -s pvnp/tests -p 'test_phase_xvi_*.py'
python -m unittest discover -s pvnp/tests -p 'test_phase_xvii_*.py'
python pvnp/phase_xvi/status.py --check

printf '\n=== Targeted Lean kernel builds ===\n'
cd lean
lake build PVNP.TwoPhasePolynomialWriter PVNP.ToroidalFiniteRows PVNP.SeparatorNormalizedRay
printf '\n=== Complete Lean build ===\n'
lake build PVNP
printf '\n=== Axiom audit ===\n'
lake env lean audit/AxiomAudit.lean > axiom-audit.txt
python audit/check_axioms.py audit/AxiomAudit.lean axiom-audit.txt

printf '\nPASS: exact-head Phase XVII verification gate\n'
