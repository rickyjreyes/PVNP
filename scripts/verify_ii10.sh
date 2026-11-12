#!/usr/bin/env bash
# Independent exact-head verification for the original polynomial writer.
# Run from any directory with a Lean 4.23.0 + Lake installation.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
printf 'PVNP HEAD: '
git rev-parse HEAD
printf 'Lean toolchain: '
cat lean/lean-toolchain
printf 'Lake version: '
lake --version

audit_log="$(mktemp)"
trap 'rm -f "$audit_log"' EXIT

printf '\n[1/6] Reject unfinished Lean proof markers\n'
if grep -rnE '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)' lean/PVNP; then
  echo 'Unfinished or unapproved proof markers found' >&2
  exit 1
fi

cd "$root/lean"
printf '\n[2/6] Kernel-check original polynomial writer and dependencies\n'
lake build PVNP.TwoPhasePolynomialWriter
printf '\n[3/6] Build complete PVNP Lean import tree\n'
lake build PVNP
printf '\n[4/6] Check permitted axioms for all recorded proof obligations\n'
lake env lean audit/AxiomAudit.lean | tee "$audit_log"
python3 audit/check_axioms.py audit/AxiomAudit.lean "$audit_log"

cd "$root"
printf '\n[5/6] Exercise actual-machine finite transducers and Phase XVIII regressions\n'
python3 -m unittest discover -s pvnp/tests -p 'test_two_phase_tape_writer.py'
python3 -m unittest discover -s pvnp/tests -p 'test_phase_xvi_*.py'
python3 -m unittest discover -s pvnp/tests -p 'test_phase_xvii_*.py'
python3 -m unittest discover -s pvnp/tests -p 'test_phase_xviii_*.py'

printf '\n[6/6] Validate the original status ledger without upgrading II-10\n'
python3 pvnp/phase_xvi/status.py --check

printf '\nAll local II-10 verification gates passed at HEAD %s\n' "$(git rev-parse HEAD)"
