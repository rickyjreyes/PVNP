#!/usr/bin/env bash
# Exact-head kernel/audit gate for original manuscript theorem II-10.
# Run from any working directory after installing lean/lean-toolchain.
# Read-only with respect to the source tree and research status registry.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

printf '\n=== II-10 original W_M | exact commit ===\n'
git rev-parse HEAD
cat lean/lean-toolchain

for f in Exec State Program Outputs FP; do
  test -f "lean/PVNP/TwoPhasePolynomial${f}.lean"
done
grep -Fq 'import PVNP.TwoPhasePolynomialFP' lean/PVNP.lean

printf '\n=== No unfinished proofs in the five original-machine modules ===\n'
if grep -nE '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)' \
     lean/PVNP/TwoPhasePolynomial{Exec,State,Program,Outputs,FP}.lean; then
  echo 'Unfinished original II-10 proof marker found' >&2
  exit 1
fi

printf '\n=== Targeted kernel build: actual machine to original FP ===\n'
(
  cd lean
  lake build PVNP.TwoPhasePolynomialExec PVNP.TwoPhasePolynomialState \
    PVNP.TwoPhasePolynomialProgram PVNP.TwoPhasePolynomialOutputs \
    PVNP.TwoPhasePolynomialFP
)

printf '\n=== Complete PVNP kernel build ===\n'
(
  cd lean
  lake build PVNP
)

printf '\n=== Axiom audit (only standard Lean axioms permitted) ===\n'
(
  cd lean
  logfile="$(mktemp)"
  trap 'rm -f "$logfile"' EXIT
  lake env lean audit/AxiomAudit.lean | tee "$logfile"
  python3 audit/check_axioms.py audit/AxiomAudit.lean "$logfile"
)

printf '\n=== Python reference-machine regressions and status consistency ===\n'
python3 -m unittest discover -s pvnp/tests -p 'test_two_phase_tape_writer.py'
python3 -m unittest discover -s pvnp/tests -p 'test_phase_xvi_*.py'
python3 -m unittest discover -s pvnp/tests -p 'test_phase_xvii_*.py'
python3 pvnp/phase_xvi/status.py --check

printf '\nPASS: original II-10 source, exact-head Lean kernel, axioms and regressions\n'
printf 'Verified commit: '
git rev-parse HEAD
