#!/usr/bin/env bash
# Independently reproduce the complete PVNP release gates on a machine
# with the pinned Lean toolchain, Mathlib cache, TeX Live, Python and Node.
# This DOES NOT change Git visibility, merge a PR or create a publication.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MODE="${1:---all}"
case "$MODE" in
  --all|--pdf-only|--lean-only|--dashboard-only) ;;
  *) echo "Usage: $0 [--all|--pdf-only|--lean-only|--dashboard-only]" >&2; exit 2 ;;
esac

RUN_DIR="${PVNP_RELEASE_VERIFY_DIR:-$ROOT/.release-verification}"
mkdir -p "$RUN_DIR"
RUN_DIR="$(cd "$RUN_DIR" && pwd)"
echo "Verification output: $RUN_DIR"
python3 "$ROOT/scripts/check_manuscript_alignment.py"
python3 "$ROOT/scripts/test_release_staging.py" | tee "$RUN_DIR/release-staging-test.txt"

# Never overwrite the tracked release PDF until the *whole* --all gate passes.
# The PDF-only mode intentionally leaves only review artifacts, not a publication.
STAGED_PDF="$RUN_DIR/staged-release/paper.pdf"
if [[ "$MODE" == --all || "$MODE" == --pdf-only ]]; then
  for exe in pdflatex pdfinfo pdftotext python3; do
    command -v "$exe" >/dev/null || { echo "Required executable missing: $exe" >&2; exit 1; }
  done
  mkdir -p "$(dirname "$STAGED_PDF")"
  rm -f "$STAGED_PDF"
  PVNP_PDF_OUTPUT="$STAGED_PDF" PVNP_PDF_REVIEW_DIR="$RUN_DIR/pdf" \
    bash "$ROOT/scripts/build_pdfs.sh"
  python3 "$ROOT/scripts/verify_pdfs.py" "$RUN_DIR/pdf/pdfs" \
    "$STAGED_PDF" | tee "$RUN_DIR/pdf-validation.txt"
fi

if [[ "$MODE" == --all || "$MODE" == --lean-only ]]; then
  command -v lake >/dev/null || { echo "Missing lake / pinned Lean toolchain" >&2; exit 1; }
  (
    cd "$ROOT/lean"
    if [[ "${PVNP_GET_MATHLIB_CACHE:-0}" == 1 ]]; then
      lake exe cache get
    fi
    if grep -rnE '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)' PVNP; then
      echo "Unfinished proof or custom axiom detected" >&2
      exit 1
    fi
    lake build PVNP 2>&1 | tee "$RUN_DIR/lean-build.txt"
    lake env lean audit/AxiomAudit.lean 2>&1 | tee "$RUN_DIR/axiom-audit.txt"
    python3 audit/check_axioms.py audit/AxiomAudit.lean "$RUN_DIR/axiom-audit.txt" \
      | tee "$RUN_DIR/axiom-audit-check.txt"
  )
fi

if [[ "$MODE" == --all || "$MODE" == --dashboard-only ]]; then
  command -v node >/dev/null || { echo "Missing node" >&2; exit 1; }
  (
    cd "$ROOT"
    node pvnp/dashboard/build.js --check
    node pvnp/dashboard/check.js
  ) 2>&1 | tee "$RUN_DIR/dashboard-check.txt"
fi

if [[ "$MODE" == --all ]]; then
  # Publish only after PDF, Lean, axiom audit and dashboard gates all succeeded.
  FINAL_PDF="$ROOT/pvnp/preprints/consolidated-wave-computation/paper.pdf"
  test -s "$STAGED_PDF" || { echo "Validated release PDF missing" >&2; exit 1; }
  install -m 0644 "$STAGED_PDF" "$FINAL_PDF"
  cmp -s "$STAGED_PDF" "$FINAL_PDF" || {
    echo "Published PDF differs from verified release artifact" >&2
    exit 1
  }
  echo "Promoted independently validated release PDF: $FINAL_PDF"
elif [[ "$MODE" == --pdf-only ]]; then
  echo "PDF-only validation passed; staged PDF retained at $STAGED_PDF (not published)."
fi

echo "All requested $MODE verification gates passed."
