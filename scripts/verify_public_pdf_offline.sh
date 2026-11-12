#!/usr/bin/env bash
# Offline consolidated PDF verification. Does not authorize publication.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
for exe in pdflatex pdfinfo pdftotext pdftoppm python3 sha256sum; do
  command -v "$exe" >/dev/null || { echo "BLOCKED: missing $exe" >&2; exit 1; }
done
OUT="$ROOT/.release-verification/pdf-offline"
mkdir -p "$OUT/visual"
git rev-parse HEAD > "$OUT/git-commit.txt"
python3 scripts/check_manuscript_alignment.py
PVNP_PDF_REVIEW_DIR="$OUT" bash scripts/build_pdfs.sh
FINAL="$ROOT/pvnp/preprints/consolidated-wave-computation/paper.pdf"
python3 scripts/verify_pdfs.py "$OUT/pdfs" "$FINAL" | tee "$OUT/content-validation.txt"
sha256sum "$FINAL" > "$OUT/consolidated-sha256.txt"
total="$(pdfinfo "$FINAL" | awk '/^Pages:/ {print $2}')"
test "$total" -gt 10
for page in 1 2 3 "$((total / 2))" "$total"; do
  pdftoppm -f "$page" -l "$page" -scale-to 1300 -singlefile -png \
    "$FINAL" "$OUT/visual/volume-page-$page" >/dev/null 2>&1
done
for part in part-i part-ii part-iii supplement; do
  pdf="$OUT/pdfs/$part.pdf"
  count="$(pdfinfo "$pdf" | awk '/^Pages:/ {print $2}')"
  test "$count" -gt 0
  for page in 1 "$count"; do
    pdftoppm -f "$page" -l "$page" -scale-to 1300 -singlefile -png \
      "$pdf" "$OUT/visual/$part-page-$page" >/dev/null 2>&1
  done
done
echo "PASS: PDF content and structural checks; render previews at $OUT/visual"
echo "PENDING: human visual, privacy, licensing and patent disclosure approval."
echo "No hosted CI was invoked."
