#!/usr/bin/env bash
# Offline consolidated PDF verification. Does not authorize publication.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
# Git Bash often exposes Python as 'python' or 'py -3', not python3.
if ! command -v python3 >/dev/null 2>&1 || ! python3 -c 'import sys' >/dev/null 2>&1; then
  mkdir -p "$ROOT/.release-verification/bin"
  if command -v python >/dev/null 2>&1 && python -c 'import sys' >/dev/null 2>&1; then
    printf '#!/usr/bin/env bash\nexec python "$@"\n' > "$ROOT/.release-verification/bin/python3"
  elif command -v py >/dev/null 2>&1 && py -3 -c 'import sys' >/dev/null 2>&1; then
    printf '#!/usr/bin/env bash\nexec py -3 "$@"\n' > "$ROOT/.release-verification/bin/python3"
  else
    echo "BLOCKED: Python 3 is unavailable" >&2
    exit 1
  fi
  chmod +x "$ROOT/.release-verification/bin/python3"
  export PATH="$ROOT/.release-verification/bin:$PATH"
fi
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
