#!/usr/bin/env bash
# Build one authoritative PVNP release PDF.
# The three original studies and independent supplement are compiled as
# temporary assets and bound verbatim, not replaced or re-dated.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT

mkdir -p "$STAGE/archive" "$ROOT/pvnp/preprints/consolidated-wave-computation"

build_archival_source() {
  local slug="$1"
  local short="$2"
  local src="$ROOT/pvnp/papers/$slug"
  local out="$STAGE/$short"
  mkdir -p "$out"
  echo "Compiling archival source $slug"
  (
    cd "$src"
    if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
      -output-directory="$out" main.tex >"$out/first-pass.log" 2>&1; then
      tail -n 100 "$out/first-pass.log"
      exit 1
    fi
    if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
      -output-directory="$out" main.tex >"$out/second-pass.log" 2>&1; then
      tail -n 100 "$out/second-pass.log"
      exit 1
    fi
  )
  test -s "$out/main.pdf"
  cp "$out/main.pdf" "$STAGE/archive/$short.pdf"
}

build_archival_source "part-i-curvature-bounded-wave-computation" "part-i"
build_archival_source "part-ii-discrete-wcc-turing-equivalence" "part-ii"
build_archival_source "part-iii-physical-complexity-reassessment" "part-iii"
build_archival_source "supplement-fixed-mass-nodal-coercivity" "supplement"

cp "$ROOT/pvnp/papers/consolidated-wave-computation/main.tex" "$STAGE/main.tex"
echo "Compiling consolidated PVNP technical volume"
(
  cd "$STAGE"
  for pass in 1 2; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
      main.tex >"$STAGE/consolidated-pass-$pass.log" 2>&1; then
      tail -n 120 "$STAGE/consolidated-pass-$pass.log"
      exit 1
    fi
  done
)

OUTPUT="$ROOT/pvnp/preprints/consolidated-wave-computation/paper.pdf"
install -m 0644 "$STAGE/main.pdf" "$OUTPUT"
test -s "$OUTPUT"

# The compiled release must contain pages beyond the introductory guide.
if command -v pdfinfo >/dev/null 2>&1; then
  pages="$(pdfinfo "$OUTPUT" | awk '/^Pages:/ {print $2}')"
  test "$pages" -ge 20 || { echo "Consolidated PDF has too few pages"; exit 1; }
  echo "Consolidated PVNP release: $pages pages"
fi
echo "Primary PDF: $OUTPUT"
