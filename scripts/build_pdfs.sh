#!/usr/bin/env bash
# Rebuild the revised three-paper PVNP sources and independent supplement,
# then bind them into ONE primary published PDF. The four standalone
# rebuilt PDFs are temporary verification artifacts, not new publications.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT

# Optional location for external CI reviewers to inspect the rebuilt
# individual PDFs and full LaTeX logs without committing them to Git.
REVIEW="${PVNP_PDF_REVIEW_DIR:-}"
if [[ -n "$REVIEW" ]]; then
  mkdir -p "$REVIEW/pdfs" "$REVIEW/logs"
fi
mkdir -p "$STAGE/archive" "$ROOT/pvnp/preprints/consolidated-wave-computation"

save_log() {
  local src="$1" label="$2"
  if [[ -n "$REVIEW" && -f "$src" ]]; then
    cp "$src" "$REVIEW/logs/$label.log"
  fi
}

build_archival_source() {
  local slug="$1" short="$2"
  local src="$ROOT/pvnp/papers/$slug"
  local out="$STAGE/$short"
  mkdir -p "$out"
  test -s "$src/main.tex" || { echo "Missing source: $src/main.tex" >&2; return 1; }
  echo "Compiling latest source: $slug"

  for pass in 1 2; do
    if ! (cd "$src" && pdflatex -interaction=nonstopmode -halt-on-error         -file-line-error -output-directory="$out" main.tex         >"$out/pass-$pass.log" 2>&1); then
      save_log "$out/pass-$pass.log" "$short-pass-$pass"
      tail -n 120 "$out/pass-$pass.log" >&2
      return 1
    fi
    save_log "$out/pass-$pass.log" "$short-pass-$pass"
  done

  test -s "$out/main.pdf" || return 1
  cp "$out/main.pdf" "$STAGE/archive/$short.pdf"
  if [[ -n "$REVIEW" ]]; then
    cp "$out/main.pdf" "$REVIEW/pdfs/$short.pdf"
  fi
}

build_archival_source "part-i-curvature-bounded-wave-computation" "part-i"
build_archival_source "part-ii-discrete-wcc-turing-equivalence" "part-ii"
build_archival_source "part-iii-physical-complexity-reassessment" "part-iii"
build_archival_source "supplement-fixed-mass-nodal-coercivity" "supplement"

cp "$ROOT/pvnp/papers/consolidated-wave-computation/main.tex" "$STAGE/main.tex"
echo "Compiling one consolidated PVNP technical volume"
for pass in 1 2; do
  if ! (cd "$STAGE" && pdflatex -interaction=nonstopmode -halt-on-error       -file-line-error main.tex       >"$STAGE/consolidated-pass-$pass.log" 2>&1); then
    save_log "$STAGE/consolidated-pass-$pass.log" "consolidated-pass-$pass"
    tail -n 120 "$STAGE/consolidated-pass-$pass.log" >&2
    exit 1
  fi
  save_log "$STAGE/consolidated-pass-$pass.log" "consolidated-pass-$pass"
done

OUTPUT="$ROOT/pvnp/preprints/consolidated-wave-computation/paper.pdf"
test -s "$STAGE/main.pdf"
install -m 0644 "$STAGE/main.pdf" "$OUTPUT"
test -s "$OUTPUT"
if [[ -n "$REVIEW" ]]; then
  cp "$OUTPUT" "$REVIEW/pdfs/consolidated.pdf"
  (cd "$ROOT" && sha256sum     pvnp/papers/part-i-curvature-bounded-wave-computation/main.tex     pvnp/papers/part-ii-discrete-wcc-turing-equivalence/main.tex     pvnp/papers/part-iii-physical-complexity-reassessment/main.tex     pvnp/papers/supplement-fixed-mass-nodal-coercivity/main.tex     pvnp/papers/consolidated-wave-computation/main.tex)     >"$REVIEW/source-sha256.txt"
  (cd "$REVIEW/pdfs" && sha256sum *.pdf) >"$REVIEW/pdf-sha256.txt"
fi

if command -v pdfinfo >/dev/null 2>&1; then
  pages="$(pdfinfo "$OUTPUT" | awk '/^Pages:/ {print $2}')"
  test "${pages:-0}" -ge 20 || { echo "Consolidated PDF has too few pages" >&2; exit 1; }
  echo "Consolidated PVNP release: $pages pages"
fi
echo "One primary release PDF: $OUTPUT"
