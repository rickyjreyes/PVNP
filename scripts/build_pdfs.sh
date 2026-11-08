#!/usr/bin/env bash
# Rebuild the three manuscripts and supplement before binding their exact pages.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1794009600}" FORCE_SOURCE_DATE=1 TZ=UTC
REVIEW="${PVNP_PDF_REVIEW_DIR:-}"
if [[ -n "$REVIEW" ]]; then
  mkdir -p "$REVIEW"/{pdfs,logs}
  REVIEW="$(cd "$REVIEW" && pwd)"
  { pdflatex --version; printf 'SOURCE_DATE_EPOCH=%s\n' "$SOURCE_DATE_EPOCH"; } > "$REVIEW/toolchain.txt"
fi
mkdir -p "$STAGE/archive" "$ROOT/pvnp/preprints/consolidated-wave-computation"
sources=()

aux_signature() {
  local dir="$1" file
  for file in main.aux main.toc main.out; do
    if [[ -f "$dir/$file" ]]; then sha256sum < "$dir/$file"; fi
  done
}

compile() {
  local src="$1" out="$2" label="$3" previous="" signature="" pass
  mkdir -p "$out"
  for pass in 1 2 3 4 5 6; do
    if ! (cd "$src" && pdflatex -interaction=nonstopmode -halt-on-error \
        -file-line-error -recorder -jobname=main -output-directory="$out" \
        '\pdftrailerid{}\input{main.tex}' > "$out/pass-$pass.log" 2>&1); then
      [[ -z "$REVIEW" ]] || cp "$out/pass-$pass.log" "$REVIEW/logs/$label-pass-$pass.log"
      tail -n 65 "$out/pass-$pass.log" >&2
      return 1
    fi
    [[ -z "$REVIEW" ]] || cp "$out/main.log" "$REVIEW/logs/$label-pass-$pass.log"
    signature="$(aux_signature "$out")"
    if (( pass >= 2 )) && [[ "$previous" == "$signature" ]]; then
      if grep -Ei 'undefined (references|citations)|((reference|citation).*undefined)|multiply.defined|Missing character:|Rerun to get|Label\(s\) may have changed' "$out/main.log"; then
        echo "Unresolved typesetting diagnostic in $label" >&2
        return 1
      fi
      [[ -z "$REVIEW" ]] || cp "$out/main.fls" "$REVIEW/logs/$label.fls"
      test -s "$out/main.pdf"
      return
    fi
    previous="$signature"
  done
  echo "References did not stabilize for $label" >&2
  return 1
}
part() {
  local slug="$1" label="$2"
  sources+=("pvnp/papers/$slug/main.tex")
  echo "Compiling $slug"
  compile "$ROOT/pvnp/papers/$slug" "$STAGE/$label" "$label"
  cp "$STAGE/$label/main.pdf" "$STAGE/archive/$label.pdf"
  [[ -z "$REVIEW" ]] || cp "$STAGE/archive/$label.pdf" "$REVIEW/pdfs/$label.pdf"
}
part part-i-curvature-bounded-wave-computation part-i
part part-ii-discrete-wcc-turing-equivalence part-ii
part part-iii-physical-complexity-reassessment part-iii
part supplement-fixed-mass-nodal-coercivity supplement
sources+=(pvnp/papers/consolidated-wave-computation/main.tex)
cp "$ROOT/pvnp/papers/consolidated-wave-computation/main.tex" "$STAGE/main.tex"
compile "$STAGE" "$STAGE" consolidated
OUTPUT="$ROOT/pvnp/preprints/consolidated-wave-computation/paper.pdf"
install -m 0644 "$STAGE/main.pdf" "$OUTPUT"
if [[ -n "$REVIEW" ]]; then
  cp "$OUTPUT" "$REVIEW/pdfs/consolidated.pdf"
  (cd "$ROOT" && sha256sum "${sources[@]}") > "$REVIEW/source-sha256.txt"
  (cd "$REVIEW/pdfs" && sha256sum part-i.pdf part-ii.pdf part-iii.pdf supplement.pdf consolidated.pdf) > "$REVIEW/pdf-sha256.txt"
fi
pdfinfo "$OUTPUT" | awk '/^Pages:/ { print "Consolidated volume:", $2, "pages" }'
