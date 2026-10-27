#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for part in part-i-curvature-bounded-wave-computation part-ii-discrete-wcc-turing-equivalence; do
  source="pvnp/papers/$part/main.tex"
  target="pvnp/preprints/$part/paper.pdf"
  build_dir="$(mktemp -d)"
  echo "Compiling $source -> $target"
  (
    cd "$(dirname "$source")"
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory="$build_dir" main.tex >/dev/null
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory="$build_dir" main.tex >/dev/null
  )
  install -m 0644 "$build_dir/main.pdf" "$target"
  rm -rf "$build_dir"
  test -s "$target"
done
