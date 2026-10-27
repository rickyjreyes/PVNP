#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for part in part-i-curvature-bounded-wave-computation part-ii-discrete-wcc-turing-equivalence part-iii-physical-complexity-reassessment supplement-fixed-mass-nodal-coercivity; do
  source="pvnp/papers/$part/main.tex"
  target="pvnp/preprints/$part/paper.pdf"
  build_dir="$(mktemp -d)"
  echo "Compiling $source -> $target"
  (
    cd "$(dirname "$source")"
    if ! pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory="$build_dir" main.tex >"$build_dir/pdflatex.stdout" 2>&1; then
      tail -n 100 "$build_dir/pdflatex.stdout"
      exit 1
    fi
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory="$build_dir" main.tex >/dev/null
  )
  install -m 0644 "$build_dir/main.pdf" "$target"
  rm -rf "$build_dir"
  test -s "$target"
done
