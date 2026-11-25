#!/usr/bin/env bash
# Offline PVNP release review. No GitHub Actions or visibility changes.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
MODE="--all"
if (( $# > 0 )); then MODE="$1"; fi
case "$MODE" in
  --all|--pdf-only|--audit-only|--approval-status) ;;
  *) echo "Usage: $0 [--all|--pdf-only|--audit-only|--approval-status]" >&2; exit 2 ;;
esac
mkdir -p "$ROOT/.release-verification/bin"
if ! command -v python3 >/dev/null 2>&1 || ! python3 -c 'import sys' >/dev/null 2>&1; then
  if command -v python >/dev/null 2>&1 && python -c 'import sys' >/dev/null 2>&1; then
    printf '#!/usr/bin/env bash\nexec python "$@"\n' > "$ROOT/.release-verification/bin/python3"
  elif command -v py >/dev/null 2>&1 && py -3 -c 'import sys' >/dev/null 2>&1; then
    printf '#!/usr/bin/env bash\nexec py -3 "$@"\n' > "$ROOT/.release-verification/bin/python3"
  else
    echo "BLOCKED: Python 3 unavailable" >&2; exit 1
  fi
  chmod +x "$ROOT/.release-verification/bin/python3"
  export PATH="$ROOT/.release-verification/bin:$PATH"
fi
if [[ "$MODE" == --all || "$MODE" == --pdf-only ]]; then
  bash scripts/verify_public_pdf_offline.sh
fi
if [[ "$MODE" == --all || "$MODE" == --audit-only ]]; then
  python3 -m unittest pvnp.tests.test_offline_publication_gates
  python3 scripts/check_public_release_docs.py
  python3 scripts/audit_release_assets.py --history
  python3 scripts/audit_public_release.py --history
fi
python3 scripts/check_publication_approval.py
echo "Offline review commands completed. HUMAN APPROVAL REQUIRED before public visibility."
