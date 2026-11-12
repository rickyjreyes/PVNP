#!/usr/bin/env bash
# Strict local technical preflight for an eventual public PVNP release.
# Cannot approve licensing, patent disclosures, privacy, or repository visibility.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if [[ "$(git rev-parse --is-shallow-repository)" != "false" ]]; then
  echo "BLOCKED: full git history required" >&2
  exit 1
fi
# Require the tested tree to match the recorded commit.
if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
  echo "BLOCKED: tracked worktree changes; commit or revert before release verification" >&2
  exit 1
fi
# Include current remote branches/tags in the all-ref secret scan; fail if fetch fails.
git fetch --all --prune --tags
echo "PVNP technical release preflight: $(git rev-parse HEAD)"

# On Windows Git Bash, Python is often installed as python.exe or py.exe,
# without a python3 executable. Make a shim in the ignored local audit folder
# so all nested shell scripts and env shebangs find a consistent python3.
if command -v python3 >/dev/null 2>&1 && python3 -c 'import sys' >/dev/null 2>&1; then
  echo "Python launcher: python3"
else
  python_launcher=""
  if command -v python >/dev/null 2>&1 && python -c 'import sys' >/dev/null 2>&1; then
    python_launcher="python"
  elif command -v py >/dev/null 2>&1 && py -3 -c 'import sys' >/dev/null 2>&1; then
    python_launcher="py -3"
  else
    echo "BLOCKED: Python 3 unavailable. Install Python and reopen Git Bash." >&2
    echo "Check: python --version, py -3 --version, python3 --version" >&2
    exit 1
  fi
  shim_dir="$ROOT/.release-verification/bin"
  mkdir -p "$shim_dir"
  if [[ "$python_launcher" == "python" ]]; then
    printf '#!/usr/bin/env bash\nexec python "$@"\n' > "$shim_dir/python3"
  else
    printf '#!/usr/bin/env bash\nexec py -3 "$@"\n' > "$shim_dir/python3"
  fi
  chmod +x "$shim_dir/python3"
  export PATH="$shim_dir:$PATH"
  echo "Python launcher: $python_launcher (Git Bash python3 compatibility shim)"
fi

python3 scripts/check_public_release_docs.py
python3 -m unittest pvnp.tests.test_public_release_audit

# Scans all locally available refs and history. Never commit scanner reports.
python3 scripts/audit_public_release.py --history

# This is the exact original-writer regression suite, including the Lean gate.
bash scripts/verify_ii10_original_wm.sh

# This separately checks all revised manuscripts, the consolidated PDF,
# full Lean project/axioms and the generated dashboard.
bash scripts/run_release_verification.sh --all

echo "TECHNICAL GATES PASSED at $(git rev-parse HEAD)"
echo "NOT PUBLICATION AUTHORIZATION: patent, third-party rights, metadata,"
echo "manual privacy review, licensing and explicit visibility approval are still required."
