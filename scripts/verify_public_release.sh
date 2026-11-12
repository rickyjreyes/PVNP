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
