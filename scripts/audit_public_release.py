#!/usr/bin/env python3
"""Non-publishing PVNP public-release preflight. No secret values are printed.

HEAD scanning is heuristic; --history requires a full-history checkout and
gitleaks. Neither is a legal, privacy, or patent clearance. Findings go into
ignored .release-verification. Do not commit that directory.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / ".release-verification" / "public-release-secret-scan.json"
MAX_BYTES = 2_000_000

PATTERNS = {
    "github_token": re.compile(rb"\bgh[pousr]_[A-Za-z0-9_]{25,}\b"),
    "aws_access_key": re.compile(rb"\b(?:AKIA|ASIA)[A-Z0-9]{16}\b"),
    "private_key_header": re.compile(rb"-----BEGIN (?:RSA |OPENSSH |EC |DSA )?PRIVATE KEY-----"),
    "openai_api_key": re.compile(rb"\bsk-[A-Za-z0-9_-]{30,}\b"),
}
SUFFIXES = {
    ".py", ".js", ".ts", ".json", ".jsonl", ".yaml", ".yml",
    ".toml", ".ini", ".conf", ".env", ".md", ".txt", ".tex",
    ".sh", ".lean", ".xml", ".html", ".css", ".csv",
}
SKIP_PARTS = {".git", ".lake", "node_modules", ".release-verification"}


def git(*args: str) -> str:
    r = subprocess.run(
        ["git", "-C", str(ROOT), *args], check=True, capture_output=True, text=True
    )
    return r.stdout.strip()


def tracked_head_scan() -> tuple[int, int]:
    files = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z"],
        capture_output=True, check=True
    ).stdout.split(b"\0")
    scanned = findings = 0
    for raw_name in files:
        if not raw_name:
            continue
        name = os.fsdecode(raw_name)
        path = ROOT / name
        if any(part in SKIP_PARTS for part in Path(name).parts):
            continue
        lower = path.name.lower()
        sensitive_name = (
            lower == ".env" or (
                lower.startswith(".env.") and lower not in
                {".env.example", ".env.sample", ".env.template"}
            )
            or lower in {"id_rsa", "id_ed25519", "credentials.json"}
            or path.suffix.lower() in {".pem", ".p12", ".pfx", ".key"}
        )
        if sensitive_name:
            print(f"REVIEW: sensitive-looking tracked filename {name}", file=sys.stderr)
            findings += 1
        if path.is_symlink():
            print(f"REVIEW: tracked symlink {name}", file=sys.stderr)
            findings += 1
            continue
        if path.suffix.lower() not in SUFFIXES and lower not in {
            ".gitignore", "dockerfile", "makefile", ".gitattributes"
        } and not lower.startswith(".env"):
            continue
        if not path.is_file() or path.stat().st_size > MAX_BYTES:
            continue
        content = path.read_bytes()
        scanned += 1
        for label, pattern in PATTERNS.items():
            if pattern.search(content):
                # Never print matches or their context.
                print(f"REVIEW: possible {label} in tracked file {name}", file=sys.stderr)
                findings += 1
    return scanned, findings


def scan_history() -> bool:
    if git("rev-parse", "--is-shallow-repository") == "true":
        print("BLOCKED: checkout is shallow; history scan cannot be complete", file=sys.stderr)
        return False
    exe = shutil.which("gitleaks")
    if not exe:
        print("BLOCKED: install Gitleaks to scan all refs and commit history", file=sys.stderr)
        return False
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    # Gitleaks v8+; no found secret or report body is echoed to stdout.
    cmd = [
        exe, "git", str(ROOT), "--log-opts=--all",
        "--report-format=json", f"--report-path={REPORT}",
        "--redact", "--exit-code=1",
    ]
    result = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if REPORT.exists():
        REPORT.chmod(0o600)  # report may contain sensitive match metadata
    if result.returncode:
        print(
            f"BLOCKED: Gitleaks history scan returned {result.returncode}; "
            f"review the local ignored report {REPORT} privately",
            file=sys.stderr,
        )
        return False
    print("PASS: Gitleaks completed on all locally available refs; manual review still required")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", action="store_true", help="require all-ref Gitleaks scan")
    args = parser.parse_args()
    print(f"Commit: {git('rev-parse', 'HEAD')}")
    scanned, findings = tracked_head_scan()
    print(f"Tracked textual files inspected: {scanned}; heuristic matches: {findings}")
    if not args.history:
        print("INCOMPLETE: run with --history in a full clone before publication")
    history_ok = scan_history() if args.history else False
    if findings or (args.history and not history_ok):
        return 1
    print("NOTE: review binaries, PDF metadata, names/addresses, third-party rights and patent disclosures manually")
    print("NOTE: this scanner is NOT authorization to change repository visibility")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
