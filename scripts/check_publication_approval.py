#!/usr/bin/env python3
"""Fail closed unless the author has completed PVNP's OFFLINE publication gates.

This checks recorded evidence only; boolean acknowledgments cannot themselves
prove copyright ownership, filing priority, privacy or legal compliance.
The approval JSON is LOCAL and GITIGNORED, not a repository file.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / ".release-verification"
APPROVAL = EVIDENCE / "publication-approval.json"
PDF = ROOT / "pvnp/preprints/consolidated-wave-computation/paper.pdf"
REQUIRED_TRUE = (
    "pdf_rebuilt_and_content_verified", "pdf_visual_inspection_approved",
    "all_ref_history_privacy_reviewed", "third_party_rights_cleared",
    "patent_disclosure_reviewed", "license_scope_approved",
    "permission_to_make_repository_public",
)

def check(data: dict, head: str) -> list[str]:
    errors = []
    if data.get("schema") != "PVNP-publication-approval-v1":
        errors.append("approval schema missing or incorrect")
    if data.get("status") != "AUTHOR_APPROVED":
        errors.append("author approval status not recorded")
    if data.get("reviewed_commit_sha") != head:
        errors.append("the approved commit differs from the current HEAD")
    for key in REQUIRED_TRUE:
        if data.get(key) is not True:
            errors.append(key + " is not approved")
    if data.get("selected_code_license") not in {"BSD-3-Clause", "MIT", "Apache-2.0"}:
        errors.append("code license not selected")
    if data.get("selected_manuscript_license") not in {"CC-BY-4.0", "All-Rights-Reserved"}:
        errors.append("manuscript license not selected")
    return errors

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--require-approved", action="store_true")
    a = p.parse_args()
    head = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                   text=True).strip()
    issues = []
    if not APPROVAL.is_file():
        issues.append("private local publication-approval.json does not exist")
    else:
        try:
            data = json.loads(APPROVAL.read_text(encoding="utf-8"))
            issues.extend(check(data, head))
        except (ValueError, OSError) as exc:
            issues.append("approval evidence cannot be read: " + type(exc).__name__)
    pdf_stage = EVIDENCE / "pdf-offline"
    digest_file = pdf_stage / "consolidated-sha256.txt"
    if not digest_file.is_file() or not PDF.is_file():
        issues.append("reproduced PDF hash evidence missing")
    else:
        expected = digest_file.read_text().split()[0]
        actual = sha256(PDF.read_bytes()).hexdigest()
        if actual != expected:
            issues.append("PDF differs from staged verified release artifact")
    validation = pdf_stage / "content-validation.txt"
    if not validation.is_file() or "PASS: all revised sources included" not in validation.read_text(errors="replace"):
        issues.append("successful offline PDF page/content verification record missing")
    source_hashes = pdf_stage / "source-sha256.txt"
    if not source_hashes.is_file():
        issues.append("PDF source hash manifest missing")
    else:
        for line in source_hashes.read_text().splitlines():
            try:
                digest, path = line.split(None, 1)
                current = ROOT / path.lstrip("*")
                if not current.is_file() or sha256(current.read_bytes()).hexdigest() != digest:
                    issues.append("PDF source changed since compilation: " + path)
            except ValueError:
                issues.append("malformed PDF source hash manifest")
    rights = EVIDENCE / "rights-history.json"
    if not rights.is_file():
        issues.append("rights/history file inventory missing")
    else:
        try:
            audit = json.loads(rights.read_text(encoding="utf-8"))
            if audit.get("commit") != head or not audit.get("history", {}).get("checked"):
                issues.append("rights/history audit not completed on current HEAD")
        except (ValueError, OSError):
            issues.append("rights/history inventory unreadable")
    if not (ROOT / "LICENSE-CODE").is_file():
        issues.append("approved active LICENSE-CODE not installed")
    if not (ROOT / "LICENSE-MANUSCRIPTS").is_file():
        issues.append("approved active LICENSE-MANUSCRIPTS not installed")
    if issues:
        for item in issues:
            print("PENDING:", item)
        print("NO-GO: none of the outstanding legal/privacy review is auto-certified")
        return 1 if a.require_approved else 0
    print("DOCUMENTED RELEASE GATES PRESENT at", head)
    print("NOTE: author acknowledgment and legal judgments remain human responsibilities")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
