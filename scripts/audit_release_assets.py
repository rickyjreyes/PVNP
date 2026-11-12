#!/usr/bin/env python3
"""Offline, non-approving rights/history inventory. Reports are gitignored."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".release-verification" / "rights-history.json"
PDF_NAMES = {"part-i-curvature-bounded-wave-computation", "part-ii-discrete-wcc-turing-equivalence", "part-iii-physical-complexity-reassessment", "supplement-fixed-mass-nodal-coercivity", "consolidated-wave-computation"}
TEX_INCLUDE = re.compile(r"\\(input|include|includegraphics|includepdf|bibliography|addbibresource)(?:\[[^]]*\])?\{([^}]+)\}")
SENSITIVE = re.compile(r"(^|/)(\.env(?:\.[^/]*)?|id_rsa|id_ed25519|credentials(?:\.[^/]*)?|private[_-]?key(?:\.[^/]*)?)($|/)|\.(pem|p12|pfx|key)$", re.I)
PRIVATE_META = re.compile(r"[/\\](Users|home)[/\\]|[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}|file://|token=", re.I)

PDF_TEXT_RISKS = {
    "email_address": re.compile(r"[\\w.+-]+@[\\w.-]+\\.[A-Za-z]{2,}"),
    "home_directory_path": re.compile(r"(?:[A-Z]:\\\\Users\\\\|/home/|/Users/)", re.I),
    "copy_or_permission_notice": re.compile(r"reproduced with permission|adapted from|all rights reserved", re.I),
}

def git(*args, binary=False):
    p = subprocess.run(["git", "-C", str(ROOT), *args], check=True, capture_output=True)
    return p.stdout if binary else p.stdout.decode(errors="replace").strip()

def classify(path):
    ext = Path(path).suffix.lower()
    if ext == ".pdf": return "pdf_manual_provenance_and_metadata_review"
    if path.startswith("pvnp/papers/") and ext == ".tex": return "authored_manuscript_rights_review"
    if ext in (".lean", ".py", ".js", ".sh", ".html", ".css"): return "code_authorship_and_dependencies_review"
    if ext in (".md", ".txt", ".rst", ".cff"): return "documentation_authorship_review"
    return "other_or_structured_data_review"

def metadata_flags(metadata):
    return [line.split(":",1)[0].strip() for line in metadata.splitlines()
            if ":" in line and PRIVATE_META.search(line.split(":",1)[1])]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", action="store_true")
    args = parser.parse_args()
    paths = sorted(x.decode(errors="replace") for x in git("ls-files", "-z", binary=True).split(b"\0") if x)
    pdfs, includes = [], []
    for path in paths:
        p = ROOT / path
        if path.endswith(".pdf"):
            record = {"path": path, "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
                      "size": p.stat().st_size, "metadata_checked": False}
            if shutil.which("pdfinfo"):
                info = subprocess.run(["pdfinfo", str(p)], capture_output=True, text=True)
                record["metadata_checked"] = info.returncode == 0
                if info.returncode == 0:
                    record["metadata_fields_to_review"] = metadata_flags(info.stdout)
            if shutil.which("pdftotext"):
                body = subprocess.run(["pdftotext", str(p), "-"], capture_output=True, text=True)
                record["pdf_text_checked"] = body.returncode == 0
                if body.returncode == 0:
                    record["pdf_text_review_flag_counts"] = {
                        name: len(pattern.findall(body.stdout))
                        for name, pattern in PDF_TEXT_RISKS.items()
                    }
            pdfs.append(record)
        if path.startswith("pvnp/papers/") and path.endswith(".tex"):
            for cmd, ref in TEX_INCLUDE.findall(p.read_text(encoding="utf-8")):
                includes.append({"source": path, "command": cmd, "target": ref})
    found = {Path(p).parent.name for p in paths
             if p.startswith("pvnp/preprints/") and p.endswith("/paper.pdf")}
    missing = sorted(PDF_NAMES - found)
    history = {"checked": False}
    if args.history:
        if git("rev-parse", "--is-shallow-repository") == "true":
            raise SystemExit("BLOCKED: full git history required")
        lines = git("log", "--all", "--name-only", "--format=").splitlines()
        history = {"checked": True, "commits": int(git("rev-list", "--all", "--count")),
                   "sensitive_historical_filenames": sorted({p for p in lines if SENSITIVE.search(p)}),
                   "scope": "all locally available refs; secret-content scan is separate"}
    output = {"commit": git("rev-parse", "HEAD"), "tracked": len(paths),
              "categories": dict(Counter(map(classify, paths))),
              "pdfs": pdfs, "tex_inclusions": includes, "missing_expected_pdfs": missing,
              "history": history, "third_party_cleared": False, "patent_cleared": False,
              "licensing_approved": False, "public_visibility_approved": False}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(f"Inventory: {len(paths)} files, {len(pdfs)} PDFs, {len(includes)} LaTeX inclusions")
    print(f"Historic refs inspected: {args.history}; missing PDF locations: {missing}")
    print("REVIEW REQUIRED: no automated license, third-party, patent or publication clearance")
    print(f"Private ignored report: {OUT}")
    return bool(missing)

if __name__ == "__main__":
    raise SystemExit(main())
