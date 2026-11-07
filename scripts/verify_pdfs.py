#!/usr/bin/env python3
"""Validate the *compiled* current PVNP PDF contents, not merely TeX sources.

Usage:
  python3 scripts/verify_pdfs.py /path/to/review/pdfs \
      pvnp/preprints/consolidated-wave-computation/paper.pdf

The four archival verification PDFs are ephemeral build artifacts. Only the
consolidated PDF is the primary publication artifact.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


def command(*args: str) -> str:
    return subprocess.check_output(args, stderr=subprocess.STDOUT, text=True)


def pages(pdf: Path) -> int:
    info = command("pdfinfo", str(pdf))
    match = re.search(r"^Pages:\s*(\d+)\s*$", info, re.MULTILINE)
    if not match:
        raise AssertionError(f"Unable to read page count of {pdf}")
    return int(match.group(1))


def pdf_text(pdf: Path) -> str:
    result = command("pdftotext", "-layout", str(pdf), "-")
    result = re.sub(r"\s+", " ", result)
    if len(result) < 350:
        raise AssertionError(f"PDF has insufficient extractable text: {pdf}")
    return result


def check(pdf: Path, minimum_pages: int, fragments: list[str]) -> int:
    if not pdf.is_file() or pdf.stat().st_size < 4096:
        raise AssertionError(f"Missing or implausibly small PDF: {pdf}")
    count = pages(pdf)
    if count < minimum_pages:
        raise AssertionError(f"{pdf}: {count} pages < {minimum_pages} expected")
    txt = pdf_text(pdf)
    for fragment in fragments:
        if fragment.lower() not in txt.lower():
            raise AssertionError(f"{pdf.name}: no PDF text matching {fragment!r}")
    print(f"PASS: {pdf.name}: {count} pages, {len(txt)} text chars")
    return count


def main() -> int:
    if len(sys.argv) != 3:
        print("Usage: verify_pdfs.py REVIEW_PDFS_DIR CONSOLIDATED_PDF", file=sys.stderr)
        return 2
    root = Path(sys.argv[1])
    final = Path(sys.argv[2])
    tests: dict[str, tuple[int, list[str]]] = {
        "part-i.pdf": (
            10, ["Curvature", "I-25", "I-26", "I-27", "I-28",
                 "Withdrawn", "Cook", "I-40"],
        ),
        "part-ii.pdf": (
            8, ["Discrete", "Original two-phase simulation",
                "conditional uniformity", "Turing"],
        ),
        "part-iii.pdf": (
            4, ["Physical", "Reconciliation with the amended Lean inventory"],
        ),
        "supplement.pdf": (
            2, ["Fixed-Mass", "coercivity", "two-site"],
        ),
    }
    counts = {name: check(root / name, *args) for name, args in tests.items()}
    combined = check(
        final, sum(counts.values()) + 4,
        ["Consolidated Technical Volume", "Unresolved original-claim register",
         "Part I", "Part II", "Part III",
         "I-16", "II-10", "III-22", "Withdrawn"],
    )
    if (root / "consolidated.pdf").is_file():
        from hashlib import sha256
        if sha256((root / "consolidated.pdf").read_bytes()).digest() != sha256(final.read_bytes()).digest():
            raise AssertionError("Published consolidated PDF differs from review artifact")
    print(f"PASS: all revised sources included, consolidated {combined} pages")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.CalledProcessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
