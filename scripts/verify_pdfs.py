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
import unicodedata
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


def page_texts(pdf: Path) -> list[str]:
    # Page embedding changes glyph coordinates. Compare text in stream order.
    raw = command("pdftotext", "-raw", str(pdf), "-")
    texts = raw.split("\f")
    if texts[-1].strip():
        raise AssertionError(f"{pdf}: incomplete page text extraction")
    return ["".join(unicodedata.normalize("NFKC", t).split()) for t in texts[:-1]]


def verify_bound_pages(final: Path, parts: list[Path]) -> None:
    volume = page_texts(final)
    cursor = 0
    for pdf in parts:
        content = page_texts(pdf)
        starts = [i for i in range(cursor, len(volume)) if volume[i] == content[0]]
        if len(starts) != 1:
            raise AssertionError(f"{pdf.name}: expected one matching title page, found {starts}")
        start = starts[0]
        if cursor and start != cursor + 1:
            raise AssertionError(f"{pdf.name}: expected one divider page before manuscript")
        for page, standalone in enumerate(content):
            if start + page >= len(volume) or volume[start + page] != standalone:
                raise AssertionError(f"{pdf.name}: embedded page {page + 1} differs from standalone PDF")
        cursor = start + len(content)
        print(f"PASS: {pdf.name} matches volume pages {start + 1}–{cursor} in order")
    if cursor != len(volume):
        raise AssertionError("Unexpected trailing pages after supplement")


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
            4, ["Physical", "Current Lean formalization status"],
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
    verify_bound_pages(final, [root / name for name in tests])
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
