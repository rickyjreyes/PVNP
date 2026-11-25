"""Non-mutating smoke checks for the public-release secret scanner.

Does not need Lean, network access or a full-history repository checkout.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "audit_public_release", ROOT / "scripts" / "audit_public_release.py"
)
assert SPEC is not None and SPEC.loader is not None
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


class ReleaseAuditPatternTests(unittest.TestCase):
    def test_synthetic_aws_key_pattern(self) -> None:
        synthetic = b"AK" + b"IA" + b"A" * 16
        self.assertIsNotNone(audit.PATTERNS["aws_access_key"].search(synthetic))

    def test_private_key_marker(self) -> None:
        synthetic = b"-----BEGIN " + b"RSA PRIVATE KEY-----"
        self.assertIsNotNone(audit.PATTERNS["private_key_header"].search(synthetic))

    def test_ordinary_research_text_not_flagged(self) -> None:
        text = b"Wave Curvature Computation: no passwords or keys here."
        self.assertFalse(any(p.search(text) for p in audit.PATTERNS.values()))

    def test_reports_are_inside_ignored_directory(self) -> None:
        self.assertEqual(audit.REPORT.parent.name, ".release-verification")


if __name__ == "__main__":
    unittest.main()
