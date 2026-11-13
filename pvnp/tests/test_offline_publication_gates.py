"""Local, network-free release-gate tests; do not grant legal clearance."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]


def module(name, relpath):
    spec = importlib.util.spec_from_file_location(name, ROOT / relpath)
    assert spec is not None and spec.loader is not None
    out = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(out)
    return out


assets = module("assets", "scripts/audit_release_assets.py")
approve = module("approve", "scripts/check_publication_approval.py")
pdfverify = module("pdfverify", "scripts/verify_pdfs.py")


class OfflineReleaseTests(unittest.TestCase):
    def test_pdf_and_source_categories_remain_manual(self):
        self.assertIn("manual", assets.classify(
            "pvnp/preprints/part-i-curvature-bounded-wave-computation/paper.pdf"))
        self.assertIn("rights_review", assets.classify(
            "pvnp/papers/part-i-curvature-bounded-wave-computation/main.tex"))

    def test_tex_inclusion_and_metadata_detection(self):
        self.assertEqual(assets.TEX_INCLUDE.findall(
            r"\includepdf[pages=-]{archive/part-i.pdf}"),
            [("includepdf", "archive/part-i.pdf")])
        self.assertIn("Creator", assets.metadata_flags(
            "Creator: C:\\Users\\example\\AppData\\TeX\nTitle: PVNP"))
        self.assertEqual(assets.metadata_flags("Title: PVNP\nPages: 22"), [])

    def test_pdf_text_flags_email_and_local_path(self):
        self.assertTrue(assets.PDF_TEXT_RISKS["email_address"].search("contact@example.org"))
        self.assertTrue(assets.PDF_TEXT_RISKS["home_directory_path"].search("C:\\Users\\example"))

    def test_pdf_verifier_decodes_utf8_not_windows_cp1252(self):
        # 0x90 occurs inside multibyte UTF-8; Windows CP1252 cannot decode it.
        text = "wave ψ and curvature —"
        with patch.object(pdfverify.subprocess, "check_output",
                          return_value=text.encode("utf-8")) as run:
            self.assertEqual(pdfverify.command("pdftotext", "-enc", "UTF-8",
                                               "sample.pdf", "-"), text)
            self.assertEqual(run.call_args.kwargs["stderr"], pdfverify.subprocess.PIPE)

    def test_pdf_verifier_requests_utf8_for_both_extraction_modes(self):
        with patch.object(pdfverify, "command", return_value=("ψ " * 200)) as run:
            self.assertGreater(len(pdfverify.pdf_text(Path("sample.pdf"))), 350)
            self.assertEqual(run.call_args.args[:4],
                             ("pdftotext", "-enc", "UTF-8", "-layout"))
        with patch.object(pdfverify, "command", return_value="ψ\n\f") as run:
            self.assertEqual(pdfverify.page_texts(Path("sample.pdf")), ["ψ"])
            self.assertEqual(run.call_args.args[:4],
                             ("pdftotext", "-enc", "UTF-8", "-raw"))

    def test_incomplete_template_never_approves(self):
        template = {
            "schema": "PVNP-publication-approval-v1",
            "status": "UNSIGNED_TEMPLATE_NOT_AUTHORIZATION",
            "reviewed_commit_sha": None,
        }
        missing = approve.check(template, "0" * 40)
        self.assertIn("author approval status not recorded", missing)
        self.assertTrue(any("permission_to_make_repository_public" in s for s in missing))

    def test_only_explicit_complete_acknowledgments_pass_logic(self):
        data = {
            "schema": "PVNP-publication-approval-v1",
            "status": "AUTHOR_APPROVED",
            "reviewed_commit_sha": "a" * 40,
            "selected_code_license": "BSD-3-Clause",
            "selected_manuscript_license": "CC-BY-4.0",
        }
        data.update({k: True for k in approve.REQUIRED_TRUE})
        self.assertEqual(approve.check(data, "a" * 40), [])
        self.assertTrue(approve.check(data, "b" * 40))


if __name__ == "__main__":
    unittest.main()
