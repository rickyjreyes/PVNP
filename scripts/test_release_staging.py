#!/usr/bin/env python3
"""Hermetic release-gate tests: no Lean, network, billing, or LaTeX required.

The real release script is copied into a fixture repository; only its external
compiler/checker commands are stubbed. Tests assert that failures cannot promote
an unverified artifact to the tracked release path.
"""
from __future__ import annotations

import os
import subprocess
import tempfile
from pathlib import Path

SCRIPT = Path(os.environ.get('PVNP_TEST_RELEASE_SCRIPT',
    Path(__file__).resolve().parents[1] / 'scripts' / 'run_release_verification.sh'))


def write(path: Path, content: str, executable: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding='utf8')
    if executable:
        path.chmod(0o755)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix='pvnp-release-gate-') as tmp:
        root = Path(tmp)
        release = root / 'pvnp/preprints/consolidated-wave-computation/paper.pdf'
        release.parent.mkdir(parents=True)
        write(root / 'scripts/run_release_verification.sh', SCRIPT.read_text(encoding='utf8'), True)
        write(root / 'scripts/check_manuscript_alignment.py', 'print("Manuscript scope PASS")\n')
        # Avoid recursion: the fixture copy of the release script invokes a stub,
        # while this outer test verifies the actual gate's control flow.
        write(root / 'scripts/test_release_staging.py', 'print("Hermetic fixture stub PASS")\n')
        write(root / 'scripts/verify_pdfs.py', '''import os, pathlib, sys
assert pathlib.Path(sys.argv[2]).read_bytes() == b'NEW-VALIDATED-PDF'
assert os.environ.get('FAIL_PDF_VERIFY') != '1'
print('Compiled PDF verification PASS')
''')
        write(root / 'scripts/build_pdfs.sh', '''#!/usr/bin/env bash
set -euo pipefail
[[ "${FAIL_PDF_BUILD:-0}" == 0 ]] || exit 3
mkdir -p "$(dirname "$PVNP_PDF_OUTPUT")" "$PVNP_PDF_REVIEW_DIR/pdfs"
printf 'NEW-VALIDATED-PDF' > "$PVNP_PDF_OUTPUT"
''', True)
        write(root / 'lean/PVNP/Test.lean', 'theorem test : True := by trivial\n')
        write(root / 'lean/audit/check_axioms.py', 'print("Axiom audit PASS")\n')
        write(root / 'bin/lake', '#!/usr/bin/env bash\n[[ "${FAIL_LEAN:-0}" == 0 ]]\n', True)
        write(root / 'bin/node', '#!/usr/bin/env bash\n[[ "${FAIL_DASH:-0}" == 0 ]]\n', True)
        for cmd in ('pdflatex', 'pdfinfo', 'pdftotext'):
            write(root / 'bin' / cmd, '#!/usr/bin/env bash\nexit 0\n', True)
        env = os.environ.copy()
        env['PATH'] = str(root / 'bin') + os.pathsep + env['PATH']
        env.pop('PVNP_RELEASE_VERIFY_DIR', None)

        def run(mode: str, **overrides: str) -> subprocess.CompletedProcess:
            e = env.copy()
            e.update(overrides)
            return subprocess.run(['bash', str(root / 'scripts/run_release_verification.sh'), mode],
                                  env=e, text=True, capture_output=True, check=False)

        assert subprocess.run(['bash', '-n', str(root / 'scripts/run_release_verification.sh')],
                              check=False).returncode == 0
        for name, mode, overrides, success in (
            ('PDF-only staging', '--pdf-only', {}, True),
            ('PDF build failure', '--all', {'FAIL_PDF_BUILD': '1'}, False),
            ('PDF content failure', '--all', {'FAIL_PDF_VERIFY': '1'}, False),
            ('Lean failure', '--all', {'FAIL_LEAN': '1'}, False),
            ('Dashboard failure', '--all', {'FAIL_DASH': '1'}, False),
        ):
            release.write_bytes(b'OLD-PUBLISHED-PDF')
            result = run(mode, **overrides)
            assert (result.returncode == 0) == success, f'{name}: {result.stderr}\n{result.stdout}'
            assert release.read_bytes() == b'OLD-PUBLISHED-PDF', name
            print('PASS:', name, 'does not modify the published PDF')
        release.write_bytes(b'OLD-PUBLISHED-PDF')
        result = run('--all')
        assert result.returncode == 0, result.stderr + '\n' + result.stdout
        assert release.read_bytes() == b'NEW-VALIDATED-PDF', result.stdout
        print('PASS: complete verification promotes the staged PDF')


if __name__ == '__main__':
    main()
