#!/usr/bin/env python3
"""Check that every Lean identifier the documentation of record names exists.

Documentation drift is invisible to the build: a document can cite a theorem
that was renamed, moved, or never existed, and `lake build` will not notice.

The names come from two places, and both are required.  The README supplies
whatever it cites in backticks; the claims ledger supplies the declarations its
reviewed claims rest on.  Taking the union matters: when the README was
rewritten from 665 lines to 135, its citation count fell from 159 names to a
single one belonging to Lean core, and this check passed unconditionally while
appearing green.  A check whose input set can silently empty is worse than no
check, so `main` now fails when the ledger contributes nothing.

Usage:  python tools/check-readme-names.py
It writes a scratch Lean file of `#check`s and runs it; a nonzero exit means
the documentation cites something that is not there.
"""
import io
import os
import re
import subprocess
import sys
from pathlib import Path
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SKIP_SUFFIX = ('.lean', '.tex', '.py', '.sh', '.json', '.txt', '.md', '.tsv')
SKIP_PREFIX = ('six:', 'thm:', 'eq:', 'lem:', 'cor:', 'def:', 'sec:', 'tab:')


def candidates(readme: str):
    names = set()
    for m in re.finditer(r'`([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+)`',
                         readme):
        n = m.group(1)
        if n.endswith(SKIP_SUFFIX) or n.startswith(SKIP_PREFIX):
            continue
        names.add(n)
    return sorted(names)


def check_names(names, runner=subprocess.run, root=ROOT) -> int:
    """Fail on every Lean failure, including errors unrelated to name lookup."""
    work = Path(root) / 'tmp' / 'verification'
    work.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='readme-',
                                     dir=work, encoding='utf-8', newline='\n',
                                     delete=False) as handle:
        scratch = Path(handle.name)
        handle.write('import MainTheory\nimport SixQubit.Audit\n')
        handle.write('open MainTheory SixQubit\n')
        for name in names:
            handle.write('#check @%s\n' % name)
    try:
        proc = runner(['lake', 'env', 'lean', '-j', '1', '-DwarningAsError=true', str(scratch)],
                      cwd=root, capture_output=True, text=True,
                      encoding='utf-8', errors='replace')
        output = proc.stdout + proc.stderr
        (work / 'readme-names.log').write_text(output, encoding='utf-8')
        print('checked %d identifiers named in README.md' % len(names))
        if proc.returncode != 0:
            print('FAIL: Lean exited %d; diagnostics in %s' %
                  (proc.returncode, work / 'readme-names.log'))
            # The console codepage here is GBK; Lean's output carries
            # unicode, and printing it raw crashes the reporter before
            # the caller ever sees the failure.
            text = output.rstrip() or '(no diagnostics)'
            sys.stdout.write(text.encode(sys.stdout.encoding or 'utf-8',
                                         'replace').decode(sys.stdout.encoding
                                                           or 'utf-8') + chr(10))
            return 1
        print('all present')
        return 0
    finally:
        scratch.unlink(missing_ok=True)


def ledger_declarations(root=ROOT):
    """Declarations the claims ledger says are covered.  These are the names a
    reader is invited to check, so they are part of the documentation of
    record."""
    import glob
    import json
    names = set()
    for path in sorted(glob.glob(os.path.join(root, 'results', 'paper-claims-*.json'))):
        with io.open(path, encoding='utf-8') as handle:
            for claim in json.load(handle).get('claims', []):
                if claim.get('status') in ('covered', 'partial'):
                    names.update(claim.get('lean_declarations', []))
    return names


def main() -> int:
    readme = io.open(os.path.join(ROOT, 'README.md'), encoding='utf-8').read()
    from_readme = set(candidates(readme))
    from_ledger = ledger_declarations()
    if not from_ledger:
        print('FAIL: the claims ledger names no declarations, so this check '
              'would verify only whatever the README happens to cite; refusing '
              'to report a pass on an input set that can silently empty.')
        return 1
    names = sorted(from_readme | from_ledger)
    print('%d identifiers: %d from README.md, %d from the claims ledger'
          % (len(names), len(from_readme), len(from_ledger)))
    return check_names(names)


if __name__ == '__main__':
    sys.exit(main())
