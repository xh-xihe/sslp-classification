#!/usr/bin/env python3
"""Check that every Lean identifier the README names actually exists.

Documentation drift is invisible to the build: a README can cite a theorem
that was renamed, moved, or never existed, and `lake build` will not notice.
This has already happened twice in this repository, so the check is mechanical.

Usage:  python tools/check-readme-names.py
It writes a scratch Lean file of `#check`s and runs it; a nonzero exit means
the README cites something that is not there.
"""
import io
import os
import re
import subprocess
import sys

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


def main() -> int:
    readme = io.open(os.path.join(ROOT, 'README.md'), encoding='utf-8').read()
    names = candidates(readme)
    scratch = os.path.join(ROOT, '.check-readme-names.lean')
    with io.open(scratch, 'w', encoding='utf-8', newline='\n') as f:
        f.write('import MainTheory\nimport SixQubit.Audit\n')
        f.write('open MainTheory SixQubit\n')
        for n in names:
            f.write('#check @%s\n' % n)
    # The Windows console codepage is GBK here; forcing utf-8 with
    # errors='replace' keeps Lean's output from crashing the reader thread.
    proc = subprocess.run(['lake', 'env', 'lean', scratch], cwd=ROOT,
                          capture_output=True, text=True,
                          encoding='utf-8', errors='replace')
    os.remove(scratch)
    bad = [line for line in (proc.stdout + proc.stderr).splitlines()
           if 'unknown' in line.lower()]
    print('checked %d identifiers named in README.md' % len(names))
    if bad:
        print('MISSING:')
        for line in bad:
            print('  ' + line)
        return 1
    print('all present')
    return 0


if __name__ == '__main__':
    sys.exit(main())
