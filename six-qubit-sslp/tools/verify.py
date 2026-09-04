#!/usr/bin/env python3
"""Verify the certification claim, end to end, with checks that cannot lie.

This exists because a hand-written check did lie. Grepping a lake log for
`': error'` matches nothing either way on a clean build, so it looked reliable
for a whole session and then silently reported a broken build as clean. Lake
prints failures as `error:` at the *start* of a line, and the exit code is
authoritative.

Runs, and fails on any one of:

  1. `lake build` over the whole package -- exit code and error lines.
     A cold run saturates the machine; see `check_build`.
  2. `lake env lean MainTheory/Audit.lean` -- every audited declaration's axiom
     set must be inside {propext, Classical.choice, Quot.sound}, with no
     sorryAx.
  3. A source sweep for real `sorry`, `native_decide` and `axiom` declarations,
     ignoring the many mentions of those words inside docstrings.
  4. tools/check-readme-names.py -- every Lean name the README cites exists.

Usage:  python tools/verify.py
"""
import io
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_DIRS = ('MainTheory', 'SS', 'SixQubit')
ERROR_LINE = re.compile(r'(^error|: error)', re.IGNORECASE | re.MULTILINE)


def run(cmd, **kw):
    """Run a command, forcing utf-8: the console codepage here is GBK and
    corrupts Lean's output otherwise."""
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True,
                          encoding='utf-8', errors='replace', **kw)


def check_build():
    # Lake fans out to every core and has no job-count flag in Lake 5.0.0
    # (`-j` and `--jobs` are both rejected); on this workstation a cold run is
    # 24 Lean workers holding ~65 GB at once.  The package's own
    # `weakLeanArgs := #["-j","1"]` caps threads *inside* each worker, which is
    # the only knob there is.  Run this when the machine is otherwise idle.
    proc = run(['lake', 'build'])
    log = proc.stdout + proc.stderr
    errs = ERROR_LINE.findall(log)
    warns = len(re.findall(r'warning', log, re.IGNORECASE))
    ok = proc.returncode == 0 and not errs and warns == 0
    detail = 'exit=%d, error lines=%d, warnings=%d' % (
        proc.returncode, len(errs), warns)
    if not ok:
        detail += '\n' + '\n'.join(
            l for l in log.splitlines() if ERROR_LINE.search(l))[:2000]
    return ok, detail


# Every audit file in the package.  Running only MainTheory/Audit.lean would
# leave the 592 entries of SixQubit/Audit.lean and the 20 of
# SixQubit/CodeWrapAudit.lean unchecked: `lake build` compiles them, but
# `#print axioms` reports through `info`, so a bad footprint there fails
# nothing.  The README's headline audit count comes from those files, so they
# have to be in this check.
AUDIT_FILES = ('MainTheory/Audit.lean', 'SixQubit/Audit.lean',
               'SixQubit/CodeWrapAudit.lean')

AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")


def check_axioms():
    total, bad, missing = 0, [], []
    for path in AUDIT_FILES:
        if not os.path.exists(os.path.join(ROOT, path)):
            missing.append(path + ' (absent)')
            continue
        proc = run(['lake', 'env', 'lean', path])
        log = proc.stdout + proc.stderr
        if proc.returncode != 0:
            return False, 'audit run failed on %s, exit=%d' % (
                path, proc.returncode)
        if 'sorryAx' in log:
            return False, 'sorryAx present in ' + path
        entries = AXIOM_LINE.findall(log.replace('\n', ' '))
        if not entries:
            missing.append(path + ' (no declarations audited)')
            continue
        total += len(entries)
        bad += [n for n, a in entries
                if set(x.strip() for x in a.split(',')) - ALLOWED]
    if missing:
        return False, 'audit files produced nothing: ' + ', '.join(missing)
    ok = not bad
    detail = '%d declarations over %d audit files, %d outside the allowed set' % (
        total, len(AUDIT_FILES), len(bad))
    if bad:
        detail += ': ' + ', '.join(bad[:5])
    return ok, detail


def check_sources():
    """Real uses only: every legitimate mention in this repository is inside
    backticks in a docstring."""
    findings = []
    for d in LEAN_DIRS:
        for base, _, files in os.walk(os.path.join(ROOT, d)):
            for f in files:
                if not f.endswith('.lean'):
                    continue
                path = os.path.join(base, f)
                text = io.open(path, encoding='utf-8', errors='replace').read()
                for i, line in enumerate(text.splitlines(), 1):
                    stripped = re.sub(r'`[^`]*`', '', line)
                    if re.search(r'(^|[^A-Za-z_])sorry([^A-Za-z_]|$)',
                                 stripped):
                        findings.append('%s:%d sorry' % (path, i))
                    if 'native_decide' in stripped:
                        findings.append('%s:%d native_decide' % (path, i))
                    if re.match(r'\s*axiom\s', line):
                        findings.append('%s:%d axiom' % (path, i))
    return not findings, ('clean' if not findings
                          else '\n'.join(findings[:10]))


def check_names():
    proc = run([sys.executable, 'tools/check-readme-names.py'])
    out = (proc.stdout + proc.stderr).strip()
    return proc.returncode == 0, out.splitlines()[-1] if out else ''


def main() -> int:
    checks = [('build', check_build), ('axioms', check_axioms),
              ('sources', check_sources), ('readme names', check_names)]
    failed = False
    for name, fn in checks:
        ok, detail = fn()
        print('[%s] %-14s %s' % ('PASS' if ok else 'FAIL', name, detail))
        failed = failed or not ok
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
