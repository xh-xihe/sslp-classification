"""Assertion helper shared by the verification scripts.

Every script that certifies a number printed in the manuscript uses this, so
that a mismatch is a nonzero exit code rather than a line of output nobody
reads.  Import it, call `expect(...)` for each claim, and end with `finish()`.
"""

import sys

_failures = []
_checks = 0


def expect(name, got, want, tol=0.0):
    """Record one claim.  Numeric comparison if tol > 0, else exact equality."""
    global _checks
    _checks += 1
    if tol > 0:
        ok = abs(float(got) - float(want)) <= tol
        shown = '%.6g vs %.6g (tol %.1g)' % (float(got), float(want), tol)
    else:
        ok = got == want
        shown = '%r vs %r' % (got, want)
    if not ok:
        _failures.append((name, shown))
    print('  [%s] %-52s %s' % ('ok' if ok else 'FAIL', name, shown))
    return ok


def expect_true(name, cond, detail=''):
    return expect(name, bool(cond), True) if not detail else expect(
        name + ' (' + detail + ')', bool(cond), True)


def finish(title=''):
    print()
    if _failures:
        print('%s: %d of %d checks FAILED' % (title or 'result', len(_failures), _checks))
        for n, s in _failures:
            print('   FAIL  %s   %s' % (n, s))
        sys.exit(1)
    print('%s: all %d checks passed' % (title or 'result', _checks))
    sys.exit(0)
