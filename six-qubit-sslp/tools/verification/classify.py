"""Classify every hypothesis of every headline theorem.

Only three categories are legitimate:
  (a) offSum ... = 0
  (b) diagBot ... = diagTop ...
  (c) MomentSystem ...

Anything else is an algebraic fact smuggled in as an assumption. That defect is
invisible from outside the proof - the theorem still says `False` and still has a
clean axiom footprint - so this check matters more than compilation does.

Usage (from the repository root):
    python tools/run.py verification/classify.py            # every orbit module
    python tools/run.py verification/classify.py 5 26 31    # selected orbits
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
SQ = os.path.join(REPO, 'SixQubit')


def modules(argv):
    if argv:
        want = set(argv)
        out = []
        for f in sorted(os.listdir(SQ)):
            m = re.fullmatch(r'Orbit(\d+)\.lean', f)
            oid = '66' if f == 'Order9.lean' else (m.group(1) if m else None)
            if oid is not None and oid in want:
                out.append(f)
        return out
    out = []
    for f in sorted(os.listdir(SQ)):
        if not f.endswith('.lean') or f == 'Audit.lean':
            continue
        src = io.open(os.path.join(SQ, f), encoding='utf-8').read()
        if 'theorem no_go_of_moments' in src:
            out.append(f)
    return out


def hypotheses(body):
    """Split the binder list on top-level parentheses."""
    out, depth, cur = [], 0, ''
    for ch in body:
        if ch == '(':
            depth += 1
            if depth == 1:
                cur = ''
                continue
        if ch == ')':
            depth -= 1
            if depth == 0:
                out.append(cur)
                continue
        if depth >= 1:
            cur += ch
    return out


mods = modules(sys.argv[1:])
bad_total = 0
print('%-12s %6s %8s %9s %8s %8s' % ('module', 'hyps', 'offSum', 'diag', 'Moment', 'OTHER'))
for f in sorted(mods, key=lambda x: 66 if x == 'Order9.lean'
                else int(re.sub(r'[^0-9]', '', x) or 0)):
    src = io.open(os.path.join(SQ, f), encoding='utf-8').read()
    k = src.find('theorem no_go_of_moments')
    if k < 0:
        print('%-12s NO HEADLINE THEOREM' % f[:-5])
        continue
    body = src[k:src.find(': False', k)]
    a = b = c = 0
    other = []
    for h in hypotheses(body):
        t = ' '.join(h.split())
        if 'offSum' in t and t.rstrip().endswith('= 0'):
            a += 1
        elif 'diagBot' in t and 'diagTop' in t:
            b += 1
        elif 'MomentSystem' in t:
            c += 1
        elif 'BitString 6 ->' in t:
            continue                       # the amplitude binders c, d
        else:
            other.append(t[:90])
    print('%-12s %6d %8d %9d %8d %8d%s'
          % (f[:-5], a + b + c + len(other), a, b, c, len(other),
             '' if not other else '   <<< SMUGGLED'))
    for t in other:
        print('      OTHER: %s' % t)
    bad_total += len(other)

print()
print('modules checked: %d' % len(mods))
print('hypotheses outside the three legitimate categories: %d' % bad_total)
if bad_total == 0:
    print('PASS - every headline hypothesis is a Knill-Laflamme row or the moment system.')
else:
    print('FAIL - an algebraic fact is being assumed rather than derived.')
    sys.exit(1)
