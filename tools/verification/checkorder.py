"""Check that every MomentSystem row matches the ORDER in which the headline
actually passes the probabilities.

If a headline passes  r_i = |d (complement y_i)|^2  while the MomentSystem rows
were generated against the lexicographic top fiber (or vice versa), the
structure is not the moment system of the code, and the headline - though
kernel-proved - does not apply to a real code.

Whitespace in generated Lean is irregular (some generators emit double spaces),
so every pattern here is whitespace-tolerant; an over-strict regex silently
turns into a false positive, which is worse than no check at all.

Usage:  python tools/run.py verification/checkorder.py
"""
import io
import os
import re
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
SQ = os.path.join(REPO, 'SixQubit')
BITS = {'true': 1, 'false': 0}
S = r'\s+'


def module_data(f):
    src = io.open(os.path.join(SQ, f), encoding='utf-8').read()
    ys, zs = {}, {}
    pat = (r'def' + S + r'(y|z)(\d+)' + S + r':' + S + r'SS\.BitString' + S +
           r'6' + S + r':=' + S + r'bs' + S + (r'(\w+)' + S) * 5 + r'(\w+)')
    for m in re.finditer(pat, src):
        tag, idx = m.group(1), int(m.group(2))
        v = [BITS[m.group(i + 3)] for i in range(6)]
        (ys if tag == 'y' else zs)[idx] = v
    return src, ys, zs


def headline_top(src):
    k = src.find('theorem no_go_of_moments')
    body = src[k:src.find(': False', k)]
    comp = [int(x) for x in re.findall(
        r'Complex\.normSq' + S + r'\(d' + S + r'\(SS\.complement' + S +
        r'y(\d+)\)\)', body)]
    if comp:
        return 'complement', comp
    lex = [int(x) for x in re.findall(
        r'Complex\.normSq' + S + r'\(d' + S + r'z(\d+)\)', body)]
    return 'lex', lex


print('%-9s %-11s %-6s %-6s %s' % ('module', 'top passed', 'tops', 'rows', 'verdict'))
flagged, unparsed = [], []
for f in sorted(os.listdir(SQ)):
    if not f.endswith('.lean') or f == 'Audit.lean':
        continue
    src, ys, zs = module_data(f)
    if 'theorem no_go_of_moments' not in src or not ys:
        continue
    kind, order = headline_top(src)
    if not order:
        unparsed.append(f[:-5])
        print('%-9s %-11s %-6s %-6s UNPARSED - treat as unchecked'
              % (f[:-5], kind, 0, '?'))
        continue
    if kind == 'complement':
        if any(i not in ys for i in order):
            unparsed.append(f[:-5]); continue
        top = [[1 - b for b in ys[i]] for i in order]
    else:
        if any(i not in zs for i in order):
            unparsed.append(f[:-5])
            print('%-9s %-11s %-6s %-6s UNPARSED - treat as unchecked'
                  % (f[:-5], kind, len(order), '?'))
            continue
        top = [zs[i] for i in order]

    # Structure fields WRAP across lines.  A field ends where the next field
    # begins ("  <name> :" at indent two) or the structure does.  Reading only
    # the first physical line silently drops terms and manufactures mismatches.
    fields = {}
    cur = None
    for ln in src.split('\n'):
        mh = re.match(r'  (\w+)\s*:\s*(.*)$', ln)
        if mh and not ln.startswith('   '):
            cur = mh.group(1)
            fields[cur] = mh.group(2)
        elif cur is not None and ln.startswith('      '):
            fields[cur] += ' ' + ln.strip()
        elif ln.strip() == '' or not ln.startswith(' '):
            cur = None

    idx = [(i,) for i in range(6)] + list(combinations(range(6), 2))
    mism = tot = 0
    for T in idx:
        nm = 'm%s' % ''.join(str(j + 1) for j in T)
        row = fields.get(nm)
        if not row or '=' not in row:
            continue
        tot += 1
        got = sorted(int(x) for x in re.findall(r'\br(\d+)\b',
                                                row.split('=')[1]))
        want = sorted(k for k in range(len(top))
                      if all(top[k][j] == 1 for j in T))
        if got != want:
            mism += 1
    v = 'OK' if mism == 0 else 'MISMATCH %d/%d  <<<<' % (mism, tot)
    if mism:
        flagged.append((f[:-5], mism, tot))
    print('%-9s %-11s %-6d %-6d %s' % (f[:-5], kind, len(top), tot, v))

print()
if unparsed:
    print('UNCHECKED (could not resolve the top ordering): %s' % ', '.join(unparsed))
if flagged:
    print('MomentSystem rows inconsistent with the headline argument order:')
    for nm, mism, tot in flagged:
        print('  %-9s %d of %d rows' % (nm, mism, tot))
    sys.exit(1)
print('every checked module: MomentSystem rows agree with the headline order')
