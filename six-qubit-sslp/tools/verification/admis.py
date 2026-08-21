"""Verify every (flip mask, dressing) pair used in a headline theorem is a
genuine weight-at-most-two Pauli:  |supp(e) union supp(z)| <= 2.

A weight-3 row would silently turn the statement into a distance-4 no-go, which
is a different and much weaker claim.

Two bugs this script used to have, fixed here because a collaborator's audit
caught them:
  * it defaulted to orbit 5 alone while the README claimed it covered all 51;
  * it returned exit code 0 even when a mask or dressing could not be resolved,
    so unresolved rows read as passing rows.
Now it defaults to EVERY module with a headline, and unresolved rows are a
failure, not a silence.

Usage:
    python tools/run.py verification/admis.py           # every module
    python tools/run.py verification/admis.py 5 26 31   # selected orbits
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
SQ = os.path.join(REPO, 'SixQubit')
BITS = {'true': 1, 'false': 0}
S = r'\s+'


def modules(argv):
    out = []
    for f in sorted(os.listdir(SQ)):
        if not f.endswith('.lean') or f == 'Audit.lean':
            continue
        src = io.open(os.path.join(SQ, f), encoding='utf-8').read()
        if 'theorem no_go_of_moments' not in src:
            continue
        oid = '66' if f == 'Order9.lean' else re.sub(r'[^0-9]', '', f)
        if argv and oid not in set(argv):
            continue
        out.append((f, oid, src))
    return out


def masks(src):
    """Resolve every BitString definition: literal, bxor, stdBasis, complement."""
    d = {}
    pat = (r'def' + S + r'(\w+)' + S + r':' + S + r'SS\.BitString' + S + r'6' +
           S + r':=' + S + r'bs' + S + (r'(\w+)' + S) * 5 + r'(\w+)')
    for m in re.finditer(pat, src):
        d[m.group(1)] = [BITS[m.group(i + 2)] for i in range(6)]
    for m in re.finditer(r'def' + S + r'(\w+)' + S + r':' + S + r'SS\.BitString' +
                         S + r'6' + S + r':=' + S + r'SS\.stdBasis' + S + r'(\d+)', src):
        i = int(m.group(2))
        d[m.group(1)] = [1 if k == i else 0 for k in range(6)]
    for _ in range(3):                      # resolve chains
        for m in re.finditer(r'def' + S + r'(\w+)' + S + r':' + S +
                             r'SS\.BitString' + S + r'6' + S + r':=' + S +
                             r'SS\.bxor' + S + r'(\w+)' + S + r'(\w+)', src):
            a, b = m.group(2), m.group(3)
            if a in d and b in d:
                d[m.group(1)] = [d[a][i] ^ d[b][i] for i in range(6)]
        for m in re.finditer(r'def' + S + r'(\w+)' + S + r':' + S +
                             r'SS\.BitString' + S + r'6' + S + r':=' + S +
                             r'SS\.complement' + S + r'(\w+)', src):
            if m.group(2) in d:
                d[m.group(1)] = [1 - x for x in d[m.group(2)]]
    return d


rc = 0
for f, oid, src in modules(sys.argv[1:]):
    defs = masks(src)
    k = src.find('theorem no_go_of_moments')
    body = src[k:src.find(': False', k)]
    MASK = r'(\(fun _ => false\)|\(fun _ => true\)|\S+)'
    off = re.findall(r'offSum' + S + r'c' + S + r'd' + S + MASK + S +
                     MASK + S + r'=' + S + r'0', body)
    dia = re.findall(r'diagBot' + S + r'c' + S + MASK + S + MASK + S +
                     r'=' + S + r'diagTop', body)
    bad, unres, prof = [], [], {}
    for kind, rows in (('offSum', off), ('diag', dia)):
        for e, z in rows:
            # a lambda dressing is the all-zero mask; resolve it before
            # stripping parentheses, or the prefix test never fires
            # only the all-false lambda is the zero mask; anything else with a
            # `fun` in it must be refused, not guessed at
            for slot in ('e', 'z'):
                v = e if slot == 'e' else z
                if 'fun' in v and 'false' not in v:
                    unres.append((kind, e, z))
                    v = None
                    break
            else:
                if 'fun' in e:
                    e = '__zero__'
                if 'fun' in z:
                    z = '__zero__'
            defs.setdefault('__zero__', [0] * 6)
            e, z = e.strip('()'), z.strip('()')
            if e not in defs or z not in defs:
                unres.append((kind, e, z))
                continue
            w = len({i for i in range(6) if defs[e][i]} |
                    {i for i in range(6) if defs[z][i]})
            prof[w] = prof.get(w, 0) + 1
            if w > 2:
                bad.append((kind, e, z, w))
    # Cross-check: the regex must have seen every row the headline declares.
    # A dressing written in an unanticipated form -- say `(fun i => i == 0)` --
    # would otherwise be skipped silently and the script would still say OK.
    # Count declared rows by the BARE keyword. Reusing the parser's own
    # `offSum c d` prefix made both counters blind to the same unexpected
    # spelling -- `offSum (c) d e1 t2 = 0` -- so they agreed while both
    # missed the row, and the script still printed OK.
    declared = (len(re.findall(r'\boffSum\b', body))
                + len(re.findall(r'\bdiagBot\b', body)))
    parsed = len(off) + len(dia)
    if parsed != declared:
        unres.append(('count', 'parsed %d rows' % parsed,
                      'headline declares %d' % declared))
    status = 'OK'
    if bad:
        status = 'INADMISSIBLE'
    elif unres:
        status = 'UNRESOLVED'
    print('orbit %-3s %-9s %2d offSum + %2d diag rows   weights %s   %s'
          % (oid, f[:-5], len(off), len(dia), dict(sorted(prof.items())), status))
    for kind, e, z, w in bad:
        print('   *** %-7s e=%-8s z=%-8s WEIGHT %d' % (kind, e, z, w))
        rc = 1
    for kind, e, z in unres:
        print('   ??? %-7s e=%-8s z=%-8s could not resolve - NOT verified'
              % (kind, e, z))
        rc = 1

print()
if rc:
    print('FAIL - some row is inadmissible or could not be resolved.')
else:
    print('PASS - every row is a genuine weight-<=2 Pauli.')
sys.exit(rc)
