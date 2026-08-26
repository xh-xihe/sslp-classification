"""Independent audit of the two spinor orbit modules (12 and 6).

Reads the generated Lean back and checks, without trusting the generator:

  1. no `sorry` and no `native_decide` anywhere in tactic position;
  2. every hypothesis of the headline theorem is one of
       (a) offSum c d <mask> <z> = 0
       (b) diagBot c <mask> <z> = diagTop d <mask> <z>
       (c) MomentSystem <normSq ...>
     and nothing else;
  3. every (mask, dressing) pair used is an admissible weight-<=2 Pauli, i.e.
     |supp(mask) union supp(z)| <= 2;
  4. the bit strings y_i / z_i really are the two residue fibers;
  5. the MomentSystem structure is exactly the two normalizations plus the
     twenty-one one- and two-coordinate moment equalities of those fibers,
     plus one nonnegativity per basis state -- no extra rows.

Run with:  python tools/run.py verification/audit_spinor.py
"""
import io
import os
import re
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
N = 6
ORBITS = {12: (4, [0, 1, 1, 1, 1, 2], 2), 6: (3, [0, 1, 1, 1, 1, 1], 1)}

supp = lambda s: {i for i, ch in enumerate(s) if ch == '1'}


def fiber(a, q, res):
    return [format(k, '06b') for k in range(64)
            if sum(a[i] for i in range(N) if format(k, '06b')[i] == '1') % q == res]


def audit(oid):
    q, avec, delta = ORBITS[oid]
    path = os.path.join(ROOT, 'SixQubit', 'Orbit%d.lean' % oid)
    src = io.open(path, encoding='utf-8').read()
    ok = True

    def check(cond, msg):
        nonlocal ok
        print('  [%s] %s' % ('ok ' if cond else 'FAIL', msg))
        ok = ok and bool(cond)

    print('=== Orbit %d  (%s)' % (oid, path))
    # 1 -----------------------------------------------------------------
    body = NLSTRIP = re.sub(r'/-.*?-/', '', src, flags=re.S)
    check('sorry' not in body, 'no `sorry` outside docstrings')
    check('native_decide' not in body, 'no `native_decide` outside docstrings')

    # bit strings of every def
    bits = dict(re.findall(r'def (\w+) : SS\.BitString 6 := bs [^-]*-- (\d{6})', src))

    # 4 -----------------------------------------------------------------
    S0 = [bits['y%d' % r] for r in range(len([k for k in bits if k.startswith('y')]))]
    S1 = [bits['z%d' % r] for r in range(len([k for k in bits if k.startswith('z')]))]
    check(S0 == fiber(avec, q, 0), 'y-strings are the residue-0 fiber (%d strings)' % len(S0))
    check(S1 == fiber(avec, q, delta),
          'z-strings are the residue-%d fiber (%d strings)' % (delta, len(S1)))
    check(re.search(r'def av : Fin 6 -> ZMod %d := !\[%s\]'
                    % (q, ', '.join(map(str, avec))), src) is not None,
          'angle vector in the file is a = (%s), q = %d' % (', '.join(map(str, avec)), q))

    # 2, 3 --------------------------------------------------------------
    head = src[src.index('theorem no_go_of_moments'):]
    head = head[:head.index('    : False := by')]
    hyps = re.findall(r'\n    \((\w+) : (.*?)\)(?=\n    \(|\n    :|$)',
                      head.rstrip() + '\n    :', re.S)
    kinds = {'a': 0, 'b': 0, 'c': 0, 'other': []}
    used = []
    for name, stmt in hyps:
        st = ' '.join(stmt.split())
        m = re.fullmatch(r'offSum c d (\w+) (\w+) = 0', st)
        if m:
            kinds['a'] += 1
            used.append((m.group(1), m.group(2)))
            continue
        m = re.fullmatch(r'diagBot c (\w+) (\w+) = diagTop d \1 \2', st)
        if m:
            kinds['b'] += 1
            used.append((m.group(1), m.group(2)))
            continue
        if st.startswith('MomentSystem'):
            args = re.findall(r'\(Complex\.normSq \((c y\d+|d z\d+)\)\)', st)
            expect = (['c y%d' % r for r in range(len(S0))]
                      + ['d z%d' % r for r in range(len(S1))])
            check(args == expect, 'MomentSystem is applied to the %d probabilities in order'
                  % len(expect))
            kinds['c'] += 1
            continue
        kinds['other'].append((name, st[:70]))
    check(not kinds['other'], 'every hypothesis is (a) offSum / (b) diag / (c) MomentSystem'
          + ('' if not kinds['other'] else '  UNCLASSIFIED: %s' % kinds['other']))
    print('       (a) offSum rows        : %d' % kinds['a'])
    print('       (b) diagBot=diagTop    : %d' % kinds['b'])
    print('       (c) MomentSystem       : %d' % kinds['c'])
    print('       total hypotheses       : %d' % (kinds['a'] + kinds['b'] + kinds['c']))
    bad = [(m, z, bits[m], bits[z]) for m, z in used
           if len(supp(bits[m]) | supp(bits[z])) > 2]
    check(not bad, 'every (mask, dressing) is an admissible weight-<=2 Pauli%s'
          % ('' if not bad else '  BAD: %s' % bad))

    # 5 -----------------------------------------------------------------
    struct = src[src.index('structure MomentSystem'):]
    struct = struct[:struct.index('/-- ')]
    rows = re.findall(r'\n  (\w+) : (.+)', struct)
    eqs = [(n, r) for n, r in rows if not n.startswith('nq') and not n.startswith('nr')]
    nns = [(n, r) for n, r in rows if n.startswith('nq') or n.startswith('nr')]
    check(len(nns) == len(S0) + len(S1),
          'one nonnegativity per basis state (%d)' % len(nns))

    def side(names, S, pref):
        return ' + '.join('%s%d' % (pref, r) for r in range(len(S)) if r in names) or '0'

    idx = [(i,) for i in range(N)] + list(combinations(range(N), 2))
    want = [('n0', '%s = 1' % ' + '.join('q%d' % r for r in range(len(S0)))),
            ('n1', '%s = 1' % ' + '.join('r%d' % r for r in range(len(S1))))]
    for T in idx:
        lhs = {r for r in range(len(S0)) if all(S0[r][j] == '1' for j in T)}
        rr = {r for r in range(len(S1)) if all(S1[r][j] == '1' for j in T)}
        want.append(('m%s' % ''.join(str(j + 1) for j in T),
                     '%s = %s' % (side(lhs, S0, 'q'), side(rr, S1, 'r'))))
    got = [(n, ' '.join(r.split())) for n, r in eqs]
    check(got == want, 'the %d equalities are exactly the moment system of these fibers'
          % len(want))
    if got != want:
        for a, b in zip(got, want):
            if a != b:
                print('        got  %s' % (a,))
                print('        want %s' % (b,))
                break
    return ok


if __name__ == '__main__':
    allok = True
    for oid in (12, 6):
        allok = audit(oid) and allok
    print()
    print('AUDIT %s' % ('PASSED' if allok else 'FAILED'))
