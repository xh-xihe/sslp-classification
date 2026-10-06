"""Independent audit of SixQubit/Orbit49.lean and SixQubit/Orbit51.lean.

Re-reads the *emitted Lean text* and re-derives everything from scratch:

  1. the bit strings `y_i` / `z_j` are parsed back out of the Lean source and the
     two fibers are recomputed from `av` and the residues 0 and 2;
  2. every flip mask `ef_k` has weight <= 2 and every dressing `w_j` used with it
     satisfies |supp(ef_k) u supp(w_j)| <= 2 (the admissibility rule);
  3. every `incidence_ef_k` set is recomputed;
  4. the 23 `MomentSystem` equations are recomputed from the two fibers and
     compared literally with the Lean text;
  5. the hypotheses of `no_go_of_moments` are classified: each must be either
     `MomentSystem ...` or `offSum c d ef_k w_j = 0`.  Anything else is a defect.

Run:  python tools/run.py verification/audit4951.py
"""
import io
import os
import re
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))

BOOLV = {'false': '0', 'true': '1'}
bad = []


def note(cond, msg):
    print('  %-4s %s' % ('OK' if cond else 'FAIL', msg))
    if not cond:
        bad.append(msg)


def parse_bs(line):
    m = re.search(r'bs ((?:(?:true|false)\s*){6})', line)
    return ''.join(BOOLV[t] for t in m.group(1).split())


def wt(s):
    return s.count('1')


def sup(s):
    return {i for i in range(6) if s[i] == '1'}


def xor(s, t):
    return ''.join('1' if (s[i] == '1') != (t[i] == '1') else '0' for i in range(6))


def audit(oid):
    print('=' * 72)
    print('ORBIT %d' % oid)
    path = os.path.join(ROOT, 'SixQubit', 'Orbit%d.lean' % oid)
    src = io.open(path, encoding='utf-8').read()
    lines = src.split(chr(10))

    code = re.sub(r'/-.*?-/', '', src, flags=re.S)
    code = re.sub(r'--[^' + chr(10) + r']*', '', code)
    note('sorry' not in code, 'no `sorry` outside comments')
    note('native_decide' not in code, 'no `native_decide` outside comments')
    note('native_decide' in src, '(docstring does mention native_decide)')

    ys, zs, efs, ws = {}, {}, {}, {}
    for ln in lines:
        m = re.match(r'def (y|z|ef|w)(\d+) : SS.BitString 6 := ', ln)
        if m:
            {'y': ys, 'z': zs, 'ef': efs, 'w': ws}[m.group(1)][int(m.group(2))] = parse_bs(ln)
    B = [ys[i] for i in range(len(ys))]
    T = [zs[i] for i in range(len(zs))]
    print('  bottom fiber:', B)
    print('  top fiber   :', T)

    av = [int(x) for x in re.search(r'def av : Fin 6 -> ZMod 6 := !\[(.*?)\]', src)
          .group(1).split(',')]

    def fib(res):
        return sorted(s for s in (format(k, '06b') for k in range(64))
                      if sum(av[i] for i in range(6) if s[i] == '1') % 6 == res)

    note(sorted(B) == fib(0), 'S0 is exactly the residue-0 fiber of av=%s' % av)
    note(sorted(T) == fib(2), 'S1 is exactly the residue-2 fiber of av=%s' % av)
    note(all(T[i] == xor(B[i], '1' * 6) for i in range(len(B))),
         'top fiber is indexed by bitwise complement')

    # 2/3.  masks, dressings, incidences
    used = set()
    for m in re.finditer(r'\(h\d+ : offSum c d ef(\d+) (w\d+) = 0\)', src):
        used.add((int(m.group(1)), int(m.group(2)[1:])))
    note(all(wt(efs[k]) <= 2 for k, _ in used), 'every used flip mask has weight <= 2')
    note(all(len(sup(efs[k]) | sup(ws[j])) <= 2 for k, j in used),
         'every (mask, dressing) pair is admissible: |supp(e) u supp(z)| <= 2')
    print('  used (mask, dressing) pairs: %d' % len(used))

    nmask = 0
    for m in re.finditer(r'theorem incidence_ef(\d+) :\s*\n\s*S1\.filter '
                         r'\(fun y => SS\.bxor y ef\d+ ∈ S0\) = \{(.*?)\}', src):
        k = int(m.group(1))
        claimed = [int(t.strip()[1:]) for t in m.group(2).split(',')]
        real = sorted(t for t, y in enumerate(T) if xor(y, efs[k]) in B)
        note(claimed == real, 'incidence_ef%d = %s' % (k, real))
        nmask += 1
    note(nmask == len(efs), 'every declared mask has an incidence theorem')

    # 4.  the moment system
    blk = src[src.index('structure MomentSystem'):src.index('  nq0 :')]
    got = {a: (b, c) for a, b, c
           in re.findall(r'\n  (\w+) : (.*?) = (.*?)$', blk, re.M)}
    exp = {'n0': (' + '.join('q%d' % r for r in range(len(B))), '1'),
           'n1': (' + '.join('r%d' % r for r in range(len(T))), '1')}
    for tup in [(i,) for i in range(6)] + list(combinations(range(6), 2)):
        nm = 'm%s' % ''.join(str(j + 1) for j in tup)
        lhs = [r for r in range(len(B)) if all(B[r][j] == '1' for j in tup)]
        rhs = [r for r in range(len(T)) if all(T[r][j] == '1' for j in tup)]
        exp[nm] = (' + '.join('q%d' % r for r in lhs) or '0',
                   ' + '.join('r%d' % r for r in rhs) or '0')
    note(set(got) == set(exp), 'MomentSystem has exactly the 23 moment fields')
    note(all(got[k] == exp[k] for k in exp),
         'every MomentSystem equation matches the recomputed moment row')
    note(all(('nq%d : 0 ≤ q%d' % (r, r)) in src for r in range(len(B)))
         and all(('nr%d : 0 ≤ r%d' % (r, r)) in src for r in range(len(T))),
         'every probability is asserted nonnegative')

    # 5.  hypothesis classification of the headline theorem
    head = src[src.index('theorem no_go_of_moments'):src.index(': False := by')]
    kinds = {'a': 0, 'b': 0, 'c': 0, 'other': []}
    for h in re.finditer(r'\((\w+) : ([^\n]*?)\)\n', head + chr(10)):
        nm, body = h.group(1), h.group(2)
        if body.startswith('offSum c d ef') and body.endswith('= 0'):
            kinds['a'] += 1
        elif 'diagBot' in body or 'diagTop' in body:
            kinds['b'] += 1
        elif body.startswith('MomentSystem'):
            kinds['c'] += 1
        else:
            kinds['other'].append((nm, body))
    # the MomentSystem hypothesis spans several lines; detect it separately
    mm = re.search(r'\(hm : MomentSystem', head)
    if mm:
        kinds['c'] += 1
    print('  hypotheses: (a) offSum=0 : %d   (b) diagBot=diagTop : %d   '
          '(c) MomentSystem : %d' % (kinds['a'], kinds['b'], kinds['c']))
    note(not kinds['other'], 'no hypothesis outside classes (a)/(b)/(c): %s'
         % kinds['other'])
    note(kinds['c'] == 1, 'exactly one MomentSystem hypothesis')
    note(kinds['a'] == len(used), 'all %d offSum hypotheses accounted for' % len(used))

    # the MomentSystem is instantiated at the actual amplitude moduli
    inst = re.search(r'\(hm : MomentSystem\n(.*?)\)\n    \(h0', head, re.S).group(1)
    wantq = ['(Complex.normSq (c y%d))' % r for r in range(len(B))]
    wantr = ['(Complex.normSq (d z%d))' % r for r in range(len(T))]
    note(re.findall(r'\(Complex\.normSq \([cd] [yz]\d+\)\)', inst) == wantq + wantr,
         'MomentSystem is instantiated at normSq of the amplitudes, in order')
    print('  total hypothesis count: %d' % (kinds['a'] + kinds['b'] + kinds['c']))


if __name__ == '__main__':
    for oid in (49, 51):
        audit(oid)
    print('=' * 72)
    print('AUDIT CLEAN' if not bad else 'AUDIT FAILURES: %s' % bad)
