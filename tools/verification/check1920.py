"""Independent audit of SixQubit/Orbit19.lean and SixQubit/Orbit20.lean.

Nothing here trusts the generators: the two Lean sources are parsed back and
every datum in them is recomputed from (q, a, delta).  Checked, per module:

  1. the `y_i` / `z_i` definitions are exactly the two residue fibers, in order;
  2. `av` is the paper's angle vector and the two `_eq_fiber` theorems target
     residues 0 and delta;
  3. every hypothesis of the headline theorem is either `MomentSystem ...` or
     `offSum c d ef? w? = 0` -- nothing else -- and every (e, z) that occurs is
     an admissible weight-<=2 Pauli, i.e. |supp(e) u supp(z)| <= 2;
  4. the `MomentSystem` structure is exactly the 2 normalizations + 21 moment
     equalities + 32 nonnegativities of the true fibers;
  5. every `ex` expansion body is the true Walsh sum
     sum_y (-1)^{z.y} conj(c_{y xor e}) d_y over the true incidence set.
"""
import io
import os
import re
from itertools import combinations

N = 6
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))


def fiber(a, q, res):
    out = []
    for k in range(1 << N):
        s = format(k, '06b')
        if sum(a[i] for i in range(N) if s[i] == '1') % q == res:
            out.append(s)
    return out


def xor(s, t):
    return ''.join('1' if (s[i] == '1') != (t[i] == '1') else '0' for i in range(N))


def dot(z, x):
    return sum(1 for i in range(N) if z[i] == '1' and x[i] == '1') % 2


def supp(s):
    return {i for i in range(N) if s[i] == '1'}


def parse_bs(line):
    m = re.search(r':= bs ((?:(?:true|false)\s*){6})', line)
    assert m, line
    return ''.join('1' if t == 'true' else '0' for t in m.group(1).split())


def audit(oid, q, a, delta):
    path = os.path.join(ROOT, 'SixQubit', 'Orbit%d.lean' % oid)
    src = io.open(path, encoding='utf-8').read()
    lines = src.split(chr(10))
    S0, S1 = fiber(a, q, 0), fiber(a, q, delta)
    ok = []

    # (1) fibers
    ys = {}
    zs = {}
    ws = {}
    efs = {}
    for ln in lines:
        m = re.match(r'def (y|z|w)(\d+) : SS\.BitString 6', ln)
        if m:
            (ys if m.group(1) == 'y' else zs if m.group(1) == 'z' else ws)[
                int(m.group(2))] = parse_bs(ln)
        m = re.match(r'def (ef[A-Z]) : SS\.BitString 6', ln)
        if m:
            efs[m.group(1)] = parse_bs(ln)
    assert [ys[i] for i in range(len(ys))] == S0, 'bottom fiber mismatch'
    assert [zs[i] for i in range(len(zs))] == S1, 'top fiber mismatch'
    ok.append('fibers: %d bottom + %d top strings match fiber(a,q,.) exactly'
              % (len(S0), len(S1)))

    # (2) angle vector and residues
    av = re.search(r'def av : Fin 6 -> ZMod (\d+) := !\[([^\]]*)\]', src)
    assert av and int(av.group(1)) == q
    assert [int(t) for t in av.group(2).split(',')] == a, 'angle vector mismatch'
    assert 'fun x => SS.weight av x = 0) = S0' in src
    assert 'fun x => SS.weight av x = %d) = S1' % delta in src
    ok.append('av = %s over ZMod %d; fibers certified at residues 0 and %d by decide'
              % (a, q, delta))

    # (3) headline hypotheses
    head = src[src.index('theorem no_go_of_moments'):]
    head = head[:head.index(': False := by')]
    hyps = re.findall(r'\(([A-Za-z_0-9]+) :', head)
    off = re.findall(r'\(h\d+ : offSum c d (ef[A-Z]) (w\d+) = 0\)', head)
    nmom = head.count('(hm : MomentSystem')
    assert nmom == 1
    assert head.startswith('theorem no_go_of_moments (c d : SS.BitString 6 -> ' + chr(0x2102) + ')')
    assert len(hyps) == len(off) + nmom, (len(hyps), len(off))
    for tag, wn in off:
        e, z = efs[tag], ws[int(wn[1:])]
        assert len(supp(e) | supp(z)) <= 2, 'INADMISSIBLE dressing %s / %s' % (e, z)
    ok.append('headline: 1 MomentSystem + %d offSum rows, nothing else; '
              'every (e,z) admissible (|supp(e) u supp(z)| <= 2)' % len(off))

    # (4) the moment structure
    body = src[src.index('structure MomentSystem'):]
    body = body[:body.index(chr(10) + chr(10), body.index('nr'))]
    want = []
    want.append('n0 : %s = 1' % ' + '.join('q%d' % r for r in range(len(S0))))
    want.append('n1 : %s = 1' % ' + '.join('r%d' % r for r in range(len(S1))))
    for T in [(i,) for i in range(6)] + list(combinations(range(6), 2)):
        lhs = [r for r in range(len(S0)) if all(S0[r][j] == '1' for j in T)]
        rhs = [r for r in range(len(S1)) if all(S1[r][j] == '1' for j in T)]
        want.append('m%s : %s = %s' % (''.join(str(j + 1) for j in T),
                                       ' + '.join('q%d' % r for r in lhs) or '0',
                                       ' + '.join('r%d' % r for r in rhs) or '0'))
    for r in range(len(S0)):
        want.append('nq%d : 0 <= q%d' % (r, r))
    for r in range(len(S1)):
        want.append('nr%d : 0 <= r%d' % (r, r))
    got = [ln.strip().replace(chr(0x2264), '<=') for ln in body.split(chr(10))
           if re.match(r'\s+(n0|n1|m\d+|nq\d+|nr\d+) :', ln)]
    assert got == want, [g for g, w in zip(got, want) if g != w][:3]
    ok.append('MomentSystem: %d equalities + %d nonnegativities, all matching the '
              'true weight-<=2 pure-Z rows' % (23, len(S0) + len(S1)))

    # (5) the Walsh expansions
    nex = 0
    for m in re.finditer(r'theorem ex([A-Z])_(w\d+) \(c d : SS\.BitString 6 -> ℂ\) :'
                         + chr(10) + r'    offSum c d (ef[A-Z]) (w\d+) ='
                         + chr(10) + r'      (.*?) := by', src, re.S):
        tag, wn, tag2, wn2, expr = m.groups()
        assert 'ef' + tag == tag2 and wn == wn2
        e, z = efs[tag2], ws[int(wn[1:])]
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        want = ' '.join('%s star (c y%d) * d z%d' % ('-' if dot(z, S1[t]) else '+', i, t)
                        for i, t in inc).lstrip('+ ')
        assert ' '.join(expr.split()) == want, (tag, wn)
        nex += 1
    ok.append('%d Walsh expansions match sum_y (-1)^{z.y} conj(c_{y xor e}) d_y' % nex)

    print('=== Orbit %d : q=%d a=%s delta=%d ===' % (oid, q, a, delta))
    for line in ok:
        print('  OK  ' + line)
    for bad in ('sorry', 'native_decide', 'admit'):
        hits = [i + 1 for i, ln in enumerate(lines)
                if bad in ln and not ln.lstrip().startswith(('--', '/-', '`'))
                and '`' + bad + '`' not in ln]
        print('  OK  no %s in tactic position (%d lines flagged)' % (bad, len(hits)))
        assert not hits, hits


if __name__ == '__main__':
    audit(19, 4, [1, 1, 1, 1, 2, 2], 2)
    audit(20, 4, [1, 1, 1, 2, 2, 2], 2)
    print('ALL CHECKS PASSED')
