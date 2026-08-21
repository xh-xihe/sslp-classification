"""Regenerate a module's `MomentSystem` against the ordering its headline uses.

The defect this repairs: the moment rows were generated with the top fiber in
LEXICOGRAPHIC order (`fiber(a, q, 1)`), while `no_go_of_moments` passes the top
probabilities as `Complex.normSq (d (SS.complement y_i))`, i.e. in BOTTOM-index
order.  Both compile, but the structure is then not the moment system of the
code, so the kernel-proved headline does not apply to it.

Here the top states are taken as `complement y_i`, in the same order the
headline passes them, and every row -- the six one-bit rows and the six two-bit
rows -- is recomputed from the bit patterns.  The bottom side is unchanged (the
bottom ordering was already y0..y6), which is a useful cross-check: the emitted
q-side must come out byte-identical to what the module already had.

The two-bit rows are renamed `c..` -> `m..` so that `verification/gate.py`,
which keys on the name `m<i><j>`, checks them too; under the old names it only
ever checked the six one-bit rows.

Usage (from the repository root):
    python tools/run.py generators/genmomrows.py            # 34 57 59 64
    python tools/run.py generators/genmomrows.py 34         # one orbit
    python tools/run.py generators/genmomrows.py --check    # print, do not write
"""
import io
import json
import os
import re
import sys
from itertools import combinations

from sympy import Matrix, Rational

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools', 'core'))
from orbit import fiber                                        # noqa: E402

SQ = os.path.join(REPO, 'SixQubit')
MAN = json.loads(io.open(os.path.join(REPO, 'tools', 'manifest.json'),
                         encoding='utf-8').read())
BITS = {'true': 1, 'false': 0}
S = r'\s+'
DEFAULT = ['34', '57', '59', '64']
PAIRS = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2)]

BEGIN = '/-! ## The moment system, solved -/'
END = '/-! ## The no-go -/'


def read_module(oid):
    path = os.path.join(SQ, 'Orbit%s.lean' % oid)
    return path, io.open(path, encoding='utf-8').read()


def parse_av(src):
    m = re.search(r'def' + S + r'av' + S + r':' + S + r'Fin' + S + r'6' + S +
                  r'->' + S + r'ZMod' + S + r'(\d+)' + S + r':=' + S +
                  r'!\[([^\]]*)\]', src)
    return int(m.group(1)), [int(x.strip()) for x in m.group(2).split(',')]


def parse_ys(src):
    ys = {}
    pat = (r'def' + S + r'y(\d+)' + S + r':' + S + r'SS\.BitString' + S + r'6' +
           S + r':=' + S + r'bs' + S + (r'(\w+)' + S) * 5 + r'(\w+)')
    for m in re.finditer(pat, src):
        ys[int(m.group(1))] = ''.join(str(BITS[m.group(i + 2)])
                                      for i in range(6))
    return [ys[i] for i in range(len(ys))]


def complement(s):
    return ''.join('1' if ch == '0' else '0' for ch in s)


def rows_for(S0, S1):
    """(label, bottom index list, top index list) for every moment row."""
    out = []
    for i in range(6):
        out.append(('m%d' % (i + 1),
                    [k for k, x in enumerate(S0) if x[i] == '1'],
                    [k for k, y in enumerate(S1) if y[i] == '1']))
    for (i, j) in PAIRS:
        out.append(('m%d%d' % (i + 1, j + 1),
                    [k for k, x in enumerate(S0) if x[i] == '1' and x[j] == '1'],
                    [k for k, y in enumerate(S1) if y[i] == '1' and y[j] == '1']))
    return out


def solve_system(n0, n1, rows):
    """Exact solution of the 14 equations; returns (values, |det|)."""
    A, b = [], []
    A.append([1] * n0 + [0] * n1)
    b.append(1)
    A.append([0] * n0 + [1] * n1)
    b.append(1)
    for _, lo, hi in rows:
        r = [0] * (n0 + n1)
        for k in lo:
            r[k] += 1
        for k in hi:
            r[n0 + k] -= 1
        A.append(r)
        b.append(0)
    M = Matrix(A)
    if M.shape[0] != M.shape[1]:
        raise SystemExit('expected a square system, got %s' % (M.shape,))
    det = M.det()
    if det == 0:
        raise SystemExit('singular moment matrix - the rows do not force '
                         'the probabilities')
    x = M.solve(Matrix(b))
    vals = [Rational(v) for v in x]
    if any(v <= 0 for v in vals):
        raise SystemExit('a forced probability is not strictly positive: %s'
                         % vals)
    return vals, abs(det)


def frac(v):
    return str(v.p) if v.q == 1 else '%d/%d' % (v.p, v.q)


def sum_of(prefix, idx):
    return ' + '.join('%s%d' % (prefix, k) for k in idx)


def emit(oid, S0, S1, rows, vals, det):
    n0, n1 = len(S0), len(S1)
    qs = ' '.join('q%d' % k for k in range(n0))
    rs = ' '.join('r%d' % k for k in range(n1))
    names = ['n0', 'n1'] + [lab for lab, _, _ in rows]
    L = []
    L.append(BEGIN)
    L.append('')
    L.append('/-- Two normalizations, the six one-bit moment equalities, the five')
    L.append('two-bit equalities for coordinate pairs (1,j), and the pair (2,3).')
    L.append('The integer coefficient matrix is nonsingular -- determinant %d up to'
             % det)
    L.append('the ordering of rows and columns -- so the fourteen probabilities are')
    L.append('forced.')
    L.append('')
    L.append('`q i` is the probability of the bottom string `y i`; `r i` is the')
    L.append('probability of the top string `complement (y i)`, which is exactly the')
    L.append('order `no_go_of_moments` passes them in.  Every row below is computed')
    L.append('against that ordering by `tools/generators/genmomrows.py`. -/')
    L.append('structure MomentSystem (%s %s : Real) : Prop where' % (qs, rs))
    L.append('  n0 : %s = 1' % sum_of('q', range(n0)))
    L.append('  n1 : %s = 1' % sum_of('r', range(n1)))
    for lab, lo, hi in rows:
        L.append('  %s : %s = %s' % (lab, sum_of('q', lo), sum_of('r', hi)))
    L.append('')
    L.append('/-- The fourteen equations determine the fourteen probabilities. -/')
    L.append('theorem MomentSystem.solution {%s %s : Real}' % (qs, rs))
    L.append('    (h : MomentSystem %s %s) :' % (qs.replace('  ', ' '),
                                                 rs.replace('  ', ' ')))
    L.append('    ' + ' ∧ '.join('q%d = %s' % (k, frac(vals[k]))
                                 for k in range(n0)) + ' ∧')
    L.append('    ' + ' ∧ '.join('r%d = %s' % (k, frac(vals[n0 + k]))
                                 for k in range(n1)) + ' := by')
    L.append('  obtain ⟨%s⟩ := h' % ', '.join(names))
    L.append('  refine ⟨%s⟩ <;> linarith'
             % ', '.join(['?_'] * (n0 + n1)))
    L.append('')
    L.append('/-- Every forced probability is strictly positive, so every displayed')
    L.append('string lies in the actual support of any putative code. -/')
    L.append('theorem MomentSystem.pos {%s %s : Real}' % (qs, rs))
    L.append('    (h : MomentSystem %s %s) :' % (qs, rs))
    L.append('    ' + ' ∧ '.join('0 < q%d' % k for k in range(n0)) + ' ∧')
    L.append('    ' + ' ∧ '.join('0 < r%d' % k for k in range(n1)) + ' := by')
    L.append('  obtain ⟨%s, %s⟩ := h.solution'
             % (', '.join('g%d' % k for k in range(n0)),
                ', '.join('h%d' % k for k in range(n1))))
    L.append('  refine ⟨%s⟩ <;> simp_all'
             % ', '.join(['?_'] * (n0 + n1)))
    L.append('')
    return '\n'.join(L) + '\n'


def run(oid, write):
    path, src = read_module(oid)
    ent = MAN[oid]
    q, a = parse_av(src)
    if q != ent['q'] or sorted(a) != sorted(ent['a']):
        raise SystemExit('orbit %s: av does not match the manifest' % oid)
    S0 = parse_ys(src)
    if S0 != fiber(a, q, 0):
        raise SystemExit('orbit %s: y0..yn are not the residue-0 fiber in '
                         'lexicographic order' % oid)
    if len(S0) != ent['n0']:
        raise SystemExit('orbit %s: bottom fiber has %d states, manifest says %d'
                         % (oid, len(S0), ent['n0']))
    S1 = [complement(x) for x in S0]            # the headline's ordering
    if sorted(S1) != fiber(a, q, ent['d']):
        raise SystemExit('orbit %s: complements are not the residue-%d fiber'
                         % (oid, ent['d']))
    if len(S1) != ent['n1']:
        raise SystemExit('orbit %s: top fiber has %d states, manifest says %d'
                         % (oid, len(S1), ent['n1']))
    rows = rows_for(S0, S1)
    vals, det = solve_system(len(S0), len(S1), rows)
    block = emit(oid, S0, S1, rows, vals, det)

    i = src.index(BEGIN)
    j = src.index(END)
    out = src[:i] + block + src[j:]
    if write:
        io.open(path, 'w', encoding='utf-8', newline='\n').write(out)
        print('orbit %s: rewrote %s (det %d)' % (oid, os.path.basename(path), det))
    else:
        print('==== orbit %s (det %d) ====' % (oid, det))
        print(block)
    for lab, lo, hi in rows:
        print('   orbit %-3s %-4s  q%s = r%s' % (oid, lab, list(lo), list(hi)))


if __name__ == '__main__':
    argv = [x for x in sys.argv[1:] if not x.startswith('--')]
    write = '--check' not in sys.argv[1:]
    for oid in (argv or DEFAULT):
        run(oid, write)
