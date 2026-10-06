"""Non-vacuity check for the orbit 49 / 51 MomentSystem structures.

If the emitted `MomentSystem` were unsatisfiable, `no_go_of_moments` would be
provable for trivial reasons.  This script parses the Lean structure back out of
the generated source, and exhibits an explicit strictly positive rational point
satisfying every one of the 23 equations, so the structure is a genuine
hypothesis.  It also confirms that the *pinned* point the Lean proof derives is
itself feasible for the linear part -- i.e. the contradiction really comes from
the amplitude relations, not from the polytope.

Run:  python tools/run.py verification/nonvac4951.py
"""
import io
import os
import re

from sympy import Matrix, Rational, symbols, linsolve, zeros

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))

bad = []


def equations(oid):
    src = io.open(os.path.join(ROOT, 'SixQubit', 'Orbit%d.lean' % oid),
                  encoding='utf-8').read()
    blk = src[src.index('structure MomentSystem'):src.index('  nq0 :')]
    rows, rhs = [], []
    for _nm, lhs, rt in re.findall(r'\n  (\w+) : (.*?) = (.*?)$', blk, re.M):
        vec = [Rational(0)] * 20
        for tok in lhs.split(' + '):
            if tok != '0':
                k = int(tok[1:]) + (0 if tok[0] == 'q' else 10)
                vec[k] += 1
        const = Rational(0)
        for tok in rt.split(' + '):
            if tok == '1':
                const += 1
            elif tok != '0':
                k = int(tok[1:]) + (0 if tok[0] == 'q' else 10)
                vec[k] -= 1
        rows.append(vec)
        rhs.append(const)
    return Matrix(rows), Matrix(rhs)


def check(oid, pinned):
    print('=' * 66)
    print('ORBIT %d' % oid)
    A, b = equations(oid)
    print('  parsed %d equations in 20 unknowns, rank %d' % (A.rows, A.rank()))
    xs = symbols('x0:20')
    sol = list(linsolve((A, b), list(xs)))[0]
    free = sorted({s for e in sol for s in e.free_symbols}, key=str)
    print('  free parameters: %s' % free)
    # an interior point: search a small rational grid for the free parameters
    pt, ok = None, False
    for num in range(1, 24):
        cand = [e.subs({s: Rational(num, 144) for s in free}) for e in sol]
        if A * Matrix(cand) == b and all(v > 0 for v in cand):
            pt, ok = cand, True
            break
    if pt is None:
        pt = [e.subs({s: Rational(1, 12) for s in free}) for e in sol]
    print('  interior point q = %s' % [str(v) for v in pt[:10]])
    print('              top r = %s' % [str(v) for v in pt[10:]])
    print('  %-4s the MomentSystem is satisfiable with ALL 20 entries > 0'
          % ('OK' if ok else 'FAIL'))
    if not ok:
        bad.append('orbit %d satisfiability' % oid)
    # the point the Lean proof pins down is itself in the polytope
    pin = Matrix(pinned)
    ok2 = (A * pin == b) and all(v >= 0 for v in pinned)
    print('  %-4s the pinned point %s is feasible for the linear part'
          % ('OK' if ok2 else 'FAIL', [str(v) for v in pinned[:10]]))
    if not ok2:
        bad.append('orbit %d pinned feasibility' % oid)


if __name__ == '__main__':
    R = Rational
    p49 = [R(1, 12)] * 8 + [R(1, 6), R(1, 6)]
    check(49, p49 + p49)
    p51 = [R(1, 12)] * 4 + [R(1, 12), R(1, 12), R(1, 12), R(1, 12),
                            R(1, 6), R(1, 6)]
    check(51, p51 + p51)
    print('=' * 66)
    print('NON-VACUITY CLEAN' if not bad else 'FAILURES: %s' % bad)
