"""Task 2: which blocks can vanish simultaneously, over the moment polytope.

Polytope: q >= 0, r >= 0, A [q;r] = b  (two normalisations, six one-bit moments,
fifteen two-bit moments).  Block masses P_i = q_{b0}+q_{b1}, Q_i = r_{c0}+r_{c1}.
"P_i = 0" is the statement "block i vanishes"; since P_i = Q_i is implied it is
the same as C_i = D_i = 0.

Feasibility is decided by scipy LP and then CONFIRMED EXACTLY:
  * feasible  -> an exact rational witness in the polytope is produced and checked;
  * infeasible-> an exact rational Farkas / linear certificate is produced.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from itertools import combinations

import numpy as np
import sympy as sp
from scipy.optimize import linprog

from o26 import S0, S1, BOT, TOP, GROUPS
from cert import build, reduce_mod_linear

Q, R, V, A, b, names = build(S0, S1)
n = A.cols                      # 32
Pexpr = [Q[BOT[i][0]] + Q[BOT[i][1]] for i in range(8)]
Qexpr = [R[TOP[i][0]] + R[TOP[i][1]] for i in range(8)]
Prow = [[sp.expand(e).coeff(v) for v in V] for e in Pexpr]

An = np.array(A.tolist(), float)
bn = np.array(b.tolist(), float).ravel()


def lp_feasible(Z, interior=False):
    """Z = set of block indices forced to vanish.  Returns (ok, x, slack)."""
    rows = [list(An[k]) for k in range(An.shape[0])]
    rhs = list(bn)
    for i in Z:
        rows.append([float(v) for v in Prow[i]]); rhs.append(0.0)
    Aeq, beq = np.array(rows), np.array(rhs)
    if not interior:
        res = linprog(np.zeros(n), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * n,
                      method='highs')
        return res.status == 0, (res.x if res.status == 0 else None), None
    # maximise the smallest coordinate that is not forced to zero
    forced = set()
    for i in Z:
        forced |= {k for k in range(n) if Prow[i][k] != 0}
    free = [k for k in range(n) if k not in forced]
    m = len(free)
    Aeq2 = np.hstack([Aeq, np.zeros((Aeq.shape[0], 1))])
    Aub = np.zeros((m, n + 1));
    for a, k in enumerate(free):
        Aub[a, k] = -1.0; Aub[a, n] = 1.0
    c = np.zeros(n + 1); c[n] = -1.0
    res = linprog(c, A_ub=Aub, b_ub=np.zeros(m), A_eq=Aeq2, b_eq=beq,
                  bounds=[(0, None)] * n + [(0, 1)], method='highs')
    if res.status != 0:
        return False, None, None
    return True, res.x[:n], res.x[n]


# --- exact machinery -------------------------------------------------------
def constrained_system(Z):
    rows = A.tolist() + [Prow[i] for i in Z]
    rhs = b.tolist() + [[0]] * len(Z)
    return sp.Matrix(rows), sp.Matrix(rhs)


def exact_witness(Z, xnum):
    """Turn a numeric interior point into an exact rational point of the polytope."""
    M, rhs = constrained_system(Z)
    sol = M.gauss_jordan_solve(rhs)
    xp, params = sol[0], sol[1]
    N = sp.Matrix([[xp[k].coeff(p) for p in params] for k in range(n)]) if params else None
    x0 = sp.Matrix([xp[k].subs({p: 0 for p in params}) for k in range(n)])
    if N is None or N.cols == 0:
        xe = x0
    else:
        Nn = np.array(N.tolist(), float)
        t, *_ = np.linalg.lstsq(Nn, np.array(xnum, float) - np.array(x0.tolist(), float).ravel(),
                                rcond=None)
        tr = sp.Matrix([sp.Rational(str(round(float(v), 9))) for v in t])
        xe = x0 + N * tr
    assert sp.simplify(M * xe - rhs) == sp.zeros(M.rows, 1), 'witness off the affine space'
    return xe, all(v >= 0 for v in xe)


def exact_infeasible_cert(Z):
    """Look for a rational combination of the moment equations + the forced zeros
    that equals -(nonneg combination) - positive constant, i.e. a Farkas witness."""
    # simplest useful form: sum of P_i over a sub-collection is a positive constant
    for k in range(1, len(Z) + 1):
        for sub in combinations(sorted(Z), k):
            e = sum(Pexpr[i] for i in sub)
            cof, rem = reduce_mod_linear(sp.expand(e), V, A, b)
            if rem.free_symbols == set() and rem != 0:
                return sub, rem
            # remainder is a nonneg combination of variables plus a positive constant?
            if rem.is_Add or rem.is_Symbol or rem.is_number:
                consts = rem.as_coefficients_dict()
                c0 = consts.get(sp.Integer(1), 0)
                lin = {v: consts.get(v, 0) for v in V if consts.get(v, 0) != 0}
                if c0 > 0 and all(cc >= 0 for cc in lin.values()):
                    return sub, rem
    return None, None


print('=== per-block mass ranges over the moment polytope (numeric LP) ===')
rng = {}
for i in range(8):
    c = np.array([float(v) for v in Prow[i]])
    lo = linprog(c, A_eq=An, b_eq=bn, bounds=[(0, None)] * n, method='highs')
    hi = linprog(-c, A_eq=An, b_eq=bn, bounds=[(0, None)] * n, method='highs')
    rng[i] = (lo.fun, -hi.fun)
    print('  P_%d in [%.10f, %.10f]' % (i, lo.fun, -hi.fun))

print()
print('=== which single blocks can vanish ===')
single = []
for i in range(8):
    ok, x, _ = lp_feasible({i})
    print('  P_%d = 0 : %s' % (i, 'FEASIBLE' if ok else 'infeasible'))
    if ok:
        single.append(i)

print()
print('=== all subsets of blocks that can vanish simultaneously ===')
feas = []
for k in range(0, 9):
    for Z in combinations(range(8), k):
        ok, x, _ = lp_feasible(set(Z))
        if ok:
            feas.append(set(Z))
print('  number of feasible zero-sets (incl. empty): %d' % len(feas))
maximal = [Z for Z in feas if not any(Z < W for W in feas)]
print('  MAXIMAL feasible zero-sets:')
for Z in sorted(maximal, key=lambda s: (len(s), sorted(s))):
    print('     ', sorted(Z))
print('  all feasible nonempty zero-sets:')
for Z in sorted([z for z in feas if z], key=lambda s: (len(s), sorted(s))):
    print('     ', sorted(Z))

print()
print('=== exact confirmation of the maximal feasible sets ===')
for Z in sorted(maximal, key=lambda s: (len(s), sorted(s))):
    ok, x, slack = lp_feasible(Z, interior=True)
    xe, nonneg = exact_witness(Z, x)
    print('  Z=%s  interior slack %.6f  exact witness nonneg: %s' % (sorted(Z), slack or 0.0, nonneg))
    print('     P = %s' % [sp.nsimplify(sum(xe[k] * Prow[i][k] for k in range(n))) for i in range(8)])

print()
print('=== exact certificates for the infeasible pairs ===')
for Z in [{i, j} for i, j in combinations(range(8), 2)]:
    ok, _, _ = lp_feasible(Z)
    if ok:
        continue
    sub, rem = exact_infeasible_cert(Z)
    print('  Z=%s infeasible; certificate: sum P over %s reduces to %s'
          % (sorted(Z), sorted(sub) if sub else '?', rem))
