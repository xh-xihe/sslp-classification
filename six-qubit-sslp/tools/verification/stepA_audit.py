"""Audit the four silent assumptions behind the orbit-26 Step A contraction.

Everything is recomputed from the raw Walsh data: the only inputs are S0, S1 and
the block labelling.  The KL off-diagonal system splits by X-mask, so for each
mask m the set of IMPLIED linear relations among the products conj(c_x) d_y with
x xor y = m is exactly the ROW SPACE of the sign matrix [ (-1)^{z . y} ] over the
admissible dressings z of m.  Every question below is a membership / intersection
question in that row space.
"""
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from o26 import S0, S1, T0, BOT, TOP, GROUPS
from scan import bits, xor, dot
from kl import dressings_full

comp = lambda u: ''.join('1' if ch == '0' else '0' for ch in u)

# ---------------------------------------------------------------- labelling
# bottom block i  = the pair ('0'+T0[i], '1'+T0[i]) inside S0
# top    block i  = the pair ('0'+comp(T0[i]), '1'+comp(T0[i])) inside S1
BOTLAB, TOPLAB = {}, {}          # fiber index -> (block, first bit)
BOTIDX, TOPIDX = {}, {}          # (block, first bit) -> fiber index
for i, u in enumerate(T0):
    for a in (0, 1):
        k = S0.index(('1' if a else '0') + u)
        BOTLAB[k] = (i, a)
        BOTIDX[(i, a)] = k
        k = S1.index(('1' if a else '0') + comp(u))
        TOPLAB[k] = (i, a)
        TOPIDX[(i, a)] = k
assert [tuple(BOTIDX[(i, a)] for a in (0, 1)) for i in range(8)] == list(map(tuple, BOT))
assert [tuple(TOPIDX[(i, a)] for a in (0, 1)) for i in range(8)] == list(map(tuple, TOP))


def mask_of(bi, a, tj, b):
    """The X-mask carrying the product conj((C_bi)_a) (D_tj)_b."""
    return xor(S0[BOTIDX[(bi, a)]], S1[TOPIDX[(tj, b)]])


# ------------------------------------------------- per-mask Walsh row space
MASKS = [bits(m) for m in range(64) if bits(m).count('1') <= 2]
INC, COL, ROW, RS = {}, {}, {}, {}
for m in MASKS:
    inc = [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
    if not inc:
        continue
    INC[m] = [(BOTLAB[k] + TOPLAB[t]) for k, t in inc]      # (bi,a,tj,b)
    COL[m] = {lab: n for n, lab in enumerate(INC[m])}
    zs = dressings_full(m)
    ROW[m] = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in inc] for z in zs])
    RS[m] = sp.Matrix([list(v) for v in ROW[m].rowspace()])   # basis, r x n


def implied(vec_by_lab):
    """Is  sum lab-coeff * conj(C)_a D_b = 0  a consequence of the KL system?"""
    ms = {mask_of(*lab) for lab in vec_by_lab}
    if len(ms) != 1:
        return None, sorted(ms)
    m = ms.pop()
    v = sp.zeros(1, len(INC[m]))
    for lab, co in vec_by_lab.items():
        v[0, COL[m][lab]] += co
    B = RS[m]
    return B.rank() == B.col_join(v).rank(), m


def relations_supported_on(m, labs):
    """Basis of the implied relations vanishing outside the monomials `labs`."""
    B = RS[m]
    keep = {COL[m][l] for l in labs}
    out_cols = [k for k in range(B.cols) if k not in keep]
    if out_cols:
        lam = B[:, out_cols].T.nullspace()
    else:
        lam = [sp.Matrix([1 if i == j else 0 for i in range(B.rows)])
               for j in range(B.rows)]
    return [sp.Matrix([[sum(l[i] * B[i, k] for i in range(B.rows))
                        for k in range(B.cols)]]) for l in lam]


def show(m, v, pad='      '):
    out = []
    for k in range(v.cols):
        if v[0, k] == 0:
            continue
        bi, a, tj, b = INC[m][k]
        out.append('%+s*cc(C%d_%d)D%d_%d' % (sp.nsimplify(v[0, k]), bi, a, tj, b))
    print(pad + ' '.join(out))


print('=' * 78)
print('T0 =', T0, '  GROUPS =', GROUPS)
print('mask  #inc  rank(rows)  dim(relations)')
for m in sorted(INC, key=lambda s: (s.count('1'), s)):
    print('  %s  %3d   %3d' % (m, len(INC[m]), RS[m].rank()))
