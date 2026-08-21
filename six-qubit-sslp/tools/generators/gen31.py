"""Transcription layer for orbit 31."""
import io
import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
import sympy as sp

from o31 import S0, S1, POS, NAME
from scan import bits, xor, dot
from kl import dressings_full
from cert import build, reduce_mod_linear

NL = chr(10)
AVEC, QQ, DELTA = [1, 1, 1, 2, 2, 2], 4, 1
n0, n1 = len(S0), len(S1)
Q, R, V, Am, bv, enames = build(S0, S1)
fields = list(enames) + ['nq%d' % k for k in range(n0)] + ['nr%d' % k for k in range(n1)]
comp = lambda s: ''.join('1' if c == '0' else '0' for c in s)
HAT = [S1.index(comp(S0[v])) for v in range(16)]
ROW = {v: POS[v][0] for v in range(16)}
COL = {v: POS[v][1] for v in range(16)}
CELL = {}
for v in range(16):
    CELL[(ROW[v], COL[v])] = v
blit = lambda s: ' '.join('true ' if c == '1' else 'false' for c in s)

L = []
W = L.append
W('import Mathlib')
W('')
W('import SS.FullKL')
W('import SixQubit.Common')
W('import SixQubit.Table31')
W('')
W('/-!')
W('# Six-qubit no-go for moment orbit 31')
W('')
W('Orbit 31 of `six_qubit_sslp_v7.tex`: q = 4, angle vector a = (1, 1, 1, 2, 2, 2),')
W('residues 0 and 1, fibers of size sixteen each and complementary.')
W('')
W('The last three angles are all `2`, so both fibers are stabilised by the Klein')
W('four-group on those qubits and split into four cosets of four.  The sixteen')
W('positions form a `4 x 4` table; `SixQubit.Table31` carries the algebra.')
W('')
W('Everything computational is decided by the Lean kernel; `native_decide` is')
W('not used.')
W('-/')
W('')
W('namespace SixQubit.Orbit31')
W('')
W('open scoped BigOperators')
W('open scoped ComplexConjugate')
W('')
W('noncomputable section')
W('')
W('def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0, b1, b2, b3, b4, b5]')
W('')
for k, s in enumerate(S0):
    W('def y%d : SS.BitString 6 := bs %s  -- %s = %s' % (k, blit(s), s, NAME[k]))
W('')
for k, s in enumerate(S1):
    W('def z%d : SS.BitString 6 := bs %s  -- %s' % (k, blit(s), s))
W('')
W('def S0 : Finset (SS.BitString 6) := {%s}' % ', '.join('y%d' % k for k in range(n0)))
W('def S1 : Finset (SS.BitString 6) := {%s}' % ', '.join('z%d' % k for k in range(n1)))
W('')
W('def av : Fin 6 -> ZMod %d := ![%s]' % (QQ, ', '.join(map(str, AVEC))))
W('')
W('/-- Each support is exactly its residue fiber, decided over all 64 strings. -/')
W('theorem S0_eq_fiber :')
W('    (Finset.univ : Finset (SS.BitString 6)).filter')
W('      (fun x => SS.weight av x = 0) = S0 := by')
W('  decide')
W('')
W('theorem S1_eq_fiber :')
W('    (Finset.univ : Finset (SS.BitString 6)).filter')
W('      (fun x => SS.weight av x = %d) = S1 := by' % DELTA)
W('  decide')
W('')
W('/-- The complement map pairs the two fibers. -/')
for v in range(16):
    W('theorem hat%d : SS.bxor y%d (SS.ones 6) = z%d := by decide' % (v, v, HAT[v]))
W('')
qs = ' '.join('q%d' % k for k in range(n0))
rs = ' '.join('r%d' % k for k in range(n1))
W('/-! ## The moment system -/')
W('')
W('structure MomentSystem (%s %s : Real) : Prop where' % (qs, rs))
for row in range(Am.rows):
    if enames[row] in ('n0', 'n1'):
        trm = ' + '.join(('q%d' % k) if k < n0 else ('r%d' % (k - n0))
                         for k in range(n0 + n1) if Am[row, k] != 0)
        W('  %s : %s = 1' % (enames[row], trm))
    else:
        lhs = ' + '.join('q%d' % k for k in range(n0) if Am[row, k] > 0) or '0'
        rhs = ' + '.join('r%d' % (k - n0) for k in range(n0, n0 + n1) if Am[row, k] < 0) or '0'
        W('  %s : %s = %s' % (enames[row], lhs, rhs))
W('')
for k in range(n0):
    W('  nq%d : 0 ≤ q%d' % (k, k))
for k in range(n1):
    W('  nr%d : 0 ≤ r%d' % (k, k))
W('')


def emit(name, expr, doc):
    cof, rem = reduce_mod_linear(expr, V, Am, bv)
    assert sp.simplify(rem) == 0, (name, rem)
    W('/-- %s -/' % doc)
    W('theorem %s {%s %s : Real} (h : MomentSystem %s %s) :' % (name, qs, rs, qs, rs))
    W('    %s = 0 := by' % sp.printing.sstr(expr).replace('**', '^'))
    W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
    W('  linear_combination ' + ' + '.join(
        '(%s) * %s' % (sp.printing.sstr(cof[row]).replace('**', '^'), enames[row])
        for row in range(Am.rows) if cof[row] != 0))
    W('')


for v in range(16):
    emit('eq%d' % v, R[HAT[v]] - Q[v],
         'The top probability at the complement of %s equals the bottom one.' % NAME[v])
for i in range(1, 4):
    emit('row%d' % i, sum(Q[CELL[(i, e)]] for e in range(4)) - sp.Rational(1, 4),
         'Row B%d carries a quarter.' % i)
for e in range(4):
    emit('col%d' % e, Q[CELL[(0, e)]] - sum(Q[CELL[(i, e)]] for i in range(1, 4))
         + sp.Rational(1, 8),
         'Column %d: alpha equals the B-column total minus 1/8.' % e)
io.open('gen31_head.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('head + moment system: %d lines' % len(L))

# ------------------------------------------------------------ family one
L = []
W = L.append
M1 = ['100000', '010000', '001000']
INC = {m: [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
       for m in M1}


def solve_row(m, tgt, zs):
    M = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in INC[m]] for z in zs])
    sol = M.T.gauss_jordan_solve(sp.Matrix(tgt))[0]
    mu = sol.subs({p: 0 for p in sol.free_symbols})
    return [(zs[u], sp.Rational(mu[u])) for u in range(len(zs)) if mu[u] != 0]


USE = {}
COMBO = {}
for m in M1:
    tgt = [0 if ROW[i] == 0 else 1 for i, t in INC[m]]
    COMBO[m] = solve_row(m, tgt, dressings_full(m))
    USE[m] = sorted({z for z, _ in COMBO[m]})
zall = sorted({z for v in USE.values() for z in v})
zname = {z: 'w%d' % k for k, z in enumerate(zall)}
mid = {m: k for k, m in enumerate(M1)}
W('/-! ## Family one: the column relation -/')
W('')
for m in M1:
    W('def ef%d : SS.BitString 6 := bs %s  -- mask %s' % (mid[m], blit(m), m))
for z in zall:
    W('def %s : SS.BitString 6 := bs %s  -- dressing %s' % (zname[z], blit(z), z))
W('')
W('def offSum (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S0),')
W('      SixQubit.signMul (SS.bdot z y) (star (c (SS.bxor y e)) * d y)')
W('')
for m in M1:
    nn, ii = mid[m], INC[m]
    W('theorem incidence%d :' % nn)
    W('    S1.filter (fun y => SS.bxor y ef%d ∈ S0) = {%s} := by decide'
      % (nn, ', '.join('z%d' % t for _, t in ii)))
    for i, t in ii:
        W('theorem fl%d_%d : SS.bxor z%d ef%d = y%d := by decide' % (nn, t, t, nn, i))
    for z in USE[m]:
        for i, t in ii:
            W('theorem sg%d_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (nn, zname[z], t, zname[z], t, 'true' if dot(z, S1[t]) else 'false'))
W('')
for m in M1:
    nn, ii = mid[m], INC[m]
    for z in USE[m]:
        body = ' '.join('%s star (c y%d) * d z%d' % ('-' if dot(z, S1[t]) else '+', i, t)
                        for i, t in ii).lstrip('+ ')
        W('theorem ex%d_%s (c d : SS.BitString 6 -> ℂ) :' % (nn, zname[z]))
        W('    offSum c d ef%d %s = %s := by' % (nn, zname[z], body))
        W('  unfold offSum')
        W('  rw [incidence%d]' % nn)
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(ii) - 1))
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('fl%d_%d' % (nn, t) for _, t in ii) + ']')
        lem = ['sg%d_%s_%d' % (nn, zname[z], t) for _, t in ii]
        if any(dot(z, S1[t]) for _, t in ii):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S1[t]) for _, t in ii):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
for m in M1:
    nn, ii = mid[m], INC[m]
    row = ROW[[i for i, t in ii if ROW[i] != 0][0]]
    terms = [(i, t) for i, t in ii if ROW[i] != 0]
    body = ' + '.join('star (c y%d) * d z%d' % (i, t) for i, t in terms)
    W('/-- Family one at row B%d: the four `B`-to-`A` incidences sum to zero. -/' % row)
    W('theorem fam1_%d (c d : SS.BitString 6 -> ℂ)' % row)
    for u, (z, _) in enumerate(COMBO[m]):
        W('    (h%d : offSum c d ef%d %s = 0)' % (u, nn, zname[z]))
    W('    : %s = 0 := by' % body)
    for u, (z, _) in enumerate(COMBO[m]):
        W('  rw [ex%d_%s] at h%d' % (nn, zname[z], u))
    W('  linear_combination ' + ' + '.join(
        '(%s : ℂ) * h%d' % (co, u) for u, (z, co) in enumerate(COMBO[m])))
    W('')
io.open('gen31_fam1.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('family one: %d lines' % len(L))

# ------------------------------------------------------------ family two
L2 = []
W = L2.append
M2 = [bits(m) for m in range(64) if bits(m).count('1') == 2
      and [(S0.index(xor(y, bits(m))), t) for t, y in enumerate(S1)
           if xor(y, bits(m)) in S0]]
INC2 = {m: [(S0.index(xor(y, m)), t) for t, y in enumerate(S1) if xor(y, m) in S0]
        for m in M2}
INV = {HAT[v]: v for v in range(16)}


def colpairs(m):
    out = {}
    for i, t in INC2[m]:
        j = INV[t]
        key = tuple(sorted((COL[i], COL[j])))
        out.setdefault(key, []).append((i, t))
    return out


def solve2(m, tgt, zs):
    M = sp.Matrix([[(-1) ** dot(z, S1[t]) for _, t in INC2[m]] for z in zs])
    try:
        sol = M.T.gauss_jordan_solve(sp.Matrix(tgt))[0]
    except ValueError:
        return None
    mu = sol.subs({p: 0 for p in sol.free_symbols})
    return [(zs[u], sp.Rational(mu[u])) for u in range(len(zs)) if mu[u] != 0]


USE2, COMBO2, ok = {}, {}, True
for m in M2:
    for key, grp in colpairs(m).items():
        tgt = [1 if (i, t) in grp else 0 for i, t in INC2[m]]
        r = solve2(m, tgt, dressings_full(m))
        if r is None:
            ok = False
            print('  mask %s pair %s NOT IN SPAN' % (m, key))
            continue
        COMBO2[(m, key)] = (grp, r)
        USE2.setdefault(m, set()).update(z for z, _ in r)
print('all family-two column-pair sums available:', ok)
zall2 = sorted({z for v in USE2.values() for z in v})
mid2 = {m: 3 + k for k, m in enumerate(M2)}
zn2 = dict(zname)
for z in zall2:
    if z not in zn2:
        zn2[z] = 'w%d' % (len(zn2))
W('/-! ## Family two: the vanishing permanents -/')
W('')
for m in M2:
    W('def ef%d : SS.BitString 6 := bs %s  -- mask %s' % (mid2[m], blit(m), m))
for z in zall2:
    if z not in zname:
        W('def %s : SS.BitString 6 := bs %s  -- dressing %s' % (zn2[z], blit(z), z))
W('')
for m in M2:
    nn, ii = mid2[m], INC2[m]
    W('theorem incidence%d :' % nn)
    W('    S1.filter (fun y => SS.bxor y ef%d ∈ S0) = {%s} := by decide'
      % (nn, ', '.join('z%d' % t for _, t in ii)))
    for i, t in ii:
        W('theorem fl%d_%d : SS.bxor z%d ef%d = y%d := by decide' % (nn, t, t, nn, i))
    for z in sorted(USE2[m]):
        for i, t in ii:
            W('theorem sg%d_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (nn, zn2[z], t, zn2[z], t, 'true' if dot(z, S1[t]) else 'false'))
W('')
for m in M2:
    nn, ii = mid2[m], INC2[m]
    for z in sorted(USE2[m]):
        body = ' '.join('%s star (c y%d) * d z%d' % ('-' if dot(z, S1[t]) else '+', i, t)
                        for i, t in ii).lstrip('+ ')
        W('theorem ex%d_%s (c d : SS.BitString 6 -> ℂ) :' % (nn, zn2[z]))
        W('    offSum c d ef%d %s = %s := by' % (nn, zn2[z], body))
        W('  unfold offSum')
        W('  rw [incidence%d]' % nn)
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * (len(ii) - 1))
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('fl%d_%d' % (nn, t) for _, t in ii) + ']')
        lem = ['sg%d_%s_%d' % (nn, zn2[z], t) for _, t in ii]
        if any(dot(z, S1[t]) for _, t in ii):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S1[t]) for _, t in ii):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
n = 0
for (m, key), (grp, cmb) in sorted(COMBO2.items(), key=lambda kv: (mid2[kv[0][0]], kv[0][1])):
    nn = mid2[m]
    W('/-- Family two, mask %s, columns %s. -/' % (m, str(key)))
    W('theorem fam2_%d (c d : SS.BitString 6 -> ℂ)' % n)
    for u, (z, _) in enumerate(cmb):
        W('    (h%d : offSum c d ef%d %s = 0)' % (u, nn, zn2[z]))
    W('    : %s = 0 := by' % ' + '.join('star (c y%d) * d z%d' % (i, t) for i, t in grp))
    for u, (z, _) in enumerate(cmb):
        W('  rw [ex%d_%s] at h%d' % (nn, zn2[z], u))
    W('  linear_combination ' + ' + '.join(
        '(%s : ℂ) * h%d' % (co, u) for u, (z, co) in enumerate(cmb)))
    W('')
    n += 1
io.open('gen31_fam2.txt', 'w', encoding='utf-8').write(NL.join(L2) + NL)
print('family two: %d lines, %d relations' % (len(L2), n))

# ---------------------------------------------------------- family three
L3 = []
W = L3.append
KLEIN = ['000011', '000101', '000110']
DB = {m: [(S0.index(xor(x, m)), i) for i, x in enumerate(S0) if xor(x, m) in S0]
      for m in KLEIN}
DT = {m: [(S1.index(xor(y, m)), j) for j, y in enumerate(S1) if xor(y, m) in S1]
      for m in KLEIN}
mid3 = {m: 12 + k for k, m in enumerate(KLEIN)}
zn3 = dict(zn2)
zall3 = sorted({z for m in KLEIN for z in dressings_full(m)})
for z in zall3:
    if z not in zn3:
        zn3[z] = 'w%d' % len(zn3)
W('/-! ## Family three: the Klein-mask diagonal conditions -/')
W('')
W('/-- `<0_L| X^e Z^z |0_L>` with the global prefactor omitted. -/')
W('def diagBot (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ x ∈ S0.filter (fun x => SS.bxor x e ∈ S0),')
W('      SixQubit.signMul (SS.bdot z x) (star (c (SS.bxor x e)) * c x)')
W('')
W('/-- `<1_L| X^e Z^z |1_L>`. -/')
W('def diagTop (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) : ℂ :=')
W('  ∑ y ∈ S1.filter (fun y => SS.bxor y e ∈ S1),')
W('      SixQubit.signMul (SS.bdot z y) (star (d (SS.bxor y e)) * d y)')
W('')
for m in KLEIN:
    W('def ef%d : SS.BitString 6 := bs %s  -- Klein mask %s' % (mid3[m], blit(m), m))
for z in zall3:
    if z not in zn2:
        W('def %s : SS.BitString 6 := bs %s  -- dressing %s' % (zn3[z], blit(z), z))
W('')
for m in KLEIN:
    nn = mid3[m]
    W('theorem diagB%d :' % nn)
    W('    S0.filter (fun x => SS.bxor x ef%d ∈ S0) = {%s} := by decide'
      % (nn, ', '.join('y%d' % i for i in range(16))))
    W('theorem diagT%d :' % nn)
    W('    S1.filter (fun y => SS.bxor y ef%d ∈ S1) = {%s} := by decide'
      % (nn, ', '.join('z%d' % j for j in range(16))))
    for i, x in enumerate(S0):
        W('theorem dfb%d_%d : SS.bxor y%d ef%d = y%d := by decide'
          % (nn, i, i, nn, S0.index(xor(x, m))))
    for j, y in enumerate(S1):
        W('theorem dft%d_%d : SS.bxor z%d ef%d = z%d := by decide'
          % (nn, j, j, nn, S1.index(xor(y, m))))
    for z in dressings_full(m):
        for i, x in enumerate(S0):
            W('theorem dsb%d_%s_%d : SS.bdot %s y%d = %s := by decide'
              % (nn, zn3[z], i, zn3[z], i, 'true' if dot(z, x) else 'false'))
        for j, y in enumerate(S1):
            W('theorem dst%d_%s_%d : SS.bdot %s z%d = %s := by decide'
              % (nn, zn3[z], j, zn3[z], j, 'true' if dot(z, y) else 'false'))
W('')
for m in KLEIN:
    nn = mid3[m]
    for z in dressings_full(m):
        nm = zn3[z]
        body = ' '.join('%s star (c y%d) * c y%d'
                        % ('-' if dot(z, S0[i]) else '+', S0.index(xor(S0[i], m)), i)
                        for i in range(16)).lstrip('+ ')
        W('theorem dbot%d_%s (c : SS.BitString 6 -> ℂ) :' % (nn, nm))
        W('    diagBot c ef%d %s = %s := by' % (nn, nm, body))
        W('  unfold diagBot')
        W('  rw [diagB%d]' % nn)
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * 15)
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('dfb%d_%d' % (nn, i) for i in range(16)) + ']')
        lem = ['dsb%d_%s_%d' % (nn, nm, i) for i in range(16)]
        if any(dot(z, S0[i]) for i in range(16)):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S0[i]) for i in range(16)):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
        body = ' '.join('%s star (d z%d) * d z%d'
                        % ('-' if dot(z, S1[j]) else '+', S1.index(xor(S1[j], m)), j)
                        for j in range(16)).lstrip('+ ')
        W('theorem dtop%d_%s (d : SS.BitString 6 -> ℂ) :' % (nn, nm))
        W('    diagTop d ef%d %s = %s := by' % (nn, nm, body))
        W('  unfold diagTop')
        W('  rw [diagT%d]' % nn)
        W('  rw [' + ', '.join(['Finset.sum_insert (by decide)'] * 15)
          + ', Finset.sum_singleton]')
        W('  rw [' + ', '.join('dft%d_%d' % (nn, j) for j in range(16)) + ']')
        lem = ['dst%d_%s_%d' % (nn, nm, j) for j in range(16)]
        if any(dot(z, S1[j]) for j in range(16)):
            lem.append('SixQubit.signMul_true')
        if any(not dot(z, S1[j]) for j in range(16)):
            lem.append('SixQubit.signMul_false')
        W('  simp only [' + ', '.join(lem) + ']')
        W('  try ring')
        W('')
io.open('gen31_fam3.txt', 'w', encoding='utf-8').write(NL.join(L3) + NL)
print('family three: %d lines' % len(L3))
