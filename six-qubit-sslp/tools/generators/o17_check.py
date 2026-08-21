"""Orbit 17: audit the Lean module against the verified data.

1. every dressing used is admissible for its flip mask (kl.dressings_full);
2. the moment equations in the Lean structure are the 23 exact moment rows;
3. the degree facts and the top anchor mass are linear consequences of them;
4. the incidence / flip / sign tables in the Lean file match the fibers.
"""
import re
from itertools import combinations

from sympy import Matrix, Rational

from orbit import fiber
from kl import dressings_full
from scan import bits, xor, dot

S0 = fiber([1] * 6, 4, 0)
S1 = fiber([1] * 6, 4, 2)
i0 = {s: k for k, s in enumerate(S0)}
i1 = {s: k for k, s in enumerate(S1)}
EDGES = list(combinations(range(6), 2))
src = open('SixQubit/Orbit17.lean', encoding='utf-8').read()


def estr(e):
    return ''.join('1' if i in e else '0' for i in range(6))


def cstr(e):
    return ''.join('0' if i in e else '1' for i in range(6))


# ---- 1. dressings ---------------------------------------------------------
bad = []
for e in EDGES:
    adm = set(dressings_full(estr(e)))
    zs = ['000000', ''.join('1' if k == e[0] else '0' for k in range(6))]
    for z in zs:
        if z not in adm:
            bad.append((e, z))
print('1. every used dressing admissible :', not bad, '' if not bad else bad)
print('   admissible dressings per edge mask :', len(dressings_full(estr(EDGES[0]))))

# ---- 2. moment equations --------------------------------------------------
def ind(s, i):
    return 1 if s[i] == '1' else 0


rows, rhs, lab = [], [], []
rows.append([1] * 16 + [0] * 16); rhs.append(1); lab.append('n0')
rows.append([0] * 16 + [1] * 16); rhs.append(1); lab.append('n1')
for i in range(6):
    rows.append([ind(x, i) for x in S0] + [-ind(y, i) for y in S1]); rhs.append(0)
    lab.append('m%d' % (i + 1))
for (i, j) in combinations(range(6), 2):
    rows.append([ind(x, i) * ind(x, j) for x in S0] + [-ind(y, i) * ind(y, j) for y in S1])
    rhs.append(0); lab.append('m%d%d' % (i + 1, j + 1))

# re-read them out of the Lean source
ok = True
for name, row, r in zip(lab, rows, rhs):
    m = re.search(r'^  %s : (.*)$' % name, src, re.M)
    if not m:
        ok = False
        print('   missing field', name)
        continue
    body = m.group(1)
    lhs_s, rhs_s = body.split(' = ')
    got = [0] * 32
    for t in lhs_s.split(' + '):
        t = t.strip()
        k = int(t[1:])
        got[k if t[0] == 'q' else 16 + k] += 1
    if rhs_s.strip() == '1':
        want = row
    else:
        for t in rhs_s.split(' + '):
            t = t.strip()
            k = int(t[1:])
            got[k if t[0] == 'q' else 16 + k] -= 1
        want = row
    if got != want:
        ok = False
        print('   MISMATCH', name, got, want)
print('2. Lean moment fields = the 23 exact moment rows :', ok)
M = Matrix(rows)
print('   rank :', M.rank(), 'of', M.shape)

# ---- 3. the derived normal form -------------------------------------------
b = Matrix(rhs)


def implied(t, val):
    sol = M.T.solve_least_squares(Matrix(t))
    if any(x != 0 for x in (M.T * sol - Matrix(t))):
        return False
    return (sol.T * b)[0, 0] == val


t = [0] * 32
t[16 + i1['111111']] = 1
res = [implied(t, Rational(1, 4))]
for v in range(6):
    t = [0] * 32
    for e in EDGES:
        if v in e:
            t[i0[cstr(e)]] = 1
    res.append(implied(t, Rational(1, 4)))
print('3. normalForm facts are linear consequences :', all(res), res)

# ---- 4. incidence / flip / sign tables ------------------------------------
prob = []
for e in EDGES:
    nm = 'e%d%d' % e
    inc = [t for t, y in enumerate(S1) if xor(y, estr(e)) in i0]
    m = re.search(r'^theorem inc_%s : .*= \{(.*)\} := by decide$' % nm, src, re.M)
    got = [int(x.strip()[1:]) for x in m.group(1).split(',')]
    if got != inc:
        prob.append(('inc', e, got, inc))
    for n, t in enumerate(inc):
        want = i0[xor(S1[t], estr(e))]
        mm = re.search(r'^theorem flip_%s_%d : SS.bxor z(\d+) %s = y(\d+) := by decide$'
                       % (nm, n, nm), src, re.M)
        if int(mm.group(1)) != t or int(mm.group(2)) != want:
            prob.append(('flip', e, n))
        z = ''.join('1' if k == e[0] else '0' for k in range(6))
        want_sg = 'true' if dot(z, S1[t]) else 'false'
        mm = re.search(r'^theorem sgp_%s_%d : SS.bdot wp%d z(\d+) = (\w+) := by decide$'
                       % (nm, n, e[0]), src, re.M)
        if int(mm.group(1)) != t or mm.group(2) != want_sg:
            prob.append(('sgp', e, n, mm.group(2), want_sg))
print('4. incidence / flip / sign tables match the fibers :', not prob, prob[:5])

# ---- 5. forbidden tactics --------------------------------------------------
for f in ['SixQubit/Orbit17.lean', 'SixQubit/Hafnian.lean']:
    s = open(f, encoding='utf-8').read()
    body = re.sub(r'/-.*?-/', '', s, flags=re.S)
    print('5. %-24s sorry:%s  native_decide:%s  decide calls:%d'
          % (f, 'sorry' in body, 'native_decide' in body, body.count('by decide')))
