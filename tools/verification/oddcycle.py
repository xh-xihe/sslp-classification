"""Search for odd cancellation cycles.

Write u_x = conj(c_x) and v_y = d_y.  A Pauli equation with exactly two
surviving terms reads

    eps_a u_i v_j + eps_b u_k v_l = 0,   hence   u_i v_j = sigma u_k v_l

with sigma = -eps_a eps_b.  Record the exponent vector w = e_{u_i} + e_{v_j}
- e_{u_k} - e_{v_l} and the sign bit s = 1 when sigma = -1.

If integers a_r satisfy sum a_r w_r = 0 while sum a_r s_r is odd, then
multiplying the relations to the powers a_r gives the same monomial on both
sides but with an overall minus sign, so twice that monomial vanishes.  Every
variable in it has strictly positive probability, hence is nonzero -- a
contradiction.

This is the mechanism the paper calls an odd cancellation cycle, and it is what
the purely linear scan cannot see: the cancellation happens in the exponent
lattice of the rank-one structure P_xy = u_x v_y, not among the products
themselves.
"""
import sys
from itertools import combinations

from sympy import Matrix, Rational, lcm

sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from orbit import fiber
from scan import ORBITS, bits, xor, dot, lp_status, dressings

REMAINING = [25, 26, 27, 29, 31, 32, 33, 35, 37, 38, 54, 56, 58, 61, 62]


def relations(S0, S1, st):
    """Every weight<=2 Pauli whose equation has exactly two surviving terms."""
    n0 = len(S0)
    out, seen = [], set()
    for m in range(1, 64):
        e = bits(m)
        if e.count('1') > 2:
            continue
        for z in dressings(e):
            terms = []
            ok = True
            for j, y in enumerate(S1):
                x = xor(y, e)
                if x not in S0:
                    continue
                i = S0.index(x)
                if st[i][0] == 'zero' or st[n0 + j][0] == 'zero':
                    continue                       # product already zero
                if st[i][0] != 'pos' or st[n0 + j][0] != 'pos':
                    ok = False                     # endpoint not pinned positive
                    break
                terms.append((i, j, (-1) ** dot(z, y)))
            if not ok or len(terms) != 2:
                continue
            (i, j, ea), (k, l, eb) = terms
            sigma = -ea * eb
            key = (i, j, k, l, sigma)
            if key in seen:
                continue
            seen.add(key)
            w = [0] * (n0 + len(S1))
            w[i] += 1; w[n0 + j] += 1; w[k] -= 1; w[n0 + l] -= 1
            out.append((w, 0 if sigma == 1 else 1, (e, z), (i, j, k, l, sigma)))
    return out


def find_cycle(rels, size):
    for combo in combinations(range(len(rels)), size):
        W = Matrix([rels[r][0] for r in combo]).T      # columns are relations
        ns = W.nullspace()
        for v in ns:
            den = 1
            for x in v:
                den = lcm(den, Rational(x).q)
            a = [int(Rational(x) * den) for x in v]
            g = 0
            for x in a:
                g = abs(x) if g == 0 else __import__('math').gcd(g, abs(x))
            if g:
                a = [x // g for x in a]
            if sum(a[t] * rels[combo[t]][1] for t in range(size)) % 2 == 1:
                return combo, a
    return None


print('%-5s %-6s %-9s %-8s %s' % ('轨道', 'delta', '纤维', '两项关系', '奇环'))
print('-' * 62)
hits, misses = [], []
for oid in REMAINING:
    a_vec, q, sizes = ORBITS[oid]
    S0 = fiber(a_vec, q, 0)
    cands = [d for d in range(1, q)
             if sizes is None or (len(S0), len(fiber(a_vec, q, d))) == sizes]
    got = None
    for delta in cands:
        S1 = fiber(a_vec, q, delta)
        if not S1:
            continue
        st = lp_status(S0, S1)
        if st is None:
            continue
        rels = relations(S0, S1, st)
        if len(rels) < 3:
            continue
        for size in (3, 4):
            r = find_cycle(rels, size)
            if r:
                got = (delta, S1, rels, r)
                break
        if got:
            break
        if not got:
            got = (delta, S1, rels, None)
    if got and got[3]:
        delta, S1, rels, (combo, a) = got
        print('%-5d %-6d %-9s %-8d 是  长度 %d, 系数 %s'
              % (oid, delta, '(%d,%d)' % (len(S0), len(S1)), len(rels), len(combo), a))
        hits.append(oid)
    else:
        nr = len(got[2]) if got else 0
        print('%-5d %-6s %-9s %-8d 否' % (oid, got[0] if got else '?', '', nr))
        misses.append(oid)
print('-' * 62)
print('奇环可证: %d / %d' % (len(hits), len(REMAINING)), hits)
print('仍剩余  :', misses)
