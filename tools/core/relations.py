"""Trustworthy extraction of the two-term relations an orbit actually has.

Three times now I have mis-read the collapse step: seeing that a mask's four
incidences fall into two reciprocal pairs, I assumed the equation collapses to a
relation BETWEEN the pairs.  It does not, in general.  A reciprocal pair
{(x,y-hat), (y,x-hat)} carries the phase-ratio link, and whether the four-term
equation then reduces to a cross-pair relation depends on the SIGNS: writing
P(y,x-hat) = sigma_x sigma_y P(x,y-hat), the four-term sum becomes
(1 + sigma_x sigma_y) P(x,y-hat) + (1 + sigma_z sigma_w) P(z,w-hat), which is a
genuine cross relation only when both sign products are +1, and is vacuous when
either is -1.

So this module never guesses.  It computes, per mask:

  direct  -- every two-term relation genuinely in the row space of the mask's
             dressing system;
  links   -- those of them that join a reciprocal pair, i.e. phase-ratio links;
  derived -- cross relations obtained by substituting the global phase-ratio
             identification into a multi-term equation, each one re-verified by
             symbolic substitution rather than assumed.
"""
import sys
from itertools import combinations

import sympy as sp

sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from orbit import fiber
from scan import bits, xor, dot
from kl import dressings_full as dressings


class DSU:
    def __init__(self, n):
        self.p = list(range(n)); self.s = [1] * n

    def find(self, x):
        if self.p[x] == x:
            return x, self.s[x]
        r, g = self.find(self.p[x])
        self.p[x] = r; self.s[x] = self.s[x] * g
        return r, self.s[x]

    def union(self, x, y, sig):
        rx, sx = self.find(x); ry, sy = self.find(y)
        if rx == ry:
            return sx * sy * sig == 1
        self.p[rx] = ry; self.s[rx] = sig * sx * sy
        return True


def analyse(a, q, delta):
    S0, S1 = fiber(a, q, 0), fiber(a, q, delta)
    n0 = len(S0)
    comp = lambda s: ''.join('1' if c == '0' else '0' for c in s)
    if sorted(comp(x) for x in S0) != sorted(S1):
        return None
    hat = [S1.index(comp(x)) for x in S0]
    inv = {hat[k]: k for k in range(n0)}

    masks = []
    for m in range(1, 64):
        e = bits(m)
        if e.count('1') > 2:
            continue
        inc = [(S0.index(xor(y, e)), t) for t, y in enumerate(S1) if xor(y, e) in S0]
        if inc:
            masks.append((e, inc))

    direct, links = [], []
    for e, inc in masks:
        M = sp.Matrix([[(-1) ** dot(z, S1[t]) for i, t in inc] for z in dressings(e)])
        MT = M.T
        r = MT.rank()
        for u, v in combinations(range(len(inc)), 2):
            for sg in (1, -1):
                tgt = sp.zeros(len(inc), 1)
                tgt[u] = 1; tgt[v] = sg
                if r == MT.row_join(tgt).rank():
                    iu, tu = inc[u]; iv, tv = inc[v]
                    rec = (inv.get(tu) == iv and inv.get(tv) == iu)
                    rel = (iu, inv[tu], iv, inv[tv], sg, e)
                    (links if rec else direct).append(rel)
                    break

    # global phase ratios from the links
    rho = DSU(n0)
    clash = False
    for iu, ju, iv, jv, sg, e in links:
        # P(iu, ju-hat) + sg P(iv, jv-hat) = 0 with {iu,ju} = {iv,jv} reciprocal
        if not rho.union(iu, iv, -sg):
            clash = True
    sgn = [rho.find(i)[1] for i in range(n0)]
    roots = {rho.find(i)[0] for i in range(n0)}

    # derived cross relations: substitute P(y,x-hat) = sigma_x sigma_y P(x,y-hat)
    derived = []
    for e, inc in masks:
        M = sp.Matrix([[(-1) ** dot(z, S1[t]) for i, t in inc] for z in dressings(e)])
        for row in range(M.rows):
            acc = {}
            ok = True
            for k, (i, t) in enumerate(inc):
                j = inv[t]
                if rho.find(i)[0] != rho.find(j)[0]:
                    ok = False; break
                key = (min(i, j), max(i, j))
                # orient every product onto (min,max)
                s = 1 if i <= j else sgn[i] * sgn[j]
                acc[key] = acc.get(key, 0) + M[row, k] * s
            if not ok:
                continue
            live = [(k, c) for k, c in acc.items() if c != 0]
            if len(live) == 2 and abs(live[0][1]) == abs(live[1][1]):
                (ka, ca), (kb, cb) = live
                derived.append((ka[0], ka[1], kb[0], kb[1],
                                1 if ca * cb > 0 else -1, e))
    seen, uniq = set(), []
    for d in derived:
        k = (d[0], d[1], d[2], d[3], d[4])
        if k not in seen:
            seen.add(k); uniq.append(d)
    return dict(S0=S0, S1=S1, hat=hat, inv=inv, direct=direct, links=links,
                derived=uniq, sgn=sgn, clash=clash, components=len(roots))


if __name__ == '__main__':
    from scan import ORBITS
    from propagate import pdim, DLP
    for oid in [25, 26, 31, 33, 37, 56]:
        a, q, sizes = ORBITS[oid]
        S0 = fiber(a, q, 0)
        ds = [d for d in range(1, q) if fiber(a, q, d)
              and (sizes is None or (len(S0), len(fiber(a, q, d))) == sizes)
              and pdim(S0, fiber(a, q, d)) == DLP[oid]]
        if not ds:
            print('%-4d no delta' % oid); continue
        r = analyse(a, q, ds[0])
        if r is None:
            print('%-4d top fiber is not the complement image' % oid); continue
        print('orbit %-4d delta=%d  links=%-3d direct-cross=%-3d derived-cross=%-3d '
              'rho components=%d%s'
              % (oid, ds[0], len(r['links']), len(r['direct']), len(r['derived']),
                 r['components'], '  SIGN CLASH' if r['clash'] else ''))
