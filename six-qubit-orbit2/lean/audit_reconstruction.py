#!/usr/bin/env python3
"""Audit the direct ordered-coefficient formula implemented in Lean.
This checks a fixed exact coefficient identity, not a code search.
"""
import importlib.util
from functools import lru_cache
from pathlib import Path
import sys
sys.dont_write_bytecode = True
root = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('original', root/'orbit2_exact_certificate.py')
v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)


def sign(e):
    return (1, 0, -1, 0)[e % 4]


def ch(ax, p):
    return 1 if ax == 0 or p == 0 or ax == p else -1


def jw(site, ax, u):
    p = v.T_LABELS[u][site]
    if ax == 0:
        return 0
    if ax == 3:
        return (10 if v.IS_B[u] else -18) if p in (1, 2) else 0
    if v.IS_B[u]:
        return 5 if p == 3 else 7 if p in (1, 2) and p != ax else 0
    return 18 if p in (1, 2) and p != ax else 0


@lru_cache(None)
def four(u, v1, x, y):
    phase = v.trace_phase([v.T_IDS[k] for k in (u, x, v1, y)])
    return 0 if phase is None else sign(phase)


def gc(u, v1, x, y):
    return four(u, v1, x, y) - 2*(u == x and v1 == y) if v.IS_B[u] else 0


def jc(u, v1, x, y):
    a = sum(jw(site, ax, u)*ch(ax, v.T_LABELS[x][site])*
            (ch(ax, v.T_LABELS[v1][site])-1) for site in range(4) for ax in range(1, 4))
    left, right = v.MUL[v.T_IDS[x]][v.T_IDS[v1]], v.MUL[v.T_IDS[u]][v.T_IDS[y]]
    correction = 0
    if left == right and v.weight(v.LABELS[left]) == 1:
        site = next(i for i, ax in enumerate(v.LABELS[left]) if ax)
        ax = v.LABELS[left][site]
        correction = jw(site, ax, u)*ch(ax, v.T_LABELS[u][site]) * sign(
            v.EXP[v.T_IDS[x]][v.T_IDS[v1]] + v.EXP[v.T_IDS[u]][v.T_IDS[y]])
    return a * four(u, v1, x, y) - 4*correction


def cc(u, v1, x, y):
    left, right = v.MUL[v.T_IDS[x]][v.T_IDS[u]], v.MUL[v.T_IDS[y]][v.T_IDS[v1]]
    if left != right:
        return 0
    w, f = v.weight(v.LABELS[left]), v.transverse_count(v.LABELS[left])
    mixed, both = v.IS_B[y] != v.IS_B[v1], v.IS_B[y] and v.IS_B[v1]
    mult = (-24 if (w, f) == (3, 2) else 0)
    if (w, f) == (4, 2):
        mult += 68*mixed + 76*both
    if (w, f) == (3, 0) and mixed:
        mult += 100
    if (w, f) == (2, 0) and both:
        mult += 8
    return mult*sign(v.EXP[v.T_IDS[x]][v.T_IDS[u]] + v.EXP[v.T_IDS[y]][v.T_IDS[v1]])


def raw(u, v1, x, y):
    return cc(u, v1, x, y) + jc(u, v1, x, y) + jc(x, y, u, v1) + 6*gc(u, v1, x, y) + 6*gc(x, y, u, v1)


def main():
    from collections import defaultdict
    groups = defaultdict(list)
    for i,(a,b) in enumerate(v.MONOMIALS):
        groups[v.MUL[v.T_IDS[a]][v.T_IDS[b]]].append(i)
    M = v.build_integer_certificate()
    checked = 0
    for indices in groups.values():
        for r in indices:
            u,w = v.MONOMIALS[r]
            rows = [(u,w)] if u == w else [(u,w),(w,u)]
            for c in indices:
                x,y = v.MONOMIALS[c]
                cols = [(x,y)] if x == y else [(x,y),(y,x)]
                actual = sum(raw(a,b,c1,d) for a,b in rows for c1,d in cols)
                assert actual == 2*M.get((r,c),0), (r,c,actual,M.get((r,c),0))
                checked += 1
    print(f'PASS: all {checked} same-character coefficients, including zero coordinates, equal 2M.')

if __name__ == '__main__':
    main()
