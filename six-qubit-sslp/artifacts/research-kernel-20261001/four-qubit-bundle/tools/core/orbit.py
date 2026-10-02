"""Analyse one moment orbit of the six-qubit classification.

Given (q, m, delta, a) it computes the two residue fibers, the 14- or 15-equation
moment certificate, the exact solution (unique or one-parameter), and every
weight-<=2 X-mask whose incidence set has exactly two edges with a separating
coordinate -- i.e. every place where the two-edge Walsh obstruction applies.
"""
from fractions import Fraction as F
from itertools import combinations
from sympy import Matrix, Rational, symbols, solve, eye

N = 6

def fiber(a, q, res):
    out = []
    for k in range(1 << N):
        s = format(k, '0%db' % N)
        if sum(a[i] for i in range(N) if s[i] == '1') % q == res:
            out.append(s)
    return out

def ind(s, i):
    return 1 if s[i] == '1' else 0

def moment_rows(S0, S1, pairs):
    """two normalizations, six one-bit, then the given two-bit coordinate pairs"""
    n0, n1 = len(S0), len(S1)
    rows, rhs, lab = [], [], []
    rows.append([1]*n0 + [0]*n1); rhs.append(1); lab.append('n0')
    rows.append([0]*n0 + [1]*n1); rhs.append(1); lab.append('n1')
    for i in range(N):
        rows.append([ind(x,i) for x in S0] + [-ind(y,i) for y in S1])
        rhs.append(0); lab.append('m%d' % (i+1))
    for (i,j) in pairs:
        rows.append([ind(x,i)*ind(x,j) for x in S0] + [-ind(y,i)*ind(y,j) for y in S1])
        rhs.append(0); lab.append('c%d%d' % (i+1,j+1))
    return Matrix(rows), Matrix(rhs), lab

def full_moment_ok(S0, S1, p0, p1):
    """check the displayed solution satisfies ALL 21 moment equations + norms"""
    if sum(p0) != 1 or sum(p1) != 1: return False
    for i in range(N):
        if sum(p0[k]*ind(S0[k],i) for k in range(len(S0))) != \
           sum(p1[k]*ind(S1[k],i) for k in range(len(S1))): return False
    for i,j in combinations(range(N),2):
        if sum(p0[k]*ind(S0[k],i)*ind(S0[k],j) for k in range(len(S0))) != \
           sum(p1[k]*ind(S1[k],i)*ind(S1[k],j) for k in range(len(S1))): return False
    return True

def xor(s, mask):
    return ''.join('1' if (s[i]=='1') != (mask[i]=='1') else '0' for i in range(N))

def masks_wt(w):
    for bits in combinations(range(N), w):
        yield ''.join('1' if i in bits else '0' for i in range(N))

def two_edge_masks(S0, S1):
    """X-masks of weight 1 or 2 with exactly two incidences and a separating coord"""
    hits = []
    for w in (1, 2):
        for u in masks_wt(w):
            inc = [(y, xor(y,u)) for y in S1 if xor(y,u) in S0]
            if len(inc) != 2: continue
            y1, y2 = inc[0][0], inc[1][0]
            # separating coordinate must not be in the mask support (weight budget)
            sep = [j for j in range(N) if y1[j] != y2[j] and u[j] == '0']
            if sep and w + 1 <= 2:
                hits.append((u, inc, sep))
    return hits
