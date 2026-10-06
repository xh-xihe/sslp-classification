"""Checks (a) and (c): the true R1 relations, entry by entry."""
from stepA_audit import *          # noqa
import sympy as sp

PAIRS = [(0, 1), (0, 2), (1, 2)]

print('=' * 78)
print('RAW CONTENT OF THE THREE WEIGHT-ONE MASKS AND THEIR WEIGHT-TWO PARTNERS')
for m in ['010000', '110000', '001000', '101000', '000001', '100001']:
    print(' mask %s : monomials %s' % (m, ['C%d_%d|D%d_%d' % l for l in INC[m]]))
    print('   full relation basis (dim %d):' % RS[m].rank())
    for r in range(RS[m].rows):
        show(m, RS[m][r, :])

print('=' * 78)
print('(a)+(c)  R1 ENTRY BY ENTRY:  which relations live on the four monomials')
print('        E_ab(g,h) = sum_c cc((C_{2g+c})_a)(D_{2h+1-c})_b')
print('                  + omega * sum_c cc((C_{2h+c})_a)(D_{2g+1-c})_b')
for (g, h) in PAIRS:
    print('-' * 70)
    for a in (0, 1):
        for b in (0, 1):
            labs = []
            for c in (0, 1):
                labs.append((2 * g + c, a, 2 * h + 1 - c, b))
                labs.append((2 * h + c, a, 2 * g + 1 - c, b))
            ms = {mask_of(*l) for l in labs}
            print('  groups (%d,%d) entry (%d,%d):  masks used = %s' % (g, h, a, b, sorted(ms)))
            if len(ms) != 1:
                print('     *** the four monomials do NOT share a mask -- no single relation possible')
                continue
            m = ms.pop()
            rels = relations_supported_on(m, labs)
            print('     dim of relations supported on exactly these 4 monomials: %d' % len(rels))
            for v in rels:
                show(m, v, '        ')
            # read omega off, if the shape is right
            for v in rels:
                co = {}
                for k in range(v.cols):
                    if v[0, k] != 0:
                        co[INC[m][k]] = v[0, k]
                t1 = [co.get((2 * g + c, a, 2 * h + 1 - c, b), 0) for c in (0, 1)]
                t2 = [co.get((2 * h + c, a, 2 * g + 1 - c, b), 0) for c in (0, 1)]
                print('        -> C_g-first coeffs %s ,  C_h-first coeffs %s' % (t1, t2))
                if t1[0] != 0:
                    print('           internal sign within group g : %s  (J needs +1, symplectic -1)'
                          % sp.nsimplify(t1[1] / t1[0]))
                    print('           omega = %s' % sp.nsimplify(t2[0] / t1[0])
                          if t1[0] != 0 else '')
                    if t2[0] != 0:
                        print('           internal sign within group h : %s'
                              % sp.nsimplify(t2[1] / t2[0]))

print('=' * 78)
print('ALSO: is the I-form  sum_c cc((C_{2g+c})_a)(D_{2h+c})_b  even on one mask?')
for (g, h) in PAIRS:
    for a in (0, 1):
        for b in (0, 1):
            labs = [(2 * g + c, a, 2 * h + c, b) for c in (0, 1)] \
                 + [(2 * h + c, a, 2 * g + c, b) for c in (0, 1)]
            ms = sorted({mask_of(*l) for l in labs})
            print('  (%d,%d) entry (%d,%d) I-form masks %s %s'
                  % (g, h, a, b, ms, '' if len(ms) > 1 else '<-- single mask!'))
