"""Checks (b) and (d): the anchor scalar R2, its per-block phase and its index."""
from stepA_audit import *          # noqa
import sympy as sp

print('=' * 78)
print('(b)+(d)  ANCHOR SCALARS.  X_i = C_j^dag D_i = sum_b cc((C_j)_b)(D_i)_b')
print('                          Y_i = C_i^dag D_j = sum_a cc((C_i)_a)(D_j)_a')
print('         flipped variants use (D)_{1-b} instead.')
mus = {}
for j in (6, 7):
    for i in range(6):
        print('-' * 70)
        # --- unflipped (the index identification Step A needs) ---
        Xlabs = [(j, b, i, b) for b in (0, 1)]        # cc(C_j)_b (D_i)_b
        Ylabs = [(i, a, j, a) for a in (0, 1)]        # cc(C_i)_a (D_j)_a
        ms = sorted({mask_of(*l) for l in Xlabs + Ylabs})
        print('  anchor j=%d block i=%d   UNFLIPPED masks %s' % (j, i, ms))
        if len(ms) == 1 and ms[0] in INC:
            m = ms[0]
            rels = relations_supported_on(m, Xlabs + Ylabs)
            print('     mask %s has %d incidences, relation dim %d; relations on the 4 X/Y monomials: %d'
                  % (m, len(INC[m]), RS[m].rank(), len(rels)))
            for v in rels:
                show(m, v, '        ')
                co = {INC[m][k]: v[0, k] for k in range(v.cols) if v[0, k] != 0}
                al = [co.get(l, 0) for l in Xlabs]
                be = [co.get(l, 0) for l in Ylabs]
                print('        X-coeffs %s   Y-coeffs %s' % (al, be))
                ok = (al[0] == al[1] != 0) and (be[0] == be[1] != 0)
                if ok:
                    mu = sp.nsimplify(-sp.Rational(al[0], 1) / be[0])
                    mus[(j, i)] = mu
                    print('        => scalar form alpha*X_i + beta*Y_i = 0 with mu_i = Y_i/X_i = %s' % mu)
                else:
                    print('        => NOT of the scalar form (coefficients differ across a)')
        else:
            print('     *** X and Y monomials do not share an admissible mask')
        # --- flipped variant, for check (d) ---
        Xf = [(j, b, i, 1 - b) for b in (0, 1)]
        Yf = [(i, a, j, 1 - a) for a in (0, 1)]
        mf = sorted({mask_of(*l) for l in Xf + Yf})
        tag = 'admissible' if (len(mf) == 1 and mf[0] in INC) else 'NOT admissible'
        print('  anchor j=%d block i=%d   FLIPPED   masks %s  (%s)' % (j, i, mf, tag))
        if len(mf) == 1 and mf[0] in INC:
            m = mf[0]
            rels = relations_supported_on(m, Xf + Yf)
            print('     relations on the 4 flipped monomials: %d' % len(rels))
            for v in rels:
                show(m, v, '        ')

print('=' * 78)
print('mu_i table (should be a single constant for Step A to work):')
for k in sorted(mus):
    print('   anchor %d block %d : mu = %s' % (k[0], k[1], mus[k]))
print('   all twelve present:', len(mus) == 12, '  all equal:', len(set(mus.values())) == 1)

print('=' * 78)
print('CROSS-ANCHOR scalars C_6^dag D_i vs C_7^dag D_i -- are those masks admissible?')
for i in range(8):
    for (u, v) in [(6, 7), (7, 6)]:
        m = {mask_of(u, b, v, b) for b in (0, 1)}
        print('   cc(C%d) D%d unflipped masks %s  admissible %s'
              % (u, i, sorted({mask_of(u, b, i, b) for b in (0, 1)}),
                 all(x in INC for x in {mask_of(u, b, i, b) for b in (0, 1)})))
        break
