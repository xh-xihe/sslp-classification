"""Finish the orbit-13 module: per-block frame hypotheses and the headline."""
import io
import sys

import sympy as sp

sys.path.insert(0, '.')
import gen13
from gen13 import (ALL, E1, J, NL, bits, dot, dress, supp, xor)

OID, Q, A, D = 13, 4, [0, 1, 1, 1, 2, 2], 2
L, data = gen13.emit(OID, Q, A, D)
(S0, S1, bidx, tidx, iso, blocks, zname, mname, DZ, fields, allv,
 n0, n1, dinc0, dinc1, emitted) = data
W = L.append
tail = lambda s: s[:J] + s[J + 1:]
btails = sorted({tail(x) for x in S0})
ttails = sorted({tail(y) for y in S1})
key0 = lambda t: '0' * 0 + t[:J] + '0' + t[J:]
key1 = lambda t: t[:J] + '1' + t[J:]


def diag_multipliers(block):
    """Multipliers nu_z over the dressings of E1 with
       sum_z nu_z diagBot(z) = u^c_{x1} + u^c_{x2}
       sum_z nu_z diagTop(z) = u^d_{y1} + u^d_{y2}."""
    x1, x2, y1, y2 = block
    rows, tgt = [], []
    for t in btails:                        # coeff of u^c_t
        rows.append([(-1) ** dot(z, key0(t)) for z in DZ])
        tgt.append(1 if t in (x1, x2) else 0)
    for t in btails:                        # coeff of conj u^c_t
        rows.append([(-1) ** dot(z, key1(t)) for z in DZ])
        tgt.append(0)
    for s in ttails:                        # coeff of u^d_s
        rows.append([(-1) ** dot(z, key0(s)) for z in DZ])
        tgt.append(1 if s in (y1, y2) else 0)
    for s in ttails:
        rows.append([(-1) ** dot(z, key1(s)) for z in DZ])
        tgt.append(0)
    M = sp.Matrix(rows)
    try:
        nu = M.gauss_jordan_solve(sp.Matrix(tgt))[0]
    except ValueError:
        return None
    nu = nu.subs({s: 0 for s in nu.free_symbols})
    return [(DZ[r], sp.Rational(nu[r])) for r in range(len(DZ)) if nu[r] != 0]


mult = {}
for b in blocks:
    m = diag_multipliers(b)
    if m is None:
        print('block %s : NO diagonal multipliers' % (b,))
        raise SystemExit(1)
    mult[b] = m
print('diagonal multipliers found for all %d blocks' % len(blocks))

# ---------- per-block frame facts from the moment system ----------
W('/-- Per-block equality of the free-qubit diagonal frame entries. -/')
W('theorem MomentSystem.frameA {%s : Real} (h : MomentSystem %s) :' % (allv, allv))
parts = []
for (x1, x2, y1, y2) in blocks:
    parts.append('q%d + q%d = r%d + r%d'
                 % (bidx[('0', x1)], bidx[('0', x2)],
                    tidx[('0', y1)], tidx[('0', y2)]))
    parts.append('q%d + q%d = r%d + r%d'
                 % (bidx[('1', x1)], bidx[('1', x2)],
                    tidx[('1', y1)], tidx[('1', y2)]))
W('    ' + ' ∧ '.join(parts) + ' := by')
W('  obtain ⟨' + ', '.join(fields) + '⟩ := h')
W('  refine ⟨' + ', '.join('?_' for _ in parts) + '⟩ <;> linarith')
W('')

# ---------- the headline ----------
offhyp = sorted(emitted)
W('/-! ## The no-go -/')
W('')
W('/-- **Orbit %d is impossible.** -/' % OID)
W('theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)')
W('    (hm : MomentSystem')
W('            ' + ' '.join('(Complex.normSq (c y%d))' % r for r in range(n0)))
W('            ' + ' '.join('(Complex.normSq (d z%d))' % r for r in range(n1)) + ')')
for r, (m, z) in enumerate(offhyp):
    W('    (ho%d : offSum c d %s %s = 0)' % (r, mname[m], zname[z]))
for r, z in enumerate(DZ):
    W('    (hd%d : diagBot c efZ %s = diagTop d efZ %s)' % (r, zname[z], zname[z]))
W('    : False := by')
for r, (m, z) in enumerate(offhyp):
    W('  rw [ex_%s_%s] at ho%d' % (mname[m], zname[z], r))
for r, z in enumerate(DZ):
    W('  rw [dexB_%s, dexT_%s] at hd%d' % (zname[z], zname[z], r))
W('  obtain ⟨' + ', '.join('fa%d' % k for k in range(2 * len(blocks)))
  + '⟩ := hm.frameA')
for bi, (x1, x2, y1, y2) in enumerate(blocks):
    a1, a2 = bidx[('0', x1)], bidx[('0', x2)]
    b1, b2 = bidx[('1', x1)], bidx[('1', x2)]
    p1, p2 = tidx[('0', y1)], tidx[('0', y2)]
    q1, q2 = tidx[('1', y1)], tidx[('1', y2)]
    for (xi, yj, nm) in ((x1, y1, 'o11'), (x1, y2, 'o12'),
                         (x2, y1, 'o21'), (x2, y2, 'o22')):
        m, inc, used = iso[(xi, yj)]
        bb, tt2 = bidx[('0', xi)], tidx[('0', yj)]
        bb1, tt1 = bidx[('1', xi)], tidx[('1', yj)]
        W('  have %s_%d : star (c y%d) * d z%d + star (c y%d) * d z%d = 0 := by'
          % (nm, bi, bb, tt2, bb1, tt1))
        W('    linear_combination ' + ' + '.join(
            '(%s : ℂ) * ho%d' % (mu, offhyp.index((m, z))) for z, mu in used))
    W('  have fc_%d : c y%d * star (c y%d) + c y%d * star (c y%d)'
      % (bi, a1, b1, a2, b2))
    W('      = d z%d * star (d z%d) + d z%d * star (d z%d) := by' % (p1, q1, p2, q2))
    W('    linear_combination ' + ' + '.join(
        '(%s : ℂ) * hd%d' % (nu, DZ.index(z)) for z, nu in mult[(x1, x2, y1, y2)]))
    W('  have blk_%d : Complex.normSq (c y%d) + Complex.normSq (c y%d) = 0 := by'
      % (bi, a1, a2))
    W('    exact SixQubit.Frame.block_zero o11_%d o12_%d o21_%d o22_%d fa%d fc_%d'
      % (bi, bi, bi, bi, 2 * bi, bi))
    W('  have blkb_%d : Complex.normSq (c y%d) + Complex.normSq (c y%d) = 0 := by'
      % (bi, b1, b2))
    W('    refine SixQubit.Frame.block_zero ?_ ?_ ?_ ?_ fa%d ?_' % (2 * bi + 1))
    W('    · linear_combination o11_%d' % bi)
    W('    · linear_combination o12_%d' % bi)
    W('    · linear_combination o21_%d' % bi)
    W('    · linear_combination o22_%d' % bi)
    W('    · linear_combination -fc_%d' % bi)
W('  obtain ⟨' + ', '.join(fields) + '⟩ := hm')
W('  linarith [' + ', '.join(
    ['blk_%d' % b for b in range(len(blocks))]
    + ['blkb_%d' % b for b in range(len(blocks))]) + ']')
W('')
W('end')
W('')
W('end SixQubit.Orbit%d' % OID)
src = NL.join(L) + NL
io.open('Orbit13.lean', 'w', encoding='utf-8').write(src)
print('Orbit13.lean : %d lines' % src.count(NL))
