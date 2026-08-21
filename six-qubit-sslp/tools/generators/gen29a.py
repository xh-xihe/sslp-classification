"""The anchored step and the main pair contradiction for orbit 29."""
import io
NL = chr(10)
VERT = [3, 5, 6, 7]
EDGE = {1: (3, 5), 2: (3, 6), 3: (3, 7), 4: (5, 6), 5: (5, 7), 6: (6, 7)}
FAM = {3: (4, 5, 6), 5: (2, 3, 6), 6: (1, 3, 5), 7: (1, 2, 4)}
TFR = {3: (0, 1, 2), 5: (0, 1, 4), 6: (0, 2, 4), 7: (1, 2, 4)}
L = []
W = L.append


def amps():
    for m in range(1, 8):
        W('    (a%d b%d : ℂ)' % (m, m))
    for n in VERT:
        W('    (S%d T%d : ℂ) (Q%d : Real)' % (n, n, n))
    for n in (0, 1, 2, 4):
        W('    (s%d t%d : ℂ)' % (n, n))


def commons():
    W('    (n7 : a7 * star a7 + b7 * star b7 = 1/4)')
    for n in VERT:
        W('    (nq%d : S%d * star S%d + T%d * star T%d = (Q%d : ℂ))' % (n, n, n, n, n, n))
    for m, (n, p) in EDGE.items():
        W('    (nc%d : a%d * star a%d + b%d * star b%d = ((Q%d + Q%d - 1/4 : Real) : ℂ))'
          % (m, m, m, m, m, n, p))
    W('    (qsum : Q3 + Q5 + Q6 + Q7 = 3/4)')
    W('    (esum : (S3 * star S3 - T3 * star T3) + (S5 * star S5 - T5 * star T5)')
    W('      + (S6 * star S6 - T6 * star T6) + (S7 * star S7 - T7 * star T7) = 0)')
    for m, (n, p) in EDGE.items():
        W('    (o%d%d : star a%d * S%d + star b%d * T%d = 0)' % (m, n, m, n, m, n))
        W('    (o%d%d : star a%d * S%d + star b%d * T%d = 0)' % (m, p, m, p, m, p))
    for n in VERT:
        i, j, k = FAM[n]
        x, y, z = TFR[n]
        W('    (E%dA : star a%d * s%d + star a%d * s%d + star a%d * s%d + star b7 * T%d = 0)'
          % (n, i, x, j, y, k, z, n))
        W('    (E%dB : star b%d * t%d + star b%d * t%d + star b%d * t%d + star a7 * S%d = 0)'
          % (n, i, x, j, y, k, z, n))
        W('    (E%dC : star b%d * s%d + star b%d * s%d + star b%d * s%d + star b7 * S%d = 0)'
          % (n, i, x, j, y, k, z, n))
        W('    (E%dD : star a%d * t%d + star a%d * t%d + star a%d * t%d + star a7 * T%d = 0)'
          % (n, i, x, j, y, k, z, n))


def pass_through():
    W('    ' + ' '.join('a%d b%d' % (m, m) for m in range(1, 8)))
    W('    ' + ' '.join('S%d T%d Q%d' % (n, n, n) for n in VERT))
    W('    ' + ' '.join('s%d t%d' % (n, n) for n in (0, 1, 2, 4)))
    W('    n7 ' + ' '.join('nq%d' % n for n in VERT) + ' qsum esum')


W('/-- A vanishing pair of squared norms bounds the recorded probability below. -/')
W('theorem nonneg_of_norm (x y : ℂ) (r : Real)')
W('    (h : x * star x + y * star y = (r : ℂ)) : 0 ≤ r := by')
W('  rw [sq, sq] at h')
W('  have hr : Complex.normSq x + Complex.normSq y = r := by exact_mod_cast h')
W('  nlinarith [Complex.normSq_nonneg x, Complex.normSq_nonneg y]')
W('')
W('/-- With an anchor direction in hand, every bottom pair is orthogonal to it and')
W('the closing argument applies. -/')
W('theorem anchored (v0 v1 : ℂ) (Qv : Real)')
W('    (hv : v0 * star v0 + v1 * star v1 = (Qv : ℂ)) (hQv : Qv ≠ 0)')
amps()
commons()
for n in VERT:
    W('    (dd%d : S%d * v1 - v0 * T%d = 0)' % (n, n, n))
W('    : False := by')
for m, (n, p) in EDGE.items():
    W('  have hb%d : (1/4 : Real) ≤ Q%d + Q%d := by' % (m, n, p))
    W('    have := nonneg_of_norm a%d b%d _ nc%d; linarith' % (m, m, m))
    W('  have p%d : star a%d * v0 + star b%d * v1 = 0 :=' % (m, m, m))
    W('    perp_v a%d b%d S%d T%d S%d T%d v0 v1 Q%d Q%d hb%d nq%d nq%d o%d%d o%d%d dd%d dd%d'
      % (m, m, n, n, p, p, n, p, m, n, p, m, n, m, p, n, p))
W('  exact finish v0 v1 Qv hv hQv')
pass_through()
W('    ' + ' '.join('dd%d' % n for n in VERT))
W('    ' + ' '.join('p%d' % m for m in range(1, 7)))
for n in VERT:
    W('    E%dA E%dB E%dC E%dD' % (n, n, n, n))
W('')
io.open('gen29a_out.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('anchored: %d lines' % len(L))

# ------------------------------------------------------------- main theorem
L = []
W = L.append
ORD = {n: i for i, n in enumerate(VERT)}


def gterm(n, p):
    """The canonical determinant fact for the unordered pair, oriented (n,p)."""
    m = [k for k, v in EDGE.items() if set(v) == {n, p}][0]
    if ORD[n] < ORD[p]:
        return 'g%d' % m
    # the coefficient is the same real number but a different syntactic term,
    # so the casts have to be pushed before `ring` can see it
    return '(by push_cast at g%d ⊢; linear_combination -g%d)' % (m, m)


W('/-- Orbit 29 has no exact code: the pair algebra alone is contradictory. -/')
W('theorem pair_contradiction')
amps()
commons()
for n in VERT:
    W('    (qle%d : Q%d ≤ 1/4)' % (n, n))
W('    : False := by')
for m, (n, p) in EDGE.items():
    W('  have g%d : ((Q%d + Q%d - 1/4 : Real) : ℂ) * (S%d * T%d - S%d * T%d) = 0 := by'
      % (m, n, p, n, p, p, n))
    W('    rw [← nc%d]' % m)
    W('    exact perp_det a%d b%d S%d T%d S%d T%d o%d%d o%d%d'
      % (m, m, n, n, p, p, m, n, m, p))
for n in VERT:
    W('  have nn%d : (0 : Real) ≤ Q%d := nonneg_of_norm S%d T%d _ nq%d' % (n, n, n, n, n))
for m, (n, p) in EDGE.items():
    x, y = [v for v in VERT if v not in (n, p)]
    W('  have k%d : S%d * T%d - S%d * T%d = 0 :=' % (m, n, p, p, n))
    W('    par_edge Q%d Q%d Q%d Q%d S%d T%d S%d T%d S%d T%d'
      % (n, p, x, y, n, n, p, p, x, x))
    W('      (by linarith) qle%d qle%d nn%d nn%d nq%d nq%d nq%d'
      % (y, x, n, p, n, p, x))
    W('      g%d %s %s' % (m, gterm(n, x), gterm(p, x)))
W('  by_cases h3 : Q3 = 0')
for anchor, hname in ((5, 'h5'), (3, 'h3')):
    if anchor == 5:
        W('  · have h5 : Q5 ≠ 0 := by intro h; linarith')
    else:
        W('  · ')
    pre, cont = '    ', '      '
    W(pre + 'exact anchored S%d T%d Q%d nq%d %s' % (anchor, anchor, anchor, anchor, hname))
    W(cont + ' '.join('a%d b%d' % (m, m) for m in range(1, 8)))
    W(cont + ' '.join('S%d T%d Q%d' % (n, n, n) for n in VERT))
    W(cont + ' '.join('s%d t%d' % (n, n) for n in (0, 1, 2, 4)))
    W(cont + 'n7 ' + ' '.join('nq%d' % n for n in VERT) + ' ' +
      ' '.join('nc%d' % m for m in range(1, 7)) + ' qsum esum')
    W(cont + ' '.join('o%d%d o%d%d' % (m, EDGE[m][0], m, EDGE[m][1]) for m in range(1, 7)))
    for n in VERT:
        W(cont + 'E%dA E%dB E%dC E%dD' % (n, n, n, n))
    for n in VERT:
        if n == anchor:
            W(cont + '(by ring)')
        else:
            mm = [k for k, v in EDGE.items() if set(v) == {n, anchor}][0]
            if ORD[n] < ORD[anchor]:
                W(cont + '(by linear_combination k%d)' % mm)
            else:
                W(cont + '(by linear_combination -k%d)' % mm)
W('')
io.open('gen29b_out.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('main: %d lines' % len(L))
