"""Emit the block-level contradiction for orbit 33."""
import io
NL = chr(10)
L = []
W = L.append
RHO = lambda a, b: ' + '.join('%s%d * star %s%d' % (a, k, b, k) for k in range(6))

W('''
/-! ## The block contradiction -/

/-- The blocks of orbit 33 cannot satisfy the reflection identities together with
the cross relations.  Everything here is polynomial: no division, no case split
beyond `mul_eq_zero` against explicit nonzero rationals. -/
theorem block_contradiction
    (p0 p1 p2 p3 p4 p5 q0 q1 q2 q3 q4 q5 : ℂ)
    (s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 t5 : ℂ)''')
NORM = ['3/10', '1/5', '1/5', '1/10', '1/10', '1/10']
for k in range(6):
    W('    (nc%d : p%d * star p%d + q%d * star q%d = %s)' % (k, k, k, k, k, NORM[k]))
for k in [0, 3]:
    W('    (nd%d : s%d * star s%d + t%d * star t%d = %s)' % (k, k, k, k, k, NORM[k]))
for k in [0, 3]:
    tw = '3/5' if k == 0 else '1/5'
    W('    (r00_%d : p%d * star p%d + s%d * star s%d' % (k, k, k, k, k))
    W('        = (%s) * (%s))' % (tw, RHO('p', 'p')))
    W('    (r01_%d : p%d * star q%d + s%d * star t%d' % (k, k, k, k, k))
    W('        = (%s) * (%s))' % (tw, RHO('p', 'q')))
    if k == 0:
        W('    (r11_%d : q%d * star q%d + t%d * star t%d' % (k, k, k, k, k))
        W('        = (%s) * (%s))' % (tw, RHO('q', 'q')))
for n in (1, 2):
    for a, u in ((0, 'p'), (1, 'q')):
        for b, v in ((0, 's'), (1, 't')):
            W('    (x%d_%d%d : %s%d * star %s0 + %s0 * star %s%d = 0)'
              % (n, b, a, v, n, u, v, u, n))
for j in (3, 4, 5):
    W('    (y0_%d : star p%d * s0 + star q%d * t0 + (star p0 * s%d + star q0 * t%d) = 0)'
      % (j, j, j, j, j))
    W('    (y1_%d : star p%d * s1 + star q%d * t1 + (star p1 * s%d + star q1 * t%d) = 0)'
      % (j, j, j, j, j))
W('    : False := by')

W('  -- blocks 1 and 2 are collinear with block 0 on the bottom fiber')
for n in (1, 2):
    W('  have hd%d : p0 * q%d - q0 * p%d = 0 :=' % (n, n, n))
    W('    det_zero p0 q0 p%d q%d s0 t0 s%d t%d (3/10) x%d_00 x%d_01 x%d_10 x%d_11 nd0'
      % (n, n, n, n, n, n, n, n))
    W('      (by norm_num)')
W('  -- and on the top fiber, after conjugating the four entries')
for a, u in ((0, 'p'), (1, 'q')):
    for b, v in ((0, 's'), (1, 't')):
        W('  have cx1_%d%d : p1 * star %s0 + p0 * star %s1 = 0 :='
          % (b, a, v, v) if u == 'p' else
          '  have cx1_%d%d : q1 * star %s0 + q0 * star %s1 = 0 :=' % (b, a, v, v))
        W('    conj_pair %s1 %s0 %s0 %s1 x1_%d%d' % (v, u, v, u, b, a))
W('  have hv1 : s0 * t1 - t0 * s1 = 0 :=')
W('    det_zero s0 t0 s1 t1 p0 q0 p1 q1 (3/10) cx1_00 cx1_10 cx1_01 cx1_11 nc0')
W('      (by norm_num)')
W('  obtain ⟨lam, hp1, hq1, hp1s, hq1s⟩ :=')
W('    scale\' p0 q0 p1 q1 (3/10) (by simp) nc0 hd1')
W('  obtain ⟨mu, hs1, ht1, _hs1s, _ht1s⟩ :=')
W('    scale\' s0 t0 s1 t1 (3/10) (by simp) nd0 hv1')
W('  -- the two multipliers are conjugate-opposite')
for n, (u, v, x) in enumerate([('p', 's', 'x1_00'), ('q', 's', 'x1_01'),
                               ('p', 't', 'x1_10'), ('q', 't', 'x1_11')]):
    W('  have e%d : (%s0 * star %s0) * (mu + star lam) = 0 := by' % (n + 1, v, u))
    W('    linear_combination (3/10 : ℂ) * %s - (star %s0) * h%s1 - %s0 * h%s1s'
      % (x, u, v, v, u))
W('  have hmu : mu + star lam = 0 := by')
W('    have key : (9/100 : ℂ) * (mu + star lam) = 0 := by')
W('      linear_combination (star s0 * p0) * e1 + (star s0 * q0) * e2')
W('        + (star t0 * p0) * e3 + (star t0 * q0) * e4')
W('        - (mu + star lam) * (p0 * star p0 + q0 * star q0) * nd0')
W('        - (3/10 : ℂ) * (mu + star lam) * nc0')
W('    rcases mul_eq_zero.mp key with h | h')
W('    · exact absurd h (by norm_num)')
W('    · exact h')
W('  have hlam : lam * star lam = (3/50 : ℂ) := by')
W('    have key : (3/10 : ℂ) * (lam * star lam - 3/50) = 0 := by')
W('      linear_combination -((3/10 : ℂ) * star p1) * hp1 - (lam * p0) * hp1s')
W('        - ((3/10 : ℂ) * star q1) * hq1 - (lam * q0) * hq1s')
W('        + (9/100 : ℂ) * nc1 - (lam * star lam) * nc0')
W('    rcases mul_eq_zero.mp key with h | h')
W('    · exact absurd h (by norm_num)')
W('    · linear_combination h')
W('  have hlne : star lam ≠ 0 := by')
W('    intro h')
W('    rw [h, mul_zero] at hlam')
W('    norm_num at hlam')

W('  -- the three far blocks are orthogonal to block 0 on the opposite fiber')
for j in (3, 4, 5):
    W('  have hA%d : star p%d * s0 + star q%d * t0 = 0 := by' % (j, j, j))
    W('    have key : (-2 : ℂ) * (star lam * (star p%d * s0 + star q%d * t0)) = 0 := by' % (j, j))
    W('      linear_combination (3/10 : ℂ) * y1_%d - (star p%d) * hs1 - (star q%d) * ht1' % (j, j, j))
    W('        - s%d * hp1s - t%d * hq1s - (star lam) * y0_%d' % (j, j, j))
    W('        - (star p%d * s0 + star q%d * t0) * hmu' % (j, j))
    W('    have h2 : star lam * (star p%d * s0 + star q%d * t0) = 0 := by' % (j, j))
    W('      rcases mul_eq_zero.mp key with h | h')
    W('      · exact absurd h (by norm_num)')
    W('      · exact h')
    W('    rcases mul_eq_zero.mp h2 with h | h')
    W('    · exact absurd h hlne')
    W('    · exact h')
W('  have hB3 : star p0 * s3 + star q0 * t3 = 0 := by linear_combination y0_3 - hA3')
W('  have hB3\' : star s3 * p0 + star t3 * q0 = 0 := conj_inner p0 s3 q0 t3 hB3')
W('  -- the resulting outer products')
for j in (3, 4, 5):
    W('  obtain ⟨w%da, w%db, w%dc⟩ := ortho2 p%d q%d s0 t0 hA%d' % (j, j, j, j, j, j))
    W('  have c%da : (3/10 : ℂ) * (p%d * star p%d) = (1/10 : ℂ) * (t0 * star t0) := by'
      % (j, j, j))
    W('    linear_combination w%da - (p%d * star p%d) * nd0 + (t0 * star t0) * nc%d'
      % (j, j, j, j))
    W('  have c%db : (3/10 : ℂ) * (p%d * star q%d) = -((1/10 : ℂ) * (s0 * star t0)) := by'
      % (j, j, j))
    W('    linear_combination w%db - (p%d * star q%d) * nd0 - (s0 * star t0) * nc%d'
      % (j, j, j, j))
    W('  have c%dc : (3/10 : ℂ) * (q%d * star q%d) = (1/10 : ℂ) * (s0 * star s0) := by'
      % (j, j, j))
    W('    linear_combination w%dc - (q%d * star q%d) * nd0 + (s0 * star s0) * nc%d'
      % (j, j, j, j))
W('  obtain ⟨v3a, v3b, _v3c⟩ := ortho2 s3 t3 p0 q0 hB3\'')
W('  have d3a : (3/10 : ℂ) * (s3 * star s3) = (1/10 : ℂ) * (q0 * star q0) := by')
W('    linear_combination v3a - (s3 * star s3) * nc0 + (q0 * star q0) * nd3')
W('  have d3b : (3/10 : ℂ) * (s3 * star t3) = -((1/10 : ℂ) * (p0 * star q0)) := by')
W('    linear_combination v3b - (s3 * star t3) * nc0 - (p0 * star q0) * nd3')
W('  -- blocks 1 and 2 carry proportional outer products')
for n in (1, 2):
    W('  obtain ⟨po%da, po%db, po%dc⟩ :=' % (n, n, n))
    W('    prop_outer p0 q0 p%d q%d (3/10) (1/5) nc0 nc%d hd%d' % (n, n, n, n))
W('  -- the reduced state is half the identity')
W('  have hRR : (3/50 : ℂ) * ((%s) - (%s)) = 0 := by' % (RHO('p','p'), RHO('q','q')))
W('    linear_combination c3a + d3a - (3/10 : ℂ) * r00_3 + (1/10 : ℂ) * r11_0')
W('  have htrace : (%s) + (%s) = 1 := by' % (RHO('p','p'), RHO('q','q')))
W('    linear_combination nc0 + nc1 + nc2 + nc3 + nc4 + nc5')
W('  have h00 : (%s) = 1/2 := by' % RHO('p','p'))
W('    have key : (3/25 : ℂ) * ((%s) - 1/2) = 0 := by' % RHO('p','p'))
W('      linear_combination hRR + (3/50 : ℂ) * htrace')
W('    rcases mul_eq_zero.mp key with h | h')
W('    · exact absurd h (by norm_num)')
W('    · linear_combination h')
W('  have h11 : (%s) = 1/2 := by linear_combination htrace - h00' % RHO('q','q'))
W('  have h01 : (%s) = 0 := by' % RHO('p','q'))
W('    have key : (3/25 : ℂ) * (%s) = 0 := by' % RHO('p','q'))
W('      linear_combination c3b + d3b - (3/10 : ℂ) * r01_3 - (1/10 : ℂ) * r01_0')
W('    rcases mul_eq_zero.mp key with h | h')
W('    · exact absurd h (by norm_num)')
W('    · exact h')
W('  -- block 0 is forced to be a multiple of the identity, which is impossible')
W('  have hpt : p0 * star p0 = t0 * star t0 := by')
W('    linear_combination r00_0 - nd0 + (3/5 : ℂ) * h00')
W('  have hqs : q0 * star q0 = s0 * star s0 := by')
W('    linear_combination r11_0 - nd0 + (3/5 : ℂ) * h11')
W('  have hst : s0 * star t0 = -(p0 * star q0) := by')
W('    linear_combination r01_0 + (3/5 : ℂ) * h01')
W('  have hp0 : p0 * star p0 = 3/20 := by')
W('    linear_combination (3/10 : ℂ) * h00 - po1a - po2a - c3a - c4a - c5a')
W('      + (3/10 : ℂ) * hpt')
W('  have hq0 : q0 * star q0 = 3/20 := by')
W('    linear_combination (3/10 : ℂ) * h11 - po1c - po2c - c3c - c4c - c5c')
W('      + (3/10 : ℂ) * hqs')
W('  have hpq : p0 * star q0 = 0 := by')
W('    linear_combination (3/10 : ℂ) * h01 - po1b - po2b - c3b - c4b - c5b')
W('      + (3/10 : ℂ) * hst')
W('  have hcon : (9/400 : ℂ) = 0 := by')
W('    linear_combination (q0 * star p0) * hpq - (q0 * star q0) * hp0 - (3/20 : ℂ) * hq0')
W('  norm_num at hcon')

io.open('genblock_a.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('part A: %d lines' % len(L))
