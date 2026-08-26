"""perp_v and finish for orbit 29."""
import io
NL = chr(10)
VERT = [3, 5, 6, 7]
FAM = {3: (4, 5, 6), 5: (2, 3, 6), 6: (1, 3, 5), 7: (1, 2, 4)}
TFR = {3: (0, 1, 2), 5: (0, 1, 4), 6: (0, 2, 4), 7: (1, 2, 4)}
L = []
W = L.append
W('/-- Every bottom pair is orthogonal to the anchor direction.  Its two top')
W('neighbours have probabilities summing to at least `1/4`, so at least one of')
W('them is nonzero and carries the transfer. -/')
W('theorem perp_v (c0 c1 a0 a1 b0 b1 v0 v1 : ℂ) (Qa Qb : Real)')
W('    (hQ : 1/4 ≤ Qa + Qb)')
W('    (na : a0 * star a0 + a1 * star a1 = (Qa : ℂ))')
W('    (nb : b0 * star b0 + b1 * star b1 = (Qb : ℂ))')
W('    (pa : star c0 * a0 + star c1 * a1 = 0)')
W('    (pb : star c0 * b0 + star c1 * b1 = 0)')
W('    (da : a0 * v1 - v0 * a1 = 0) (db : b0 * v1 - v0 * b1 = 0)')
W('    : star c0 * v0 + star c1 * v1 = 0 := by')
W('  by_cases hA : Qa = 0')
W('  · have hB : Qb ≠ 0 := by intro h; rw [hA, h] at hQ; norm_num at hQ')
W('    exact perp_par c0 c1 b0 b1 v0 v1 _ pb db nb (by simpa using hB)')
W('  · exact perp_par c0 c1 a0 a1 v0 v1 _ pa da na (by simpa using hA)')
W('')
W('/-- The closing argument, once an anchor top pair `v` is in hand. -/')
W('theorem finish (v0 v1 : ℂ) (Qv : Real)')
W('    (hv : v0 * star v0 + v1 * star v1 = (Qv : ℂ)) (hQv : Qv ≠ 0)')
for m in range(1, 8):
    W('    (a%d b%d : ℂ)' % (m, m))
for n in VERT:
    W('    (S%d T%d : ℂ) (Q%d : Real)' % (n, n, n))
for n in (0, 1, 2, 4):
    W('    (s%d t%d : ℂ)' % (n, n))
W('    (n7 : a7 * star a7 + b7 * star b7 = 1/4)')
for n in VERT:
    W('    (nq%d : S%d * star S%d + T%d * star T%d = (Q%d : ℂ))' % (n, n, n, n, n, n))
W('    (qsum : Q3 + Q5 + Q6 + Q7 = 3/4)')
W('    (esum : (S3 * star S3 - T3 * star T3) + (S5 * star S5 - T5 * star T5)')
W('      + (S6 * star S6 - T6 * star T6) + (S7 * star S7 - T7 * star T7) = 0)')
for n in VERT:
    W('    (d%d : S%d * v1 - v0 * T%d = 0)' % (n, n, n))
for m in range(1, 7):
    W('    (p%d : star a%d * v0 + star b%d * v1 = 0)' % (m, m, m))
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
W('    : False := by')
W('  have hQvC : ((Qv : Real) : ℂ) ≠ 0 := by simpa using hQv')
W('  have hu : star (-star v1) * v0 + star (star v0) * v1 = 0 := by')
W('    simp only [star_neg, star_star]; ring')
for m in range(1, 7):
    W('  have cu%d : a%d * (star v0) - (-star v1) * b%d = 0 :=' % (m, m, m))
    W('    par_of_perp a%d b%d (-star v1) (star v0) v0 v1 _ p%d hu hv hQvC' % (m, m, m))
for n in VERT:
    i, j, k = FAM[n]
    x, y, z = TFR[n]
    W('  have pv%d : star (-star v1) * S%d + star (star v0) * T%d = 0 := by' % (n, n, n))
    W('    simp only [star_neg, star_star]; linear_combination -d%d' % n)
    W('  obtain ⟨k%dS, k%dT⟩ := endgame (-star v1) (star v0)' % (n, n))
    W('    a%d b%d a%d b%d a%d b%d a7 b7' % (i, i, j, j, k, k))
    W('    s%d t%d s%d t%d s%d t%d S%d T%d' % (x, x, y, y, z, z, n, n))
    W('    cu%d cu%d cu%d n7 pv%d E%dA E%dB E%dC E%dD' % (i, j, k, n, n, n, n, n))
W('  by_cases hv1 : v1 = 0')
W('  · have hv0 : v0 ≠ 0 := by')
W('      intro h')
W('      apply hQv')
W('      have hz : ((Qv : Real) : ℂ) = 0 := by rw [← hv, h, hv1]; ring')
W('      exact_mod_cast hz')
for n in VERT:
    W('    have z%d : T%d = 0 := by' % (n, n))
    W('      have hk := k%dT' % n)
    W('      simp only [star_star] at hk')
    W('      rcases mul_eq_zero.mp hk with h | h')
    W('      · exact absurd h hv0')
    W('      · exact h')
W('    have hbad : ((3/4 : Real) : ℂ) = 0 := by')
W('      rw [← qsum]; push_cast')
W('      linear_combination esum - nq3 - nq5 - nq6 - nq7')
W('        + (2 * star T3) * z3 + (2 * star T5) * z5')
W('        + (2 * star T6) * z6 + (2 * star T7) * z7')
W('    norm_num at hbad')
for idx, n in enumerate(VERT):
    W('  %s have z%d : S%d = 0 := by' % ('·' if idx == 0 else ' ', n, n))
    W('      have hk := k%dS' % n)
    W('      simp only [star_neg, star_star] at hk')
    W('      rcases mul_eq_zero.mp hk with h | h')
    W('      · exact absurd (neg_eq_zero.mp h) hv1')
    W('      · exact h')
W('    have hbad : ((3/4 : Real) : ℂ) = 0 := by')
W('      rw [← qsum]; push_cast')
W('      linear_combination -esum - nq3 - nq5 - nq6 - nq7')
W('        + (2 * star S3) * z3 + (2 * star S5) * z5')
W('        + (2 * star S6) * z6 + (2 * star S7) * z7')
W('    norm_num at hbad')
W('')
io.open('gen29pf_out.txt', 'w', encoding='utf-8').write(NL.join(L) + NL)
print('perp_v + finish: %d lines' % len(L))
