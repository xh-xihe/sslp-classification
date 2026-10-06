"""Part two of `SixQubit/Flip5.lean`: the Bell branch and the anchor rescaling.

Imports the shared renderers from `gen5flip`, which also (re)writes part one.
"""
import io
import os

import gen5flip as F

wrapped = F.wrapped

L = []
w = L.append


def st(t):
    return 'star (%s)' % t


def sclI(vu, va, vb, r, rp):
    return ('sc * (%s * %s + %s * %s) + %s * %s + %s * %s'
            % (st('%s %d' % (vu, 2 * rp + 0)), '%s %d' % (vb, 2 * r + 0),
               st('%s %d' % (vu, 2 * rp + 1)), '%s %d' % (vb, 2 * r + 1),
               st('%s %d' % (va, 2 * rp + 0)), '%s %d' % (vu, 2 * r + 0),
               st('%s %d' % (va, 2 * rp + 1)), '%s %d' % (vu, 2 * r + 1)))


def sclJ(vu, va, vb, s, sp_):
    return ('sc * (%s * %s + %s * %s) + %s * %s + %s * %s'
            % (st('%s %d' % (vu, sp_)), '%s %d' % (vb, s),
               st('%s %d' % (vu, 2 + sp_)), '%s %d' % (vb, 2 + s),
               st('%s %d' % (va, sp_)), '%s %d' % (vu, s),
               st('%s %d' % (va, 2 + sp_)), '%s %d' % (vu, 2 + s)))


UAU = []
for r in range(2):
    for s in range(2):
        trm = []
        for p in range(2):
            for q in range(2):
                trm.append('u %d * star (a %d) * u %d' % (2 * r + p, 2 * q + p, 2 * q + s))
        UAU.append(' + '.join(trm))

w('/-! ## The Bell branch -/')
w('')
w('/-- The entries of `U A† U`. -/')
w('def uau (u a : Fin 4 → ℂ) : Fin 4 → ℂ :=')
for k in range(4):
    pre = '  ![' if k == 0 else '    '
    tail = ',' if k < 3 else ']'
    for ln in wrapped(pre, UAU[k], '      '):
        w(ln)
    L[-1] = L[-1] + tail
w('')
for k in range(4):
    w('@[simp] theorem uau_%d (u a : Fin 4 → ℂ) :' % k)
    for ln in wrapped('    uau u a %d = ' % k, UAU[k], '      '):
        w(ln)
    L[-1] = L[-1] + ' := rfl'
w('')
w("theorem dcj_eq (u : Fin 4 → ℂ) : dcj u = star (dtu u) := by")
w("  simp only [dcj, dtu, star_sub, star_mul']")
w('')
w('/-- The discriminant is the real number `‖u‖⁴ - 4 |det U|²`. -/')
w('theorem dsc_real (u : Fin 4 → ℂ) (hu : nsq u = 1/3) :')
w('    dsc u = ((1/9 - 4 * Complex.normSq (dtu u) : Real) : ℂ) := by')
w('  have h1 : ip u u = ((1/3 : Real) : ℂ) := by rw [ip_self, hu]')
w('  have h2 : dcj u * dtu u = ((Complex.normSq (dtu u) : Real) : ℂ) := by')
w('    rw [dcj_eq]')
w('    linear_combination mul_star (dtu u)')
w('  push_cast at h1 h2')
w('  simp only [dsc]')
w('  push_cast')
w('  linear_combination (ip u u + 1/3) * h1 - 4 * h2')
w('')
w('/-- **The Bell branch.**  When the discriminant vanishes the reduced density')
w('matrix `U U†` of the anchor is `1/6` times the identity. -/')
w('theorem bell_G (u : Fin 4 → ℂ) (hu : nsq u = 1/3)')
w('    (hd : Complex.normSq (dtu u) = 1/36) :')
w('    u 0 * star (u 0) + u 1 * star (u 1) = 1/6 ∧')
w('      u 2 * star (u 2) + u 3 * star (u 3) = 1/6 ∧')
w('      u 0 * star (u 2) + u 1 * star (u 3) = 0 ∧')
w('      u 2 * star (u 0) + u 3 * star (u 1) = 0 := by')
w('  have hcs : u 2 * star (u 0) + u 3 * star (u 1)')
w('      = star (u 0 * star (u 2) + u 1 * star (u 3)) := by')
w("    simp only [star_add, star_mul', star_star]; ring")
w('  have lagC : (u 0 * star (u 0) + u 1 * star (u 1)) * (u 2 * star (u 2) + u 3 * star (u 3))')
w('      - (u 0 * star (u 2) + u 1 * star (u 3)) * (u 2 * star (u 0) + u 3 * star (u 1))')
w('      = dtu u * star (dtu u) := by')
w("    simp only [dtu, star_sub, star_mul']; ring")
w('  rw [hcs] at lagC')
w('  rw [mul_star, mul_star, mul_star, mul_star, mul_star, mul_star] at lagC')
w('  have lagR : (Complex.normSq (u 0) + Complex.normSq (u 1))')
w('      * (Complex.normSq (u 2) + Complex.normSq (u 3))')
w('      - Complex.normSq (u 0 * star (u 2) + u 1 * star (u 3)) = Complex.normSq (dtu u) := by')
w('    exact_mod_cast lagC')
w('  have hsum : Complex.normSq (u 0) + Complex.normSq (u 1) + Complex.normSq (u 2)')
w('      + Complex.normSq (u 3) = 1/3 := by')
w('    simpa only [nsq] using hu')
w('  have hnn := Complex.normSq_nonneg (u 0 * star (u 2) + u 1 * star (u 3))')
w('  have hz : Complex.normSq (u 0 * star (u 2) + u 1 * star (u 3)) = 0 := by')
w('    nlinarith [lagR, hsum, hd, hnn,')
w('      sq_nonneg (Complex.normSq (u 0) + Complex.normSq (u 1) - Complex.normSq (u 2)')
w('        - Complex.normSq (u 3))]')
w('  have hg1 : Complex.normSq (u 0) + Complex.normSq (u 1) = 1/6 := by')
w('    nlinarith [lagR, hsum, hd, hz,')
w('      sq_nonneg (Complex.normSq (u 0) + Complex.normSq (u 1) - Complex.normSq (u 2)')
w('        - Complex.normSq (u 3))]')
w('  have hg2 : Complex.normSq (u 2) + Complex.normSq (u 3) = 1/6 := by linarith')
w('  have hz0 : u 0 * star (u 2) + u 1 * star (u 3) = 0 := Complex.normSq_eq_zero.mp hz')
w('  refine ⟨?_, ?_, hz0, ?_⟩')
w('  · rw [mul_star, mul_star]')
w('    have : ((Complex.normSq (u 0) + Complex.normSq (u 1) : Real) : ℂ) = ((1/6 : Real) : ℂ) := by')
w('      exact_mod_cast congrArg (fun t : Real => (t : ℂ)) hg1')
w('    push_cast at this ⊢')
w('    linear_combination this')
w('  · rw [mul_star, mul_star]')
w('    have : ((Complex.normSq (u 2) + Complex.normSq (u 3) : Real) : ℂ) = ((1/6 : Real) : ℂ) := by')
w('      exact_mod_cast congrArg (fun t : Real => (t : ℂ)) hg2')
w('    push_cast at this ⊢')
w('    linear_combination this')
w('  · rw [hcs, hz0, star_zero]')
w('')
w('/-- In the Bell branch the top vector is determined by the bottom one:')
w('`Bᵢ = -6 U Aᵢ† U`, the coordinate form of `Bᵢ = -Aᵢ†` in Schmidt gauge. -/')
w('theorem bell_step (u a b : Fin 4 → ℂ) (sc : ℂ)')
w('    (g00 : u 0 * star (u 0) + u 1 * star (u 1) = 1/6)')
w('    (g01 : u 0 * star (u 2) + u 1 * star (u 3) = 0)')
w('    (g10 : u 2 * star (u 0) + u 3 * star (u 1) = 0)')
w('    (g11 : u 2 * star (u 2) + u 3 * star (u 3) = 1/6)')
for s in range(2):
    for spp in range(2):
        for ln in wrapped('    (k%d%d : ' % (s, spp), sclJ('u', 'a', 'b', s, spp), '      '):
            w(ln)
        L[-1] = L[-1] + ' = 0)'
w('    : sc * b 0 = -6 * uau u a 0 ∧ sc * b 1 = -6 * uau u a 1 ∧')
w('      sc * b 2 = -6 * uau u a 2 ∧ sc * b 3 = -6 * uau u a 3 := by')
w('  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [uau_0, uau_1, uau_2, uau_3]')
GN = [['g00', 'g01'], ['g10', 'g11']]
for r in range(2):
    for s in range(2):
        parts = ['(6 * u %d) * k%d%d' % (2 * r + p, s, p) for p in range(2)]
        parts += ['(-(6 * sc * b %d)) * %s' % (2 * q + s, GN[r][q]) for q in range(2)]
        for ln in wrapped('  · linear_combination ', ' + '.join(parts), '      '):
            w(ln)
w('')
w('/-- The Bell branch makes the mixed Gram matrix symmetric. -/')
w('theorem bell_sym (u ai aj bi bj : Fin 4 → ℂ) (sc : ℂ)')
w('    (i0 : sc * bi 0 = -6 * uau u ai 0) (i1 : sc * bi 1 = -6 * uau u ai 1)')
w('    (i2 : sc * bi 2 = -6 * uau u ai 2) (i3 : sc * bi 3 = -6 * uau u ai 3)')
w('    (j0 : sc * bj 0 = -6 * uau u aj 0) (j1 : sc * bj 1 = -6 * uau u aj 1)')
w('    (j2 : sc * bj 2 = -6 * uau u aj 2) (j3 : sc * bj 3 = -6 * uau u aj 3) :')
w('    sc * ip ai bj = sc * ip aj bi := by')
w('  simp only [uau_0, uau_1, uau_2, uau_3] at i0 i1 i2 i3 j0 j1 j2 j3')
w('  simp only [ip]')
parts = ['(star (ai %d)) * j%d' % (k, k) for k in range(4)]
parts += ['(-(star (aj %d))) * i%d' % (k, k) for k in range(4)]
for ln in wrapped('  linear_combination ', ' + '.join(parts), '    '):
    w(ln)
w('')
w('/-! ## The anchor rescaling -/')
w('')
w('/-- Tightness in Cauchy--Schwarz makes the two anchors parallel: there is a')
w('unit scalar `sc` with `sc • v = u`.  This is the honest form of the paper`s')
w('rephasing of `|1_L⟩`. -/')
w('theorem anchor_scale (u v a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)')
w('    (hu : nsq u = 1/3) (hv : nsq v = 1/3)')
w('    (hq1 : ip u b1 = 0) (hq2 : ip u b2 = 0) (hq3 : ip u b3 = 0) (hq4 : ip u b4 = 0)')
w('    (hf : ∀ k l : Fin 4, u k * star (u l) + fr a1 a2 a3 a4 k l')
w('            = fr b1 b2 b3 b4 k l + v k * star (v l)) :')
w('    ∃ sc : ℂ, (∀ l : Fin 4, sc * v l = u l) ∧ star sc * sc = 1 := by')
w('  simp only [fr] at hf')
w('  have key : ip u u * ip u u + (ip u a1 * ip a1 u + ip u a2 * ip a2 u + ip u a3 * ip a3 u')
w('        + ip u a4 * ip a4 u')
w('      ) = (ip u b1 * ip b1 u + ip u b2 * ip b2 u + ip u b3 * ip b3 u + ip u b4 * ip b4 u)')
w('        + ip u v * ip v u := by')
w('    simp only [ip]')
w('    linear_combination (star (u 0) * u 0) * hf 0 0 + (star (u 0) * u 1) * hf 0 1')
w('      + (star (u 0) * u 2) * hf 0 2 + (star (u 0) * u 3) * hf 0 3 + (star (u 1) * u 0) * hf 1 0')
w('      + (star (u 1) * u 1) * hf 1 1 + (star (u 1) * u 2) * hf 1 2 + (star (u 1) * u 3) * hf 1 3')
w('      + (star (u 2) * u 0) * hf 2 0 + (star (u 2) * u 1) * hf 2 1 + (star (u 2) * u 2) * hf 2 2')
w('      + (star (u 2) * u 3) * hf 2 3 + (star (u 3) * u 0) * hf 3 0 + (star (u 3) * u 1) * hf 3 1')
w('      + (star (u 3) * u 2) * hf 3 2 + (star (u 3) * u 3) * hf 3 3')
w('  rw [ip_mul_ip u u, ip_mul_ip u a1, ip_mul_ip u a2, ip_mul_ip u a3, ip_mul_ip u a4,')
w('    ip_mul_ip u b1, ip_mul_ip u b2, ip_mul_ip u b3, ip_mul_ip u b4, ip_mul_ip u v] at key')
w('  have keyR : Complex.normSq (ip u u) + (Complex.normSq (ip u a1) + Complex.normSq (ip u a2)')
w('        + Complex.normSq (ip u a3) + Complex.normSq (ip u a4)')
w('      ) = (Complex.normSq (ip u b1) + Complex.normSq (ip u b2) + Complex.normSq (ip u b3)')
w('        + Complex.normSq (ip u b4)) + Complex.normSq (ip u v) := by')
w('    exact_mod_cast key')
w('  have huu : Complex.normSq (ip u u) = 1/9 := by')
w('    rw [ip_self, hu, Complex.normSq_ofReal]; norm_num')
w('  have hz1 : Complex.normSq (ip u b1) = 0 := by rw [hq1]; simp')
w('  have hz2 : Complex.normSq (ip u b2) = 0 := by rw [hq2]; simp')
w('  have hz3 : Complex.normSq (ip u b3) = 0 := by rw [hq3]; simp')
w('  have hz4 : Complex.normSq (ip u b4) = 0 := by rw [hq4]; simp')
w('  have hcs := cs u v')
w('  rw [hu, hv] at hcs')
w('  have hnn1 := Complex.normSq_nonneg (ip u a1)')
w('  have hnn2 := Complex.normSq_nonneg (ip u a2)')
w('  have hnn3 := Complex.normSq_nonneg (ip u a3)')
w('  have hnn4 := Complex.normSq_nonneg (ip u a4)')
w('  have hnv : Complex.normSq (ip u v) = 1/9 := by linarith')
w('  have huv : nsq u * nsq v ≤ Complex.normSq (ip u v) := by rw [hu, hv, hnv]; norm_num')
w('  obtain ⟨p0, p1, p2, p3⟩ := par huv')
w('  have hiu : ip u u = ((1/3 : Real) : ℂ) := by rw [ip_self, hu]')
w('  rw [hiu] at p0 p1 p2 p3')
w('  have hmu : ip u v * star (ip u v) = ((1/9 : Real) : ℂ) := by rw [mul_star, hnv]')
w('  push_cast at p0 p1 p2 p3 hmu')
for k in range(4):
    w('  have s%d : 3 * star (ip u v) * v %d = u %d := by' % (k, k, k))
    w('    linear_combination (9 * star (ip u v)) * p%d + (9 * u %d) * hmu' % (k, k))
w('  refine ⟨3 * star (ip u v), ?_, ?_⟩')
w('  · intro l')
w('    fin_cases l')
w('    exacts [s0, s1, s2, s3]')
w("  · simp only [star_mul', star_star, star_ofNat]")
w('    linear_combination 9 * hmu')
w('')

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
OUT = os.path.join(ROOT, 'build_zh', 'flip5_part2.lean')
io.open(OUT, 'w', encoding='utf-8', newline='\n').write('\n'.join(L) + '\n')
print('flip5 part 2: %d lines -> %s' % (len(L), OUT))
