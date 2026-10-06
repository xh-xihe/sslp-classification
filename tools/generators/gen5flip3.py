"""Part three of `SixQubit/Flip5.lean`: the per-index reduction of the eight
weight-two flip rows to the intertwiner equations, and the assembled
contradiction `core`.
"""
import io
import os

import gen5flip as F
import gen5flip2 as F2

wrapped = F.wrapped
sclI, sclJ = F2.sclI, F2.sclJ

L = []
w = L.append


def st(t):
    return 'star (%s)' % t


def rawI(vu, vv, va, vb, r, rp):
    return ('%s * %s + %s * %s + %s * %s + %s * %s'
            % (st('%s %d' % (vu, 2 * rp + 0)), '%s %d' % (vb, 2 * r + 0),
               st('%s %d' % (vu, 2 * rp + 1)), '%s %d' % (vb, 2 * r + 1),
               st('%s %d' % (va, 2 * rp + 0)), '%s %d' % (vv, 2 * r + 0),
               st('%s %d' % (va, 2 * rp + 1)), '%s %d' % (vv, 2 * r + 1)))


def rawJ(vu, vv, va, vb, s, sp_):
    return ('%s * %s + %s * %s + %s * %s + %s * %s'
            % (st('%s %d' % (vu, sp_)), '%s %d' % (vb, s),
               st('%s %d' % (vu, 2 + sp_)), '%s %d' % (vb, 2 + s),
               st('%s %d' % (va, sp_)), '%s %d' % (vv, s),
               st('%s %d' % (va, 2 + sp_)), '%s %d' % (vv, 2 + s)))


def cnjI(vu, va, vb, r, rp):
    return ('star sc * (%s * %s + %s * %s) + %s * %s + %s * %s'
            % ('%s %d' % (vu, 2 * rp + 0), st('%s %d' % (vb, 2 * r + 0)),
               '%s %d' % (vu, 2 * rp + 1), st('%s %d' % (vb, 2 * r + 1)),
               '%s %d' % (va, 2 * rp + 0), st('%s %d' % (vu, 2 * r + 0)),
               '%s %d' % (va, 2 * rp + 1), st('%s %d' % (vu, 2 * r + 1))))


def cnjJ(vu, va, vb, s, sp_):
    return ('star sc * (%s * %s + %s * %s) + %s * %s + %s * %s'
            % ('%s %d' % (vu, sp_), st('%s %d' % (vb, s)),
               '%s %d' % (vu, 2 + sp_), st('%s %d' % (vb, 2 + s)),
               '%s %d' % (va, sp_), st('%s %d' % (vu, s)),
               '%s %d' % (va, 2 + sp_), st('%s %d' % (vu, 2 + s))))


# ------------------------------------------------------------- flip_reduce
w('/-! ## From the flip rows to the intertwiner -/')
w('')
w('/-- **The eight weight-two flip rows of one active coordinate.**  After the')
w('anchor rescaling they say `B U† + U A† = 0` and `U† B + A† U = 0`; eliminating')
w('between the two gives the intertwining relations `G A = A H` and `G B = B H`.')
w('The four `U† B + A† U` entries are returned as well, for the Bell branch. -/')
w('theorem flip_reduce (u v a b : Fin 4 → ℂ) (sc : ℂ)')
w('    (hsv : ∀ l : Fin 4, sc * v l = u l) (hsc : sc ≠ 0)')
for r in range(2):
    for rp in range(2):
        for ln in wrapped('    (i%d%d : ' % (r, rp), rawI('u', 'v', 'a', 'b', r, rp), '      '):
            w(ln)
        L[-1] = L[-1] + ' = 0)'
for s in range(2):
    for spp in range(2):
        for ln in wrapped('    (j%d%d : ' % (s, spp), rawJ('u', 'v', 'a', 'b', s, spp), '      '):
            w(ln)
        L[-1] = L[-1] + ' = 0)'
w('    : (cin u a 0 = 0 ∧ cin u a 1 = 0 ∧ cin u a 2 = 0 ∧ cin u a 3 = 0) ∧')
w('      (cin u b 0 = 0 ∧ cin u b 1 = 0 ∧ cin u b 2 = 0 ∧ cin u b 3 = 0) ∧')
for s in range(2):
    for spp in range(2):
        pre = '      (' if (s, spp) == (0, 0) else '        '
        for ln in wrapped(pre, sclJ('u', 'a', 'b', s, spp), '          '):
            w(ln)
        L[-1] = L[-1] + (' = 0 ∧' if (s, spp) != (1, 1) else ' = 0) := by')
w('  have cancel : ∀ z : ℂ, sc * z = 0 → z = 0 := by')
w('    intro z hz')
w('    rcases mul_eq_zero.mp hz with h | h')
w('    · exact absurd h hsc')
w('    · exact h')
for l in range(4):
    w('  have s%d := hsv %d' % (l, l))
for r in range(2):
    for rp in range(2):
        w('  have p%d%d : %s' % (r, rp, ''))
        L.pop()
        for ln in wrapped('  have p%d%d : ' % (r, rp), sclI('u', 'a', 'b', r, rp), '      '):
            w(ln)
        L[-1] = L[-1] + ' = 0 := by'
        w('    linear_combination sc * i%d%d - (star (a %d)) * s%d - (star (a %d)) * s%d'
          % (r, rp, 2 * rp + 0, 2 * r + 0, 2 * rp + 1, 2 * r + 1))
for s in range(2):
    for spp in range(2):
        for ln in wrapped('  have q%d%d : ' % (s, spp), sclJ('u', 'a', 'b', s, spp), '      '):
            w(ln)
        L[-1] = L[-1] + ' = 0 := by'
        w('    linear_combination sc * j%d%d - (star (a %d)) * s%d - (star (a %d)) * s%d'
          % (s, spp, spp, s, 2 + spp, 2 + s))
for r in range(2):
    for rp in range(2):
        for ln in wrapped('  have pc%d%d : ' % (r, rp), cnjI('u', 'a', 'b', r, rp), '      '):
            w(ln)
        L[-1] = L[-1] + ' = 0 := by'
        w('    have h := congrArg star p%d%d' % (r, rp))
        w("    simp only [star_add, star_mul', star_star, star_zero] at h")
        w('    linear_combination h')
for s in range(2):
    for spp in range(2):
        for ln in wrapped('  have qc%d%d : ' % (s, spp), cnjJ('u', 'a', 'b', s, spp), '      '):
            w(ln)
        L[-1] = L[-1] + ' = 0 := by'
        w('    have h := congrArg star q%d%d' % (s, spp))
        w("    simp only [star_add, star_mul', star_star, star_zero] at h")
        w('    linear_combination h')
for r in range(2):
    for s in range(2):
        k = 2 * r + s
        w('  have ca%d : cin u a %d = 0 := by' % (k, k))
        w('    simp only [cin_%d]' % k)
        parts = ['(u %d) * qc%d%d' % (2 * r + p, p, s) for p in range(2)]
        parts += ['(-(u %d)) * pc%d%d' % (2 * p + s, p, r) for p in range(2)]
        for ln in wrapped('    linear_combination ', ' + '.join(parts), '      '):
            w(ln)
for r in range(2):
    for s in range(2):
        k = 2 * r + s
        w('  have cbs%d : sc * cin u b %d = 0 := by' % (k, k))
        w('    simp only [cin_%d]' % k)
        parts = ['(u %d) * q%d%d' % (2 * r + p, s, p) for p in range(2)]
        parts += ['(-(u %d)) * p%d%d' % (2 * p + s, r, p) for p in range(2)]
        for ln in wrapped('    linear_combination ', ' + '.join(parts), '      '):
            w(ln)
        w('  have cb%d : cin u b %d = 0 := cancel _ cbs%d' % (k, k, k))
w('  exact ⟨⟨ca0, ca1, ca2, ca3⟩, ⟨cb0, cb1, cb2, cb3⟩, q00, q01, q10, q11⟩')
w('')

# --------------------------------------------------------- non-vanishing
w('/-! ## Non-vanishing in the line branch -/')
w('')
w('/-- A nonzero vector of the flip-kernel line has a nonzero `τ`. -/')
w('theorem tau_ne (u x : Fin 4 → ℂ) (hd : dsc u ≠ 0) (hx : nsq x = 1/6)')
w('    (e0 : dsc u * x 0 = tau u x * ww u 0) (e1 : dsc u * x 1 = tau u x * ww u 1)')
w('    (e2 : dsc u * x 2 = tau u x * ww u 2) (e3 : dsc u * x 3 = tau u x * ww u 3) :')
w('    tau u x ≠ 0 := by')
w('  intro h')
w('  rw [h, zero_mul] at e0 e1 e2 e3')
for k in range(4):
    w('  have z%d : x %d = 0 := by' % (k, k))
    w('    rcases mul_eq_zero.mp e%d with h\' | h\'' % k)
    w('    · exact absurd h\' hd')
    w('    · exact h\'')
w('  rw [nsq, z0, z1, z2, z3] at hx')
w('  norm_num at hx')
w('')
w('/-- The projection of a top vector onto the line is nonzero. -/')
w('theorem ipw_ne (u x : Fin 4 → ℂ) (hd : dsc u ≠ 0) (hx : nsq x = 1/6)')
w('    (h : dsc u * ip x x = star (tau u x) * ip (ww u) x) : ip (ww u) x ≠ 0 := by')
w('  intro hz')
w('  rw [hz, mul_zero, ip_self, hx] at h')
w('  rcases mul_eq_zero.mp h with h\' | h\'')
w('  · exact hd h\'')
w('  · norm_num at h\'')
w('')

# ------------------------------------------------------------------- core
PR = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
w('/-! ## The assembled contradiction -/')
w('')
w('/-- **Orbit 5, the flip-kernel dichotomy.**  Ten vectors of `ℂ⁴` with the orbit-5')
w('norms, the anchor orthogonalities, a common marginal on the free pair, the six')
w('two-flip relations and the eight weight-two flip rows of each active coordinate')
w('cannot exist.  If `dsc u = 0` the flip rows give `Bᵢ = -6 U Aᵢ† U`, hence the')
w('twelve cross orthogonalities and `Trace5.bell_contradiction`; otherwise they')
w('confine every `aᵢ` and `bᵢ` to one line and the two-flip relations become the')
w('odd triangle of `Triangle.contradiction`. -/')
w('theorem core (u v a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)')
w('    (hu : nsq u = 1/3) (hv : nsq v = 1/3)')
w('    (ha1 : nsq a1 = 1/6) (ha2 : nsq a2 = 1/6) (ha3 : nsq a3 = 1/6) (ha4 : nsq a4 = 1/6)')
w('    (hb1 : nsq b1 = 1/6) (hb2 : nsq b2 = 1/6) (hb3 : nsq b3 = 1/6) (hb4 : nsq b4 = 1/6)')
w('    (hq1 : ip u b1 = 0) (hq2 : ip u b2 = 0) (hq3 : ip u b3 = 0) (hq4 : ip u b4 = 0)')
w('    (hf : ∀ k l : Fin 4, u k * star (u l) + fr a1 a2 a3 a4 k l')
w('            = fr b1 b2 b3 b4 k l + v k * star (v l))')
for (i, j) in PR:
    w('    (x%d%d : ip a%d b%d + ip a%d b%d = 0)' % (i, j, i, j, j, i))
for i in range(1, 5):
    for r in range(2):
        for rp in range(2):
            for ln in wrapped('    (m%d%d%d : ' % (i, r, rp),
                              rawI('u', 'v', 'a%d' % i, 'b%d' % i, r, rp), '      '):
                w(ln)
            L[-1] = L[-1] + ' = 0)'
    for s in range(2):
        for spp in range(2):
            for ln in wrapped('    (n%d%d%d : ' % (i, s, spp),
                              rawJ('u', 'v', 'a%d' % i, 'b%d' % i, s, spp), '      '):
                w(ln)
            L[-1] = L[-1] + ' = 0)'
w('    : False := by')
w('  obtain ⟨hp1, hp2, hp3, hp4, hfr⟩ :=')
w('    cs_tight u v a1 a2 a3 a4 b1 b2 b3 b4 hu hv hq1 hq2 hq3 hq4 hf')
w('  obtain ⟨sc, hsv, hss⟩ :=')
w('    anchor_scale u v a1 a2 a3 a4 b1 b2 b3 b4 hu hv hq1 hq2 hq3 hq4 hf')
w('  have hsc : sc ≠ 0 := by')
w('    intro h')
w('    rw [h, mul_zero] at hss')
w('    exact zero_ne_one hss')
for i in range(1, 5):
    w('  obtain ⟨⟨ca%d0, ca%d1, ca%d2, ca%d3⟩, ⟨cb%d0, cb%d1, cb%d2, cb%d3⟩,'
      % (i, i, i, i, i, i, i, i))
    w('    k%d00, k%d01, k%d10, k%d11⟩ :=' % (i, i, i, i))
    w('    flip_reduce u v a%d b%d sc hsv hsc m%d00 m%d01 m%d10 m%d11 n%d00 n%d01 n%d10 n%d11'
      % (i, i, i, i, i, i, i, i, i, i))
w('  by_cases hcase : Complex.normSq (dtu u) = 1/36')
w('  · obtain ⟨g00, g11, g01, g10⟩ := bell_G u hu hcase')
for i in range(1, 5):
    w('    obtain ⟨B%d0, B%d1, B%d2, B%d3⟩ :=' % (i, i, i, i))
    w('      bell_step u a%d b%d sc g00 g01 g10 g11 k%d00 k%d01 k%d10 k%d11'
      % (i, i, i, i, i, i))
for (i, j) in PR:
    w('    have y%d%d : ip a%d b%d = ip a%d b%d :=' % (i, j, i, j, j, i))
    w('      mul_left_cancel₀ hsc (bell_sym u a%d a%d b%d b%d sc B%d0 B%d1 B%d2 B%d3 B%d0 B%d1 B%d2 B%d3)'
      % (i, j, i, j, i, i, i, i, j, j, j, j))
for (i, j) in PR:
    w('    have z%d%d : ip a%d b%d = 0 := by linear_combination (1/2) * x%d%d + (1/2) * y%d%d'
      % (i, j, i, j, i, j, i, j))
    w('    have z%d%d : ip a%d b%d = 0 := by linear_combination (1/2) * x%d%d - (1/2) * y%d%d'
      % (j, i, j, i, i, j, i, j))
w('    exact bell_contradiction u a1 a2 a3 a4 b1 b2 b3 b4 hu ha1 ha2 ha3 ha4 hb1 hb2 hb3 hb4')
w('      hp1 hp2 hp3 hp4 hfr z12 z13 z14 z21 z23 z24 z31 z32 z34 z41 z42 z43')
w('  · have hdsc : dsc u ≠ 0 := by')
w('      rw [dsc_real u hu]')
w('      intro h')
w('      apply hcase')
w('      have hr : (1/9 - 4 * Complex.normSq (dtu u) : Real) = 0 := by exact_mod_cast h')
w('      linarith')
for i in [1, 2, 3]:
    w('    obtain ⟨la%d0, la%d1, la%d2, la%d3⟩ := line_key u a%d ca%d0 ca%d1 ca%d2 ca%d3 hp%d'
      % (i, i, i, i, i, i, i, i, i, i))
    w('    obtain ⟨lb%d0, lb%d1, lb%d2, lb%d3⟩ := line_key u b%d cb%d0 cb%d1 cb%d2 cb%d3 hq%d'
      % (i, i, i, i, i, i, i, i, i, i))
for i in [1, 2, 3]:
    for j in [1, 2, 3]:
        w('    have w%d%d := line_ip u a%d b%d la%d0 la%d1 la%d2 la%d3' % (i, j, i, j, i, i, i, i))
for j in [1, 2, 3]:
    w('    have d%d := line_ip u b%d b%d lb%d0 lb%d1 lb%d2 lb%d3' % (j, j, j, j, j, j, j))
for (i, j) in [(1, 2), (1, 3), (2, 3)]:
    w('    have t%d%d : star (tau u a%d) * ip (ww u) b%d + star (tau u a%d) * ip (ww u) b%d = 0 := by'
      % (i, j, i, j, j, i))
    w('      linear_combination (-1 : ℂ) * w%d%d + (-1 : ℂ) * w%d%d + dsc u * x%d%d'
      % (i, j, j, i, i, j))
for i in [1, 2, 3]:
    w('    have ta%d : tau u a%d ≠ 0 := tau_ne u a%d hdsc ha%d la%d0 la%d1 la%d2 la%d3'
      % (i, i, i, i, i, i, i, i))
for j in [1, 2]:
    w('    have tb%d : ip (ww u) b%d ≠ 0 := ipw_ne u b%d hdsc hb%d d%d' % (j, j, j, j, j))
w('    exact Triangle.contradiction t12 t13 t23 (star_ne_zero.mpr ta3) tb1 tb2')
w('')

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
OUT = os.path.join(ROOT, 'build_zh', 'flip5_part3.lean')
io.open(OUT, 'w', encoding='utf-8', newline='\n').write('\n'.join(L) + '\n')
print('flip5 part 3: %d lines -> %s' % (len(L), OUT))

full = []
for nm in ['flip5_part1.lean', 'flip5_part2.lean', 'flip5_part3.lean']:
    full.append(io.open(os.path.join(ROOT, 'build_zh', nm), encoding='utf-8').read().rstrip('\n'))
txt = '\n\n'.join(full) + '\n\nend\n\nend SixQubit.Flip5\n'
io.open(os.path.join(ROOT, 'SixQubit', 'Flip5.lean'), 'w', encoding='utf-8',
        newline='\n').write(txt)
print('SixQubit/Flip5.lean: %d lines' % txt.count('\n'))
