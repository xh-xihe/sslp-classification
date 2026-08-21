"""Emit the long, mechanically generated part of `SixQubit/Trace5.lean`.

The declarations produced, in order:

* `fr`                   -- one entry of the frame operator of a four-vector family;
* `fr_diag`              -- the diagonal entries of the frame operator are the column masses;
* `cs_tight`             -- sandwiching the marginal equality in the anchor `u`;
* `frame_swap`           -- the Gram sum of the bottom family equals the mixed Gram sum;
* `frame_idem`           -- `Sum_t R k t * conj (R k t) = (1/6) R k k` for an orthogonal family;
* `frame_kernel`         -- the frame operator annihilates a vector orthogonal to the family;
* `mass_le`              -- `e^2 <= e/6` forces `e <= 1/6`;
* `orthogonal_overflow`  -- five pairwise orthogonal nonzero vectors do not fit in `C^4`;
* `bell_contradiction`   -- the trace contradiction.

Every sum over the four coordinates of `C^4`, and every sum over the sixteen
entries of the marginal, is written out here rather than by hand.
"""

IDX = [0, 1, 2, 3]
AV = ['a1', 'a2', 'a3', 'a4']
BV = ['b1', 'b2', 'b3', 'b4']
PAIRS = [(i, j) for i in range(1, 5) for j in range(1, 5) if i != j]

L = []
w = L.append


def frsum(vs, k, l):
    return ' + '.join('%s %s * star (%s %s)' % (v, k, v, l) for v in vs)


def sum_ip(vs, ws):
    return ' + '.join('ip %s %s * ip %s %s' % (v, x, x, v) for v in vs for x in ws)


def sum_nsq(vs, ws):
    return ' + '.join('Complex.normSq (ip %s %s)' % (v, x) for v in vs for x in ws)


def mass(k):
    return ' + '.join('Complex.normSq (%s %s)' % (a, k) for a in AV)


def frdiag(k, t):
    return 'fr a1 a2 a3 a4 %s %s' % (k, t)


def wrap(prefix, body, cont, sep=' + ', tail=''):
    """emit `prefix body tail`, broken over lines at `sep` boundaries"""
    parts = body.split(sep)
    line = prefix + parts[0]
    for p in parts[1:]:
        piece = sep.strip() + ' ' + p
        if len(line) + len(piece) + 1 > 100:
            w(line)
            line = cont + piece
        else:
            line = line + ' ' + piece
    w(line + tail)


def orth_hyps(indent='    '):
    for (i, j) in PAIRS:
        w('%s(ho%d%d : ip a%d a%d = 0)' % (indent, i, j, i, j))


HOARGS = ' '.join('ho%d%d' % (i, j) for (i, j) in PAIRS)

# ------------------------------------------------------------- frame operator
w('/-! ## The frame operator -/')
w('')
w('/-- One entry of the frame operator `R = Σᵢ aᵢ aᵢ†` of a four-vector family. -/')
w('def fr (a1 a2 a3 a4 : Fin 4 → ℂ) (k l : Fin 4) : ℂ :=')
w('  ' + frsum(AV, 'k', 'l'))
w('')
w('/-- The diagonal entries of the frame operator are the real column masses. -/')
w('theorem fr_diag (a1 a2 a3 a4 : Fin 4 → ℂ) (k : Fin 4) :')
wrap('    fr a1 a2 a3 a4 k k = ((', mass('k'), '      ', tail=' : Real) : ℂ) := by')
w('  simp only [fr]')
w('  push_cast [← SixQubit.star_mul_self]')
w('  ring')
w('')
# ---------------------------------------------------------------- tightness
w('/-! ## The tightness step -/')
w('')
w('/-- **Tightness.**  If the two marginals on the free pair agree and the anchor')
w('`u` is orthogonal to all four top vectors, then `u` is orthogonal to all four')
w('bottom vectors as well, and the two anchors contribute the same rank-one piece,')
w('so the two frame operators agree. -/')
w('theorem cs_tight (u v a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)')
w('    (hu : nsq u = 1/3) (hv : nsq v = 1/3)')
w('    (hq1 : ip u b1 = 0) (hq2 : ip u b2 = 0) (hq3 : ip u b3 = 0) (hq4 : ip u b4 = 0)')
w('    (hf : ∀ k l : Fin 4, u k * star (u l) + fr a1 a2 a3 a4 k l')
w('            = fr b1 b2 b3 b4 k l + v k * star (v l)) :')
w('    ip u a1 = 0 ∧ ip u a2 = 0 ∧ ip u a3 = 0 ∧ ip u a4 = 0 ∧')
w('      ∀ k l : Fin 4, fr a1 a2 a3 a4 k l = fr b1 b2 b3 b4 k l := by')
w('  simp only [fr] at hf')
wrap('  have key : ip u u * ip u u + (', sum_ip(['u'], AV), '        ')
wrap('      ) = (', sum_ip(['u'], BV), '        ', tail=') + ip u v * ip v u := by')
w('    simp only [ip]')
wrap('    linear_combination ',
     ' + '.join('(star (u %d) * u %d) * hf %d %d' % (k, l, k, l) for k in IDX for l in IDX),
     '      ')
w('  rw [ip_mul_ip u u, ip_mul_ip u a1, ip_mul_ip u a2, ip_mul_ip u a3, ip_mul_ip u a4,')
w('    ip_mul_ip u b1, ip_mul_ip u b2, ip_mul_ip u b3, ip_mul_ip u b4, ip_mul_ip u v] at key')
wrap('  have keyR : Complex.normSq (ip u u) + (', sum_nsq(['u'], AV), '        ')
wrap('      ) = (', sum_nsq(['u'], BV), '        ',
     tail=') + Complex.normSq (ip u v) := by')
w('    exact_mod_cast key')
w('  have huu : Complex.normSq (ip u u) = 1/9 := by')
w('    rw [ip_self, hu, Complex.normSq_ofReal]; norm_num')
for i in range(1, 5):
    w('  have hz%d : Complex.normSq (ip u b%d) = 0 := by rw [hq%d]; simp' % (i, i, i))
w('  have hcs := cs u v')
w('  rw [hu, hv] at hcs')
for i in range(1, 5):
    w('  have hnn%d := Complex.normSq_nonneg (ip u a%d)' % (i, i))
for i in range(1, 5):
    w('  have hp%d : ip u a%d = 0 := Complex.normSq_eq_zero.mp (by linarith)' % (i, i))
w('  have hnv : Complex.normSq (ip u v) = 1/9 := by linarith')
w('  have huv : nsq u * nsq v ≤ Complex.normSq (ip u v) := by rw [hu, hv, hnv]; norm_num')
w('  obtain ⟨w0, w1, w2, w3⟩ := par huv')
w('  have hiu : ip u u = ((1/3 : Real) : ℂ) := by rw [ip_self, hu]')
w('  rw [hiu] at w0 w1 w2 w3')
w('  have hmu : ip u v * star (ip u v) = ((1/9 : Real) : ℂ) := by rw [mul_star, hnv]')
w('  have hthird : star (((1/3 : Real)) : ℂ) = ((1/3 : Real) : ℂ) := by simp')
w('  have hvl : ∀ l : Fin 4, ((1/3 : Real) : ℂ) * v l = u l * ip u v := by')
w('    intro l; fin_cases l')
w('    exacts [w0, w1, w2, w3]')
w('  have hvv : ∀ k l : Fin 4, v k * star (v l) = u k * star (u l) := by')
w('    intro k l')
w('    have e1 := hvl k')
w('    have e2 := congrArg star (hvl l)')
w("    rw [star_mul', hthird, star_mul'] at e2")
w('    push_cast at e1 e2 hmu')
w('    linear_combination (3 * star (v l)) * e1 + (9 * u k * ip u v) * e2')
w('      + (9 * u k * star (u l)) * hmu')
w('  refine ⟨hp1, hp2, hp3, hp4, ?_⟩')
w('  intro k l')
w('  simp only [fr]')
w('  linear_combination hf k l + hvv k l')
w('')
# --------------------------------------------------------------- frame swap
w('/-! ## The trace identities -/')
w('')
w('/-- Equality of the two frame operators transports the Gram sum of the bottom')
w('family to the mixed Gram sum. -/')
w('theorem frame_swap (a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)')
w('    (hf : ∀ k l : Fin 4, fr a1 a2 a3 a4 k l = fr b1 b2 b3 b4 k l) :')
wrap('    (', sum_ip(AV, AV), '      ')
wrap('      ) = (', sum_ip(AV, BV), '      ', tail=') := by')
w('  simp only [fr] at hf')
w('  simp only [ip]')
lcs = []
for k in IDX:
    for l in IDX:
        coeff = ' + '.join('star (%s %d) * %s %d' % (a, k, a, l) for a in AV)
        lcs.append('(%s) * hf %d %d' % (coeff, k, l))
wrap('  linear_combination ', ' + '.join(lcs), '    ')
w('')
w('/-- For a pairwise orthogonal family of squared norm `1/6` the frame operator')
w('satisfies `R² = R/6`; this is the `k`-th diagonal entry of that identity. -/')
w('theorem frame_idem (a1 a2 a3 a4 : Fin 4 → ℂ)')
orth_hyps()
w('    (hs1 : ip a1 a1 = (1/6 : ℂ)) (hs2 : ip a2 a2 = (1/6 : ℂ))')
w('    (hs3 : ip a3 a3 = (1/6 : ℂ)) (hs4 : ip a4 a4 = (1/6 : ℂ)) (k : Fin 4) :')
wrap('    ', ' + '.join('%s * star (%s)' % (frdiag('k', t), frdiag('k', t)) for t in IDX),
     '      ')
wrap('      = (1/6 : ℂ) * ((', mass('k'), '        ', tail=' : Real) : ℂ) := by')
w('  simp only [ip] at ' + HOARGS)
w('  simp only [ip] at hs1 hs2 hs3 hs4')
w("  simp only [fr, star_add, star_mul', star_star]")
w('  push_cast [← SixQubit.star_mul_self]')
terms = []
for i, ai in enumerate(AV):
    for j, aj in enumerate(AV):
        c = '(%s k * star (%s k))' % (ai, aj)
        terms.append('%s * %s' % (c, ('hs%d' % (i + 1)) if i == j
                                  else ('ho%d%d' % (i + 1, j + 1))))
wrap('  linear_combination ', ' + '.join(terms), '    ')
w('')
w('/-- The frame operator annihilates every vector orthogonal to the family. -/')
w('theorem frame_kernel (u a1 a2 a3 a4 : Fin 4 → ℂ)')
w('    (hk1 : ip a1 u = 0) (hk2 : ip a2 u = 0) (hk3 : ip a3 u = 0) (hk4 : ip a4 u = 0)')
w('    (k : Fin 4) :')
wrap('    ', ' + '.join('%s * u %d' % (frdiag('k', t), t) for t in IDX), '      ',
     tail=' = 0 := by')
w('  simp only [ip] at hk1 hk2 hk3 hk4')
w('  simp only [fr]')
wrap('  linear_combination ',
     ' + '.join('(%s k) * hk%d' % (a, i + 1) for i, a in enumerate(AV)), '    ')
w('')
w('/-- A real with `e² ≤ e/6` is at most `1/6`. -/')
w('theorem mass_le {e : Real} (h : e * e ≤ 1/6 * e) : e ≤ 1/6 := by')
w('  nlinarith')
w('')
# -------------------------------------------------------- orthogonal overflow
w('/-! ## Five orthogonal vectors do not fit in `ℂ⁴` -/')
w('')
w('/-- **Overflow.**  Four pairwise orthogonal vectors of squared norm `1/6`')
w('together with a further orthogonal vector of squared norm `1/3` cannot live in')
w('`ℂ⁴`: the frame operator of the four is `1/6` times an idempotent of trace `4`,')
w('hence `1/6` times the identity, which cannot annihilate a nonzero vector. -/')
w('theorem orthogonal_overflow (u a1 a2 a3 a4 : Fin 4 → ℂ)')
w('    (hu : nsq u = 1/3)')
w('    (ha1 : nsq a1 = 1/6) (ha2 : nsq a2 = 1/6) (ha3 : nsq a3 = 1/6) (ha4 : nsq a4 = 1/6)')
w('    (hq1 : ip u a1 = 0) (hq2 : ip u a2 = 0) (hq3 : ip u a3 = 0) (hq4 : ip u a4 = 0)')
orth_hyps()
w('    : False := by')
for i in range(1, 5):
    w('  have hs%d : ip a%d a%d = (1/6 : ℂ) := by rw [ip_self, ha%d]; norm_num' % (i, i, i, i))
for i in range(1, 5):
    w('  have hk%d : ip a%d u = 0 := by rw [← ip_star, hq%d, star_zero]' % (i, i, i))
for k in IDX:
    w('  have hi%d := frame_idem a1 a2 a3 a4 %s hs1 hs2 hs3 hs4 %d' % (k, HOARGS, k))
    w('  have hker%d := frame_kernel u a1 a2 a3 a4 hk1 hk2 hk3 hk4 %d' % (k, k))
    w('  rw [mul_star, mul_star, mul_star, mul_star] at hi%d' % k)
    w('  push_cast at hi%d' % k)
for k in IDX:
    body = ' + '.join('Complex.normSq (%s)' % frdiag(k, t) for t in IDX)
    wrap('  have hm%d : ' % k, body, '      ')
    wrap('      = 1/6 * (', mass(k), '        ', tail=') := by')
    wrap('    have h2 : ((', body, '        ')
    wrap('        : Real) : ℂ) = ((1/6 * (', mass(k), '          ',
         tail=') : Real) : ℂ) := by')
    w('      push_cast')
    w('      linear_combination hi%d' % k)
    w('    exact_mod_cast h2')
    wrap('  have hw%d : Complex.normSq (%s) = (' % (k, frdiag(k, k)), mass(k), '        ')
    wrap('      ) * (', mass(k), '        ', tail=') := by')
    w('    rw [fr_diag, Complex.normSq_ofReal]')
for k in IDX:
    for t in IDX:
        w('  have hnn%d%d := Complex.normSq_nonneg (%s)' % (k, t, frdiag(k, t)))
w('  simp only [nsq] at ha1 ha2 ha3 ha4 hu')
for k in IDX:
    wrap('  have hqq%d : (' % k, mass(k), '        ')
    wrap('      ) * (', mass(k), '        ', tail=') ≤ 1/6 * (')
    wrap('      ', mass(k), '        ', tail=') := by')
    w('    rw [← hw%d, ← hm%d]' % (k, k))
    w('    linarith [%s]' % ', '.join('hnn%d%d' % (k, t) for t in IDX if t != k))
    wrap('  have hle%d : (' % k, mass(k), '        ',
         tail=') ≤ 1/6 := mass_le hqq%d' % k)
for k in IDX:
    wrap('  have he%d : (' % k, mass(k), '        ', tail=') = 1/6 := by linarith')
for k in IDX:
    w('  rw [he%d] at hm%d hw%d' % (k, k, k))
for k in IDX:
    w('  have hzz%d : %s = ((1/6 : Real) : ℂ) := by rw [fr_diag, he%d]'
      % (k, frdiag(k, k), k))
    for t in IDX:
        if t != k:
            rest = ', '.join('hnn%d%d' % (k, s) for s in IDX if s != t)
            w('  have hzo%d%d : %s = 0 :=' % (k, t, frdiag(k, t)))
            w('    Complex.normSq_eq_zero.mp (by linarith [hw%d, hm%d, %s])' % (k, k, rest))
for k in IDX:
    w('  have hux%d : u %d = 0 := by' % (k, k))
    w('    have h := hker%d' % k)
    w('    rw [' + ', '.join(['hzz%d' % k] + ['hzo%d%d' % (k, t) for t in IDX if t != k])
      + '] at h')
    w('    push_cast at h')
    w('    linear_combination 6 * h')
w('  rw [hux0, hux1, hux2, hux3] at hu')
w('  simp at hu')
w('')
# --------------------------------------------------------- bell contradiction
w('/-! ## The trace contradiction -/')
w('')
w('/-- **The trace contradiction.**  Four bottom vectors and four top vectors of')
w('`ℂ⁴`, all of squared norm `1/6`, with a common frame operator, all orthogonal')
w('to an anchor `u` of squared norm `1/3`, and with `aᵢ†bⱼ = 0` off the diagonal,')
w('cannot exist. -/')
w('theorem bell_contradiction (u a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)')
w('    (hu : nsq u = 1/3)')
w('    (ha1 : nsq a1 = 1/6) (ha2 : nsq a2 = 1/6) (ha3 : nsq a3 = 1/6) (ha4 : nsq a4 = 1/6)')
w('    (hb1 : nsq b1 = 1/6) (hb2 : nsq b2 = 1/6) (hb3 : nsq b3 = 1/6) (hb4 : nsq b4 = 1/6)')
w('    (hq1 : ip u a1 = 0) (hq2 : ip u a2 = 0) (hq3 : ip u a3 = 0) (hq4 : ip u a4 = 0)')
w('    (hf : ∀ k l : Fin 4, fr a1 a2 a3 a4 k l = fr b1 b2 b3 b4 k l)')
for (i, j) in PAIRS:
    w('    (hx%d%d : ip a%d b%d = 0)' % (i, j, i, j))
w('    : False := by')
w('  have swap := frame_swap a1 a2 a3 a4 b1 b2 b3 b4 hf')
rw = ['ip_mul_ip %s %s' % (v, x) for v in AV for x in AV]
rw += ['ip_mul_ip %s %s' % (v, x) for v in AV for x in BV]
wrap('  rw [', ', '.join(rw), '    ', sep=', ', tail='] at swap')
wrap('  have swapR : (', sum_nsq(AV, AV), '      ')
wrap('      ) = (', sum_nsq(AV, BV), '      ', tail=') := by')
w('    exact_mod_cast swap')
for i in range(1, 5):
    w('  have hd%d : Complex.normSq (ip a%d a%d) = 1/36 := by' % (i, i, i))
    w('    rw [ip_self, ha%d, Complex.normSq_ofReal]; norm_num' % i)
for (i, j) in PAIRS:
    w('  have hy%d%d : Complex.normSq (ip a%d b%d) = 0 := by rw [hx%d%d]; simp'
      % (i, j, i, j, i, j))
for i in range(1, 5):
    w('  have hc%d := cs a%d b%d' % (i, i, i))
    w('  rw [ha%d, hb%d] at hc%d' % (i, i, i))
for (i, j) in PAIRS:
    w('  have hg%d%d := Complex.normSq_nonneg (ip a%d a%d)' % (i, j, i, j))
for (i, j) in PAIRS:
    w('  have ho%d%d : ip a%d a%d = 0 := Complex.normSq_eq_zero.mp (by linarith)'
      % (i, j, i, j))
w('  exact orthogonal_overflow u a1 a2 a3 a4 hu ha1 ha2 ha3 ha4 hq1 hq2 hq3 hq4')
w('    ' + HOARGS)
