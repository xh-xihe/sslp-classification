"""Emit SixQubit/ParityFour.lean -- the shared C^2 algebra of the parity-four triad.

The long sums (16 and 64 wedge terms) are machine-written so that no index is
typed by hand.  Nothing here mentions bit strings; it is ordinary commutative
algebra over the complex numbers plus real positivity.
"""
import io
import os

NS = 'Complex.normSq'


def wedge(i, j):
    return 'a%d * t%d - b%d * s%d' % (i, j, i, j)


def emit_total(L, n):
    """The `total` identity for n bottom and n top vectors."""
    W = L.append
    A = ' + '.join('a%d * star a%d' % (i, i) for i in range(1, n + 1))
    C = ' + '.join('b%d * star b%d' % (i, i) for i in range(1, n + 1))
    B = ' + '.join('a%d * star b%d' % (i, i) for i in range(1, n + 1))
    Bs = ' + '.join('star a%d * b%d' % (i, i) for i in range(1, n + 1))
    Ad = ' + '.join('s%d * star s%d' % (j, j) for j in range(1, n + 1))
    Cd = ' + '.join('t%d * star t%d' % (j, j) for j in range(1, n + 1))
    Bd = ' + '.join('s%d * star t%d' % (j, j) for j in range(1, n + 1))
    Bds = ' + '.join('star s%d * t%d' % (j, j) for j in range(1, n + 1))
    lhs = ' + '.join('(%s) * star (%s)' % (wedge(i, j), wedge(i, j))
                     for i in range(1, n + 1) for j in range(1, n + 1))
    W('/-- The complex wedge identity for %d bottom and %d top vectors:' % (n, n))
    W('the total squared wedge is fixed by the two frame operators alone. -/')
    W('theorem totalC%d {%s : ℂ}' % (n, ' '.join(
        ['a%d' % i for i in range(1, n + 1)] + ['b%d' % i for i in range(1, n + 1)]
        + ['s%d' % j for j in range(1, n + 1)] + ['t%d' % j for j in range(1, n + 1)])))
    W('    (fA : %s = %s)' % (A, Ad))
    W('    (fC : %s = %s)' % (C, Cd))
    W('    (fB : %s = %s) :' % (B, Bd))
    W('    %s' % lhs)
    W('      = 2 * (%s) * (%s)' % (A, C))
    W('        - 2 * ((%s) * (%s)) := by' % (B, Bs))
    W('  have hBs : %s = %s := by' % (Bs, Bds))
    W('    have h := congrArg star fB')
    W('    simp only [star_add, star_mul\', star_star] at h')
    W('    linear_combination h')
    W('  simp only [star_sub, star_mul\']')
    W('  linear_combination (-(%s)) * fC + (-(%s)) * fA' % (A, C))
    W('    + (%s) * hBs + (%s) * fB' % (B, Bs))
    W('')
    W('/-- The same identity over the reals. -/')
    W('theorem total%d {%s : ℂ}' % (n, ' '.join(
        ['a%d' % i for i in range(1, n + 1)] + ['b%d' % i for i in range(1, n + 1)]
        + ['s%d' % j for j in range(1, n + 1)] + ['t%d' % j for j in range(1, n + 1)])))
    W('    (fA : %s' % ' + '.join('%s a%d' % (NS, i) for i in range(1, n + 1)))
    W('        = %s)' % ' + '.join('%s s%d' % (NS, j) for j in range(1, n + 1)))
    W('    (fC : %s' % ' + '.join('%s b%d' % (NS, i) for i in range(1, n + 1)))
    W('        = %s)' % ' + '.join('%s t%d' % (NS, j) for j in range(1, n + 1)))
    W('    (fB : %s = %s) :' % (B, Bd))
    W('    %s' % ' + '.join('%s (%s)' % (NS, wedge(i, j))
                            for i in range(1, n + 1) for j in range(1, n + 1)))
    W('      = 2 * (%s) * (%s)'
      % (' + '.join('%s a%d' % (NS, i) for i in range(1, n + 1)),
         ' + '.join('%s b%d' % (NS, i) for i in range(1, n + 1))))
    W('        - 2 * %s (%s) := by' % (NS, B))
    W('  have fA\' : %s = %s := by' % (A, Ad))
    W('    rw [%s]' % ', '.join(
        ['SixQubit.Frame.self_mul_star a%d' % i for i in range(1, n + 1)]
        + ['SixQubit.Frame.self_mul_star s%d' % j for j in range(1, n + 1)]))
    W('    exact_mod_cast fA')
    W('  have fC\' : %s = %s := by' % (C, Cd))
    W('    rw [%s]' % ', '.join(
        ['SixQubit.Frame.self_mul_star b%d' % i for i in range(1, n + 1)]
        + ['SixQubit.Frame.self_mul_star t%d' % j for j in range(1, n + 1)]))
    W('    exact_mod_cast fC')
    W('  have key := totalC%d fA\' fC\' fB' % n)
    W('  have hnB : ((%s (%s) : Real) : ℂ) = (%s) * (%s) := by' % (NS, B, B, Bs))
    W('    rw [← SixQubit.Frame.self_mul_star]')
    W('    simp only [star_add, star_mul\', star_star]')
    W('    try ring')
    W('  rw [%s] at key' % ', '.join(
        'SixQubit.Frame.self_mul_star (%s)' % wedge(i, j)
        for i in range(1, n + 1) for j in range(1, n + 1)))
    W('  rw [%s] at key' % ', '.join(
        ['SixQubit.Frame.self_mul_star a%d' % i for i in range(1, n + 1)]
        + ['SixQubit.Frame.self_mul_star b%d' % i for i in range(1, n + 1)]))
    W('  rw [← hnB] at key')
    W('  exact_mod_cast key')
    W('')


def emit_slice(L):
    W = L.append
    idx = range(1, 5)
    P = ' + '.join('%s a%d + %s b%d' % (NS, i, NS, i) for i in idx)
    W('/-- **A three-cube slice carries no mass.**  Four bottom and four top')
    W('vectors in `ℂ²`, indexed so that bottom `i` is the unique NON-neighbour of')
    W('top `i`; the twelve neighbour inner products vanish, the three slice frame')
    W('entries agree, and each bottom mass obeys the neighbour-sum identity.')
    W('Then the whole slice has zero mass. -/')
    W('theorem slice_zero {a1 a2 a3 a4 b1 b2 b3 b4 s1 s2 s3 s4 t1 t2 t3 t4 : ℂ}')
    for i in idx:
        for j in idx:
            if i != j:
                W('    (o%d%d : star a%d * s%d + star b%d * t%d = 0)' % (i, j, i, j, i, j))
    W('    (fA : %s' % ' + '.join('%s a%d' % (NS, i) for i in idx))
    W('        = %s)' % ' + '.join('%s s%d' % (NS, j) for j in idx))
    W('    (fC : %s' % ' + '.join('%s b%d' % (NS, i) for i in idx))
    W('        = %s)' % ' + '.join('%s t%d' % (NS, j) for j in idx))
    W('    (fB : %s = %s)'
      % (' + '.join('a%d * star b%d' % (i, i) for i in idx),
         ' + '.join('s%d * star t%d' % (j, j) for j in idx)))
    for i in idx:
        W('    (m%d : %s' % (i, ' + '.join('%s s%d + %s t%d' % (NS, j, NS, j)
                                           for j in idx if j != i)))
        W('        = (%s) / 2 + (%s a%d + %s b%d))' % (P, NS, i, NS, i))
    W('    : %s = 0 := by' % P)
    A = ' + '.join('%s a%d' % (NS, i) for i in idx)
    C = ' + '.join('%s b%d' % (NS, i) for i in idx)
    pp = {i: '(%s a%d + %s b%d)' % (NS, i, NS, i) for i in idx}
    for i in idx:
        for j in idx:
            if i != j:
                W('  have w%d%d := wedge_of_orth o%d%d' % (i, j, i, j))
    W('  have tot := total4 fA fC fB')
    for i in idx:
        nb = [j for j in idx if j != i]
        W('  have r%d : %s' % (i, ' + '.join('%s (%s)' % (NS, wedge(i, j)) for j in nb)))
        W('      = %s * ((%s) / 2 + (%s a%d + %s b%d)) := by' % (pp[i], P, NS, i, NS, i))
        W('    rw [%s, ← m%d]' % (', '.join('w%d%d' % (i, j) for j in nb), i))
        W('    ring')
    W('  have hb : (0:Real) ≤ %s (%s) := Complex.normSq_nonneg _'
      % (NS, ' + '.join('a%d * star b%d' % (i, i) for i in idx)))
    for i in idx:
        W('  have d%d : (0:Real) ≤ %s (%s) := Complex.normSq_nonneg _' % (i, NS, wedge(i, i)))
    for i in idx:
        W('  have pa%d : (0:Real) ≤ %s a%d := Complex.normSq_nonneg _' % (i, NS, i))
        W('  have pb%d : (0:Real) ≤ %s b%d := Complex.normSq_nonneg _' % (i, NS, i))
    W('  have collapse : %s ≤ 0 := by'
      % ' + '.join('%s * %s' % (pp[i], pp[i]) for i in idx))
    W('    linarith [tot, %s, %s, hb,'
      % (', '.join('r%d' % i for i in idx), ', '.join('d%d' % i for i in idx)))
    W('      sq_nonneg ((%s) - (%s))]' % (A, C))
    W('  have hPz : (%s) * (%s) ≤ 0 := by' % (P, P))
    W('    linarith [collapse, %s]'
      % ', '.join('sq_nonneg (%s - %s)' % (pp[idx[i]], pp[idx[j]])
                  for i in range(4) for j in range(i + 1, 4)))
    W('  have hPnn : (0:Real) ≤ %s := by' % P)
    W('    linarith [%s]' % ', '.join('pa%d, pb%d' % (i, i) for i in idx))
    W('  exact sq_le_zero_eq hPnn hPz')
    W('')


def main():
    L = []
    W = L.append
    W('import Mathlib')
    W('')
    W('import SS.FullKL')
    W('import SixQubit.Common')
    W('import SixQubit.Frame')
    W('')
    W('/-!')
    W('# The parity-four `ℂ²` obstruction')
    W('')
    W('Orbits 14, 15 and 24 all reduce to the same picture.  A free qubit -- a')
    W('zero-angle qubit, or the effective qubit of a repetition pair -- collects the')
    W('amplitudes into vectors `c_x, d_y ∈ ℂ²` indexed by the two parity classes of')
    W('four effective bits.  The weight-at-most-two Knill--Laflamme rows isolate')
    W('`⟨c_x , d_y⟩ = 0` on every Hamming edge, and the diagonal rows on the free')
    W('qubit equate the two frame operators.')
    W('')
    W('The paper argues through connectivity of the positive support.  That is')
    W('awkward to formalize, because the support depends on where in the moment')
    W('cross-polytope one sits.  The route taken here is a uniform inequality that')
    W('never mentions the support at all.')
    W('')
    W('Write `c ∧ d = c₀d₁ - c₁d₀`.  Lagrange\'s identity says')
    W('`|c ∧ d|² + |⟨c,d⟩|² = ‖c‖²‖d‖²`, so on an edge the wedge carries the whole')
    W('product of masses.  Summing the wedge over *all* pairs, edge or not, gives')
    W('a quantity fixed by the frames alone,')
    W('')
    W('```')
    W('Σ_{x,y} |c_x ∧ d_y|² = 2 A C - 2 |B|²  ≤  (A + C)² / 2 ,')
    W('```')
    W('where `A, C, B` are the entries of the common frame operator.  The moment')
    W('system supplies the missing half: the degree-at-most-two moments force')
    W('`Σ_{y ~ x} ‖d_y‖² = μ/2 + ‖c_x‖²` on a three-cube slice of total mass `μ`,')
    W('so the edge part of the wedge sum is already `μ²/2 + Σ‖c_x‖⁴`.  The two')
    W('bounds collide, leaving `Σ‖c_x‖⁴ ≤ 0`, hence `μ = 0`.')
    W('')
    W('No division, no ratios, no case split on the support.  `native_decide` is')
    W('not used.')
    W('-/')
    W('')
    W('namespace SixQubit.ParityFour')
    W('')
    W('open scoped ComplexConjugate')
    W('')
    W('noncomputable section')
    W('')
    W('/-! ## Lagrange\'s identity -/')
    W('')
    W('/-- `|u ∧ v|² + |⟨u,v⟩|² = ‖u‖²‖v‖²` in `ℂ²`. -/')
    W('theorem lagrange (u0 u1 v0 v1 : ℂ) :')
    W('    %s (u0 * v1 - u1 * v0)' % NS)
    W('        + %s (star u0 * v0 + star u1 * v1)' % NS)
    W('      = (%s u0 + %s u1) * (%s v0 + %s v1) := by' % (NS, NS, NS, NS))
    W('  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,')
    W('    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,')
    W('    Complex.conj_re, Complex.conj_im]')
    W('  ring')
    W('')
    W('/-- On an orthogonal pair the wedge carries the full product of masses. -/')
    W('theorem wedge_of_orth {u0 u1 v0 v1 : ℂ}')
    W('    (h : star u0 * v0 + star u1 * v1 = 0) :')
    W('    %s (u0 * v1 - u1 * v0) = (%s u0 + %s u1) * (%s v0 + %s v1) := by'
      % (NS, NS, NS, NS, NS))
    W('  have := lagrange u0 u1 v0 v1')
    W('  rw [h] at this')
    W('  simpa using this')
    W('')
    W('/-! ## Propagation -/')
    W('')
    W('/-- Two vectors orthogonal to a common `c` are parallel, weighted by `‖c‖²`.')
    W('No division and no nonvanishing hypothesis. -/')
    W('theorem prop_wedge {c0 c1 d0 d1 e0 e1 : ℂ}')
    W('    (h1 : star c0 * d0 + star c1 * d1 = 0)')
    W('    (h2 : star c0 * e0 + star c1 * e1 = 0) :')
    W('    (c0 * star c0 + c1 * star c1) * (d0 * e1 - d1 * e0) = 0 := by')
    W('  linear_combination (c0 * e1 - c1 * e0) * h1 + (c1 * d0 - c0 * d1) * h2')
    W('')
    W('/-- Plücker: parallelism propagates through a nonzero middle vector. -/')
    W('theorem plucker {a0 a1 b0 b1 c0 c1 : ℂ}')
    W('    (hab : a0 * b1 - a1 * b0 = 0) (hac : a0 * c1 - a1 * c0 = 0) :')
    W('    (a0 * star a0 + a1 * star a1) * (b0 * c1 - b1 * c0) = 0 := by')
    W('  linear_combination (star a0 * b0 + star a1 * b1) * hac')
    W('    - (star a0 * c0 + star a1 * c1) * hab')
    W('')
    W('/-- A real with nonpositive square is zero. -/')
    W('theorem sq_nonpos {x : Real} (h : x * x ≤ 0) : x = 0 :=')
    W('  mul_self_eq_zero.mp (le_antisymm h (mul_self_nonneg x))')
    W('')
    W('/-- A nonnegative real with nonpositive square is zero. -/')
    W('theorem sq_le_zero_eq {x : Real} (h1 : 0 ≤ x) (h2 : x * x ≤ 0) : x = 0 := by')
    W('  nlinarith')
    W('')
    W('/-! ## The wedge total -/')
    W('')
    emit_total(L, 4)
    emit_total(L, 8)
    W('/-! ## The slice obstruction -/')
    W('')
    emit_slice(L)
    W('end')
    W('')
    W('end SixQubit.ParityFour')
    out = os.path.join('SixQubit', 'ParityFour.lean')
    with io.open(out, 'w', encoding='utf-8', newline='\n') as f:
        f.write(chr(10).join(L) + chr(10))
    print('wrote %s  (%d lines)' % (out, len(L) + 1))


main()
