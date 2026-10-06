#!/usr/bin/env python3
"""Emit the attainment halves of `eq:small-beta` for sizes 7, 8 and 9.

`eq:small-beta` of `main.tex` tabulates

    beta_5 = 5,  beta_6 = 9,  beta_7 = 18,  beta_8 = 42,  beta_9 = 120,

and this repository certifies `BetaExact N` only for `N = 1, ..., 6`.  The
upper halves at 7, 8 and 9 are universal enumerations far beyond the
six-variable coverage tree, but the *attainment* halves are single explicit
matrices, and this script produces them.

The witnesses were found by hill climbing on the inverse denominator over
zero--one matrices; each one reaches the tabulated value exactly, which is
independent corroboration of the table.  They are hard-coded here rather than
re-searched, so the emitted Lean is reproducible.

The emitted proof never expands a determinant.  For a witness `A` with
inverse denominator `k` it emits the integer matrix `B = k * A^{-1}` and the
single identity `A * B = k * I`; over the rationals that identity exhibits
`A⁻¹`, gives `det A != 0` through `Matrix.det_ne_zero_of_right_inverse`, and
makes `k` a universal clearing multiplier.  One inverse entry of reduced
denominator `k` supplies the opposite divisibility.

Usage:  python tools/generators/emit_beta_lower_lean.py
"""
import io
import math
import os
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

WITNESS = {
    7: (18, [
        [1, 0, 1, 0, 1, 0, 1],
        [1, 0, 0, 1, 1, 1, 0],
        [1, 1, 0, 1, 0, 0, 0],
        [0, 1, 0, 1, 1, 0, 1],
        [0, 1, 1, 1, 0, 1, 1],
        [1, 1, 0, 0, 1, 1, 1],
        [0, 1, 1, 0, 1, 1, 0],
    ]),
    8: (42, [
        [0, 1, 1, 0, 1, 0, 0, 0],
        [0, 1, 0, 1, 1, 1, 0, 1],
        [1, 1, 0, 0, 0, 0, 1, 1],
        [1, 1, 1, 0, 0, 1, 0, 1],
        [0, 0, 1, 0, 1, 1, 1, 1],
        [1, 0, 1, 1, 1, 0, 0, 0],
        [1, 0, 0, 0, 1, 1, 1, 0],
        [0, 1, 1, 1, 0, 1, 1, 0],
    ]),
    9: (120, [
        [1, 0, 1, 0, 1, 0, 0, 1, 1],
        [0, 1, 1, 1, 1, 0, 1, 1, 0],
        [1, 1, 0, 1, 0, 1, 0, 1, 1],
        [1, 0, 0, 1, 0, 0, 1, 1, 0],
        [0, 0, 1, 1, 0, 0, 1, 0, 1],
        [1, 1, 1, 0, 0, 1, 1, 0, 0],
        [1, 0, 1, 1, 1, 1, 0, 0, 0],
        [1, 1, 0, 1, 1, 0, 1, 0, 1],
        [0, 0, 0, 0, 1, 1, 1, 1, 1],
    ]),
}

WORD = {7: 'Seven', 8: 'Eight', 9: 'Nine'}
SPELL = {18: 'eighteen', 42: 'fortyTwo', 120: 'oneTwenty'}
SPELLED = {18: 'eighteen', 42: 'forty-two', 120: 'one hundred and twenty'}


def inverse(M, n):
    """Exact rational inverse by Gauss-Jordan over Fraction."""
    A = [[Fraction(M[i][j]) for j in range(n)] +
         [Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [[A[i][j + n] for j in range(n)] for i in range(n)]


def matrix_literal(rows, indent):
    width = max(len('%d' % x) for row in rows for x in row)
    body = []
    for r, row in enumerate(rows):
        cells = ', '.join('%*d' % (width, x) for x in row)
        body.append(' ' * indent + cells + (';' if r + 1 < len(rows) else ']'))
    return ('!![' + body[0].lstrip() + '\n' + '\n'.join(body[1:]))


def emit(n):
    k, M = WITNESS[n]
    inv = inverse(M, n)
    denominators = {inv[i][j].denominator for i in range(n) for j in range(n)}
    lcm = 1
    for d in denominators:
        lcm = lcm * d // math.gcd(lcm, d)
    assert lcm == k, (n, lcm, k)
    B = [[k * inv[i][j] for j in range(n)] for i in range(n)]
    assert all(x.denominator == 1 for row in B for x in row)
    B = [[int(x) for x in row] for row in B]
    for i in range(n):
        for j in range(n):
            assert sum(M[i][t] * B[t][j] for t in range(n)) == (k if i == j else 0)
    # A smallest set of inverse entries whose denominators already have
    # least common multiple `k`.  At size nine no single entry reaches 120.
    spots, running = [], 1
    while running != k:
        best, gain = None, running
        for i in range(n):
            for j in range(n):
                if (i, j) in spots:
                    continue
                d = inv[i][j].denominator
                cand = running * d // math.gcd(running, d)
                if cand > gain:
                    best, gain = (i, j), cand
        assert best is not None, (n, running, k)
        spots.append(best)
        running = gain
    entries = [inv[i][j] for (i, j) in spots]

    word, name = WORD[n], SPELL[k]
    fin = 'F%d' % n
    txt = []
    add = txt.append
    add('import MainTheory.BinaryBeta')
    add('')
    add('/-!')
    add('# A kernel certificate that the %s-variable binary denominator reaches %d'
        % (['', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight',
            'nine'][n], k))
    add('')
    add('`eq:small-beta` tabulates `beta_5 = 5`, `beta_6 = 9`, `beta_7 = 18`,')
    add('`beta_8 = 42` and `beta_9 = 120`.  This repository certifies')
    add('`BetaExact N` for `N = 1, ..., 6`; the last three entries are cited by')
    add('the paper and were proved nowhere.  `beta_7 = 18` is the one the text')
    add('uses, as the general distance-two six-qubit cutoff of')
    add('`eq:6qubit-d2-bound`.')
    add('')
    add('This file proves the attainment half, `%d <= beta_%d`.  The upper half,'
        % (k, n))
    add('`BetaBound %d %d`, is a universal statement over every nonsingular'
        % (n, k))
    add('binary matrix of size at most %d; the six-variable analogue is this' % n)
    add('package\'s largest generated artefact -- a coverage tree over the 1716')
    add('weakly increasing patterns in `Fin 8` -- and the larger sizes are out')
    add('of reach by that route.  It is deliberately not claimed.')
    add('')
    add('The proof never expands a `%d x %d` determinant.  It exhibits the' % (n, n))
    add('integer matrix `clearedInverse = %d * A^{-1}` and checks the single' % k)
    add('identity `A * clearedInverse = %d I` entrywise.  That identity gives' % k)
    add('everything: over the rationals it exhibits `A^{-1}` outright')
    add('(`Matrix.inv_eq_right_inv`), hence `det A != 0` with no expansion; it')
    add('makes `%d` a universal clearing multiplier, since the cleared solution' % k)
    add('of `A x = h` is the integer vector `clearedInverse *. h`, so')
    add('`inverseDenominator A | %d`; and the inverse entries at %s have' %
        (k, ', '.join('(%d,%d)' % sp for sp in spots)))
    add('reduced denominators %s, whose least common multiple is %d, so' %
        (', '.join(str(e.denominator) for e in entries), k))
    add('`%d | inverseDenominator A`.' % k)
    add('')
    add('Generated by `tools/generators/emit_beta_lower_lean.py`.')
    add('-/')
    add('')
    add('namespace MainTheory.BinaryBeta%sLower' % word)
    add('')
    add('open MainTheory.BinaryBeta')
    add('open MainTheory.SharpClearing')
    add('')
    add('abbrev %s := Fin %d' % (fin, n))
    add('')
    add('/-- A nonsingular %d-variable binary matrix whose inverse has an entry' % n)
    add('of reduced denominator %s. -/' % SPELLED[k])
    add('def attainingMatrix : Matrix %s %s ℤ :=' % (fin, fin))
    add('  ' + matrix_literal(M, 5))
    add('')
    add('/-- %s times the inverse of `attainingMatrix`, an integer matrix. -/'
        % SPELLED[k].capitalize())
    add('def clearedInverse : Matrix %s %s ℤ :=' % (fin, fin))
    add('  ' + matrix_literal(B, 5))
    add('')
    add('theorem attainingMatrix_isZeroOne : IsZeroOne attainingMatrix := by')
    add('  intro i j')
    add('  fin_cases i <;> fin_cases j <;> norm_num [attainingMatrix]')
    add('')
    add('set_option maxRecDepth 40000 in')
    add('/-- The one computation this file performs. -/')
    add('theorem mul_clearedInverse :')
    add('    attainingMatrix * clearedInverse = (%d : ℤ) • (1 : Matrix %s %s ℤ) := by'
        % (k, fin, fin))
    add('  ext i j')
    add('  fin_cases i <;> fin_cases j <;>')
    add('    norm_num [attainingMatrix, clearedInverse, Matrix.mul_apply,')
    add('      Fin.sum_univ_succ, Matrix.one_apply]')
    add('')
    add('/-! ## The rational inverse -/')
    add('')
    add('/-- Casting a matrix product to the rationals is the product of the')
    add('casts. -/')
    add('theorem ratMatrix_mul (A B : Matrix %s %s ℤ) :' % (fin, fin))
    add('    ratMatrix (A * B) = ratMatrix A * ratMatrix B :=')
    add('  Matrix.map_mul')
    add('')
    add('/-- `A^{-1}`, as the integer matrix scaled by `1/%d`. -/' % k)
    add('noncomputable def ratInverse : Matrix %s %s ℚ :=' % (fin, fin))
    add('  (%d : ℚ)⁻¹ • ratMatrix clearedInverse' % k)
    add('')
    add('theorem ratMul_clearedInverse :')
    add('    ratMatrix attainingMatrix * ratMatrix clearedInverse')
    add('      = (%d : ℚ) • (1 : Matrix %s %s ℚ) := by' % (k, fin, fin))
    add('  rw [← ratMatrix_mul, mul_clearedInverse]')
    add('  ext i j')
    add('  simp only [ratMatrix, Matrix.map_apply, Matrix.smul_apply,')
    add('    Matrix.one_apply, smul_eq_mul, eq_intCast]')
    add('  by_cases h : i = j <;> simp [h]')
    add('')
    add('theorem ratMul_ratInverse :')
    add('    ratMatrix attainingMatrix * ratInverse = 1 := by')
    add('  rw [ratInverse, Matrix.mul_smul, ratMul_clearedInverse, smul_smul]')
    add('  norm_num')
    add('')
    add('theorem inv_eq_ratInverse : (ratMatrix attainingMatrix)⁻¹ = ratInverse :=')
    add('  Matrix.inv_eq_right_inv ratMul_ratInverse')
    add('')
    add('theorem attainingMatrix_det_ne_zero : attainingMatrix.det ≠ 0 := by')
    add('  have h : (ratMatrix attainingMatrix).det ≠ 0 :=')
    add('    Matrix.det_ne_zero_of_right_inverse ratMul_ratInverse')
    add('  have hm : (ratMatrix attainingMatrix).det = (attainingMatrix.det : ℚ) :=')
    add('    ((Int.castRingHom ℚ).map_det attainingMatrix).symm')
    add('  rw [hm] at h')
    add('  exact_mod_cast h')
    add('')
    add('/-! ## Both divisibilities -/')
    add('')
    for t, ((i0, j0), e) in enumerate(zip(spots, entries)):
        add('/-- An inverse entry of reduced denominator %d. -/' % e.denominator)
        add('theorem inverse_entry_%d :' % t)
        add('    (ratMatrix attainingMatrix)⁻¹ (%d : %s) (%d : %s) = (%d / %d : ℚ) := by'
            % (i0, fin, j0, fin, e.numerator, e.denominator))
        add('  have hb : clearedInverse (%d : %s) (%d : %s) = %d := by decide'
            % (i0, fin, j0, fin, B[i0][j0]))
        add('  rw [inv_eq_ratInverse]')
        add('  simp only [ratInverse, Matrix.smul_apply, ratMatrix,')
        add('    Matrix.map_apply, eq_intCast, smul_eq_mul, hb]')
        add('  norm_num')
        add('')
    if len(spots) == 1:
        add('theorem %s_dvd_inverseDenominator :' % name)
        add('    %d ∣ inverseDenominator attainingMatrix := by' % k)
        add('  have h := inverse_entry_den_dvd attainingMatrix (%d : %s) (%d : %s)'
            % (spots[0][0], fin, spots[0][1], fin))
        add('  rw [inverse_entry_0] at h')
        add('  norm_num at h')
        add('  exact h')
    else:
        add('/-- No single inverse entry has denominator %d, but %d of them' % (k, len(spots)))
        add('together do: each denominator divides the sharp multiplier, so their')
        add('least common multiple does. -/')
        add('theorem %s_dvd_inverseDenominator :' % name)
        add('    %d ∣ inverseDenominator attainingMatrix := by' % k)
        for t, (i0, j0) in enumerate(spots):
            add('  have h%d := inverse_entry_den_dvd attainingMatrix (%d : %s) (%d : %s)'
                % (t, i0, fin, j0, fin))
            add('  rw [inverse_entry_%d] at h%d' % (t, t))
            add('  norm_num at h%d' % t)
        expr = 'h0'
        for t in range(1, len(spots)):
            expr = 'Nat.lcm_dvd %s h%d' % (expr, t)
        lcm_expr = 'Nat.lcm ' * (len(spots) - 1)
        chain = str(entries[0].denominator)
        for e in entries[1:]:
            chain = 'Nat.lcm (%s) %d' % (chain, e.denominator)
        add('  have hlcm : %s = %d := by norm_num [Nat.lcm]' % (chain, k))
        add('  rw [← hlcm]')
        add('  exact %s' % expr)
    add('')
    add('/-- %s universally clears: the cleared solution of `A x = h` is the'
        % SPELLED[k].capitalize())
    add('integer vector `clearedInverse *. h`. -/')
    add('theorem universallyClears_%s : UniversallyClears attainingMatrix %d := by'
        % (name, k))
    add('  intro h')
    add('  refine ⟨clearedInverse.mulVec h, fun i => ?_⟩')
    add('  rw [inv_eq_ratInverse, ratInverse, Matrix.smul_mulVec]')
    add('  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc]')
    add('  norm_num')
    add('  simp only [ratMatrix, Matrix.mulVec, dotProduct]')
    add('  push_cast')
    add('  rfl')
    add('')
    add('theorem inverseDenominator_dvd_%s :' % name)
    add('    inverseDenominator attainingMatrix ∣ %d :=' % k)
    add('  inverseDenominator_dvd_of_universallyClears attainingMatrix %d' % k)
    add('    (by norm_num) universallyClears_%s' % name)
    add('')
    add('theorem inverseDenominator_eq_%s :' % name)
    add('    inverseDenominator attainingMatrix = %d :=' % k)
    add('  Nat.dvd_antisymm inverseDenominator_dvd_%s' % name)
    add('    %s_dvd_inverseDenominator' % name)
    add('')
    add('/-- **The attainment half of `beta_%d = %d`.** -/' % (n, k))
    add('theorem beta%sAttained : BetaAttained %d %d :=' % (word, n, k))
    add('  ⟨%d, by norm_num, by norm_num, attainingMatrix,' % n)
    add('    attainingMatrix_isZeroOne, attainingMatrix_det_ne_zero,')
    add('    inverseDenominator_eq_%s⟩' % name)
    add('')
    add('end MainTheory.BinaryBeta%sLower' % word)
    add('')
    return '\n'.join(txt)


def main():
    for n in (7, 8, 9):
        path = os.path.join(ROOT, 'MainTheory', 'BinaryBeta%sLower.lean' % WORD[n])
        io.open(path, 'w', encoding='utf-8', newline='\n').write(emit(n))
        print('wrote', path)


if __name__ == '__main__':
    main()
