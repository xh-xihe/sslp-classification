"""Emit `SixQubit/K4Kernel.lean`, the bit-string-free algebra layer of the
orbit-36 rigidity theorem, and verify every polynomial certificate it contains.

The module has five parts, matching the five steps of
`documents/20260821/supplementary.tex`, section "Rigidity of the order-five
orbit 36":

1. `pair_relation`      -- the three `X_i Z_j` dressings have coefficient matrix
                           `[[-1,1,1],[1,-1,1],[1,1,-1]]` (determinant `4`), so
                           `U_j = V_j`, and the `X_i` equation collapses to the
                           star sum `sum_j conj(c_ij) R_j = 0`;
2. `cube_eq` / `exists_cubeRoot`
                        -- three complex numbers with zero sum and zero sum of
                           squares satisfy `y^3 = z^3 = x^3 = xyz`; if `x != 0`
                           they are `x * (1, w, w^2)` for a primitive cube root;
3. `det_K4`             -- the determinant of the symmetric zero-diagonal `4x4`
                           matrix is `x^2+y^2+z^2-2xy-2xz-2yz` for the three
                           opposite-edge products;
4. `detPoly_eq_zero`    -- a nonzero kernel vector kills that determinant, by
                           the four Cramer identities `det * r_i = adj_i . (C r)`;
5. `vertex_factorization`
                        -- positive edge weights with equal opposite products
                           factor as `w_ij = s_i s_j`.

Everything here is division free except the two places where a division is the
statement itself (`w = y / x`, and the square root in step 5).

The Cramer coefficients in step 4 and the determinant expansion in step 3 are
computed by sympy below, not typed by hand, and every `linear_combination`
certificate emitted into the Lean file is checked as a polynomial identity
before the file is written.

Usage:  python tools/run.py generators/gen36alg.py
"""

from __future__ import annotations

import os

import sympy as sp

# ---------------------------------------------------------------------------
# symbols
# ---------------------------------------------------------------------------

x, y, z = sp.symbols('x y z')
c12, c13, c14, c23, c24, c34 = sp.symbols('c12 c13 c14 c23 c24 c34')
r1, r2, r3, r4 = sp.symbols('r1 r2 r3 r4')
m1, m2, m3, s1, s2, s3 = sp.symbols('m1 m2 m3 s1 s2 s3')
w12, w13, w14, w23, w24, w34, g = sp.symbols('w12 w13 w14 w23 w24 w34 g')
rho, ii, sq3, ww = sp.symbols('rho ii sq3 ww')

CHECKS = []


def cert(name, goal, terms):
    """Record and verify one `linear_combination` certificate.

    `goal` is `lhs - rhs` of the Lean goal; `terms` is a list of pairs
    `(coefficient, lhs - rhs of a hypothesis)`.
    """
    residual = sp.expand(goal - sum(co * hy for co, hy in terms))
    assert residual == 0, (name, residual)
    CHECKS.append(name)


def lean(e):
    """Render a sympy expression as a Lean term."""
    text = sp.sstr(e)
    text = text.replace('**', '^')
    out = []
    for ch in text:
        if ch == '*':
            out.append(' * ')
        else:
            out.append(ch)
    return ''.join(out).replace('  ', ' ')


def wrap(prefix, body, cont, width=98):
    """Break `prefix + body` at top-level ` + ` / ` - ` boundaries."""
    tokens = []
    buf = ''
    depth = 0
    i = 0
    while i < len(body):
        if body[i] == '(':
            depth += 1
        elif body[i] == ')':
            depth -= 1
        if depth == 0 and body[i:i + 3] in (' + ', ' - ') and buf:
            tokens.append(buf)
            buf = body[i + 1:i + 3].strip() + ' '
            i += 3
            continue
        buf += body[i]
        i += 1
    tokens.append(buf)
    lines = []
    line = prefix + tokens[0]
    for tok in tokens[1:]:
        if len(line) + 1 + len(tok) > width:
            lines.append(line)
            line = cont + tok
        else:
            line = line + ' ' + tok
    lines.append(line)
    return lines


# ---------------------------------------------------------------------------
# 1.  the 3x3 Walsh system of the X_i Z_j dressings
# ---------------------------------------------------------------------------

d1, d2, d3 = sp.symbols('d1 d2 d3')
H1 = -d1 + d2 + d3
H2 = d1 - d2 + d3
H3 = d1 + d2 - d3
cert('walsh3.d1', d1, [(sp.Rational(1, 2), H2), (sp.Rational(1, 2), H3)])
cert('walsh3.d2', d2, [(sp.Rational(1, 2), H1), (sp.Rational(1, 2), H3)])
cert('walsh3.d3', d3, [(sp.Rational(1, 2), H1), (sp.Rational(1, 2), H2)])

U1, U2, U3, V1, V2, V3 = sp.symbols('U1 U2 U3 V1 V2 V3')
SX = (U1 + V1) + (U2 + V2) + (U3 + V3)
cert('xi_reduction.starSum', U1 + U2 + U3,
     [(sp.Rational(1, 2), SX), (sp.Rational(1, 2), U1 - V1),
      (sp.Rational(1, 2), U2 - V2), (sp.Rational(1, 2), U3 - V3)])

# ---------------------------------------------------------------------------
# 2.  the cubic-root lemma
# ---------------------------------------------------------------------------

E1 = x + y + z                       # hypothesis h1
E2 = x ** 2 + y ** 2 + z ** 2        # hypothesis h2

CUB = {
    'sym2': (x * y + y * z + z * x,
             [((x + y + z) / 2, E1), (sp.Rational(-1, 2), E2)]),
    'sqRel': (x ** 2 + x * y + y ** 2,
              [((x + y - z) / 2, E1), (sp.Rational(1, 2), E2)]),
    'prodYZ': (y * z - x ** 2,
               [((y + z - x) / 2, E1), (sp.Rational(-1, 2), E2)]),
    'prodZX': (z * x - y ** 2,
               [((z + x - y) / 2, E1), (sp.Rational(-1, 2), E2)]),
    'prodXY': (x * y - z ** 2,
               [((x + y - z) / 2, E1), (sp.Rational(-1, 2), E2)]),
    'cubeY': (y ** 3 - x ** 3,
              [((y - x) * (x + y - z) / 2, E1), ((y - x) / 2, E2)]),
    'cubeZ': (z ** 3 - x ** 3,
              [((z - x) * (x + z - y) / 2, E1), ((z - x) / 2, E2)]),
    'cubeP': (x * y * z - x ** 3,
              [(x * (y + z - x) / 2, E1), (-x / 2, E2)]),
}
for key, (goal, terms) in CUB.items():
    cert('cubic.' + key, goal, terms)

# `y^2 = x*z`, used to identify the second root
cert('cubic.yzRel', y ** 2 - x * z,
     [(sp.Rational(1, 2) * (x + y - z), E1), (sp.Rational(1, 2), E2),
      (-x, E1)])
# `3x^2 = 0` once `y = x`
cert('cubic.degenerate', 3 * x ** 2,
     [(1, x ** 2 + x * y + y ** 2), (-(y + 2 * x), y - x)])

# the primitive cube root rho = (-1 + i sqrt 3)/2
RHO = (-1 + ii * sq3) / 2
cert('rho.quadratic', sp.expand(RHO ** 2 + RHO + 1),
     [(sp.Rational(-1, 4), sq3 ** 2 - 3), (sq3 ** 2 / 4, ii ** 2 + 1)])
cert('rho.factor', sp.expand((ww - rho) * (ww - rho ** 2)),
     [(1, ww ** 2 + ww + 1), (rho - 1 - ww, rho ** 2 + rho + 1)])
cert('rho.cubic', sp.expand((ww - 1) * (ww ** 2 + ww + 1)), [(1, ww ** 3 - 1)])

# three unit-modulus numbers summing to zero
cert('unit.sym2', m1 * m2 + m1 * m3 + m2 * m3,
     [(m1 * m2 * m3, s1 + s2 + s3), (-(m2 * m3), m1 * s1 - 1),
      (-(m1 * m3), m2 * s2 - 1), (-(m1 * m2), m3 * s3 - 1)])
cert('unit.sumSq', m1 ** 2 + m2 ** 2 + m3 ** 2,
     [(m1 + m2 + m3, m1 + m2 + m3), (-2, m1 * m2 + m1 * m3 + m2 * m3)])

# ---------------------------------------------------------------------------
# 3.  the determinant of the symmetric zero-diagonal 4x4 matrix
# ---------------------------------------------------------------------------

C = sp.Matrix([[0, c12, c13, c14],
               [c12, 0, c23, c24],
               [c13, c23, 0, c34],
               [c14, c24, c34, 0]])
X, Y, Z = c12 * c34, c13 * c24, c14 * c23
DET = sp.expand(C.det())
detPoly = sp.expand(X ** 2 + Y ** 2 + Z ** 2 - 2 * X * Y - 2 * X * Z - 2 * Y * Z)
assert sp.expand(DET - detPoly) == 0
CHECKS.append('det.expansion')

# `x^2+y^2+z^2 = 0` from the matching equation and a vanishing determinant
cert('det.sumSq', x ** 2 + y ** 2 + z ** 2,
     [((x + y + z) / 2, x + y + z),
      (sp.Rational(1, 2), x ** 2 + y ** 2 + z ** 2
       - 2 * x * y - 2 * x * z - 2 * y * z)])

# ---------------------------------------------------------------------------
# 4.  Cramer: det * r_i is an explicit combination of the four kernel rows
# ---------------------------------------------------------------------------

RVEC = [r1, r2, r3, r4]
ROWS = [sum(C[i, j] * RVEC[j] for j in range(4)) for i in range(4)]
ADJ = C.adjugate()
CRAMER = []
for i in range(4):
    coefs = [sp.factor(ADJ[i, j]) for j in range(4)]
    cert('cramer.r%d' % (i + 1), sp.expand(DET * RVEC[i]),
         list(zip(coefs, ROWS)))
    CRAMER.append(coefs)

# ---------------------------------------------------------------------------
# 5.  the vertex factorization of the edge weights
# ---------------------------------------------------------------------------

G2 = w12 * w13 * w23                    # g * g
NUM = {1: w12 * w13, 2: w12 * w23, 3: w13 * w23, 4: w14 * w23}
H12 = w12 * w34 - w13 * w24
H23 = w13 * w24 - w14 * w23
VERT = {
    (1, 2): (w12, []),
    (1, 3): (w13, []),
    (1, 4): (w14, []),
    (2, 3): (w23, []),
    (2, 4): (w24, [(w12 * w23, H23)]),
    (3, 4): (w34, [(w13 * w23, H12), (w13 * w23, H23)]),
}
for (i, j), (wij, extra) in VERT.items():
    goal = sp.expand(wij * G2 - NUM[i] * NUM[j])
    cert('vertex.w%d%d' % (i, j), goal, extra)

# ---------------------------------------------------------------------------
# emit the Lean module
# ---------------------------------------------------------------------------

CVARS = 'c12 c13 c14 c23 c24 c34'
RVARS = 'r1 r2 r3 r4'

KERNEL_ROWS = [
    'c12 * r2 + c13 * r3 + c14 * r4 = 0',
    'c12 * r1 + c23 * r3 + c24 * r4 = 0',
    'c13 * r1 + c23 * r2 + c34 * r4 = 0',
    'c14 * r1 + c24 * r2 + c34 * r3 = 0',
]

HEADER = '''import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# The symmetric `K₄` kernel of the order-five orbit 36

This module is the bit-string-free algebra layer of the orbit-36 rigidity
theorem.  It mentions no fibers, no Pauli operators and no moment data: only
complex numbers, and the relations that the cross Knill--Laflamme equations
impose on them.  In the notation of the source chapter, the four vertex
amplitudes are `r₁, …, r₄`, the six edge amplitudes are `c₁₂, …, c₃₄`, and the
three opposite-edge products are

```
x = c₁₂ c₃₄ ,   y = c₁₃ c₂₄ ,   z = c₁₄ c₂₃ .
```

The five sections are, in dependency order:

1. **The pair relation.**  For a fixed vertex `i` the three dressings
   `XᵢZⱼ` give a `3 × 3` system with matrix `[[-1,1,1],[1,-1,1],[1,1,-1]]` of
   determinant `4`, so the three differences vanish and the `Xᵢ` equation
   collapses to a star sum.

2. **The cubic-root lemma.**  Three complex numbers with zero sum and zero sum
   of squares satisfy `y³ = z³ = x³ = xyz`; when `x ≠ 0` they are `x` times
   `(1, w, w²)` for a primitive cube root of unity, which is `(-1 ± i√3)/2`.
   The route is division free: squaring the first hypothesis gives
   `xy + yz + zx = 0` directly, hence `yz = x²`, `zx = y²`, `xy = z²`.

3. **The determinant.**  The determinant of the symmetric zero-diagonal `4 × 4`
   matrix of edge amplitudes is `x² + y² + z² - 2xy - 2xz - 2yz`.  This is the
   genuine `Matrix.det`, expanded by `simp` and closed by `ring`.

4. **Kernel nontriviality.**  Four scalar kernel equations with one nonzero
   coordinate force that determinant to vanish.  The proof is the Cramer
   identity `det · rᵢ = ∑ⱼ adj(C)ᵢⱼ (C r)ⱼ`, one `linear_combination` per
   coordinate with the cofactors as coefficients, followed by a four-way case
   split on which coordinate is nonzero.  No division, no rank argument.

5. **Vertex factorization.**  Positive edge weights whose three opposite
   products agree factor as `w_{ij} = sᵢ sⱼ`.

Composed, sections 2--4 give `oppositeWeights`: the matching equation plus a
nontrivial kernel force `|c₁₂|²|c₃₄|² = |c₁₃|²|c₂₄|² = |c₁₄|²|c₂₃|²`, which is
exactly what the magnitude stage of the chapter consumes.

Every polynomial certificate below is produced and checked by
`tools/generators/gen36alg.py`.  `native_decide` is not used.
-/

namespace SixQubit.K4Kernel

open scoped ComplexConjugate

noncomputable section

/-! ## 1.  The pair relation -/

/-- The coefficient matrix `[[-1,1,1],[1,-1,1],[1,1,-1]]` of the three `XᵢZⱼ`
dressings has determinant `4`, so its kernel is trivial.  Adding any two of the
rows isolates twice one coordinate. -/
theorem walsh3_eq_zero {d1 d2 d3 : ℂ}
    (h1 : -d1 + d2 + d3 = 0)
    (h2 : d1 - d2 + d3 = 0)
    (h3 : d1 + d2 - d3 = 0) :
    d1 = 0 ∧ d2 = 0 ∧ d3 = 0 :=
  ⟨by linear_combination h2 / 2 + h3 / 2,
   by linear_combination h1 / 2 + h3 / 2,
   by linear_combination h1 / 2 + h2 / 2⟩

/-- **The pair relation.**  The three weight-two dressings `XᵢZⱼ`, `j ≠ i`,
force `Uⱼ = Vⱼ` for each of the three `j`.  Here `Uⱼ = conj (c_{ij}) Rⱼ` and
`Vⱼ = conj (rⱼ) C_{ij}`, but the lemma is pure linear algebra over `ℂ`. -/
theorem pair_relation {U1 U2 U3 V1 V2 V3 : ℂ}
    (h1 : -(U1 - V1) + (U2 - V2) + (U3 - V3) = 0)
    (h2 : (U1 - V1) - (U2 - V2) + (U3 - V3) = 0)
    (h3 : (U1 - V1) + (U2 - V2) - (U3 - V3) = 0) :
    U1 = V1 ∧ U2 = V2 ∧ U3 = V3 :=
  ⟨by linear_combination h2 / 2 + h3 / 2,
   by linear_combination h1 / 2 + h3 / 2,
   by linear_combination h1 / 2 + h2 / 2⟩

/-- **The `Xᵢ` equation collapses to a star sum.**  Together with the pair
relation, the undressed `Xᵢ` equation `∑ⱼ (Uⱼ + Vⱼ) = 0` becomes
`∑ⱼ Uⱼ = 0`. -/
theorem xi_reduction {U1 U2 U3 V1 V2 V3 : ℂ}
    (hX : U1 + V1 + (U2 + V2) + (U3 + V3) = 0)
    (h1 : -(U1 - V1) + (U2 - V2) + (U3 - V3) = 0)
    (h2 : (U1 - V1) - (U2 - V2) + (U3 - V3) = 0)
    (h3 : (U1 - V1) + (U2 - V2) - (U3 - V3) = 0) :
    U1 = V1 ∧ U2 = V2 ∧ U3 = V3 ∧ U1 + U2 + U3 = 0 := by
  obtain ⟨p1, p2, p3⟩ := pair_relation h1 h2 h3
  exact ⟨p1, p2, p3, by linear_combination hX / 2 + p1 / 2 + p2 / 2 + p3 / 2⟩

/-- The same statement with the amplitudes spelled out, which is the shape the
cross Knill--Laflamme rows of orbit 36 produce: `cⱼ` is the edge amplitude
`c_{ij}`, `rⱼ` the vertex amplitude, and `Cⱼ`, `Rⱼ` their partners in the top
logical word. -/
theorem starSum_of_dressings {c1 c2 c3 r1 r2 r3 R1 R2 R3 C1 C2 C3 : ℂ}
    (hX : star c1 * R1 + star r1 * C1 + (star c2 * R2 + star r2 * C2)
            + (star c3 * R3 + star r3 * C3) = 0)
    (h1 : -(star c1 * R1 - star r1 * C1) + (star c2 * R2 - star r2 * C2)
            + (star c3 * R3 - star r3 * C3) = 0)
    (h2 : (star c1 * R1 - star r1 * C1) - (star c2 * R2 - star r2 * C2)
            + (star c3 * R3 - star r3 * C3) = 0)
    (h3 : (star c1 * R1 - star r1 * C1) + (star c2 * R2 - star r2 * C2)
            - (star c3 * R3 - star r3 * C3) = 0) :
    star c1 * R1 = star r1 * C1 ∧ star c2 * R2 = star r2 * C2
      ∧ star c3 * R3 = star r3 * C3
      ∧ star c1 * R1 + star c2 * R2 + star c3 * R3 = 0 :=
  xi_reduction hX h1 h2 h3

/-! ## 2.  The cubic-root lemma -/

/-- Squaring `x + y + z = 0` and subtracting `x² + y² + z² = 0` gives the second
elementary symmetric function for free. -/
theorem sym2_eq_zero {x y z : ℂ}
    (h1 : x + y + z = 0) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 0) :
    x * y + y * z + z * x = 0 := by
  linear_combination (x + y + z) / 2 * h1 - h2 / 2

/-- Eliminating `z` between the two hypotheses: `y` is a root of
`t² + x t + x² = 0`. -/
theorem sq_rel {x y z : ℂ}
    (h1 : x + y + z = 0) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 0) :
    x ^ 2 + x * y + y ^ 2 = 0 := by
  linear_combination (x + y - z) / 2 * h1 + h2 / 2

/-- Each of the three numbers is the product of the other two. -/
theorem prod_pairs {x y z : ℂ}
    (h1 : x + y + z = 0) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 0) :
    y * z = x ^ 2 ∧ z * x = y ^ 2 ∧ x * y = z ^ 2 :=
  ⟨by linear_combination (y + z - x) / 2 * h1 - h2 / 2,
   by linear_combination (z + x - y) / 2 * h1 - h2 / 2,
   by linear_combination (x + y - z) / 2 * h1 - h2 / 2⟩

/-- **The cubic-root lemma, division-free form.**  Zero sum and zero sum of
squares make `x`, `y`, `z` the three roots of `t³ = xyz`. -/
theorem cube_eq {x y z : ℂ}
    (h1 : x + y + z = 0) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 0) :
    y ^ 3 = x ^ 3 ∧ z ^ 3 = x ^ 3 ∧ x * y * z = x ^ 3 :=
  ⟨by linear_combination (y - x) * (x + y - z) / 2 * h1 + (y - x) / 2 * h2,
   by linear_combination (z - x) * (x + z - y) / 2 * h1 + (z - x) / 2 * h2,
   by linear_combination x * (y + z - x) / 2 * h1 - x / 2 * h2⟩

/-- **The moduli are equal.**  This is the form the magnitude stage of the
chapter consumes; it needs no nonvanishing hypothesis. -/
theorem normSq_eq {x y z : ℂ}
    (h1 : x + y + z = 0) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 0) :
    Complex.normSq y = Complex.normSq x ∧ Complex.normSq z = Complex.normSq x := by
  obtain ⟨hy, hz, -⟩ := cube_eq h1 h2
  have cube : ∀ {p q : ℂ}, p ^ 3 = q ^ 3 → Complex.normSq p = Complex.normSq q := by
    intro p q h
    have h3 : Complex.normSq p ^ 3 = Complex.normSq q ^ 3 := by
      rw [← map_pow, ← map_pow, h]
    exact (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective h3
  exact ⟨cube hy, cube hz⟩

/-- A primitive cube root of unity, `exp (2πi/3) = (-1 + i√3)/2`. -/
def rho : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2

theorem rho_quadratic : rho ^ 2 + rho + 1 = 0 := by
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  simp only [rho]
  linear_combination -h3 / 4 + (Real.sqrt 3 : ℂ) ^ 2 / 4 * Complex.I_sq

theorem rho_pow_three : rho ^ 3 = 1 := by
  linear_combination (rho - 1) * rho_quadratic

/-- A cube root of unity other than `1` is `rho` or `rho²`. -/
theorem cubeRoot_eq {w : ℂ} (h : w ^ 3 = 1) (hne : w ≠ 1) :
    w = rho ∨ w = rho ^ 2 := by
  have hq : w ^ 2 + w + 1 = 0 := by
    rcases mul_eq_zero.mp (show (w - 1) * (w ^ 2 + w + 1) = 0 by
      linear_combination h) with h' | h'
    · exact absurd (sub_eq_zero.mp h') hne
    · exact h'
  rcases mul_eq_zero.mp (show (w - rho) * (w - rho ^ 2) = 0 by
    linear_combination hq + (rho - 1 - w) * rho_quadratic) with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (sub_eq_zero.mp h')

/-- **The cubic-root lemma, normalized form.**  With `x ≠ 0` the triple is
`x · (1, w, w²)` for a primitive cube root of unity `w`. -/
theorem exists_cubeRoot {x y z : ℂ}
    (h1 : x + y + z = 0) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 0) (hx : x ≠ 0) :
    ∃ w : ℂ, w ^ 3 = 1 ∧ w ≠ 1 ∧ y = w * x ∧ z = w ^ 2 * x := by
  have hs := sq_rel h1 h2
  refine ⟨y / x, ?_, ?_, ?_, ?_⟩
  · rw [div_pow, (cube_eq h1 h2).1, div_self (pow_ne_zero 3 hx)]
  · intro hw
    have hyx : y = x := by field_simp at hw; exact hw
    have hx2 : x ^ 2 = 0 := by
      linear_combination hs / 3 - (y + 2 * x) / 3 * hyx
    exact hx (by simpa using hx2)
  · field_simp
  · have hstep : (y / x) ^ 2 * x = y ^ 2 / x := by field_simp
    rw [hstep, eq_comm, div_eq_iff hx]
    linear_combination hs - x * h1

/-- **Three unit-modulus numbers summing to zero** are a common phase times
`(1, w, w²)`.  This is the phase-rigidity form of the same lemma: the conjugate
sum supplies the second symmetric function without any division. -/
theorem unit_triple {m1 m2 m3 : ℂ}
    (n1 : Complex.normSq m1 = 1) (n2 : Complex.normSq m2 = 1)
    (n3 : Complex.normSq m3 = 1) (hs : m1 + m2 + m3 = 0) :
    ∃ w : ℂ, w ^ 3 = 1 ∧ w ≠ 1 ∧ m2 = w * m1 ∧ m3 = w ^ 2 * m1 := by
  have unit : ∀ {m : ℂ}, Complex.normSq m = 1 → m * star m = 1 := by
    intro m hm
    rw [mul_comm, SixQubit.star_mul_self, hm]
    norm_num
  have hc : star m1 + star m2 + star m3 = 0 := by
    have := congrArg star hs
    simpa using this
  have he2 : m1 * m2 + m1 * m3 + m2 * m3 = 0 := by
    linear_combination (m1 * m2 * m3) * hc - (m2 * m3) * unit n1
      - (m1 * m3) * unit n2 - (m1 * m2) * unit n3
  have hsq : m1 ^ 2 + m2 ^ 2 + m3 ^ 2 = 0 := by
    linear_combination (m1 + m2 + m3) * hs - 2 * he2
  have hm1 : m1 ≠ 0 := by
    intro h
    rw [h] at n1
    simp at n1
  exact exists_cubeRoot hs hsq hm1

/-! ## 3.  The determinant of the symmetric zero-diagonal `4 × 4` matrix -/

/-- The `K₄` amplitude matrix: symmetric, zero diagonal, entries the six edge
amplitudes. -/
def K4 (c12 c13 c14 c23 c24 c34 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, c12, c13, c14;
     c12, 0, c23, c24;
     c13, c23, 0, c34;
     c14, c24, c34, 0]

/-- `x² + y² + z² - 2xy - 2xz - 2yz`, the determinant written in the three
opposite-edge products. -/
def detPoly (x y z : ℂ) : ℂ :=
  x ^ 2 + y ^ 2 + z ^ 2 - 2 * (x * y) - 2 * (x * z) - 2 * (y * z)

/-- **The determinant expansion.**  For the symmetric zero-diagonal `4 × 4`
matrix, `det C = x² + y² + z² - 2xy - 2xz - 2yz` with `x = c₁₂c₃₄`,
`y = c₁₃c₂₄`, `z = c₁₄c₂₃`. -/
theorem det_K4 (c12 c13 c14 c23 c24 c34 : ℂ) :
    (K4 c12 c13 c14 c23 c24 c34).det
      = detPoly (c12 * c34) (c13 * c24) (c14 * c23) := by
  simp only [K4, detPoly]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- `x² + y² + z² = 0` follows from the matching equation `x + y + z = 0` and a
vanishing determinant. -/
theorem sumSq_eq_zero {x y z : ℂ} (hm : x + y + z = 0) (hd : detPoly x y z = 0) :
    x ^ 2 + y ^ 2 + z ^ 2 = 0 := by
  simp only [detPoly] at hd
  linear_combination (x + y + z) / 2 * hm + hd / 2

/-! ## 4.  A nontrivial kernel kills the determinant -/
'''

FOOTER = '''
/-! ## 5.  Vertex factorization of the edge weights -/

/-- **Vertex factorization.**  Positive edge weights on `K₄` whose three
opposite-edge products agree factor through the vertices.  The witness is
`s₁ = √(w₁₂w₁₃/w₂₃)` and `sⱼ = w₁ⱼ/s₁`, written here over the common
denominator `g = √(w₁₂w₁₃w₂₃)`.

Only four of the six weights are assumed positive: positivity of `w₂₄` and
`w₃₄` is a consequence, since the conclusion exhibits them as products of
positive numbers. -/
theorem vertex_factorization {w12 w13 w14 w23 w24 w34 : ℝ}
    (p12 : 0 < w12) (p13 : 0 < w13) (p14 : 0 < w14) (p23 : 0 < w23)
    (h1 : w12 * w34 = w13 * w24) (h2 : w13 * w24 = w14 * w23) :
    ∃ s1 s2 s3 s4 : ℝ, 0 < s1 ∧ 0 < s2 ∧ 0 < s3 ∧ 0 < s4 ∧
      w12 = s1 * s2 ∧ w13 = s1 * s3 ∧ w14 = s1 * s4 ∧
      w23 = s2 * s3 ∧ w24 = s2 * s4 ∧ w34 = s3 * s4 := by
  have hprod : (0 : ℝ) < w12 * w13 * w23 := mul_pos (mul_pos p12 p13) p23
  obtain ⟨g, hgpos, hg⟩ : ∃ g : ℝ, 0 < g ∧ g * g = w12 * w13 * w23 :=
    ⟨Real.sqrt (w12 * w13 * w23), Real.sqrt_pos.mpr hprod,
      Real.mul_self_sqrt hprod.le⟩
  refine ⟨w12 * w13 / g, w12 * w23 / g, w13 * w23 / g, w14 * w23 / g,
    div_pos (mul_pos p12 p13) hgpos, div_pos (mul_pos p12 p23) hgpos,
    div_pos (mul_pos p13 p23) hgpos, div_pos (mul_pos p14 p23) hgpos,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [div_mul_div_comm, hg, eq_div_iff hprod.ne']
'''


def emit():
    lines = [HEADER.rstrip('\n')]
    w = lines.append

    # --- section 4: the four Cramer identities ------------------------------
    names = ['r1', 'r2', 'r3', 'r4']
    for i in range(4):
        w('')
        w('/-- Cramer identity for coordinate `%s`: `det C · %s` is the explicit'
          % (names[i], names[i]))
        w('combination of the four kernel rows with the cofactors of row %d as'
          % (i + 1))
        w('coefficients. -/')
        w('theorem detPoly_mul_%s {%s %s : ℂ}' % (names[i], CVARS, RVARS))
        for k in range(4):
            tail = ' :' if k == 3 else ''
            w('    (e%d : %s)%s' % (k + 1, KERNEL_ROWS[k], tail))
        w('    detPoly (c12 * c34) (c13 * c24) (c14 * c23) * %s = 0 := by'
          % names[i])
        w('  simp only [detPoly]')
        body = ''
        for k in range(4):
            co = CRAMER[i][k]
            negative = sp.sstr(co).startswith('-')
            expr = -co if negative else co
            piece = '(%s) * e%d' % (lean(expr), k + 1)
            if k == 0:
                body = ('-' + piece) if negative else piece
            else:
                body += (' - ' if negative else ' + ') + piece
        for ln in wrap('  linear_combination ', body, '    '):
            w(ln)

    # --- the four-way case split -------------------------------------------
    w('')
    w('/-- **Kernel nontriviality.**  If the four kernel rows hold and some')
    w('coordinate of `r` is nonzero, the determinant vanishes. -/')
    w('theorem detPoly_eq_zero {%s %s : ℂ}' % (CVARS, RVARS))
    for k in range(4):
        w('    (e%d : %s)' % (k + 1, KERNEL_ROWS[k]))
    w('    (hr : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0 ∨ r4 ≠ 0) :')
    w('    detPoly (c12 * c34) (c13 * c24) (c14 * c23) = 0 := by')
    w('  rcases hr with h | h | h | h')
    for i in range(4):
        w('  · exact (mul_eq_zero.mp (detPoly_mul_%s e1 e2 e3 e4)).resolve_right h'
          % names[i])

    w('')
    w('/-- The same statement for the honest `Matrix.det`. -/')
    w('theorem det_K4_eq_zero {%s %s : ℂ}' % (CVARS, RVARS))
    for k in range(4):
        w('    (e%d : %s)' % (k + 1, KERNEL_ROWS[k]))
    w('    (hr : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0 ∨ r4 ≠ 0) :')
    w('    (K4 c12 c13 c14 c23 c24 c34).det = 0 := by')
    w('  rw [det_K4]')
    w('  exact detPoly_eq_zero e1 e2 e3 e4 hr')

    # --- the punchline ------------------------------------------------------
    w('')
    w('/-- **The opposite edge weights agree.**  Sections 2--4 composed: the')
    w('matching equation `c₁₂c₃₄ + c₁₃c₂₄ + c₁₄c₂₃ = 0` together with a nontrivial')
    w('kernel of the edge matrix forces')
    w('`|c₁₂|²|c₃₄|² = |c₁₃|²|c₂₄|² = |c₁₄|²|c₂₃|²`. -/')
    w('theorem oppositeWeights {%s %s : ℂ}' % (CVARS, RVARS))
    for k in range(4):
        w('    (e%d : %s)' % (k + 1, KERNEL_ROWS[k]))
    w('    (hr : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0 ∨ r4 ≠ 0)')
    w('    (hm : c12 * c34 + c13 * c24 + c14 * c23 = 0) :')
    w('    Complex.normSq c12 * Complex.normSq c34')
    w('        = Complex.normSq c13 * Complex.normSq c24')
    w('      ∧ Complex.normSq c13 * Complex.normSq c24')
    w('        = Complex.normSq c14 * Complex.normSq c23 := by')
    w('  have hsq := sumSq_eq_zero hm (detPoly_eq_zero e1 e2 e3 e4 hr)')
    w('  obtain ⟨hy, hz⟩ := normSq_eq hm hsq')
    w('  rw [← Complex.normSq_mul, ← Complex.normSq_mul, ← Complex.normSq_mul]')
    w('  exact ⟨hy.symm, hy.trans hz.symm⟩')

    lines.append(FOOTER.rstrip('\n'))

    # --- the six cleared vertex goals ---------------------------------------
    order = [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
    for (i, j) in order:
        extra = VERT[(i, j)][1]
        if not extra:
            w('  · ring')
        else:
            body = ''
            for k, (co, hy) in enumerate(extra):
                tag = 'h1' if hy is H12 else 'h2'
                piece = '(%s) * %s' % (lean(co), tag)
                body += (piece if k == 0 else ' + ' + piece)
            for ln in wrap('  · linear_combination ', body, '      '):
                w(ln)

    w('')
    w('end')
    w('')
    w('end SixQubit.K4Kernel')
    return '\n'.join(lines) + '\n'


def instance_check():
    """Cheap re-check that the abstract algebra above is the orbit-36 algebra.

    First the fibers, in the *repository's* bit order (`tools/core/orbit.py`
    indexes a string left to right, `a[i]` against `s[i]`); the source chapter
    uses the opposite convention, so this has to be checked and not assumed.
    Then the canonical amplitudes of the chapter are substituted into the four
    kernel rows, the matching equation, the determinant, and the vertex
    factorization.
    """
    from orbit import fiber

    def point(support, last):
        return ''.join('1' if i in support else '0' for i in range(4)) + last

    named = {'u': point(set(), '00'), 'v': point(set(), '11')}
    for i in range(4):
        named['s%d' % (i + 1)] = point(set(range(4)) - {i}, '10')
    for i in range(4):
        for j in range(i + 1, 4):
            named['e%d%d' % (i + 1, j + 1)] = point({i, j}, '01')

    S0 = set(fiber([1, 1, 1, 1, 2, 3], 5, 0))
    S4 = set(fiber([1, 1, 1, 1, 2, 3], 5, 4))
    assert len(S0) == len(S4) == 12, (len(S0), len(S4))
    assert set(named.values()) == S0, sorted(S0 - set(named.values()))
    assert S4 == {''.join('01'[b == '0'] for b in s) for s in S0}

    # canonical amplitudes: r_i = 1/sqrt 10, c_ij = colour/sqrt 15 with the
    # proper three-edge-colouring 12|34, 13|24, 14|23 of K_4
    om = sp.Rational(-1, 2) + sp.I * sp.sqrt(3) / 2
    rr = {i: 1 / sp.sqrt(10) for i in (1, 2, 3, 4)}
    colour = {(1, 2): 1, (3, 4): 1, (1, 3): om, (2, 4): om,
              (1, 4): om ** 2, (2, 3): om ** 2}
    cc = {}
    for (i, j), col in colour.items():
        cc[(i, j)] = col / sp.sqrt(15)
        cc[(j, i)] = col / sp.sqrt(15)

    for i in (1, 2, 3, 4):
        row = sum(cc[(i, j)] * rr[j] for j in (1, 2, 3, 4) if j != i)
        assert sp.simplify(row) == 0, (i, sp.simplify(row))

    xv, yv, zv = cc[(1, 2)] * cc[(3, 4)], cc[(1, 3)] * cc[(2, 4)], \
        cc[(1, 4)] * cc[(2, 3)]
    assert sp.simplify(xv + yv + zv) == 0
    assert sp.simplify(xv ** 2 + yv ** 2 + zv ** 2) == 0
    assert sp.simplify(xv ** 2 + yv ** 2 + zv ** 2
                       - 2 * xv * yv - 2 * xv * zv - 2 * yv * zv) == 0

    wt = {k: sp.simplify(sp.Abs(v) ** 2) for k, v in cc.items()}
    for k, v in wt.items():
        assert v == sp.Rational(1, 15), (k, v)
    assert all(sp.simplify(rr[i] * sp.conjugate(rr[i]) - sp.Rational(1, 10)) == 0
               for i in rr)
    sval = sp.sqrt(sp.Rational(1, 15))
    for i in range(1, 5):
        for j in range(i + 1, 5):
            assert sp.simplify(wt[(i, j)] - sval * sval) == 0
    return len(S0)


def main() -> None:
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(os.path.dirname(here))
    target = os.path.join(root, 'SixQubit', 'K4Kernel.lean')
    size = instance_check()
    text = emit()
    with open(target, 'w', encoding='utf-8', newline='\n') as handle:
        handle.write(text)
    print('checked %d polynomial certificates' % len(CHECKS))
    print('det C = %s' % DET)
    print('orbit-36 fibers verified against tools/core/orbit.fiber: '
          '|S0| = |S4| = %d, S4 = complement(S0)' % size)
    print('canonical amplitudes satisfy C r = 0, x + y + z = 0, '
          'x^2 + y^2 + z^2 = 0, det = 0, w_ij = 1/15')
    print('wrote %s (%d lines)' % (target, text.count('\n')))


if __name__ == '__main__':
    main()
