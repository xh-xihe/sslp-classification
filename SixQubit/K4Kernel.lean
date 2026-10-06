import Mathlib

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

/-- Cramer identity for coordinate `r1`: `det C · r1` is the explicit
combination of the four kernel rows with the cofactors of row 1 as
coefficients. -/
theorem detPoly_mul_r1 {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0) :
    detPoly (c12 * c34) (c13 * c24) (c14 * c23) * r1 = 0 := by
  simp only [detPoly]
  linear_combination (2 * c23 * c24 * c34) * e1 + (c34 * (c12 * c34 - c13 * c24 - c14 * c23)) * e2
    - (c24 * (c12 * c34 - c13 * c24 + c14 * c23)) * e3
    - (c23 * (c12 * c34 + c13 * c24 - c14 * c23)) * e4

/-- Cramer identity for coordinate `r2`: `det C · r2` is the explicit
combination of the four kernel rows with the cofactors of row 2 as
coefficients. -/
theorem detPoly_mul_r2 {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0) :
    detPoly (c12 * c34) (c13 * c24) (c14 * c23) * r2 = 0 := by
  simp only [detPoly]
  linear_combination (c34 * (c12 * c34 - c13 * c24 - c14 * c23)) * e1 + (2 * c13 * c14 * c34) * e2
    - (c14 * (c12 * c34 + c13 * c24 - c14 * c23)) * e3
    - (c13 * (c12 * c34 - c13 * c24 + c14 * c23)) * e4

/-- Cramer identity for coordinate `r3`: `det C · r3` is the explicit
combination of the four kernel rows with the cofactors of row 3 as
coefficients. -/
theorem detPoly_mul_r3 {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0) :
    detPoly (c12 * c34) (c13 * c24) (c14 * c23) * r3 = 0 := by
  simp only [detPoly]
  linear_combination -(c24 * (c12 * c34 - c13 * c24 + c14 * c23)) * e1
    - (c14 * (c12 * c34 + c13 * c24 - c14 * c23)) * e2 + (2 * c12 * c14 * c24) * e3
    + (c12 * (c12 * c34 - c13 * c24 - c14 * c23)) * e4

/-- Cramer identity for coordinate `r4`: `det C · r4` is the explicit
combination of the four kernel rows with the cofactors of row 4 as
coefficients. -/
theorem detPoly_mul_r4 {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0) :
    detPoly (c12 * c34) (c13 * c24) (c14 * c23) * r4 = 0 := by
  simp only [detPoly]
  linear_combination -(c23 * (c12 * c34 + c13 * c24 - c14 * c23)) * e1
    - (c13 * (c12 * c34 - c13 * c24 + c14 * c23)) * e2
    + (c12 * (c12 * c34 - c13 * c24 - c14 * c23)) * e3 + (2 * c12 * c13 * c23) * e4

/-- **Kernel nontriviality.**  If the four kernel rows hold and some
coordinate of `r` is nonzero, the determinant vanishes. -/
theorem detPoly_eq_zero {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hr : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0 ∨ r4 ≠ 0) :
    detPoly (c12 * c34) (c13 * c24) (c14 * c23) = 0 := by
  rcases hr with h | h | h | h
  · exact (mul_eq_zero.mp (detPoly_mul_r1 e1 e2 e3 e4)).resolve_right h
  · exact (mul_eq_zero.mp (detPoly_mul_r2 e1 e2 e3 e4)).resolve_right h
  · exact (mul_eq_zero.mp (detPoly_mul_r3 e1 e2 e3 e4)).resolve_right h
  · exact (mul_eq_zero.mp (detPoly_mul_r4 e1 e2 e3 e4)).resolve_right h

/-- The same statement for the honest `Matrix.det`. -/
theorem det_K4_eq_zero {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hr : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0 ∨ r4 ≠ 0) :
    (K4 c12 c13 c14 c23 c24 c34).det = 0 := by
  rw [det_K4]
  exact detPoly_eq_zero e1 e2 e3 e4 hr

/-- **The opposite edge weights agree.**  Sections 2--4 composed: the
matching equation `c₁₂c₃₄ + c₁₃c₂₄ + c₁₄c₂₃ = 0` together with a nontrivial
kernel of the edge matrix forces
`|c₁₂|²|c₃₄|² = |c₁₃|²|c₂₄|² = |c₁₄|²|c₂₃|²`. -/
theorem oppositeWeights {c12 c13 c14 c23 c24 c34 r1 r2 r3 r4 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hr : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0 ∨ r4 ≠ 0)
    (hm : c12 * c34 + c13 * c24 + c14 * c23 = 0) :
    Complex.normSq c12 * Complex.normSq c34
        = Complex.normSq c13 * Complex.normSq c24
      ∧ Complex.normSq c13 * Complex.normSq c24
        = Complex.normSq c14 * Complex.normSq c23 := by
  have hsq := sumSq_eq_zero hm (detPoly_eq_zero e1 e2 e3 e4 hr)
  obtain ⟨hy, hz⟩ := normSq_eq hm hsq
  rw [← Complex.normSq_mul, ← Complex.normSq_mul, ← Complex.normSq_mul]
  exact ⟨hy.symm, hy.trans hz.symm⟩

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
  · ring
  · ring
  · ring
  · ring
  · linear_combination (w12 * w23) * h2
  · linear_combination (w13 * w23) * h1 + (w13 * w23) * h2

end

end SixQubit.K4Kernel
