import Mathlib

import SS.FullKL
import SixQubit.Common
import SixQubit.Frame

/-!
# The parity-four `ℂ²` obstruction

Orbits 14, 15 and 24 all reduce to the same picture.  A free qubit -- a
zero-angle qubit, or the effective qubit of a repetition pair -- collects the
amplitudes into vectors `c_x, d_y ∈ ℂ²` indexed by the two parity classes of
four effective bits.  The weight-at-most-two Knill--Laflamme rows isolate
`⟨c_x , d_y⟩ = 0` on every Hamming edge, and the diagonal rows on the free
qubit equate the two frame operators.

The paper argues through connectivity of the positive support.  That is
awkward to formalize, because the support depends on where in the moment
cross-polytope one sits.  The route taken here is a uniform inequality that
never mentions the support at all.

Write `c ∧ d = c₀d₁ - c₁d₀`.  Lagrange's identity says
`|c ∧ d|² + |⟨c,d⟩|² = ‖c‖²‖d‖²`, so on an edge the wedge carries the whole
product of masses.  Summing the wedge over *all* pairs, edge or not, gives
a quantity fixed by the frames alone,

```
Σ_{x,y} |c_x ∧ d_y|² = 2 A C - 2 |B|²  ≤  (A + C)² / 2 ,
```
where `A, C, B` are the entries of the common frame operator.  The moment
system supplies the missing half: the degree-at-most-two moments force
`Σ_{y ~ x} ‖d_y‖² = μ/2 + ‖c_x‖²` on a three-cube slice of total mass `μ`,
so the edge part of the wedge sum is already `μ²/2 + Σ‖c_x‖⁴`.  The two
bounds collide, leaving `Σ‖c_x‖⁴ ≤ 0`, hence `μ = 0`.

No division, no ratios, no case split on the support.  `native_decide` is
not used.
-/

namespace SixQubit.ParityFour

open scoped ComplexConjugate

noncomputable section

/-! ## Lagrange's identity -/

/-- `|u ∧ v|² + |⟨u,v⟩|² = ‖u‖²‖v‖²` in `ℂ²`. -/
theorem lagrange (u0 u1 v0 v1 : ℂ) :
    Complex.normSq (u0 * v1 - u1 * v0)
        + Complex.normSq (star u0 * v0 + star u1 * v1)
      = (Complex.normSq u0 + Complex.normSq u1) * (Complex.normSq v0 + Complex.normSq v1) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- On an orthogonal pair the wedge carries the full product of masses. -/
theorem wedge_of_orth {u0 u1 v0 v1 : ℂ}
    (h : star u0 * v0 + star u1 * v1 = 0) :
    Complex.normSq (u0 * v1 - u1 * v0) = (Complex.normSq u0 + Complex.normSq u1) * (Complex.normSq v0 + Complex.normSq v1) := by
  have := lagrange u0 u1 v0 v1
  rw [h] at this
  simpa using this

/-! ## Propagation -/

/-- Two vectors orthogonal to a common `c` are parallel, weighted by `‖c‖²`.
No division and no nonvanishing hypothesis. -/
theorem prop_wedge {c0 c1 d0 d1 e0 e1 : ℂ}
    (h1 : star c0 * d0 + star c1 * d1 = 0)
    (h2 : star c0 * e0 + star c1 * e1 = 0) :
    (c0 * star c0 + c1 * star c1) * (d0 * e1 - d1 * e0) = 0 := by
  linear_combination (c0 * e1 - c1 * e0) * h1 + (c1 * d0 - c0 * d1) * h2

/-- Plücker: parallelism propagates through a nonzero middle vector. -/
theorem plucker {a0 a1 b0 b1 c0 c1 : ℂ}
    (hab : a0 * b1 - a1 * b0 = 0) (hac : a0 * c1 - a1 * c0 = 0) :
    (a0 * star a0 + a1 * star a1) * (b0 * c1 - b1 * c0) = 0 := by
  linear_combination (star a0 * b0 + star a1 * b1) * hac
    - (star a0 * c0 + star a1 * c1) * hab

/-- A real with nonpositive square is zero. -/
theorem sq_nonpos {x : Real} (h : x * x ≤ 0) : x = 0 :=
  mul_self_eq_zero.mp (le_antisymm h (mul_self_nonneg x))

/-- A nonnegative real with nonpositive square is zero. -/
theorem sq_le_zero_eq {x : Real} (h1 : 0 ≤ x) (h2 : x * x ≤ 0) : x = 0 := by
  nlinarith

/-! ## The wedge total -/

/-- The complex wedge identity for 4 bottom and 4 top vectors:
the total squared wedge is fixed by the two frame operators alone. -/
theorem totalC4 {a1 a2 a3 a4 b1 b2 b3 b4 s1 s2 s3 s4 t1 t2 t3 t4 : ℂ}
    (fA : a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 = s1 * star s1 + s2 * star s2 + s3 * star s3 + s4 * star s4)
    (fC : b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 = t1 * star t1 + t2 * star t2 + t3 * star t3 + t4 * star t4)
    (fB : a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 = s1 * star t1 + s2 * star t2 + s3 * star t3 + s4 * star t4) :
    (a1 * t1 - b1 * s1) * star (a1 * t1 - b1 * s1) + (a1 * t2 - b1 * s2) * star (a1 * t2 - b1 * s2) + (a1 * t3 - b1 * s3) * star (a1 * t3 - b1 * s3) + (a1 * t4 - b1 * s4) * star (a1 * t4 - b1 * s4) + (a2 * t1 - b2 * s1) * star (a2 * t1 - b2 * s1) + (a2 * t2 - b2 * s2) * star (a2 * t2 - b2 * s2) + (a2 * t3 - b2 * s3) * star (a2 * t3 - b2 * s3) + (a2 * t4 - b2 * s4) * star (a2 * t4 - b2 * s4) + (a3 * t1 - b3 * s1) * star (a3 * t1 - b3 * s1) + (a3 * t2 - b3 * s2) * star (a3 * t2 - b3 * s2) + (a3 * t3 - b3 * s3) * star (a3 * t3 - b3 * s3) + (a3 * t4 - b3 * s4) * star (a3 * t4 - b3 * s4) + (a4 * t1 - b4 * s1) * star (a4 * t1 - b4 * s1) + (a4 * t2 - b4 * s2) * star (a4 * t2 - b4 * s2) + (a4 * t3 - b4 * s3) * star (a4 * t3 - b4 * s3) + (a4 * t4 - b4 * s4) * star (a4 * t4 - b4 * s4)
      = 2 * (a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4) * (b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4)
        - 2 * ((a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4) * (star a1 * b1 + star a2 * b2 + star a3 * b3 + star a4 * b4)) := by
  have hBs : star a1 * b1 + star a2 * b2 + star a3 * b3 + star a4 * b4 = star s1 * t1 + star s2 * t2 + star s3 * t3 + star s4 * t4 := by
    have h := congrArg star fB
    simp only [star_add, star_mul', star_star] at h
    linear_combination h
  simp only [star_sub, star_mul']
  linear_combination (-(a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4)) * fC + (-(b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4)) * fA
    + (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4) * hBs + (star a1 * b1 + star a2 * b2 + star a3 * b3 + star a4 * b4) * fB

/-- The same identity over the reals. -/
theorem total4 {a1 a2 a3 a4 b1 b2 b3 b4 s1 s2 s3 s4 t1 t2 t3 t4 : ℂ}
    (fA : Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3 + Complex.normSq a4
        = Complex.normSq s1 + Complex.normSq s2 + Complex.normSq s3 + Complex.normSq s4)
    (fC : Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 + Complex.normSq b4
        = Complex.normSq t1 + Complex.normSq t2 + Complex.normSq t3 + Complex.normSq t4)
    (fB : a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 = s1 * star t1 + s2 * star t2 + s3 * star t3 + s4 * star t4) :
    Complex.normSq (a1 * t1 - b1 * s1) + Complex.normSq (a1 * t2 - b1 * s2) + Complex.normSq (a1 * t3 - b1 * s3) + Complex.normSq (a1 * t4 - b1 * s4) + Complex.normSq (a2 * t1 - b2 * s1) + Complex.normSq (a2 * t2 - b2 * s2) + Complex.normSq (a2 * t3 - b2 * s3) + Complex.normSq (a2 * t4 - b2 * s4) + Complex.normSq (a3 * t1 - b3 * s1) + Complex.normSq (a3 * t2 - b3 * s2) + Complex.normSq (a3 * t3 - b3 * s3) + Complex.normSq (a3 * t4 - b3 * s4) + Complex.normSq (a4 * t1 - b4 * s1) + Complex.normSq (a4 * t2 - b4 * s2) + Complex.normSq (a4 * t3 - b4 * s3) + Complex.normSq (a4 * t4 - b4 * s4)
      = 2 * (Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3 + Complex.normSq a4) * (Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 + Complex.normSq b4)
        - 2 * Complex.normSq (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4) := by
  have fA' : a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 = s1 * star s1 + s2 * star s2 + s3 * star s3 + s4 * star s4 := by
    rw [SixQubit.Frame.self_mul_star a1, SixQubit.Frame.self_mul_star a2, SixQubit.Frame.self_mul_star a3, SixQubit.Frame.self_mul_star a4, SixQubit.Frame.self_mul_star s1, SixQubit.Frame.self_mul_star s2, SixQubit.Frame.self_mul_star s3, SixQubit.Frame.self_mul_star s4]
    exact_mod_cast fA
  have fC' : b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 = t1 * star t1 + t2 * star t2 + t3 * star t3 + t4 * star t4 := by
    rw [SixQubit.Frame.self_mul_star b1, SixQubit.Frame.self_mul_star b2, SixQubit.Frame.self_mul_star b3, SixQubit.Frame.self_mul_star b4, SixQubit.Frame.self_mul_star t1, SixQubit.Frame.self_mul_star t2, SixQubit.Frame.self_mul_star t3, SixQubit.Frame.self_mul_star t4]
    exact_mod_cast fC
  have key := totalC4 fA' fC' fB
  have hnB : ((Complex.normSq (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4) : Real) : ℂ) = (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4) * (star a1 * b1 + star a2 * b2 + star a3 * b3 + star a4 * b4) := by
    rw [← SixQubit.Frame.self_mul_star]
    simp only [star_add, star_mul', star_star]
    try ring
  rw [SixQubit.Frame.self_mul_star (a1 * t1 - b1 * s1), SixQubit.Frame.self_mul_star (a1 * t2 - b1 * s2), SixQubit.Frame.self_mul_star (a1 * t3 - b1 * s3), SixQubit.Frame.self_mul_star (a1 * t4 - b1 * s4), SixQubit.Frame.self_mul_star (a2 * t1 - b2 * s1), SixQubit.Frame.self_mul_star (a2 * t2 - b2 * s2), SixQubit.Frame.self_mul_star (a2 * t3 - b2 * s3), SixQubit.Frame.self_mul_star (a2 * t4 - b2 * s4), SixQubit.Frame.self_mul_star (a3 * t1 - b3 * s1), SixQubit.Frame.self_mul_star (a3 * t2 - b3 * s2), SixQubit.Frame.self_mul_star (a3 * t3 - b3 * s3), SixQubit.Frame.self_mul_star (a3 * t4 - b3 * s4), SixQubit.Frame.self_mul_star (a4 * t1 - b4 * s1), SixQubit.Frame.self_mul_star (a4 * t2 - b4 * s2), SixQubit.Frame.self_mul_star (a4 * t3 - b4 * s3), SixQubit.Frame.self_mul_star (a4 * t4 - b4 * s4)] at key
  rw [SixQubit.Frame.self_mul_star a1, SixQubit.Frame.self_mul_star a2, SixQubit.Frame.self_mul_star a3, SixQubit.Frame.self_mul_star a4, SixQubit.Frame.self_mul_star b1, SixQubit.Frame.self_mul_star b2, SixQubit.Frame.self_mul_star b3, SixQubit.Frame.self_mul_star b4] at key
  rw [← hnB] at key
  exact_mod_cast key

/-- The complex wedge identity for 8 bottom and 8 top vectors:
the total squared wedge is fixed by the two frame operators alone. -/
theorem totalC8 {a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 s1 s2 s3 s4 s5 s6 s7 s8 t1 t2 t3 t4 t5 t6 t7 t8 : ℂ}
    (fA : a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7 + a8 * star a8 = s1 * star s1 + s2 * star s2 + s3 * star s3 + s4 * star s4 + s5 * star s5 + s6 * star s6 + s7 * star s7 + s8 * star s8)
    (fC : b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7 + b8 * star b8 = t1 * star t1 + t2 * star t2 + t3 * star t3 + t4 * star t4 + t5 * star t5 + t6 * star t6 + t7 * star t7 + t8 * star t8)
    (fB : a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7 + a8 * star b8 = s1 * star t1 + s2 * star t2 + s3 * star t3 + s4 * star t4 + s5 * star t5 + s6 * star t6 + s7 * star t7 + s8 * star t8) :
    (a1 * t1 - b1 * s1) * star (a1 * t1 - b1 * s1) + (a1 * t2 - b1 * s2) * star (a1 * t2 - b1 * s2) + (a1 * t3 - b1 * s3) * star (a1 * t3 - b1 * s3) + (a1 * t4 - b1 * s4) * star (a1 * t4 - b1 * s4) + (a1 * t5 - b1 * s5) * star (a1 * t5 - b1 * s5) + (a1 * t6 - b1 * s6) * star (a1 * t6 - b1 * s6) + (a1 * t7 - b1 * s7) * star (a1 * t7 - b1 * s7) + (a1 * t8 - b1 * s8) * star (a1 * t8 - b1 * s8) + (a2 * t1 - b2 * s1) * star (a2 * t1 - b2 * s1) + (a2 * t2 - b2 * s2) * star (a2 * t2 - b2 * s2) + (a2 * t3 - b2 * s3) * star (a2 * t3 - b2 * s3) + (a2 * t4 - b2 * s4) * star (a2 * t4 - b2 * s4) + (a2 * t5 - b2 * s5) * star (a2 * t5 - b2 * s5) + (a2 * t6 - b2 * s6) * star (a2 * t6 - b2 * s6) + (a2 * t7 - b2 * s7) * star (a2 * t7 - b2 * s7) + (a2 * t8 - b2 * s8) * star (a2 * t8 - b2 * s8) + (a3 * t1 - b3 * s1) * star (a3 * t1 - b3 * s1) + (a3 * t2 - b3 * s2) * star (a3 * t2 - b3 * s2) + (a3 * t3 - b3 * s3) * star (a3 * t3 - b3 * s3) + (a3 * t4 - b3 * s4) * star (a3 * t4 - b3 * s4) + (a3 * t5 - b3 * s5) * star (a3 * t5 - b3 * s5) + (a3 * t6 - b3 * s6) * star (a3 * t6 - b3 * s6) + (a3 * t7 - b3 * s7) * star (a3 * t7 - b3 * s7) + (a3 * t8 - b3 * s8) * star (a3 * t8 - b3 * s8) + (a4 * t1 - b4 * s1) * star (a4 * t1 - b4 * s1) + (a4 * t2 - b4 * s2) * star (a4 * t2 - b4 * s2) + (a4 * t3 - b4 * s3) * star (a4 * t3 - b4 * s3) + (a4 * t4 - b4 * s4) * star (a4 * t4 - b4 * s4) + (a4 * t5 - b4 * s5) * star (a4 * t5 - b4 * s5) + (a4 * t6 - b4 * s6) * star (a4 * t6 - b4 * s6) + (a4 * t7 - b4 * s7) * star (a4 * t7 - b4 * s7) + (a4 * t8 - b4 * s8) * star (a4 * t8 - b4 * s8) + (a5 * t1 - b5 * s1) * star (a5 * t1 - b5 * s1) + (a5 * t2 - b5 * s2) * star (a5 * t2 - b5 * s2) + (a5 * t3 - b5 * s3) * star (a5 * t3 - b5 * s3) + (a5 * t4 - b5 * s4) * star (a5 * t4 - b5 * s4) + (a5 * t5 - b5 * s5) * star (a5 * t5 - b5 * s5) + (a5 * t6 - b5 * s6) * star (a5 * t6 - b5 * s6) + (a5 * t7 - b5 * s7) * star (a5 * t7 - b5 * s7) + (a5 * t8 - b5 * s8) * star (a5 * t8 - b5 * s8) + (a6 * t1 - b6 * s1) * star (a6 * t1 - b6 * s1) + (a6 * t2 - b6 * s2) * star (a6 * t2 - b6 * s2) + (a6 * t3 - b6 * s3) * star (a6 * t3 - b6 * s3) + (a6 * t4 - b6 * s4) * star (a6 * t4 - b6 * s4) + (a6 * t5 - b6 * s5) * star (a6 * t5 - b6 * s5) + (a6 * t6 - b6 * s6) * star (a6 * t6 - b6 * s6) + (a6 * t7 - b6 * s7) * star (a6 * t7 - b6 * s7) + (a6 * t8 - b6 * s8) * star (a6 * t8 - b6 * s8) + (a7 * t1 - b7 * s1) * star (a7 * t1 - b7 * s1) + (a7 * t2 - b7 * s2) * star (a7 * t2 - b7 * s2) + (a7 * t3 - b7 * s3) * star (a7 * t3 - b7 * s3) + (a7 * t4 - b7 * s4) * star (a7 * t4 - b7 * s4) + (a7 * t5 - b7 * s5) * star (a7 * t5 - b7 * s5) + (a7 * t6 - b7 * s6) * star (a7 * t6 - b7 * s6) + (a7 * t7 - b7 * s7) * star (a7 * t7 - b7 * s7) + (a7 * t8 - b7 * s8) * star (a7 * t8 - b7 * s8) + (a8 * t1 - b8 * s1) * star (a8 * t1 - b8 * s1) + (a8 * t2 - b8 * s2) * star (a8 * t2 - b8 * s2) + (a8 * t3 - b8 * s3) * star (a8 * t3 - b8 * s3) + (a8 * t4 - b8 * s4) * star (a8 * t4 - b8 * s4) + (a8 * t5 - b8 * s5) * star (a8 * t5 - b8 * s5) + (a8 * t6 - b8 * s6) * star (a8 * t6 - b8 * s6) + (a8 * t7 - b8 * s7) * star (a8 * t7 - b8 * s7) + (a8 * t8 - b8 * s8) * star (a8 * t8 - b8 * s8)
      = 2 * (a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7 + a8 * star a8) * (b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7 + b8 * star b8)
        - 2 * ((a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7 + a8 * star b8) * (star a1 * b1 + star a2 * b2 + star a3 * b3 + star a4 * b4 + star a5 * b5 + star a6 * b6 + star a7 * b7 + star a8 * b8)) := by
  have hBs : star a1 * b1 + star a2 * b2 + star a3 * b3 + star a4 * b4 + star a5 * b5 + star a6 * b6 + star a7 * b7 + star a8 * b8 = star s1 * t1 + star s2 * t2 + star s3 * t3 + star s4 * t4 + star s5 * t5 + star s6 * t6 + star s7 * t7 + star s8 * t8 := by
    have h := congrArg star fB
    simp only [star_add, star_mul', star_star] at h
    linear_combination h
  simp only [star_sub, star_mul']
  linear_combination (-(a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7 + a8 * star a8)) * fC + (-(b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7 + b8 * star b8)) * fA
    + (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7 + a8 * star b8) * hBs + (star a1 * b1 + star a2 * b2 + star a3 * b3 + star a4 * b4 + star a5 * b5 + star a6 * b6 + star a7 * b7 + star a8 * b8) * fB

/-- The same identity over the reals. -/
theorem total8 {a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 s1 s2 s3 s4 s5 s6 s7 s8 t1 t2 t3 t4 t5 t6 t7 t8 : ℂ}
    (fA : Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3 + Complex.normSq a4 + Complex.normSq a5 + Complex.normSq a6 + Complex.normSq a7 + Complex.normSq a8
        = Complex.normSq s1 + Complex.normSq s2 + Complex.normSq s3 + Complex.normSq s4 + Complex.normSq s5 + Complex.normSq s6 + Complex.normSq s7 + Complex.normSq s8)
    (fC : Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 + Complex.normSq b4 + Complex.normSq b5 + Complex.normSq b6 + Complex.normSq b7 + Complex.normSq b8
        = Complex.normSq t1 + Complex.normSq t2 + Complex.normSq t3 + Complex.normSq t4 + Complex.normSq t5 + Complex.normSq t6 + Complex.normSq t7 + Complex.normSq t8)
    (fB : a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7 + a8 * star b8 = s1 * star t1 + s2 * star t2 + s3 * star t3 + s4 * star t4 + s5 * star t5 + s6 * star t6 + s7 * star t7 + s8 * star t8) :
    Complex.normSq (a1 * t1 - b1 * s1) + Complex.normSq (a1 * t2 - b1 * s2) + Complex.normSq (a1 * t3 - b1 * s3) + Complex.normSq (a1 * t4 - b1 * s4) + Complex.normSq (a1 * t5 - b1 * s5) + Complex.normSq (a1 * t6 - b1 * s6) + Complex.normSq (a1 * t7 - b1 * s7) + Complex.normSq (a1 * t8 - b1 * s8) + Complex.normSq (a2 * t1 - b2 * s1) + Complex.normSq (a2 * t2 - b2 * s2) + Complex.normSq (a2 * t3 - b2 * s3) + Complex.normSq (a2 * t4 - b2 * s4) + Complex.normSq (a2 * t5 - b2 * s5) + Complex.normSq (a2 * t6 - b2 * s6) + Complex.normSq (a2 * t7 - b2 * s7) + Complex.normSq (a2 * t8 - b2 * s8) + Complex.normSq (a3 * t1 - b3 * s1) + Complex.normSq (a3 * t2 - b3 * s2) + Complex.normSq (a3 * t3 - b3 * s3) + Complex.normSq (a3 * t4 - b3 * s4) + Complex.normSq (a3 * t5 - b3 * s5) + Complex.normSq (a3 * t6 - b3 * s6) + Complex.normSq (a3 * t7 - b3 * s7) + Complex.normSq (a3 * t8 - b3 * s8) + Complex.normSq (a4 * t1 - b4 * s1) + Complex.normSq (a4 * t2 - b4 * s2) + Complex.normSq (a4 * t3 - b4 * s3) + Complex.normSq (a4 * t4 - b4 * s4) + Complex.normSq (a4 * t5 - b4 * s5) + Complex.normSq (a4 * t6 - b4 * s6) + Complex.normSq (a4 * t7 - b4 * s7) + Complex.normSq (a4 * t8 - b4 * s8) + Complex.normSq (a5 * t1 - b5 * s1) + Complex.normSq (a5 * t2 - b5 * s2) + Complex.normSq (a5 * t3 - b5 * s3) + Complex.normSq (a5 * t4 - b5 * s4) + Complex.normSq (a5 * t5 - b5 * s5) + Complex.normSq (a5 * t6 - b5 * s6) + Complex.normSq (a5 * t7 - b5 * s7) + Complex.normSq (a5 * t8 - b5 * s8) + Complex.normSq (a6 * t1 - b6 * s1) + Complex.normSq (a6 * t2 - b6 * s2) + Complex.normSq (a6 * t3 - b6 * s3) + Complex.normSq (a6 * t4 - b6 * s4) + Complex.normSq (a6 * t5 - b6 * s5) + Complex.normSq (a6 * t6 - b6 * s6) + Complex.normSq (a6 * t7 - b6 * s7) + Complex.normSq (a6 * t8 - b6 * s8) + Complex.normSq (a7 * t1 - b7 * s1) + Complex.normSq (a7 * t2 - b7 * s2) + Complex.normSq (a7 * t3 - b7 * s3) + Complex.normSq (a7 * t4 - b7 * s4) + Complex.normSq (a7 * t5 - b7 * s5) + Complex.normSq (a7 * t6 - b7 * s6) + Complex.normSq (a7 * t7 - b7 * s7) + Complex.normSq (a7 * t8 - b7 * s8) + Complex.normSq (a8 * t1 - b8 * s1) + Complex.normSq (a8 * t2 - b8 * s2) + Complex.normSq (a8 * t3 - b8 * s3) + Complex.normSq (a8 * t4 - b8 * s4) + Complex.normSq (a8 * t5 - b8 * s5) + Complex.normSq (a8 * t6 - b8 * s6) + Complex.normSq (a8 * t7 - b8 * s7) + Complex.normSq (a8 * t8 - b8 * s8)
      = 2 * (Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3 + Complex.normSq a4 + Complex.normSq a5 + Complex.normSq a6 + Complex.normSq a7 + Complex.normSq a8) * (Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 + Complex.normSq b4 + Complex.normSq b5 + Complex.normSq b6 + Complex.normSq b7 + Complex.normSq b8)
        - 2 * Complex.normSq (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7 + a8 * star b8) := by
  have fA' : a1 * star a1 + a2 * star a2 + a3 * star a3 + a4 * star a4 + a5 * star a5 + a6 * star a6 + a7 * star a7 + a8 * star a8 = s1 * star s1 + s2 * star s2 + s3 * star s3 + s4 * star s4 + s5 * star s5 + s6 * star s6 + s7 * star s7 + s8 * star s8 := by
    rw [SixQubit.Frame.self_mul_star a1, SixQubit.Frame.self_mul_star a2, SixQubit.Frame.self_mul_star a3, SixQubit.Frame.self_mul_star a4, SixQubit.Frame.self_mul_star a5, SixQubit.Frame.self_mul_star a6, SixQubit.Frame.self_mul_star a7, SixQubit.Frame.self_mul_star a8, SixQubit.Frame.self_mul_star s1, SixQubit.Frame.self_mul_star s2, SixQubit.Frame.self_mul_star s3, SixQubit.Frame.self_mul_star s4, SixQubit.Frame.self_mul_star s5, SixQubit.Frame.self_mul_star s6, SixQubit.Frame.self_mul_star s7, SixQubit.Frame.self_mul_star s8]
    exact_mod_cast fA
  have fC' : b1 * star b1 + b2 * star b2 + b3 * star b3 + b4 * star b4 + b5 * star b5 + b6 * star b6 + b7 * star b7 + b8 * star b8 = t1 * star t1 + t2 * star t2 + t3 * star t3 + t4 * star t4 + t5 * star t5 + t6 * star t6 + t7 * star t7 + t8 * star t8 := by
    rw [SixQubit.Frame.self_mul_star b1, SixQubit.Frame.self_mul_star b2, SixQubit.Frame.self_mul_star b3, SixQubit.Frame.self_mul_star b4, SixQubit.Frame.self_mul_star b5, SixQubit.Frame.self_mul_star b6, SixQubit.Frame.self_mul_star b7, SixQubit.Frame.self_mul_star b8, SixQubit.Frame.self_mul_star t1, SixQubit.Frame.self_mul_star t2, SixQubit.Frame.self_mul_star t3, SixQubit.Frame.self_mul_star t4, SixQubit.Frame.self_mul_star t5, SixQubit.Frame.self_mul_star t6, SixQubit.Frame.self_mul_star t7, SixQubit.Frame.self_mul_star t8]
    exact_mod_cast fC
  have key := totalC8 fA' fC' fB
  have hnB : ((Complex.normSq (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7 + a8 * star b8) : Real) : ℂ) = (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 + a5 * star b5 + a6 * star b6 + a7 * star b7 + a8 * star b8) * (star a1 * b1 + star a2 * b2 + star a3 * b3 + star a4 * b4 + star a5 * b5 + star a6 * b6 + star a7 * b7 + star a8 * b8) := by
    rw [← SixQubit.Frame.self_mul_star]
    simp only [star_add, star_mul', star_star]
    try ring
  rw [SixQubit.Frame.self_mul_star (a1 * t1 - b1 * s1), SixQubit.Frame.self_mul_star (a1 * t2 - b1 * s2), SixQubit.Frame.self_mul_star (a1 * t3 - b1 * s3), SixQubit.Frame.self_mul_star (a1 * t4 - b1 * s4), SixQubit.Frame.self_mul_star (a1 * t5 - b1 * s5), SixQubit.Frame.self_mul_star (a1 * t6 - b1 * s6), SixQubit.Frame.self_mul_star (a1 * t7 - b1 * s7), SixQubit.Frame.self_mul_star (a1 * t8 - b1 * s8), SixQubit.Frame.self_mul_star (a2 * t1 - b2 * s1), SixQubit.Frame.self_mul_star (a2 * t2 - b2 * s2), SixQubit.Frame.self_mul_star (a2 * t3 - b2 * s3), SixQubit.Frame.self_mul_star (a2 * t4 - b2 * s4), SixQubit.Frame.self_mul_star (a2 * t5 - b2 * s5), SixQubit.Frame.self_mul_star (a2 * t6 - b2 * s6), SixQubit.Frame.self_mul_star (a2 * t7 - b2 * s7), SixQubit.Frame.self_mul_star (a2 * t8 - b2 * s8), SixQubit.Frame.self_mul_star (a3 * t1 - b3 * s1), SixQubit.Frame.self_mul_star (a3 * t2 - b3 * s2), SixQubit.Frame.self_mul_star (a3 * t3 - b3 * s3), SixQubit.Frame.self_mul_star (a3 * t4 - b3 * s4), SixQubit.Frame.self_mul_star (a3 * t5 - b3 * s5), SixQubit.Frame.self_mul_star (a3 * t6 - b3 * s6), SixQubit.Frame.self_mul_star (a3 * t7 - b3 * s7), SixQubit.Frame.self_mul_star (a3 * t8 - b3 * s8), SixQubit.Frame.self_mul_star (a4 * t1 - b4 * s1), SixQubit.Frame.self_mul_star (a4 * t2 - b4 * s2), SixQubit.Frame.self_mul_star (a4 * t3 - b4 * s3), SixQubit.Frame.self_mul_star (a4 * t4 - b4 * s4), SixQubit.Frame.self_mul_star (a4 * t5 - b4 * s5), SixQubit.Frame.self_mul_star (a4 * t6 - b4 * s6), SixQubit.Frame.self_mul_star (a4 * t7 - b4 * s7), SixQubit.Frame.self_mul_star (a4 * t8 - b4 * s8), SixQubit.Frame.self_mul_star (a5 * t1 - b5 * s1), SixQubit.Frame.self_mul_star (a5 * t2 - b5 * s2), SixQubit.Frame.self_mul_star (a5 * t3 - b5 * s3), SixQubit.Frame.self_mul_star (a5 * t4 - b5 * s4), SixQubit.Frame.self_mul_star (a5 * t5 - b5 * s5), SixQubit.Frame.self_mul_star (a5 * t6 - b5 * s6), SixQubit.Frame.self_mul_star (a5 * t7 - b5 * s7), SixQubit.Frame.self_mul_star (a5 * t8 - b5 * s8), SixQubit.Frame.self_mul_star (a6 * t1 - b6 * s1), SixQubit.Frame.self_mul_star (a6 * t2 - b6 * s2), SixQubit.Frame.self_mul_star (a6 * t3 - b6 * s3), SixQubit.Frame.self_mul_star (a6 * t4 - b6 * s4), SixQubit.Frame.self_mul_star (a6 * t5 - b6 * s5), SixQubit.Frame.self_mul_star (a6 * t6 - b6 * s6), SixQubit.Frame.self_mul_star (a6 * t7 - b6 * s7), SixQubit.Frame.self_mul_star (a6 * t8 - b6 * s8), SixQubit.Frame.self_mul_star (a7 * t1 - b7 * s1), SixQubit.Frame.self_mul_star (a7 * t2 - b7 * s2), SixQubit.Frame.self_mul_star (a7 * t3 - b7 * s3), SixQubit.Frame.self_mul_star (a7 * t4 - b7 * s4), SixQubit.Frame.self_mul_star (a7 * t5 - b7 * s5), SixQubit.Frame.self_mul_star (a7 * t6 - b7 * s6), SixQubit.Frame.self_mul_star (a7 * t7 - b7 * s7), SixQubit.Frame.self_mul_star (a7 * t8 - b7 * s8), SixQubit.Frame.self_mul_star (a8 * t1 - b8 * s1), SixQubit.Frame.self_mul_star (a8 * t2 - b8 * s2), SixQubit.Frame.self_mul_star (a8 * t3 - b8 * s3), SixQubit.Frame.self_mul_star (a8 * t4 - b8 * s4), SixQubit.Frame.self_mul_star (a8 * t5 - b8 * s5), SixQubit.Frame.self_mul_star (a8 * t6 - b8 * s6), SixQubit.Frame.self_mul_star (a8 * t7 - b8 * s7), SixQubit.Frame.self_mul_star (a8 * t8 - b8 * s8)] at key
  rw [SixQubit.Frame.self_mul_star a1, SixQubit.Frame.self_mul_star a2, SixQubit.Frame.self_mul_star a3, SixQubit.Frame.self_mul_star a4, SixQubit.Frame.self_mul_star a5, SixQubit.Frame.self_mul_star a6, SixQubit.Frame.self_mul_star a7, SixQubit.Frame.self_mul_star a8, SixQubit.Frame.self_mul_star b1, SixQubit.Frame.self_mul_star b2, SixQubit.Frame.self_mul_star b3, SixQubit.Frame.self_mul_star b4, SixQubit.Frame.self_mul_star b5, SixQubit.Frame.self_mul_star b6, SixQubit.Frame.self_mul_star b7, SixQubit.Frame.self_mul_star b8] at key
  rw [← hnB] at key
  exact_mod_cast key

/-! ## The slice obstruction -/

/-- **A three-cube slice carries no mass.**  Four bottom and four top
vectors in `ℂ²`, indexed so that bottom `i` is the unique NON-neighbour of
top `i`; the twelve neighbour inner products vanish, the three slice frame
entries agree, and each bottom mass obeys the neighbour-sum identity.
Then the whole slice has zero mass. -/
theorem slice_zero {a1 a2 a3 a4 b1 b2 b3 b4 s1 s2 s3 s4 t1 t2 t3 t4 : ℂ}
    (o12 : star a1 * s2 + star b1 * t2 = 0)
    (o13 : star a1 * s3 + star b1 * t3 = 0)
    (o14 : star a1 * s4 + star b1 * t4 = 0)
    (o21 : star a2 * s1 + star b2 * t1 = 0)
    (o23 : star a2 * s3 + star b2 * t3 = 0)
    (o24 : star a2 * s4 + star b2 * t4 = 0)
    (o31 : star a3 * s1 + star b3 * t1 = 0)
    (o32 : star a3 * s2 + star b3 * t2 = 0)
    (o34 : star a3 * s4 + star b3 * t4 = 0)
    (o41 : star a4 * s1 + star b4 * t1 = 0)
    (o42 : star a4 * s2 + star b4 * t2 = 0)
    (o43 : star a4 * s3 + star b4 * t3 = 0)
    (fA : Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3 + Complex.normSq a4
        = Complex.normSq s1 + Complex.normSq s2 + Complex.normSq s3 + Complex.normSq s4)
    (fC : Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 + Complex.normSq b4
        = Complex.normSq t1 + Complex.normSq t2 + Complex.normSq t3 + Complex.normSq t4)
    (fB : a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4 = s1 * star t1 + s2 * star t2 + s3 * star t3 + s4 * star t4)
    (m1 : Complex.normSq s2 + Complex.normSq t2 + Complex.normSq s3 + Complex.normSq t3 + Complex.normSq s4 + Complex.normSq t4
        = (Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) / 2 + (Complex.normSq a1 + Complex.normSq b1))
    (m2 : Complex.normSq s1 + Complex.normSq t1 + Complex.normSq s3 + Complex.normSq t3 + Complex.normSq s4 + Complex.normSq t4
        = (Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) / 2 + (Complex.normSq a2 + Complex.normSq b2))
    (m3 : Complex.normSq s1 + Complex.normSq t1 + Complex.normSq s2 + Complex.normSq t2 + Complex.normSq s4 + Complex.normSq t4
        = (Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) / 2 + (Complex.normSq a3 + Complex.normSq b3))
    (m4 : Complex.normSq s1 + Complex.normSq t1 + Complex.normSq s2 + Complex.normSq t2 + Complex.normSq s3 + Complex.normSq t3
        = (Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) / 2 + (Complex.normSq a4 + Complex.normSq b4))
    : Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4 = 0 := by
  have w12 := wedge_of_orth o12
  have w13 := wedge_of_orth o13
  have w14 := wedge_of_orth o14
  have w21 := wedge_of_orth o21
  have w23 := wedge_of_orth o23
  have w24 := wedge_of_orth o24
  have w31 := wedge_of_orth o31
  have w32 := wedge_of_orth o32
  have w34 := wedge_of_orth o34
  have w41 := wedge_of_orth o41
  have w42 := wedge_of_orth o42
  have w43 := wedge_of_orth o43
  have tot := total4 fA fC fB
  have r1 : Complex.normSq (a1 * t2 - b1 * s2) + Complex.normSq (a1 * t3 - b1 * s3) + Complex.normSq (a1 * t4 - b1 * s4)
      = (Complex.normSq a1 + Complex.normSq b1) * ((Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) / 2 + (Complex.normSq a1 + Complex.normSq b1)) := by
    rw [w12, w13, w14, ← m1]
    ring
  have r2 : Complex.normSq (a2 * t1 - b2 * s1) + Complex.normSq (a2 * t3 - b2 * s3) + Complex.normSq (a2 * t4 - b2 * s4)
      = (Complex.normSq a2 + Complex.normSq b2) * ((Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) / 2 + (Complex.normSq a2 + Complex.normSq b2)) := by
    rw [w21, w23, w24, ← m2]
    ring
  have r3 : Complex.normSq (a3 * t1 - b3 * s1) + Complex.normSq (a3 * t2 - b3 * s2) + Complex.normSq (a3 * t4 - b3 * s4)
      = (Complex.normSq a3 + Complex.normSq b3) * ((Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) / 2 + (Complex.normSq a3 + Complex.normSq b3)) := by
    rw [w31, w32, w34, ← m3]
    ring
  have r4 : Complex.normSq (a4 * t1 - b4 * s1) + Complex.normSq (a4 * t2 - b4 * s2) + Complex.normSq (a4 * t3 - b4 * s3)
      = (Complex.normSq a4 + Complex.normSq b4) * ((Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) / 2 + (Complex.normSq a4 + Complex.normSq b4)) := by
    rw [w41, w42, w43, ← m4]
    ring
  have hb : (0:Real) ≤ Complex.normSq (a1 * star b1 + a2 * star b2 + a3 * star b3 + a4 * star b4) := Complex.normSq_nonneg _
  have d1 : (0:Real) ≤ Complex.normSq (a1 * t1 - b1 * s1) := Complex.normSq_nonneg _
  have d2 : (0:Real) ≤ Complex.normSq (a2 * t2 - b2 * s2) := Complex.normSq_nonneg _
  have d3 : (0:Real) ≤ Complex.normSq (a3 * t3 - b3 * s3) := Complex.normSq_nonneg _
  have d4 : (0:Real) ≤ Complex.normSq (a4 * t4 - b4 * s4) := Complex.normSq_nonneg _
  have pa1 : (0:Real) ≤ Complex.normSq a1 := Complex.normSq_nonneg _
  have pb1 : (0:Real) ≤ Complex.normSq b1 := Complex.normSq_nonneg _
  have pa2 : (0:Real) ≤ Complex.normSq a2 := Complex.normSq_nonneg _
  have pb2 : (0:Real) ≤ Complex.normSq b2 := Complex.normSq_nonneg _
  have pa3 : (0:Real) ≤ Complex.normSq a3 := Complex.normSq_nonneg _
  have pb3 : (0:Real) ≤ Complex.normSq b3 := Complex.normSq_nonneg _
  have pa4 : (0:Real) ≤ Complex.normSq a4 := Complex.normSq_nonneg _
  have pb4 : (0:Real) ≤ Complex.normSq b4 := Complex.normSq_nonneg _
  have collapse : (Complex.normSq a1 + Complex.normSq b1) * (Complex.normSq a1 + Complex.normSq b1) + (Complex.normSq a2 + Complex.normSq b2) * (Complex.normSq a2 + Complex.normSq b2) + (Complex.normSq a3 + Complex.normSq b3) * (Complex.normSq a3 + Complex.normSq b3) + (Complex.normSq a4 + Complex.normSq b4) * (Complex.normSq a4 + Complex.normSq b4) ≤ 0 := by
    linarith [tot, r1, r2, r3, r4, d1, d2, d3, d4, hb,
      sq_nonneg ((Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3 + Complex.normSq a4) - (Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 + Complex.normSq b4))]
  have hPz : (Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) * (Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4) ≤ 0 := by
    linarith [collapse, sq_nonneg ((Complex.normSq a1 + Complex.normSq b1) - (Complex.normSq a2 + Complex.normSq b2)), sq_nonneg ((Complex.normSq a1 + Complex.normSq b1) - (Complex.normSq a3 + Complex.normSq b3)), sq_nonneg ((Complex.normSq a1 + Complex.normSq b1) - (Complex.normSq a4 + Complex.normSq b4)), sq_nonneg ((Complex.normSq a2 + Complex.normSq b2) - (Complex.normSq a3 + Complex.normSq b3)), sq_nonneg ((Complex.normSq a2 + Complex.normSq b2) - (Complex.normSq a4 + Complex.normSq b4)), sq_nonneg ((Complex.normSq a3 + Complex.normSq b3) - (Complex.normSq a4 + Complex.normSq b4))]
  have hPnn : (0:Real) ≤ Complex.normSq a1 + Complex.normSq b1 + Complex.normSq a2 + Complex.normSq b2 + Complex.normSq a3 + Complex.normSq b3 + Complex.normSq a4 + Complex.normSq b4 := by
    linarith [pa1, pb1, pa2, pb2, pa3, pb3, pa4, pb4]
  exact sq_le_zero_eq hPnn hPz

end

end SixQubit.ParityFour
