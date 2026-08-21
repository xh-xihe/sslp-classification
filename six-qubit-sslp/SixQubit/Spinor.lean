import Mathlib

import SS.FullKL
import SixQubit.Common

/-!
# Lines in `ℂ²`: the two spinor mechanisms

Two of the six-qubit no-go orbits carry a zero-angle qubit, so their amplitudes
group into spinors in `ℂ²`, and both arguments turn on the geometry of *lines*
in that plane.  This module isolates the three purely algebraic steps, so that
the orbit modules stay thin.

## `cancel_perp` — cancelling rank-one matrices

Orbit 12 meets the cross Knill--Laflamme block

```
ũ u† + ṽ v† = 0
```

on the two-qubit subsystem carrying the zero-angle qubit and the half-angle
qubit.  The textbook reading is that two nonzero rank-one matrices can cancel
only when both their column spaces and their row spaces coincide, after which
one reduces to scalars on a pair of lines and eliminates.  That route needs
spans, unit vectors and division.

The formalization avoids all of it.  Write

```
s = a† ũ ,   t = a† ṽ ,   Bu = u† w ,   Bv = v† w
```

for the two edge monomials appearing in the two complementary physical-pair
rows `s + Bv = 0` and `Bu + t = 0`.  Contracting the four scalar equations of
the cross block with `a` gives `u_q* s + v_q* t = 0` for each coordinate `q`;
contracting *those* with `w` gives `Bu s + Bv t = 0`, and substituting the two
pair rows turns it into `2 s t = 0`.  A nonzero `u` and a nonzero `v` then
force `s = t = 0` separately, hence `Bu = Bv = 0`: the top edge vector `w` is
orthogonal to both anchors.  No division, no spans, no unit vectors.

## `edge_zero` — positivity of the diagonal block

The equality of the two reduced states on the same two-qubit subsystem has a
diagonal block `u u† + v v† = Σ b_e b_e†`.  Contracting it on both sides with
one of the `b_e` and using `u† w = v† w = 0` leaves a sum of squared moduli
equal to zero whose distinguished term is `‖w‖⁴`.  Hence `w = 0`.

The proof again never builds a matrix: it is a single `linear_combination`
over the four entries of the block, followed by a cast to `ℝ`.

## `lagrange` — Lagrange's identity

Used by orbit 6 to run Cauchy--Schwarz *with its defect term*, so that the
contraction of the reduced state on the zero-angle qubit with the anchor `u`
becomes an exact equation between nonnegative reals rather than an inequality.

`native_decide` is not used, and nothing here mentions bit strings.
-/

namespace SixQubit.Spinor

open scoped ComplexConjugate

noncomputable section

/-! ## Lagrange's identity in `ℂ²` -/

/-- **Lagrange's identity.**  The Cauchy--Schwarz defect for two vectors of
`ℂ²` is the squared modulus of their determinant. -/
theorem lagrange (c0 c1 u0 u1 : ℂ) :
    Complex.normSq (star c0 * u0 + star c1 * u1) + Complex.normSq (c0 * u1 - c1 * u0)
      = (Complex.normSq c0 + Complex.normSq c1) * (Complex.normSq u0 + Complex.normSq u1) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-! ## Cancelling rank-one matrices -/

/-- **The two complementary pair rows collapse.**  Given the four scalar
entries of the cross block `ũ u† + ṽ v† = 0`, the two physical-pair rows

```
a† ũ + v† w = 0 ,      u† w + a† ṽ = 0 ,
```

and nonzero anchors `u` and `v`, the top edge vector `w` is orthogonal to both
anchors. -/
theorem cancel_perp {u0 u1 v0 v1 ut0 ut1 vt0 vt1 a0 a1 w0 w1 : ℂ}
    (K00 : star u0 * ut0 + star v0 * vt0 = 0)
    (K01 : star u0 * ut1 + star v0 * vt1 = 0)
    (K10 : star u1 * ut0 + star v1 * vt0 = 0)
    (K11 : star u1 * ut1 + star v1 * vt1 = 0)
    (P1 : star a0 * ut0 + star a1 * ut1 + (star v0 * w0 + star v1 * w1) = 0)
    (P2 : star u0 * w0 + star u1 * w1 + (star a0 * vt0 + star a1 * vt1) = 0)
    (hu : 0 < Complex.normSq u0 + Complex.normSq u1)
    (hv : 0 < Complex.normSq v0 + Complex.normSq v1) :
    star u0 * w0 + star u1 * w1 = 0 ∧ star v0 * w0 + star v1 * w1 = 0 := by
  -- contract the cross block with `a`
  have Sq0 : star u0 * (star a0 * ut0 + star a1 * ut1)
      + star v0 * (star a0 * vt0 + star a1 * vt1) = 0 := by
    linear_combination star a0 * K00 + star a1 * K01
  have Sq1 : star u1 * (star a0 * ut0 + star a1 * ut1)
      + star v1 * (star a0 * vt0 + star a1 * vt1) = 0 := by
    linear_combination star a0 * K10 + star a1 * K11
  -- contract those with `w` and substitute the two pair rows
  have hst : (star a0 * ut0 + star a1 * ut1) * (star a0 * vt0 + star a1 * vt1) = 0 := by
    linear_combination (-w0 / 2) * Sq0 + (-w1 / 2) * Sq1
      + ((star a0 * ut0 + star a1 * ut1) / 2) * P2
      + ((star a0 * vt0 + star a1 * vt1) / 2) * P1
  have main : (star a0 * ut0 + star a1 * ut1) = 0
      ∧ (star a0 * vt0 + star a1 * vt1) = 0 := by
    rcases mul_eq_zero.mp hst with h | h
    · refine ⟨h, ?_⟩
      by_contra hne
      have e0 : star v0 * (star a0 * vt0 + star a1 * vt1) = 0 := by
        linear_combination Sq0 - star u0 * h
      have e1 : star v1 * (star a0 * vt0 + star a1 * vt1) = 0 := by
        linear_combination Sq1 - star u1 * h
      have hv0 : v0 = 0 := by
        have := (mul_eq_zero.mp e0).resolve_right hne
        simpa using congrArg star this
      have hv1 : v1 = 0 := by
        have := (mul_eq_zero.mp e1).resolve_right hne
        simpa using congrArg star this
      rw [hv0, hv1] at hv; simp at hv
    · refine ⟨?_, h⟩
      by_contra hne
      have e0 : star u0 * (star a0 * ut0 + star a1 * ut1) = 0 := by
        linear_combination Sq0 - star v0 * h
      have e1 : star u1 * (star a0 * ut0 + star a1 * ut1) = 0 := by
        linear_combination Sq1 - star v1 * h
      have hu0 : u0 = 0 := by
        have := (mul_eq_zero.mp e0).resolve_right hne
        simpa using congrArg star this
      have hu1 : u1 = 0 := by
        have := (mul_eq_zero.mp e1).resolve_right hne
        simpa using congrArg star this
      rw [hu0, hu1] at hu; simp at hu
  exact ⟨by linear_combination P2 - main.2, by linear_combination P1 - main.1⟩

/-! ## Positivity of the diagonal block -/

/-- **The distinguished edge vector vanishes.**  The diagonal block
`u u† + v v† = w w† + Σ p_k p_k†` of the reduced-state equality, contracted
with a vector `w` orthogonal to both anchors, forces `w = 0`.

`D0` and `D1` are the two diagonal entries (they come from the moment
polytope, hence are stated over `ℝ`); `Doff` is the off-diagonal entry
(it comes from the two free-qubit diagonal rows, hence is stated over `ℂ`). -/
theorem edge_zero {u0 u1 v0 v1 w0 w1 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5 : ℂ}
    (D0 : Complex.normSq u0 + Complex.normSq v0
        = Complex.normSq w0 + Complex.normSq p1 + Complex.normSq p2
          + Complex.normSq p3 + Complex.normSq p4 + Complex.normSq p5)
    (D1 : Complex.normSq u1 + Complex.normSq v1
        = Complex.normSq w1 + Complex.normSq q1 + Complex.normSq q2
          + Complex.normSq q3 + Complex.normSq q4 + Complex.normSq q5)
    (Doff : star u1 * u0 + star v1 * v0
        = star w1 * w0 + star q1 * p1 + star q2 * p2
          + star q3 * p3 + star q4 * p4 + star q5 * p5)
    (hu : star u0 * w0 + star u1 * w1 = 0)
    (hv : star v0 * w0 + star v1 * w1 = 0) :
    Complex.normSq w0 + Complex.normSq w1 = 0 := by
  -- the conjugate off-diagonal entry
  have Doffs : star u0 * u1 + star v0 * v1
      = star w0 * w1 + star p1 * q1 + star p2 * q2
        + star p3 * q3 + star p4 * q4 + star p5 * q5 := by
    have hc := congrArg star Doff
    simp only [star_add, star_mul', star_star] at hc
    linear_combination hc
  -- the two diagonal entries, over `ℂ`
  have Dc0 : star u0 * u0 + star v0 * v0
      = star w0 * w0 + star p1 * p1 + star p2 * p2
        + star p3 * p3 + star p4 * p4 + star p5 * p5 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) D0
    push_cast at hc
    simp only [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have Dc1 : star u1 * u1 + star v1 * v1
      = star w1 * w1 + star q1 * q1 + star q2 * q2
        + star q3 * q3 + star q4 * q4 + star q5 * q5 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) D1
    push_cast at hc
    simp only [← SixQubit.star_mul_self] at hc
    linear_combination hc
  -- the contracted identity: a sum of squared moduli that must vanish
  have main : (star w0 * w0 + star w1 * w1) * (star w0 * w0 + star w1 * w1)
      + (star p1 * w0 + star q1 * w1) * (p1 * star w0 + q1 * star w1)
      + (star p2 * w0 + star q2 * w1) * (p2 * star w0 + q2 * star w1)
      + (star p3 * w0 + star q3 * w1) * (p3 * star w0 + q3 * star w1)
      + (star p4 * w0 + star q4 * w1) * (p4 * star w0 + q4 * star w1)
      + (star p5 * w0 + star q5 * w1) * (p5 * star w0 + q5 * star w1) = 0 := by
    linear_combination (u0 * star w0 + u1 * star w1) * hu
      + (v0 * star w0 + v1 * star w1) * hv
      - (star w0 * w0) * Dc0 - (star w1 * w1) * Dc1
      - (star w0 * w1) * Doff - (star w1 * w0) * Doffs
  -- read it as an equation between nonnegative reals
  have hreal : (Complex.normSq w0 + Complex.normSq w1) * (Complex.normSq w0 + Complex.normSq w1)
      + Complex.normSq (star p1 * w0 + star q1 * w1)
      + Complex.normSq (star p2 * w0 + star q2 * w1)
      + Complex.normSq (star p3 * w0 + star q3 * w1)
      + Complex.normSq (star p4 * w0 + star q4 * w1)
      + Complex.normSq (star p5 * w0 + star q5 * w1) = 0 := by
    have hc : (((Complex.normSq w0 + Complex.normSq w1)
          * (Complex.normSq w0 + Complex.normSq w1)
        + Complex.normSq (star p1 * w0 + star q1 * w1)
        + Complex.normSq (star p2 * w0 + star q2 * w1)
        + Complex.normSq (star p3 * w0 + star q3 * w1)
        + Complex.normSq (star p4 * w0 + star q4 * w1)
        + Complex.normSq (star p5 * w0 + star q5 * w1) : ℝ) : ℂ) = 0 := by
      push_cast
      simp only [← SixQubit.star_mul_self, star_add, star_mul', star_star]
      linear_combination main
    exact_mod_cast hc
  nlinarith [Complex.normSq_nonneg w0, Complex.normSq_nonneg w1,
    Complex.normSq_nonneg (star p1 * w0 + star q1 * w1),
    Complex.normSq_nonneg (star p2 * w0 + star q2 * w1),
    Complex.normSq_nonneg (star p3 * w0 + star q3 * w1),
    Complex.normSq_nonneg (star p4 * w0 + star q4 * w1),
    Complex.normSq_nonneg (star p5 * w0 + star q5 * w1)]

end

end SixQubit.Spinor
