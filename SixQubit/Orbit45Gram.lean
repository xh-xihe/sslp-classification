import Mathlib

import SixQubit.Frame

/-!
# Orbit 45: division-free Gram algebra

This file contains no bit strings and no finite certificate.  It is the small
complex/real algebraic core used by the full-fibre orbit-45 reduction.

The three moving blocks have masses `g1,g2,g3`.  Their cross-KL products form
a closed triangle of side lengths `g_j / 4`; this is exactly the statement
that every `g_j <= 1/2`.  The two remaining masses are forced equal by a
two-term cross-KL cancellation.  The frame-potential identities at the end
compute the weight-two enumerator without choosing phases or dividing by an
amplitude.
-/

namespace SixQubit.Orbit45Gram

open scoped ComplexConjugate

/-! ## Small cancellation lemmas -/

/-- Equal component norms and one balanced sesquilinear product force the
corresponding two-by-two determinant to vanish.  The proof is division-free;
the zero-amplitude case is handled explicitly. -/
theorem det_zero_of_balanced (a b A B : ℂ)
    (hab : Complex.normSq a = Complex.normSq b)
    (hp : star a * A = star b * B) :
    a * B - b * A = 0 := by
  by_cases ha : a = 0
  · have hna : Complex.normSq a = 0 := by rw [ha, Complex.normSq_zero]
    have hnb : Complex.normSq b = 0 := by linarith
    have hb : b = 0 := Complex.normSq_eq_zero.mp hnb
    simp [ha, hb]
  · have hsa : star a ≠ 0 := by simpa using ha
    have hn : star a * a = b * star b := by
      rw [Complex.star_def, mul_comm b (conj b),
        ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast hab
    have key : star a * (a * B - b * A) = 0 := by
      linear_combination -b * hp + B * hn
    exact (mul_eq_zero.mp key).resolve_left hsa

/-- Two cancelling complex products whose squared moduli are the squares of
nonnegative masses have equal masses. -/
theorem masses_eq_of_opposite (p q : ℂ) (g h : ℝ)
    (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hp : Complex.normSq p = (g / 4) ^ 2)
    (hq : Complex.normSq q = (h / 4) ^ 2)
    (hop : p + q = 0) : g = h := by
  have hpq : p = -q := by linear_combination hop
  have hsq : (g / 4) ^ 2 = (h / 4) ^ 2 := by
    rw [← hp, ← hq, hpq, Complex.normSq_neg]
  nlinarith

/-! ## The closed triangle -/

private lemma norm_eq_quarter (z : ℂ) (g : ℝ) (hg : 0 ≤ g)
    (hz : Complex.normSq z = (g / 4) ^ 2) : ‖z‖ = g / 4 := by
  have hn : 0 ≤ ‖z‖ := norm_nonneg z
  have hq : 0 ≤ g / 4 := by positivity
  have hs : ‖z‖ ^ 2 = (g / 4) ^ 2 := by rw [Complex.sq_norm, hz]
  nlinarith

/-- Side one of a closed complex triangle is no longer than the other two. -/
theorem side_le_other_two (p1 p2 p3 : ℂ) (g1 g2 g3 : ℝ)
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hg3 : 0 ≤ g3)
    (hp1 : Complex.normSq p1 = (g1 / 4) ^ 2)
    (hp2 : Complex.normSq p2 = (g2 / 4) ^ 2)
    (hp3 : Complex.normSq p3 = (g3 / 4) ^ 2)
    (hs : p1 + p2 + p3 = 0) : g1 ≤ g2 + g3 := by
  have heq : p1 = -(p2 + p3) := by linear_combination hs
  have htri : ‖p1‖ ≤ ‖p2‖ + ‖p3‖ := by
    rw [heq, norm_neg]
    exact norm_add_le p2 p3
  rw [norm_eq_quarter p1 g1 hg1 hp1,
    norm_eq_quarter p2 g2 hg2 hp2,
    norm_eq_quarter p3 g3 hg3 hp3] at htri
  linarith

/-- A closed triangle with nonnegative side masses summing to one gives the
three inequalities used by orbit 45. -/
theorem triangle_half_bounds (p1 p2 p3 : ℂ) (g1 g2 g3 : ℝ)
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hg3 : 0 ≤ g3)
    (hp1 : Complex.normSq p1 = (g1 / 4) ^ 2)
    (hp2 : Complex.normSq p2 = (g2 / 4) ^ 2)
    (hp3 : Complex.normSq p3 = (g3 / 4) ^ 2)
    (hs : p1 + p2 + p3 = 0) (hgm : g1 + g2 + g3 = 1) :
    g1 ≤ 1 / 2 ∧ g2 ≤ 1 / 2 ∧ g3 ≤ 1 / 2 := by
  have h1 := side_le_other_two p1 p2 p3 g1 g2 g3 hg1 hg2 hg3 hp1 hp2 hp3 hs
  have h2 := side_le_other_two p2 p1 p3 g2 g1 g3 hg2 hg1 hg3 hp2 hp1 hp3 (by
    linear_combination hs)
  have h3 := side_le_other_two p3 p1 p2 g3 g1 g2 hg3 hg1 hg2 hp3 hp1 hp2 (by
    linear_combination hs)
  constructor
  · linarith
  constructor <;> linarith

/-! ## Frame-potential identities -/

/-- The exact three-vector frame identity before the block norms are
specialized.  It is a polynomial identity in real and imaginary parts. -/
theorem frame_potential_identity
    (a1 b1 a2 b2 a3 b3 : ℂ) :
    Complex.normSq (star a2 * a1 + star b1 * b2)
      + Complex.normSq (star a3 * a1 + star b1 * b3)
      + Complex.normSq (star a2 * a3 + star b3 * b2)
    = Complex.normSq (a1 * b1 + a2 * b2 + a3 * b3)
      + (Complex.normSq a1 * Complex.normSq a2
          + Complex.normSq b1 * Complex.normSq b2)
      + (Complex.normSq a1 * Complex.normSq a3
          + Complex.normSq b1 * Complex.normSq b3)
      + (Complex.normSq a2 * Complex.normSq a3
          + Complex.normSq b2 * Complex.normSq b3)
      - (Complex.normSq a1 * Complex.normSq b1
          + Complex.normSq a2 * Complex.normSq b2
          + Complex.normSq a3 * Complex.normSq b3) := by
  simp only [Complex.star_def, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- With equal component masses and vanishing bilinear frame sum, the three
off-diagonal Gram entries have the claimed exact total. -/
theorem frame_potential
    (a1 b1 a2 b2 a3 b3 : ℂ) (g1 g2 g3 : ℝ)
    (ha1 : Complex.normSq a1 = g1 / 4)
    (hb1 : Complex.normSq b1 = g1 / 4)
    (ha2 : Complex.normSq a2 = g2 / 4)
    (hb2 : Complex.normSq b2 = g2 / 4)
    (ha3 : Complex.normSq a3 = g3 / 4)
    (hb3 : Complex.normSq b3 = g3 / 4)
    (hgm : g1 + g2 + g3 = 1)
    (ht : a1 * b1 + a2 * b2 + a3 * b3 = 0) :
    Complex.normSq (star a2 * a1 + star b1 * b2)
      + Complex.normSq (star a3 * a1 + star b1 * b3)
      + Complex.normSq (star a2 * a3 + star b3 * b2)
      = (1 - 2 * (g1 ^ 2 + g2 ^ 2 + g3 ^ 2)) / 16 := by
  have h := frame_potential_identity a1 b1 a2 b2 a3 b3
  rw [ht, Complex.normSq_zero, ha1, hb1, ha2, hb2, ha3, hb3] at h
  nlinarith

/-- The fourth off-diagonal correlation has the same squared modulus as the
bilinear two-block sum when the corresponding component norms agree. -/
theorem pair_cross_norm
    (a4 b4 a5 b5 : ℂ)
    (ha : Complex.normSq a4 = Complex.normSq a5)
    (hb : Complex.normSq b4 = Complex.normSq b5) :
    Complex.normSq (star a5 * b4 + star a4 * b5)
      = Complex.normSq (a4 * b4 + a5 * b5) := by
  have hid :
      Complex.normSq (star a5 * b4 + star a4 * b5)
        - Complex.normSq (a4 * b4 + a5 * b5)
      = -(Complex.normSq a4 - Complex.normSq a5)
          * (Complex.normSq b4 - Complex.normSq b5) := by
    simp only [Complex.star_def, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [ha, hb] at hid
  linarith

/-! ## The simplex parameter and the interval -/

/-- The orbit-45 change of variables. -/
def r (g : ℝ) : ℝ := 1 - 2 * g

/-- The three triangle inequalities are exactly nonnegativity of the simplex
coordinates, and their sum is one. -/
theorem simplex_of_masses (g1 g2 g3 : ℝ)
    (hgm : g1 + g2 + g3 = 1)
    (h1 : g1 ≤ 1 / 2) (h2 : g2 ≤ 1 / 2) (h3 : g3 ≤ 1 / 2) :
    0 ≤ r g1 ∧ 0 ≤ r g2 ∧ 0 ≤ r g3 ∧ r g1 + r g2 + r g3 = 1 := by
  unfold r
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The two exact degree-two positivity certificates for the simplex give the
closed interval `[2/3,1]`. -/
theorem simplex_interval (r1 r2 r3 : ℝ)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hr3 : 0 ≤ r3)
    (hs : r1 + r2 + r3 = 1) :
    (2 / 3 : ℝ) ≤ (1 + (r1 ^ 2 + r2 ^ 2 + r3 ^ 2)) / 2
      ∧ (1 + (r1 ^ 2 + r2 ^ 2 + r3 ^ 2)) / 2 ≤ 1 := by
  have hlo :
      3 * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - (r1 + r2 + r3) ^ 2
        = (r1 - r2) ^ 2 + (r2 - r3) ^ 2 + (r3 - r1) ^ 2 := by ring
  have hupp :
      (r1 + r2 + r3) ^ 2 - (r1 ^ 2 + r2 ^ 2 + r3 ^ 2)
        = 2 * (r1 * r2 + r1 * r3 + r2 * r3) := by ring
  constructor
  · nlinarith [sq_nonneg (r1 - r2), sq_nonneg (r2 - r3), sq_nonneg (r3 - r1)]
  · nlinarith [mul_nonneg hr1 hr2, mul_nonneg hr1 hr3, mul_nonneg hr2 hr3]

/-- The mass and simplex formulas for `A2` are identical. -/
theorem a2_change_of_variables (g1 g2 g3 : ℝ)
    (hgm : g1 + g2 + g3 = 1) :
    2 * (g1 ^ 2 + g2 ^ 2 + g3 ^ 2)
      = (1 + (r g1 ^ 2 + r g2 ^ 2 + r g3 ^ 2)) / 2 := by
  unfold r
  nlinarith

end SixQubit.Orbit45Gram
