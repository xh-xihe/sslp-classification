import SixQubit.Orbit8UniversalSaturation

/-!
# Orbit 8 universal converse, IX: the complementary-hafnian obstruction

This file contains the purely algebraic equality-case obstruction used after
the code equations have produced the complementary hafnians.  It is stated
without divisions: the five star edges have already been normalized to one.
-/

namespace SixQubit.Orbit8Universal

open scoped ComplexConjugate

noncomputable section

/-- The seven triangle hafnians forced by any three active singleton
vertices, together with three forced four-vertex hafnians, are inconsistent
when the two displayed edge variables are nonzero.  This single lemma covers
all support sizes `3,4,5,6`; extra active vertices only add equations. -/
lemma normalized_support3_impossible
    (x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 : ℂ)
    (hx13 : x13 ≠ 0) (hx14 : x14 ≠ 0)
    (t134 : x13 + x14 + x34 = 0)
    (t135 : x13 + x15 + x35 = 0)
    (t145 : x14 + x15 + x45 = 0)
    (t234 : x23 + x24 + x34 = 0)
    (t235 : x23 + x25 + x35 = 0)
    (t245 : x24 + x25 + x45 = 0)
    (t345 : x34 + x35 + x45 = 0)
    (q1345 : x13*x45 + x14*x35 + x15*x34 = 0)
    (q1235 : x12*x35 + x13*x25 + x15*x23 = 0)
    (q1245 : x12*x45 + x14*x25 + x15*x24 = 0) : False := by
  have h34 : x34 = -x13-x14 := by linear_combination t134
  have h35 : x35 = x14 := by
    linear_combination (1/2 : ℂ) * (t345 - t134 + t135 - t145)
  have h45 : x45 = x13 := by
    linear_combination (1/2 : ℂ) * (t345 - t134 - t135 + t145)
  have h15 : x15 = -x13-x14 := by linear_combination t135 - h35
  have h23 : x23 = x13 := by
    linear_combination (1/2 : ℂ) *
      (t234 - t134 + t235 - t245 - h35 + h45)
  have h24 : x24 = x14 := by
    linear_combination (1/2 : ℂ) *
      (t234 - t134 - t235 + t245 + h35 - h45)
  have h25 : x25 = -x13-x14 := by linear_combination t235 - h23 - h35
  rw [h34, h35, h45, h15] at q1345
  rw [h35, h25, h15, h23] at q1235
  rw [h45, h25, h15, h24] at q1245
  have q1 : x13^2 + x13*x14 + x14^2 = 0 := by
    linear_combination (1/2 : ℂ) * q1345
  have q2 : x12*x14 - 2*x13*(x13+x14) = 0 := by
    linear_combination q1235
  have q3 : x12*x13 - 2*x14*(x13+x14) = 0 := by
    linear_combination q1245
  have hbprod : x14 * (x12 + 2*x14) = 0 := by
    linear_combination q2 + 2*q1
  have haprod : x13 * (x12 + 2*x13) = 0 := by
    linear_combination q3 + 2*q1
  have hdb : x12 = -2*x14 := by
    rcases mul_eq_zero.mp hbprod with h | h
    · exact (hx14 h).elim
    · linear_combination h
  have hda : x12 = -2*x13 := by
    rcases mul_eq_zero.mp haprod with h | h
    · exact (hx13 h).elim
    · linear_combination h
  have hab : x13 = x14 := by
    linear_combination (1/2 : ℂ) * (hda - hdb)
  rw [hab] at q1
  have hz : x14 = 0 := by
    have hsq : x14^2 = 0 := by linear_combination (1/3 : ℂ) * q1
    exact (sq_eq_zero_iff).mp hsq
  exact hx14 hz

end

end SixQubit.Orbit8Universal
