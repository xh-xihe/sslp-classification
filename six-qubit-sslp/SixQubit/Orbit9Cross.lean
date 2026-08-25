import Mathlib

/-!
# Orbit 9: exact algebra for the inactive-to-`K₄` cross edges

This is the label-free polynomial core of the last support-reduction step.
It contains no amplitude or support assumptions.  The first theorem derives
the opposite-edge normal form of a row-kernel `K₄`; the second proves that
the four cross variables vanish from the exact pair-flip rows and the
inactive companion row.
-/

namespace SixQubit.Orbit9Cross

noncomputable section

/-- A symmetric zero-diagonal four-vertex row-kernel matrix has equal
opposite edges.  Its hafnian then becomes the sum of their three squares. -/
theorem k4_normal_form
    (m01 m02 m03 m12 m13 m23 : ℂ)
    (r0 : m01 + m02 + m03 = 0)
    (r1 : m01 + m12 + m13 = 0)
    (r2 : m02 + m12 + m23 = 0)
    (r3 : m03 + m13 + m23 = 0)
    (hhaf : m01 * m23 + m02 * m13 + m03 * m12 = 0) :
    m01 = m23 ∧ m02 = m13 ∧ m03 = m12 ∧
      m01 + m02 + m03 = 0 ∧ m01 ^ 2 + m02 ^ 2 + m03 ^ 2 = 0 := by
  have h01 : m01 = m23 := by
    linear_combination (1 / 2 : ℂ) * (r0 + r1 - r2 - r3)
  have h02 : m02 = m13 := by
    linear_combination (1 / 2 : ℂ) * (r0 - r1 + r2 - r3)
  have h03 : m03 = m12 := by
    linear_combination (1 / 2 : ℂ) * (r0 - r1 - r2 + r3)
  refine ⟨h01, h02, h03, r0, ?_⟩
  rw [← h01, ← h02, ← h03] at hhaf
  simpa [pow_two] using hhaf

/-- The exact cross-edge kernel certificate.  Here `A,B,C` are the three
opposite-edge labels of the active `K₄`, and `z0,…,z3` are the four
inactive-to-active cross variables.  Three of the four pair-flip rows already
force the `z` vector to be constant; the inactive companion sum then kills
that constant.  The certificate is division-free except for cancellation by
the explicitly supplied nonzero edge `C`. -/
theorem cross_edges_zero
    (A B C z0 z1 z2 z3 : ℂ)
    (hsum : A + B + C = 0)
    (hsq : A ^ 2 + B ^ 2 + C ^ 2 = 0)
    (hC : C ≠ 0)
    (e0 : C * z0 + B * z1 + A * z2 = 0)
    (e1 : B * z0 + C * z1 + A * z3 = 0)
    (e2 : A * z0 + C * z2 + B * z3 = 0)
    (hcomp : z0 + z1 + z2 + z3 = 0) :
    z0 = 0 ∧ z1 = 0 ∧ z2 = 0 ∧ z3 = 0 := by
  have w0 : C * (z0 - z3) + B * (z1 - z3) + A * (z2 - z3) = 0 := by
    linear_combination e0 - z3 * hsum
  have w1 : B * (z0 - z3) + C * (z1 - z3) = 0 := by
    linear_combination e1 - z3 * hsum
  have w2 : A * (z0 - z3) + C * (z2 - z3) = 0 := by
    linear_combination e2 - z3 * hsum
  have hz0mul : (2 * C ^ 2) * (z0 - z3) = 0 := by
    linear_combination C * w0 - B * w1 - A * w2 + (z0 - z3) * hsq
  have hfac : (2 * C ^ 2 : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hC)
  have hz0 : z0 = z3 := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz0mul).resolve_left hfac)
  have hz1 : z1 = z3 := by
    rw [hz0] at w1
    simp only [sub_self, mul_zero, zero_add] at w1
    exact sub_eq_zero.mp ((mul_eq_zero.mp w1).resolve_left hC)
  have hz2 : z2 = z3 := by
    rw [hz0] at w2
    simp only [sub_self, mul_zero, zero_add] at w2
    exact sub_eq_zero.mp ((mul_eq_zero.mp w2).resolve_left hC)
  have hz3 : z3 = 0 := by
    rw [hz0, hz1, hz2] at hcomp
    linear_combination (1 / 4 : ℂ) * hcomp
  simp [hz0, hz1, hz2, hz3]

end

end SixQubit.Orbit9Cross
