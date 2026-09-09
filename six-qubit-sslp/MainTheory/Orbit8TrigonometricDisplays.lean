import MainTheory.Orbit8FamilyDisplays

set_option autoImplicit false

namespace MainTheory.Orbit8TrigonometricDisplays

open SixQubit.Orbit8Family MainTheory.Orbit8EnumeratorDisplays

theorem circle (theta : ℝ) : Real.cos theta^2+Real.sin theta^2=1 := by
  nlinarith [Real.sin_sq_add_cos_sq theta]

theorem Z_expectations (theta : ℝ) :
    lambda (code (Real.cos theta) (Real.sin theta)) PZ4= -((Real.cos theta)^2 : ℝ) ∧
    lambda (code (Real.cos theta) (Real.sin theta)) PZ0= -((Real.sin theta)^2 : ℝ) := by
  constructor
  · rw [lambda,trProj_Z4 _ _ (circle theta)]
    push_cast
    ring
  · rw [lambda,trProj_Z0 _ _ (circle theta)]
    push_cast
    ring

theorem XX_YY_expectations (theta : ℝ) :
    lambda (code (Real.cos theta) (Real.sin theta)) PXX=
      -((Real.sin theta*Real.cos theta : ℝ) : ℂ) ∧
    lambda (code (Real.cos theta) (Real.sin theta)) PYY=
      -((Real.sin theta*Real.cos theta : ℝ) : ℂ) := by
  constructor
  · rw [lambda,trProj_XX]
    push_cast
    ring
  · rw [lambda,trProj_YY]
    push_cast
    ring

theorem alpha_theta (theta : ℝ) :
    normalizedA (code (Real.cos theta) (Real.sin theta)) 1=
      Real.cos theta^4+Real.sin theta^4 ∧
    Real.cos theta^4+Real.sin theta^4=1-(1/2 : ℝ)*Real.sin (2*theta)^2 := by
  constructor
  · rw [normalizedA,Aco_one _ _ (circle theta),alpha]
    ring
  · rw [Real.sin_two_mul]
    nlinarith [sq_nonneg (Real.cos theta^2-Real.sin theta^2),circle theta,
      sq_nonneg (Real.cos theta^2+Real.sin theta^2-1)]

end MainTheory.Orbit8TrigonometricDisplays
