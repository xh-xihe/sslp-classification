import MainTheory.QuaternionProjectiveOrders

/-! Discrete relative angles imposed by the short projective orders. -/

namespace MainTheory.QuaternionAxisAngles

noncomputable section

open Quaternion MainTheory.QuaternionProjectiveOrders

theorem quarter_sum (r s : ℝ) (hr : AllowedScalar r) (hs : AllowedScalar s)
    (ht : r+s = 1) : r = 0 ∨ r = 1/2 ∨ r = 1 := by
  have he : s=1-r := by linarith
  rw [he] at hs
  rcases hr with hr | hr | hr | hr <;>
    rcases hs with hs | hs | hs | hs
  all_goals first
    | exact Or.inl hr
    | exact Or.inr (Or.inr (by linarith))
    | exact Or.inr (Or.inl (by nlinarith))

def AllowedWithoutQuarter (a : ℝ) : Prop := a^2=1 ∨ a=0 ∨ 4*a^2=1

theorem rational_scalar (a : ℝ) (ha : AllowedWithoutQuarter a) :
    a=1 ∨ a= -1 ∨ a=0 ∨ a=1/2 ∨ a= -1/2 := by
  rcases ha with ha | ha | ha
  · have hp : (a-1)*(a+1)=0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl ha))
  · have hp : (a-1/2)*(a+1/2)=0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))

theorem third_sum (r s : ℝ) (hr : AllowedWithoutQuarter r) (hs : AllowedWithoutQuarter s)
    (ht : r+s=1/2) : r=1 ∨ r= -1/2 ∨ r=1/2 ∨ r=0 := by
  rcases rational_scalar r hr with hr | hr | hr | hr | hr <;>
    rcases rational_scalar s hs with hs | hs | hs | hs | hs <;>
    simp_all <;> norm_num at *

def imaginaryDot (p q : ℍ[ℝ]) : ℝ := p.imI*q.imI+p.imJ*q.imJ+p.imK*q.imK

theorem product_scalar_sum (p q : ℍ[ℝ]) :
    (p*q).re+(p*star q).re=2*p.re*q.re := by
  simp only [Quaternion.re_mul,Quaternion.re_star,Quaternion.imI_star,
    Quaternion.imJ_star,Quaternion.imK_star]
  ring

theorem quarter_relative_dot (p q : ℍ[ℝ]) (he : p.re=q.re) (hq : 2*q.re^2=1)
    (hpq : AllowedScalar (p*q).re) (hpqs : AllowedScalar (p*star q).re) :
    imaginaryDot p q = 1/2 ∨ imaginaryDot p q=0 ∨ imaginaryDot p q= -1/2 := by
  have hsum : (p*q).re+(p*star q).re=1 := by
    rw [product_scalar_sum,he]
    nlinarith [hq]
  have hr := quarter_sum _ _ hpq hpqs hsum
  have heq : (p*q).re = 1/2-imaginaryDot p q := by
    simp only [Quaternion.re_mul,imaginaryDot,he]
    nlinarith [hq]
  rcases hr with hr | hr | hr
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

theorem third_relative_dot (p q : ℍ[ℝ]) (he : p.re=q.re) (hq : 4*q.re^2=1)
    (hpq : AllowedWithoutQuarter (p*q).re)
    (hpqs : AllowedWithoutQuarter (p*star q).re) :
    imaginaryDot p q= -3/4 ∨ imaginaryDot p q=3/4 ∨
      imaginaryDot p q= -1/4 ∨ imaginaryDot p q=1/4 := by
  have hsum : (p*q).re+(p*star q).re=1/2 := by
    rw [product_scalar_sum,he]
    nlinarith [hq]
  have hr := third_sum _ _ hpq hpqs hsum
  have heq : (p*q).re=1/4-imaginaryDot p q := by
    simp only [Quaternion.re_mul,imaginaryDot,he]
    nlinarith [hq]
  rcases hr with hr | hr | hr | hr
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

end

end MainTheory.QuaternionAxisAngles
