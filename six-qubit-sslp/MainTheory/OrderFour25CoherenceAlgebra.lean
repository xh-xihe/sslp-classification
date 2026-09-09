import Mathlib
set_option autoImplicit false
namespace MainTheory.OrderFour25CoherenceAlgebra

theorem square (z : ℂ) : star z*z=(Complex.normSq z : ℂ) := by
  simp only [Complex.star_def,Complex.normSq_eq_conj_mul_self]

theorem tail_coherence (a0 a1 r0 r1 : ℂ)
    (ha : Complex.normSq a1=3/16) (hr : Complex.normSq r0=1/16)
    (h : star a0*r0+star a1*r1=0) : star r0*r1= -(star a0*a1)/3 := by
  have sa : star a1*a1=(3/16 : ℂ) := by rw [square,ha]; norm_num
  have sr : star r0*r0=(1/16 : ℂ) := by rw [square,hr]; norm_num
  linear_combination (16/3 : ℂ)*(a1*star r0*h-star a0*a1*sr-star r0*r1*sa)

theorem opposite_anchors (a0 a1 b1 r0 s0 s1 : ℂ)
    (ha : Complex.normSq a1=3/16) (hs : Complex.normSq s0=3/16)
    (hr : r0 ≠ 0)
    (hk : star b1*s1=star a0*r0)
    (hf : star a1*r0+star b1*s0=0) : star s0*s1= -(star a0*a1) := by
  have he : r0*(star a1*s1+star a0*s0)=0 := by
    linear_combination s1*hf-s0*hk
  have he' := (mul_eq_zero.mp he).resolve_left hr
  have sa : star a1*a1=(3/16 : ℂ) := by rw [square,ha]; norm_num
  have ss : star s0*s0=(3/16 : ℂ) := by rw [square,hs]; norm_num
  linear_combination (16/3 : ℂ)*(a1*star s0*he'-star s0*s1*sa-star a0*a1*ss)

end MainTheory.OrderFour25CoherenceAlgebra
