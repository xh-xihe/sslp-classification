import MainTheory.Orbit31CanonicalPhase

/-! Literal division-free algebra behind the SI permanent-triangle arguments.
Physical branch substitutions are certified separately. -/
set_option autoImplicit false
namespace MainTheory.Orbit31PermanentAlgebra
noncomputable section
open MainTheory.Orbit31SignedSupport (B)

def permanent (c : Fin 16 → ℂ) (i j : Fin 3) (e f : Fin 4) : ℂ :=
  c (B i e)*c (B j f)+c (B i f)*c (B j e)

theorem odd_permanent_triangle (r s : Fin 3 → ℂ)
    (hr : ∀ i, r i ≠ 0) (hs : ∀ i, s i ≠ 0)
    (h01 : r 0*s 1+s 0*r 1=0)
    (h02 : r 0*s 2+s 0*r 2=0)
    (h12 : r 1*s 2+s 1*r 2=0) : False := by
  have he : (2 : ℂ)*r 0*s 1*s 2 = 0 := by
    linear_combination s 2*h01+s 1*h02-s 0*h12
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (hr 0)) (hs 1)) (hs 2)) he

theorem mixed_triangle (a b x y z w : ℂ) (hb : b ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hl : a*x+b*y=0) (hr : a*z+b*w=0) (hp : x*w+y*z=0) : False := by
  have he : (2 : ℂ)*b*y*z=0 := by
    linear_combination z*hl-x*hr+b*hp
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb) hy) hz) he

theorem product_equality (a0 a1 x0 x1 y0 y1 : ℂ) (hy0 : y0 ≠ 0)
    (h1 : a0*y0+a1*y1=0) (h2 : x0*y1+x1*y0=0) : a0*x0=a1*x1 := by
  have he : (a0*x0-a1*x1)*y0=0 := by
    linear_combination x0*h1-a1*h2
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hy0)

theorem common_product (a x : Fin 4 → ℂ) (hleft : a 0*x 0=a 1*x 1)
    (hright : a 2*x 2=a 3*x 3)
    (hsum : a 0*x 0+a 1*x 1-a 2*x 2-a 3*x 3=0) :
    a 0*x 0=a 2*x 2 ∧ a 0*x 0=a 3*x 3 := by
  constructor
  · linear_combination (1/2)*hsum+(1/2)*hleft-(1/2)*hright
  · linear_combination (1/2)*hsum+(1/2)*hleft+(1/2)*hright

theorem positive_identity (a0 a3 x0 x3 K : ℂ)
    (h0 : a0*x0=K) (h3 : a3*x3=K)
    (hstate : star a0*a3+star x3*x0=0) :
    Complex.normSq (a0*a3)+Complex.normSq K=0 := by
  have hstar := congrArg star h3
  simp only [star_mul] at hstar
  have he : ((Complex.normSq (a0*a3)+Complex.normSq K : ℝ) : ℂ) = 0 := by
    simp only [Complex.ofReal_add,Complex.normSq_eq_conj_mul_self]
    change star (a0*a3)*(a0*a3)+star K*K=0
    rw [star_mul]
    linear_combination (a0*star a3)*hstate-star K*h0-(a0*x0)*hstar
  have hre := congrArg Complex.re he
  simpa only [Complex.ofReal_re,Complex.zero_re] using hre

theorem positive_contradiction (a0 a3 x0 x3 K : ℂ)
    (ha0 : a0 ≠ 0) (ha3 : a3 ≠ 0)
    (h0 : a0*x0=K) (h3 : a3*x3=K)
    (hstate : star a0*a3+star x3*x0=0) : False := by
  have he := positive_identity a0 a3 x0 x3 K h0 h3 hstate
  have hpos := Complex.normSq_pos.mpr (mul_ne_zero ha0 ha3)
  have hn := Complex.normSq_nonneg K
  linarith

end
end MainTheory.Orbit31PermanentAlgebra
