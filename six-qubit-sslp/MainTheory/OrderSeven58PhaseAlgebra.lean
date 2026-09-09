import MainTheory.ComplementPhaseRatios

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.OrderSeven58PhaseAlgebra

theorem common (r : Fin 9 → ℂ)
    (h08 : r 8=r 0) (h46 : r 6=r 4) (h07 : r 7=r 0)
    (h36 : r 6=r 3) (h35 : r 5= -r 3) (h57 : r 7= -r 5) :
    r 0=r 3 ∧ r 0=r 4 ∧ r 0=r 6 ∧ r 0=r 7 ∧ r 0=r 8 := by
  have h03 : r 0=r 3 := by linear_combination h57-h07-h35
  exact ⟨h03,h03.trans (h36.symm.trans h46),h03.trans h36.symm,h07.symm,h08.symm⟩

theorem product_equation (r a b c d : ℂ) (hr : r ≠ 0)
    (h : r*star (a*b)= -(r*star (c*d))) : a*b= -(c*d) := by
  have he : star (a*b)= -star (c*d) := by
    apply mul_left_cancel₀ hr
    linear_combination h
  have hs := congrArg star he
  simpa only [star_star,star_neg] using hs

theorem fatal_equation (r a b c d : ℂ) (hr : r ≠ 0)
    (h : r*star (a*b)+r*star (c*d)+r*star (d*c)+r*star (b*a)=0) :
    a*b+c*d=0 := by
  simp only [star_mul'] at h
  have he : r*(star a*star b+star c*star d)=0 := by linear_combination h/2
  have hs := (mul_eq_zero.mp he).resolve_left hr
  have hh := congrArg star hs
  simpa only [star_add,star_mul',star_star,star_zero] using hh

theorem contradiction_value (c : Fin 9 → ℂ) (h0 : c 0 ≠ 0)
    (h46 : c 4*c 6= -(c 0*c 8)) (h36 : c 3*c 6= -(c 0*c 7)) :
    c 3*c 8+c 4*c 7= -(2*c 3*c 4*c 6/c 0) := by
  field_simp [h0]
  linear_combination c 3*h46+c 4*h36

theorem value_nonzero (c : Fin 9 → ℂ) (h0 : c 0 ≠ 0) (h3 : c 3 ≠ 0)
    (h4 : c 4 ≠ 0) (h6 : c 6 ≠ 0) : -(2*c 3*c 4*c 6/c 0) ≠ 0 := by
  exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) h3) h4) h6) h0)

end MainTheory.OrderSeven58PhaseAlgebra
