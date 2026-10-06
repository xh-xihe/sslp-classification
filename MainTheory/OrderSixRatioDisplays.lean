import MainTheory.NegativePhaseEquations

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.OrderSixRatioDisplays

open MainTheory.NegativePhaseEquations

theorem plus55 (C : Fin 11 → ℂ) (h3 : C 3 ≠ 0) (h5 : C 5 ≠ 0) (h10 : C 10 ≠ 0)
    (h1 : C 2*C 10+C 3*C 9=0) (h2 : C 4*C 10+C 5*C 9=0) :
    C 2/C 3= -(C 9/C 10) ∧ -(C 9/C 10)=C 4/C 5 := by
  exact ⟨ratio _ _ _ _ h3 h10 h1,(ratio _ _ _ _ h5 h10 h2).symm⟩

theorem minus55 (C : Fin 11 → ℂ) (h3 : C 3 ≠ 0) (h5 : C 5 ≠ 0)
    (h : C 2*C 5+C 3*C 4=0) : C 2/C 3= -(C 4/C 5) := ratio _ _ _ _ h3 h5 h

theorem solved54 (C : Fin 9 → ℂ) (h4 : C 4 ≠ 0)
    (h1 : C 4*C 6= -(C 0*C 8)) (h2 : C 4*C 5= -(C 0*C 7)) :
    C 6= -(C 0*C 8/C 4) ∧ C 5= -(C 0*C 7/C 4) := by
  constructor
  · field_simp [h4]
    linear_combination h1
  · field_simp [h4]
    linear_combination h2

theorem contradiction54 (C : Fin 9 → ℂ) (h4 : C 4 ≠ 0)
    (h1 : C 4*C 6= -(C 0*C 8)) (h2 : C 4*C 5= -(C 0*C 7))
    (h3 : C 6*C 7= -(C 5*C 8)) :
    -(C 0*C 7*C 8/C 4)=C 0*C 7*C 8/C 4 := by
  field_simp [h4]
  linear_combination C 4*h3-C 7*h1-C 8*h2

theorem plus56 (C : Fin 10 → ℂ) (h4 : C 4 ≠ 0) (h5 : C 5 ≠ 0) (h7 : C 7 ≠ 0)
    (h2 : C 2*C 7+C 4*C 5=0) (h3 : C 2*C 6+C 3*C 5=0) :
    C 3/C 4=C 6/C 7 := by
  have he : (C 3*C 7-C 6*C 4)*C 5=0 := by
    linear_combination C 7*h3-C 6*h2
  have hz := (mul_eq_zero.mp he).resolve_right h5
  apply (div_eq_div_iff h4 h7).2
  linear_combination hz

theorem minus56 (C : Fin 10 → ℂ) (h4 : C 4 ≠ 0) (h7 : C 7 ≠ 0)
    (h1 : C 3*C 7+C 4*C 6=0) : C 3/C 4= -(C 6/C 7) := ratio _ _ _ _ h4 h7 h1

end MainTheory.OrderSixRatioDisplays
