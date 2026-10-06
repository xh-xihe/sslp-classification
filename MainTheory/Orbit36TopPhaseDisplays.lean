import SixQubit.Orbit36Enum

set_option autoImplicit false

namespace MainTheory.Orbit36TopPhaseDisplays

open SixQubit.Orbit36 SixQubit.Orbit36Enum

theorem tau_formula {c d : SS.BitString 6 → ℂ} {tau : ℂ}
    (h : TopForm c d tau) (hb : c y1 ≠ 0) : tau = d z1 / star (c y1) := by
  rw [h.t1, mul_div_cancel_right₀ _ (star_ne_zero.mpr hb)]

theorem last_flip_relations {c d : SS.BitString 6 → ℂ} {tau : ℂ}
    (h : TopForm c d tau) : ∀ i : Fin 4,
      star (c y1) * d (![z2,z3,z4,z5] i) + star (c (![y2,y3,y4,y5] i)) * d z1 = 0 ∧
      star (c y0) * d (![z2,z3,z4,z5] i) + star (c (![y2,y3,y4,y5] i)) * d z0 = 0 := by
  intro i
  fin_cases i <;> constructor <;> simp [h.t0,h.t1,h.t2,h.t3,h.t4,h.t5] <;> ring

theorem matching_of_topForm {c d : SS.BitString 6 → ℂ} {tau : ℂ}
    (h : TopForm c d tau) (hoff : offSum c d ex56 w0 = 0) :
    c y6 * c y11 + c y7 * c y10 + c y8 * c y9 = 0 := by
  have htau : tau ≠ 0 := by
    intro hz
    have hh := h.unit
    rw [hz, mul_zero] at hh
    exact zero_ne_one hh
  rw [ex_ex56_w0, h.t6, h.t7, h.t8, h.t9, h.t10, h.t11] at hoff
  have hh : (-2*tau) * star (c y6 * c y11 + c y7 * c y10 + c y8 * c y9) = 0 := by
    simp only [star_add, star_mul']
    linear_combination hoff
  exact star_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) htau))

end MainTheory.Orbit36TopPhaseDisplays
