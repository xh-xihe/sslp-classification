import SixQubit.Orbit36Phase

set_option autoImplicit false

namespace MainTheory.Orbit36NormalizedPhases

theorem normalized_norm {a : ℝ} {z : ℂ} (ha : 0 < a)
    (hz : Complex.normSq z = 1/a) : ‖(Real.sqrt a : ℂ) * z‖ = 1 := by
  have hh : Complex.normSq ((Real.sqrt a : ℂ) * z) = 1 := by
    rw [map_mul, Complex.normSq_ofReal, Real.mul_self_sqrt ha.le, hz]
    field_simp
  rw [Complex.normSq_eq_norm_sq] at hh
  nlinarith [norm_nonneg ((Real.sqrt a : ℂ) * z)]

theorem vertex_unit {r : ℂ} (hr : Complex.normSq r = 1/10) :
    ‖(Real.sqrt 10 : ℂ) * r‖ = 1 := normalized_norm (by norm_num) hr

theorem edge_unit {c : ℂ} (hc : Complex.normSq c = 1/15) :
    ‖(Real.sqrt 15 : ℂ) * c‖ = 1 := normalized_norm (by norm_num) hc

theorem normalized_row_sum (r : Fin 4 → ℂ) (C : Matrix (Fin 4) (Fin 4) ℂ)
    (h : C.mulVec r = 0) (i : Fin 4) :
    ∑ j, ((Real.sqrt 10 : ℂ) * r i) * ((Real.sqrt 10 : ℂ) * r j) *
      ((Real.sqrt 15 : ℂ) * C i j) = 0 := by
  have hi := congrFun h i
  change (∑ j, C i j * r j) = 0 at hi
  calc
    _ = ((Real.sqrt 10 : ℂ) * (Real.sqrt 10 : ℂ) * (Real.sqrt 15 : ℂ) * r i) *
        ∑ j, C i j * r j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hi, mul_zero]

end MainTheory.Orbit36NormalizedPhases
