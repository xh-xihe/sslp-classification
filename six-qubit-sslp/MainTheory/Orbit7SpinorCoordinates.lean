import SixQubit.Orbit7UniversalMatrix
import SixQubit.Spinor

set_option autoImplicit false

namespace MainTheory.Orbit7SpinorCoordinates

open SixQubit.Orbit7Universal

noncomputable def nvec (c d : ℝ) : Spinor := ![(c : ℂ),(d : ℂ)]
noncomputable def mvec (c d : ℝ) : Spinor := ![-(d : ℂ),(c : ℂ)]
noncomputable def avec (c d : ℝ) (x y : ℂ) : Spinor :=
  ![(c : ℂ)*x-(d : ℂ)*y,(d : ℂ)*x+(c : ℂ)*y]

theorem orthonormal (c d : ℝ) (h : c^2+d^2 = 1) :
    spinInner (nvec c d) (nvec c d) = 1 ∧
    spinInner (mvec c d) (mvec c d) = 1 ∧
    spinInner (nvec c d) (mvec c d) = 0 ∧
    spinInner (mvec c d) (nvec c d) = 0 := by
  have hC : (c : ℂ)^2+(d : ℂ)^2=1 := by exact_mod_cast h
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp [spinInner,nvec,mvec]
  all_goals try { solve | ring }
  all_goals linear_combination hC

theorem coordinate_expansion (c d : ℝ) (h : c^2+d^2=1) (a : Spinor) :
    a = fun i => spinInner (nvec c d) a * nvec c d i +
      spinInner (mvec c d) a * mvec c d i := by
  have hC : (c : ℂ)^2+(d : ℂ)^2=1 := by exact_mod_cast h
  funext i
  fin_cases i <;> simp [spinInner,nvec,mvec]
  · linear_combination -(a 0)*hC
  · linear_combination -(a 1)*hC

theorem avec_norm (c d : ℝ) (h : c^2+d^2=1) (x y : ℂ) :
    Complex.normSq (avec c d x y 0) + Complex.normSq (avec c d x y 1) =
      Complex.normSq x + Complex.normSq y := by
  have ht := SixQubit.Spinor.lagrange (c : ℂ) (-d : ℂ) x y
  have h' : c*c+d*d=1 := by nlinarith [h]
  simpa [avec,Complex.normSq_ofReal,h',sub_eq_add_neg,mul_comm,add_comm] using ht

theorem cross_parameter (c d : ℝ) (h : c^2+d^2=1) (x y : ℂ) (b : Spinor)
    (hcross : b 0 + spinInner (avec c d x y) (nvec c d) = 0)
    (hnorm : Complex.normSq (b 0) + Complex.normSq (b 1) =
      Complex.normSq (avec c d x y 0) + Complex.normSq (avec c d x y 1)) :
    ∃ z : ℂ, b = ![-star x,star z] ∧ ‖z‖ = ‖y‖ := by
  have hC : (c : ℂ)^2+(d : ℂ)^2=1 := by exact_mod_cast h
  have hin : spinInner (avec c d x y) (nvec c d) = star x := by
    simp [spinInner,avec,nvec]
    linear_combination ((starRingEnd ℂ) x)*hC
  rw [hin] at hcross
  have hb0 : b 0 = -star x := eq_neg_of_add_eq_zero_left hcross
  refine ⟨star (b 1),?_,?_⟩
  · funext i
    fin_cases i <;> simp [hb0]
  · rw [avec_norm c d h x y,hb0] at hnorm
    have hn : Complex.normSq (b 1) = Complex.normSq y := by
      simpa using hnorm
    simp only [Complex.normSq_eq_norm_sq] at hn
    simp only [norm_star]
    nlinarith [norm_nonneg (b 1),norm_nonneg y]

end MainTheory.Orbit7SpinorCoordinates
