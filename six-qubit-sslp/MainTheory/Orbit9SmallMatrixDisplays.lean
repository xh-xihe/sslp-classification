import MainTheory.Orbit8TriangleDisplays
import MainTheory.TriangleIncidenceFive
import MainTheory.Orbit9K5Determinant

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit9SmallMatrixDisplays

noncomputable def k5 (E F : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0,1,1,1,1; 1,0,F,E,-E-F; 1,F,0,-E-F,E;
    1,E,-E-F,0,F; 1,-E-F,E,F,0]

theorem k5_triangle_solution (x12 x13 x14 x23 x24 x34 : ℂ)
    (h123 : x12+x13+x23=0) (h124 : x12+x14+x24=0)
    (h134 : x13+x14+x34=0) (h234 : x23+x24+x34=0) :
    x23= -x13-x12 ∧ x14= -x13-x12 ∧ x24=x13 ∧ x34=x12 := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination h123
  · linear_combination (h124+h134+h123-h234)/2
  · linear_combination (h124-h134-h123+h234)/2
  · linear_combination (h134-h124-h123+h234)/2

theorem k5_normal_form (x12 x13 x14 x23 x24 x34 : ℂ)
    (h123 : x12+x13+x23=0) (h124 : x12+x14+x24=0)
    (h134 : x13+x14+x34=0) (h234 : x23+x24+x34=0) :
    (!![0,1,1,1,1; 1,0,x12,x13,x14; 1,x12,0,x23,x24;
      1,x13,x23,0,x34; 1,x14,x24,x34,0] : Matrix (Fin 5) (Fin 5) ℂ)=k5 x13 x12 := by
  obtain ⟨h23,h14,h24,h34⟩ := k5_triangle_solution x12 x13 x14 x23 x24 x34
    h123 h124 h134 h234
  rw [h23,h14,h24,h34]
  rfl

theorem k5_determinant (E F : ℂ) : (k5 E F).det=32*E*F*(E+F) := by
  exact MainTheory.Orbit9K5Determinant.determinant E F

theorem k5_determinant_nonzero (E F : ℂ) (hE : E ≠ 0) (hF : F ≠ 0)
    (hEF : E+F ≠ 0) : (k5 E F).det ≠ 0 := by
  rw [k5_determinant]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hE) hF) hEF

noncomputable def cross (A B C : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![C,B,A,0; B,C,0,A; A,0,C,B; 0,A,B,C]

theorem cross_minor (A B C : ℂ) (hsq : A^2+B^2+C^2=0) (hC : C ≠ 0) :
    ((cross A B C).submatrix (fun i : Fin 3 => i.castSucc) (fun i : Fin 3 => i.castSucc)).det=
      -C*(A^2+B^2-C^2) ∧ -C*(A^2+B^2-C^2)=2*C^3 ∧ 2*C^3 ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · simp [cross,Matrix.det_fin_three]
    ring
  · linear_combination -C*hsq
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ hC)

end MainTheory.Orbit9SmallMatrixDisplays
