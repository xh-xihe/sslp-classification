import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.Orbit9K5Determinant

noncomputable def matrix (E F : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0,1,1,1,1; 1,0,F,E,-E-F; 1,F,0,-E-F,E;
    1,E,-E-F,0,F; 1,-E-F,E,F,0]

def basisData : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2,-2,0,0,0; 1,1,1,1,1; 1,1,1,-1,-1; 1,1,-1,1,-1; 1,1,-1,-1,1]

noncomputable def basis : Matrix (Fin 5) (Fin 5) ℂ := basisData.map (Int.castRingHom ℂ)

theorem basis_gram_data : basisData.transpose*basisData=Matrix.diagonal ![8,8,4,4,4] := by decide

theorem basis_gram : basis.transpose*basis=Matrix.diagonal ![8,8,4,4,4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis,basisData,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.diagonal_apply,Fin.sum_univ_succ]

theorem basis_det_nonzero : basis.det ≠ 0 := by
  have h := congrArg Matrix.det basis_gram
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal] at h
  norm_num [Fin.prod_univ_succ] at h
  intro hz
  rw [hz] at h
  norm_num at h

theorem diagonalization (E F : ℂ) :
    matrix E F*basis=basis*Matrix.diagonal ![2,-2,2*F,2*E,-2*(E+F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix,basis,basisData,Matrix.mul_apply,Matrix.diagonal_apply,
      Fin.sum_univ_succ] <;> ring

theorem determinant (E F : ℂ) : (matrix E F).det=32*E*F*(E+F) := by
  have h := congrArg Matrix.det (diagonalization E F)
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal] at h
  have he : (matrix E F).det=∏ i : Fin 5,(![2,-2,2*F,2*E,-2*(E+F)] : Fin 5 → ℂ) i := by
    apply mul_right_cancel₀ basis_det_nonzero
    simpa only [mul_comm basis.det] using h
  rw [he]
  norm_num [Fin.prod_univ_succ]
  ring

end MainTheory.Orbit9K5Determinant
