import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit7JacobianDeterminant

noncomputable def matrix0 (tau _omega : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  !![tau]

theorem matrix0_det (tau omega : ℂ) : (matrix0 tau omega).det = tau := by
  rw [Matrix.det_fin_one]
  rfl

noncomputable def matrix1 (tau _omega : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,1;
    tau,0]

theorem matrix1_det (tau omega : ℂ) : (matrix1 tau omega).det = -tau := by
  have hs1 : (matrix1 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove = matrix0 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hrow : ∀ j : Fin 2, (-1 : ℂ)^j.val*matrix1 tau omega 0 j*
      ((matrix1 tau omega).submatrix Fin.succ j.succAbove).det =
        (![0,(-1 : ℂ)^1*(1)*(tau)] : Fin 2 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*0*_ = 0
      ring
    · change (-1 : ℂ)^1*(1)*
        ((matrix1 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove).det = (-1 : ℂ)^1*(1)*(tau)
      rw [hs1,matrix0_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]

noncomputable def matrix2 (_tau _omega : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  !![0]

theorem matrix2_det (tau omega : ℂ) : (matrix2 tau omega).det = 0 := by
  rw [Matrix.det_fin_one]
  rfl

noncomputable def matrix3 (tau omega : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  !![omega^2*tau]

theorem matrix3_det (tau omega : ℂ) : (matrix3 tau omega).det = omega^2*tau := by
  rw [Matrix.det_fin_one]
  rfl

noncomputable def matrix4 (tau omega : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![omega*tau,1;
    omega^2*tau,0]

theorem matrix4_det (tau omega : ℂ) : (matrix4 tau omega).det = -omega^2*tau := by
  have hs0 : (matrix4 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove = matrix2 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hs1 : (matrix4 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove = matrix3 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hrow : ∀ j : Fin 2, (-1 : ℂ)^j.val*matrix4 tau omega 0 j*
      ((matrix4 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(omega*tau)*(0),(-1 : ℂ)^1*(1)*(omega^2*tau)] : Fin 2 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(omega*tau)*
        ((matrix4 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove).det = (-1 : ℂ)^0*(omega*tau)*(0)
      rw [hs0,matrix2_det]
    · change (-1 : ℂ)^1*(1)*
        ((matrix4 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove).det = (-1 : ℂ)^1*(1)*(omega^2*tau)
      rw [hs1,matrix3_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]

noncomputable def matrix5 (tau omega : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![omega*tau,0;
    omega^2*tau,tau]

theorem matrix5_det (tau omega : ℂ) : (matrix5 tau omega).det = omega*tau^2 := by
  have hs0 : (matrix5 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove = matrix0 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hrow : ∀ j : Fin 2, (-1 : ℂ)^j.val*matrix5 tau omega 0 j*
      ((matrix5 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(omega*tau)*(tau),0] : Fin 2 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(omega*tau)*
        ((matrix5 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove).det = (-1 : ℂ)^0*(omega*tau)*(tau)
      rw [hs0,matrix0_det]
    · change (-1 : ℂ)^1*0*_ = 0
      ring
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix6 (tau omega : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![tau,omega^2*tau,1;
    omega*tau,0,1;
    omega^2*tau,tau,0]

theorem matrix6_det (tau omega : ℂ) : (matrix6 tau omega).det = omega^4*tau^2 + omega*tau^2 - tau^2 := by
  have hs0 : (matrix6 tau omega).submatrix Fin.succ (0 : Fin 3).succAbove = matrix1 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hs1 : (matrix6 tau omega).submatrix Fin.succ (1 : Fin 3).succAbove = matrix4 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hs2 : (matrix6 tau omega).submatrix Fin.succ (2 : Fin 3).succAbove = matrix5 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hrow : ∀ j : Fin 3, (-1 : ℂ)^j.val*matrix6 tau omega 0 j*
      ((matrix6 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(tau)*(-tau),(-1 : ℂ)^1*(omega^2*tau)*(-omega^2*tau),(-1 : ℂ)^2*(1)*(omega*tau^2)] : Fin 3 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(tau)*
        ((matrix6 tau omega).submatrix Fin.succ (0 : Fin 3).succAbove).det = (-1 : ℂ)^0*(tau)*(-tau)
      rw [hs0,matrix1_det]
    · change (-1 : ℂ)^1*(omega^2*tau)*
        ((matrix6 tau omega).submatrix Fin.succ (1 : Fin 3).succAbove).det = (-1 : ℂ)^1*(omega^2*tau)*(-omega^2*tau)
      rw [hs1,matrix4_det]
    · change (-1 : ℂ)^2*(1)*
        ((matrix6 tau omega).submatrix Fin.succ (2 : Fin 3).succAbove).det = (-1 : ℂ)^2*(1)*(omega*tau^2)
      rw [hs2,matrix5_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix7 (tau omega : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  !![omega*tau]

theorem matrix7_det (tau omega : ℂ) : (matrix7 tau omega).det = omega*tau := by
  rw [Matrix.det_fin_one]
  rfl

noncomputable def matrix8 (tau omega : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![omega^2*tau,1;
    omega*tau,0]

theorem matrix8_det (tau omega : ℂ) : (matrix8 tau omega).det = -omega*tau := by
  have hs0 : (matrix8 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove = matrix2 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hs1 : (matrix8 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove = matrix7 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hrow : ∀ j : Fin 2, (-1 : ℂ)^j.val*matrix8 tau omega 0 j*
      ((matrix8 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(omega^2*tau)*(0),(-1 : ℂ)^1*(1)*(omega*tau)] : Fin 2 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(omega^2*tau)*
        ((matrix8 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove).det = (-1 : ℂ)^0*(omega^2*tau)*(0)
      rw [hs0,matrix2_det]
    · change (-1 : ℂ)^1*(1)*
        ((matrix8 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove).det = (-1 : ℂ)^1*(1)*(omega*tau)
      rw [hs1,matrix7_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]

noncomputable def matrix9 (tau omega : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![omega*tau,omega^2*tau;
    omega^2*tau,omega*tau]

theorem matrix9_det (tau omega : ℂ) : (matrix9 tau omega).det = -omega^4*tau^2 + omega^2*tau^2 := by
  have hs0 : (matrix9 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove = matrix7 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hs1 : (matrix9 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove = matrix3 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hrow : ∀ j : Fin 2, (-1 : ℂ)^j.val*matrix9 tau omega 0 j*
      ((matrix9 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(omega*tau)*(omega*tau),(-1 : ℂ)^1*(omega^2*tau)*(omega^2*tau)] : Fin 2 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(omega*tau)*
        ((matrix9 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove).det = (-1 : ℂ)^0*(omega*tau)*(omega*tau)
      rw [hs0,matrix7_det]
    · change (-1 : ℂ)^1*(omega^2*tau)*
        ((matrix9 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove).det = (-1 : ℂ)^1*(omega^2*tau)*(omega^2*tau)
      rw [hs1,matrix3_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix10 (tau omega : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![tau,0,1;
    omega*tau,omega^2*tau,1;
    omega^2*tau,omega*tau,0]

theorem matrix10_det (tau omega : ℂ) : (matrix10 tau omega).det = -omega^4*tau^2 + omega^2*tau^2 - omega*tau^2 := by
  have hs0 : (matrix10 tau omega).submatrix Fin.succ (0 : Fin 3).succAbove = matrix8 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hs2 : (matrix10 tau omega).submatrix Fin.succ (2 : Fin 3).succAbove = matrix9 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hrow : ∀ j : Fin 3, (-1 : ℂ)^j.val*matrix10 tau omega 0 j*
      ((matrix10 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(tau)*(-omega*tau),0,(-1 : ℂ)^2*(1)*(-omega^4*tau^2 + omega^2*tau^2)] : Fin 3 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(tau)*
        ((matrix10 tau omega).submatrix Fin.succ (0 : Fin 3).succAbove).det = (-1 : ℂ)^0*(tau)*(-omega*tau)
      rw [hs0,matrix8_det]
    · change (-1 : ℂ)^1*0*_ = 0
      ring
    · change (-1 : ℂ)^2*(1)*
        ((matrix10 tau omega).submatrix Fin.succ (2 : Fin 3).succAbove).det = (-1 : ℂ)^2*(1)*(-omega^4*tau^2 + omega^2*tau^2)
      rw [hs2,matrix9_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix11 (tau omega : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,tau,omega*tau,0;
    tau,0,omega^2*tau,1;
    omega*tau,omega^2*tau,0,1;
    omega^2*tau,omega*tau,tau,0]

theorem matrix11_det (tau omega : ℂ) : (matrix11 tau omega).det = -omega^5*tau^3 - omega^4*tau^3 + omega^3*tau^3 - omega^2*tau^3 - omega*tau^3 + tau^3 := by
  have hs1 : (matrix11 tau omega).submatrix Fin.succ (1 : Fin 4).succAbove = matrix6 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hs2 : (matrix11 tau omega).submatrix Fin.succ (2 : Fin 4).succAbove = matrix10 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hrow : ∀ j : Fin 4, (-1 : ℂ)^j.val*matrix11 tau omega 0 j*
      ((matrix11 tau omega).submatrix Fin.succ j.succAbove).det =
        (![0,(-1 : ℂ)^1*(tau)*(omega^4*tau^2 + omega*tau^2 - tau^2),(-1 : ℂ)^2*(omega*tau)*(-omega^4*tau^2 + omega^2*tau^2 - omega*tau^2),0] : Fin 4 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*0*_ = 0
      ring
    · change (-1 : ℂ)^1*(tau)*
        ((matrix11 tau omega).submatrix Fin.succ (1 : Fin 4).succAbove).det = (-1 : ℂ)^1*(tau)*(omega^4*tau^2 + omega*tau^2 - tau^2)
      rw [hs1,matrix6_det]
    · change (-1 : ℂ)^2*(omega*tau)*
        ((matrix11 tau omega).submatrix Fin.succ (2 : Fin 4).succAbove).det = (-1 : ℂ)^2*(omega*tau)*(-omega^4*tau^2 + omega^2*tau^2 - omega*tau^2)
      rw [hs2,matrix10_det]
    · change (-1 : ℂ)^3*0*_ = 0
      ring
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix12 (tau _omega : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,1;
    tau,1]

theorem matrix12_det (tau omega : ℂ) : (matrix12 tau omega).det = -tau := by
  have hs1 : (matrix12 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove = matrix0 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hrow : ∀ j : Fin 2, (-1 : ℂ)^j.val*matrix12 tau omega 0 j*
      ((matrix12 tau omega).submatrix Fin.succ j.succAbove).det =
        (![0,(-1 : ℂ)^1*(1)*(tau)] : Fin 2 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*0*_ = 0
      ring
    · change (-1 : ℂ)^1*(1)*
        ((matrix12 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove).det = (-1 : ℂ)^1*(1)*(tau)
      rw [hs1,matrix0_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]

noncomputable def matrix13 (_tau _omega : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  !![1]

theorem matrix13_det (tau omega : ℂ) : (matrix13 tau omega).det = 1 := by
  rw [Matrix.det_fin_one]
  rfl

noncomputable def matrix14 (tau omega : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![omega*tau,1;
    omega^2*tau,1]

theorem matrix14_det (tau omega : ℂ) : (matrix14 tau omega).det = -omega^2*tau + omega*tau := by
  have hs0 : (matrix14 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove = matrix13 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hs1 : (matrix14 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove = matrix3 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hrow : ∀ j : Fin 2, (-1 : ℂ)^j.val*matrix14 tau omega 0 j*
      ((matrix14 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(omega*tau)*(1),(-1 : ℂ)^1*(1)*(omega^2*tau)] : Fin 2 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(omega*tau)*
        ((matrix14 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove).det = (-1 : ℂ)^0*(omega*tau)*(1)
      rw [hs0,matrix13_det]
    · change (-1 : ℂ)^1*(1)*
        ((matrix14 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove).det = (-1 : ℂ)^1*(1)*(omega^2*tau)
      rw [hs1,matrix3_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix15 (tau omega : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![tau,omega^2*tau,0;
    omega*tau,0,1;
    omega^2*tau,tau,1]

theorem matrix15_det (tau omega : ℂ) : (matrix15 tau omega).det = omega^4*tau^2 - omega^3*tau^2 - tau^2 := by
  have hs0 : (matrix15 tau omega).submatrix Fin.succ (0 : Fin 3).succAbove = matrix12 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hs1 : (matrix15 tau omega).submatrix Fin.succ (1 : Fin 3).succAbove = matrix14 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hrow : ∀ j : Fin 3, (-1 : ℂ)^j.val*matrix15 tau omega 0 j*
      ((matrix15 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(tau)*(-tau),(-1 : ℂ)^1*(omega^2*tau)*(-omega^2*tau + omega*tau),0] : Fin 3 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(tau)*
        ((matrix15 tau omega).submatrix Fin.succ (0 : Fin 3).succAbove).det = (-1 : ℂ)^0*(tau)*(-tau)
      rw [hs0,matrix12_det]
    · change (-1 : ℂ)^1*(omega^2*tau)*
        ((matrix15 tau omega).submatrix Fin.succ (1 : Fin 3).succAbove).det = (-1 : ℂ)^1*(omega^2*tau)*(-omega^2*tau + omega*tau)
      rw [hs1,matrix14_det]
    · change (-1 : ℂ)^2*0*_ = 0
      ring
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix16 (tau omega : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![omega^2*tau,1;
    omega*tau,1]

theorem matrix16_det (tau omega : ℂ) : (matrix16 tau omega).det = omega^2*tau - omega*tau := by
  have hs0 : (matrix16 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove = matrix13 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hs1 : (matrix16 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove = matrix7 tau omega := by
    ext i k
    fin_cases i; fin_cases k; rfl
  have hrow : ∀ j : Fin 2, (-1 : ℂ)^j.val*matrix16 tau omega 0 j*
      ((matrix16 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(omega^2*tau)*(1),(-1 : ℂ)^1*(1)*(omega*tau)] : Fin 2 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(omega^2*tau)*
        ((matrix16 tau omega).submatrix Fin.succ (0 : Fin 2).succAbove).det = (-1 : ℂ)^0*(omega^2*tau)*(1)
      rw [hs0,matrix13_det]
    · change (-1 : ℂ)^1*(1)*
        ((matrix16 tau omega).submatrix Fin.succ (1 : Fin 2).succAbove).det = (-1 : ℂ)^1*(1)*(omega*tau)
      rw [hs1,matrix7_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix17 (tau omega : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![tau,0,0;
    omega*tau,omega^2*tau,1;
    omega^2*tau,omega*tau,1]

theorem matrix17_det (tau omega : ℂ) : (matrix17 tau omega).det = omega^2*tau^2 - omega*tau^2 := by
  have hs0 : (matrix17 tau omega).submatrix Fin.succ (0 : Fin 3).succAbove = matrix16 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hrow : ∀ j : Fin 3, (-1 : ℂ)^j.val*matrix17 tau omega 0 j*
      ((matrix17 tau omega).submatrix Fin.succ j.succAbove).det =
        (![(-1 : ℂ)^0*(tau)*(omega^2*tau - omega*tau),0,0] : Fin 3 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*(tau)*
        ((matrix17 tau omega).submatrix Fin.succ (0 : Fin 3).succAbove).det = (-1 : ℂ)^0*(tau)*(omega^2*tau - omega*tau)
      rw [hs0,matrix16_det]
    · change (-1 : ℂ)^1*0*_ = 0
      ring
    · change (-1 : ℂ)^2*0*_ = 0
      ring
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix18 (tau omega : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,tau,omega*tau,0;
    tau,0,omega^2*tau,0;
    omega*tau,omega^2*tau,0,1;
    omega^2*tau,omega*tau,tau,1]

theorem matrix18_det (tau omega : ℂ) : (matrix18 tau omega).det = -omega^4*tau^3 + 2*omega^3*tau^3 - omega^2*tau^3 + tau^3 := by
  have hs1 : (matrix18 tau omega).submatrix Fin.succ (1 : Fin 4).succAbove = matrix15 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hs2 : (matrix18 tau omega).submatrix Fin.succ (2 : Fin 4).succAbove = matrix17 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hrow : ∀ j : Fin 4, (-1 : ℂ)^j.val*matrix18 tau omega 0 j*
      ((matrix18 tau omega).submatrix Fin.succ j.succAbove).det =
        (![0,(-1 : ℂ)^1*(tau)*(omega^4*tau^2 - omega^3*tau^2 - tau^2),(-1 : ℂ)^2*(omega*tau)*(omega^2*tau^2 - omega*tau^2),0] : Fin 4 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*0*_ = 0
      ring
    · change (-1 : ℂ)^1*(tau)*
        ((matrix18 tau omega).submatrix Fin.succ (1 : Fin 4).succAbove).det = (-1 : ℂ)^1*(tau)*(omega^4*tau^2 - omega^3*tau^2 - tau^2)
      rw [hs1,matrix15_det]
    · change (-1 : ℂ)^2*(omega*tau)*
        ((matrix18 tau omega).submatrix Fin.succ (2 : Fin 4).succAbove).det = (-1 : ℂ)^2*(omega*tau)*(omega^2*tau^2 - omega*tau^2)
      rw [hs2,matrix17_det]
    · change (-1 : ℂ)^3*0*_ = 0
      ring
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

noncomputable def matrix19 (tau omega : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0,0,0,tau,omega^2*tau;
    0,tau,omega*tau,0,0;
    tau,0,omega^2*tau,0,1;
    omega*tau,omega^2*tau,0,1,1;
    omega^2*tau,omega*tau,tau,1,0]

theorem matrix19_det (tau omega : ℂ) : (matrix19 tau omega).det = -omega^6*tau^4 + 3*omega^5*tau^4 - omega^3*tau^4 + 2*omega^2*tau^4 + omega*tau^4 - tau^4 := by
  have hs3 : (matrix19 tau omega).submatrix Fin.succ (3 : Fin 5).succAbove = matrix11 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hs4 : (matrix19 tau omega).submatrix Fin.succ (4 : Fin 5).succAbove = matrix18 tau omega := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hrow : ∀ j : Fin 5, (-1 : ℂ)^j.val*matrix19 tau omega 0 j*
      ((matrix19 tau omega).submatrix Fin.succ j.succAbove).det =
        (![0,0,0,(-1 : ℂ)^3*(tau)*(-omega^5*tau^3 - omega^4*tau^3 + omega^3*tau^3 - omega^2*tau^3 - omega*tau^3 + tau^3),(-1 : ℂ)^4*(omega^2*tau)*(-omega^4*tau^3 + 2*omega^3*tau^3 - omega^2*tau^3 + tau^3)] : Fin 5 → ℂ) j := by
    intro j
    fin_cases j
    · change (-1 : ℂ)^0*0*_ = 0
      ring
    · change (-1 : ℂ)^1*0*_ = 0
      ring
    · change (-1 : ℂ)^2*0*_ = 0
      ring
    · change (-1 : ℂ)^3*(tau)*
        ((matrix19 tau omega).submatrix Fin.succ (3 : Fin 5).succAbove).det = (-1 : ℂ)^3*(tau)*(-omega^5*tau^3 - omega^4*tau^3 + omega^3*tau^3 - omega^2*tau^3 - omega*tau^3 + tau^3)
      rw [hs3,matrix11_det]
    · change (-1 : ℂ)^4*(omega^2*tau)*
        ((matrix19 tau omega).submatrix Fin.succ (4 : Fin 5).succAbove).det = (-1 : ℂ)^4*(omega^2*tau)*(-omega^4*tau^3 + 2*omega^3*tau^3 - omega^2*tau^3 + tau^3)
      rw [hs4,matrix18_det]
  rw [Matrix.det_succ_row_zero]
  simp_rw [hrow]
  norm_num [Fin.sum_univ_succ]
  ring

alias determinant_raw := matrix19_det

end MainTheory.Orbit7JacobianDeterminant
