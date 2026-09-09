import MainTheory.PauliTransferTwo

set_option autoImplicit false

namespace MainTheory.CitedSingleQubitMatrices

open MainTheory.PauliTransferTwo

noncomputable def H : Mat2 := (Real.sqrt 2 : ℂ)⁻¹ • !![1,1;1,-1]
noncomputable def S : Mat2 := !![1,0;0,Complex.I]
noncomputable def YHS : Mat2 := pauli 2*H*S
noncomputable def YHSadj : Mat2 := pauli 2*H*S.conjTranspose
noncomputable def Zthird : Mat2 :=
  Matrix.diagonal ![Complex.exp (-((Real.pi/3 : ℝ) : ℂ)*Complex.I),
    Complex.exp (((Real.pi/3 : ℝ) : ℂ)*Complex.I)]
noncomputable def T : Mat2 := !![-Complex.I,-1;Complex.I,-1]
noncomputable def Tadj : Mat2 := !![-Complex.I,1;Complex.I,1]
noncomputable def D : Mat2 :=
  !![1-Complex.I*(Real.sqrt 3 : ℂ),0;0,1+Complex.I*(Real.sqrt 3 : ℂ)]

theorem yhs_matrix : YHS=(Real.sqrt 2 : ℂ)⁻¹ • T := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [YHS,H,S,T,pauli,Matrix.mul_apply,Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq]

theorem yhsadj_matrix : YHSadj=(Real.sqrt 2 : ℂ)⁻¹ • Tadj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [YHSadj,H,S,Tadj,pauli,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring_nf <;> simp [Complex.I_sq]

theorem zthird_matrix : Zthird=(1/2 : ℂ) • D := by
  have hp : Complex.exp (((Real.pi/3 : ℝ) : ℂ)*Complex.I) =
      (1+Complex.I*(Real.sqrt 3 : ℂ))/2 := by
    rw [Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin,
      Real.cos_pi_div_three,Real.sin_pi_div_three]
    push_cast
    ring
  have hm : Complex.exp (-((Real.pi/3 : ℝ) : ℂ)*Complex.I) =
      (1-Complex.I*(Real.sqrt 3 : ℂ))/2 := by
    rw [Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg,
      ← Complex.ofReal_cos,← Complex.ofReal_sin,
      Real.cos_pi_div_three,Real.sin_pi_div_three]
    push_cast
    ring
  unfold Zthird
  rw [hp,hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D] <;> ring

noncomputable def coefficientA : ℝ := Real.sqrt ((3-Real.sqrt 3)/12)
noncomputable def coefficientB : ℝ := Real.sqrt ((3+Real.sqrt 3)/6)
noncomputable def citedV : Mat2 :=
  (coefficientA : ℂ) • (pauli 1+pauli 2)-(coefficientB : ℂ) • pauli 3
noncomputable def W : Mat2 :=
  !![-2,((Real.sqrt 3 : ℂ)-1)*(1-Complex.I);
    ((Real.sqrt 3 : ℂ)-1)*(1+Complex.I),2]

theorem coefficientA_eq : coefficientA=coefficientB*(Real.sqrt 3-1)/2 := by
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hr1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith
  have hr3 : Real.sqrt (3 : ℝ) ≤ 3 := by nlinarith
  have hA : coefficientA^2=(3-Real.sqrt 3)/12 := Real.sq_sqrt
    (div_nonneg (sub_nonneg.mpr hr3) (by norm_num))
  have hB : coefficientB^2=(3+Real.sqrt 3)/6 := Real.sq_sqrt (by positivity)
  have hA0 : 0 ≤ coefficientA := Real.sqrt_nonneg _
  have hB0 : 0 ≤ coefficientB := Real.sqrt_nonneg _
  have hsq : (coefficientB*(Real.sqrt 3-1)/2)^2=coefficientA^2 := by
    linear_combination ((Real.sqrt 3-1)^2/4)*hB-hA+((Real.sqrt 3+1)/24)*hr
  have hq : 0 ≤ coefficientB*(Real.sqrt 3-1)/2 :=
    div_nonneg (mul_nonneg hB0 (sub_nonneg.mpr hr1)) (by norm_num)
  nlinarith [sq_nonneg (coefficientA-coefficientB*(Real.sqrt 3-1)/2)]

theorem citedV_matrix : citedV=((coefficientB : ℂ)/2) • W := by
  rw [citedV,coefficientA_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W,pauli] <;> ring

end MainTheory.CitedSingleQubitMatrices
