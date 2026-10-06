import MainTheory.FiveQubitCitedGateSemantics
import MainTheory.FiveQubitCorrectedGateData

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.FiveQubitCorrectedGateSemantics

open SixQubit.Realize MainTheory.FiveQubitPerfectCore MainTheory.ExactZQFinite
open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.FiveQubitCitedGateSemantics

theorem T_value (i j : Fin 2) :
    toC (MainTheory.FiveQubitCorrectedGateData.Tcorrected i j)=
      MainTheory.CitedSingleQubitMatrices.Tadj i j := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [MainTheory.FiveQubitCorrectedGateData.Tcorrected,
      MainTheory.CitedSingleQubitMatrices.Tadj,toC,toCre,toCim,rz,SS.rp,z8]

noncomputable def factors : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  Fin.snoc (fun _ : Fin 4 => MainTheory.CitedSingleQubitMatrices.YHSadj)
    MainTheory.CitedSingleQubitMatrices.Zthird

noncomputable def logical : Matrix (Fin 2) (Fin 2) ℂ := fun j i =>
  toC (MainTheory.FiveQubitCorrectedGateData.logical j i)/8

theorem gate_coordinate (x y : Fin 32) :
    tensorKernel factors (bits x) (bits y)=
      (1/8 : ℂ)*toC (MainTheory.FiveQubitCorrectedGateData.correctedKernel x y) := by
  simp only [tensorKernel,factors]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,
    MainTheory.CitedSingleQubitMatrices.yhsadj_matrix,
    MainTheory.CitedSingleQubitMatrices.zthird_matrix,
    Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,inverse_sqrt_two_fourth]
  simp only [MainTheory.FiveQubitCorrectedGateData.correctedKernel,
    toC_mul,toC_prod,T_value,D_value,index_value]
  change _ = (1/8 : ℂ)*((∏ j : Fin 4,
    MainTheory.CitedSingleQubitMatrices.Tadj (bitIndex (bits x j.castSucc))
      (bitIndex (bits y j.castSucc)))*
    MainTheory.CitedSingleQubitMatrices.D (bitIndex (bits x 4)) (bitIndex (bits y 4)))
  simp only [show Fin.last 4=(4 : Fin 5) by rfl]
  ring

theorem action (i : Fin 2) :
    (tensorKernel factors).mulVec (constructed i)=fun x => ∑ j,logical j i*constructed j x := by
  funext x
  obtain ⟨x,rfl⟩ := bitsEquiv.surjective x
  simp only [bitsEquiv_apply]
  simp only [Matrix.mulVec,dotProduct]
  rw [sum_bits]
  simp_rw [gate_coordinate,constructed_coordinate]
  have h := congrArg toC (MainTheory.FiveQubitCorrectedGateData.corrected_checked i x)
  simp only [toC_sum,toC_mul] at h
  change (∑ y,toC (MainTheory.FiveQubitCorrectedGateData.correctedKernel x y)*
    MainTheory.FiveQubitCitedGateResidual.word i y)=
    ∑ j,toC (MainTheory.FiveQubitCorrectedGateData.logical j i)*
      MainTheory.FiveQubitCitedGateResidual.word j x at h
  calc
    _ = (scale/8)*(∑ y,toC (MainTheory.FiveQubitCorrectedGateData.correctedKernel x y)*
        MainTheory.FiveQubitCitedGateResidual.word i y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      rw [h,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [logical]
      ring

end MainTheory.FiveQubitCorrectedGateSemantics
