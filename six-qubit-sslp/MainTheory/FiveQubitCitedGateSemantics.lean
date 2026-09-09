import MainTheory.FiveQubitCitedGateResidual
import MainTheory.FiveQubitPerfectCoordinates
import MainTheory.CitedSingleQubitMatrices

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.FiveQubitCitedGateSemantics

open SixQubit.Realize MainTheory.FiveQubitPerfectCore
open MainTheory.FiveQubitCitedGateResidual MainTheory.ExactZQFinite
open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel

theorem index_value (b : Bool) : MainTheory.FiveQubitCitedGateData.index b=bitIndex b := by
  cases b <;> rfl

theorem W_value (i j : Fin 2) : toC (MainTheory.FiveQubitCitedGateData.W i j)=
    MainTheory.CitedSingleQubitMatrices.W i j := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [MainTheory.FiveQubitCitedGateData.W,MainTheory.CitedSingleQubitMatrices.W,
      toC,toCre,toCim,rz,SS.rp,z8] <;> ring

theorem T_value (i j : Fin 2) : toC (MainTheory.FiveQubitCitedGateData.T i j)=
    MainTheory.CitedSingleQubitMatrices.T i j := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [MainTheory.FiveQubitCitedGateData.T,MainTheory.CitedSingleQubitMatrices.T,
      toC,toCre,toCim,rz,SS.rp,z8]

theorem D_value (i j : Fin 2) : toC (MainTheory.FiveQubitCitedGateData.D i j)=
    MainTheory.CitedSingleQubitMatrices.D i j := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [MainTheory.FiveQubitCitedGateData.D,MainTheory.CitedSingleQubitMatrices.D,
      toC,toCre,toCim,rz,SS.rp,z8,ZQ.zero]

noncomputable def constructed (i : Fin 2) : SS.State 5 ℂ := fun x =>
  ∑ b : Fin 2,MainTheory.CitedSingleQubitMatrices.citedV (bitIndex (x 4)) b *
    state i (Fin.snoc (fun j : Fin 4 => x j.castSucc) (decide (b=1)))

noncomputable def scale : ℂ := (MainTheory.CitedSingleQubitMatrices.coefficientB : ℂ)/8

theorem constructed_coordinate (i : Fin 2) (x : Fin 32) :
    constructed i (bits x)=scale*word i x := by
  have h := congrArg toC (MainTheory.FiveQubitCitedGateData.rawWord_checked i x)
  simp only [toC_sum,toC_mul,toC_intCast,W_value,index_value] at h
  change word i x = _ at h
  rw [h]
  simp only [constructed,MainTheory.CitedSingleQubitMatrices.citedV_matrix,
    Matrix.smul_apply,smul_eq_mul,state,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change _ = scale*(MainTheory.CitedSingleQubitMatrices.W (bitIndex (bits x 4)) b * _)
  unfold scale
  ring

noncomputable def factors : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ :=
  Fin.snoc (fun _ : Fin 4 => MainTheory.CitedSingleQubitMatrices.YHS)
    MainTheory.CitedSingleQubitMatrices.Zthird

theorem inverse_sqrt_two_fourth : (Real.sqrt 2 : ℂ)⁻¹^4=(1/4 : ℂ) := by
  have h : (Real.sqrt 2 : ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [inv_pow,show (Real.sqrt 2 : ℂ)^4=((Real.sqrt 2 : ℂ)^2)^2 by ring,h]
  norm_num

theorem gate_coordinate (x y : Fin 32) :
    tensorKernel factors (bits x) (bits y)=(1/8 : ℂ)*gate x y := by
  simp only [tensorKernel,factors]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,
    MainTheory.CitedSingleQubitMatrices.yhs_matrix,MainTheory.CitedSingleQubitMatrices.zthird_matrix,
    Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,inverse_sqrt_two_fourth]
  simp only [gate,MainTheory.FiveQubitCitedGateData.kernel,toC_mul,toC_prod,T_value,D_value,index_value]
  change _ = (1/8 : ℂ)*((∏ j : Fin 4,
    MainTheory.CitedSingleQubitMatrices.T (bitIndex (bits x j.castSucc))
      (bitIndex (bits y j.castSucc)))*
    MainTheory.CitedSingleQubitMatrices.D (bitIndex (bits x 4)) (bitIndex (bits y 4)))
  simp only [show Fin.last 4=(4 : Fin 5) by rfl]
  ring

theorem action_coordinate (i : Fin 2) (x : Fin 32) :
    (tensorKernel factors).mulVec (constructed i) (bits x)=(scale/8)*image i x := by
  simp only [Matrix.mulVec,dotProduct]
  rw [sum_bits]
  simp_rw [gate_coordinate,constructed_coordinate]
  have h := congrFun (actual_image i) x
  change (∑ y,gate x y*word i y)=image i x at h
  rw [← h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem scale_ne_zero : scale ≠ 0 := by
  have hp : 0 < MainTheory.CitedSingleQubitMatrices.coefficientB := by
    unfold MainTheory.CitedSingleQubitMatrices.coefficientB
    positivity
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hp)) (by norm_num)

theorem cited_gate_does_not_preserve : ¬ ∃ a : Fin 2 → ℂ,
    (tensorKernel factors).mulVec (constructed 0)=fun x => ∑ j,a j*constructed j x := by
  rintro ⟨a,ha⟩
  apply image_not_in_span
  refine ⟨fun j => 8*a j, ?_⟩
  rw [actual_image]
  ext x
  have h := congrFun ha (bits x)
  rw [action_coordinate] at h
  simp_rw [constructed_coordinate] at h
  have hs : scale*(image 0 x-∑ j,8*a j*word j x)=0 := by
    simp only [Fin.sum_univ_two] at h ⊢
    linear_combination 8*h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left scale_ne_zero)

end MainTheory.FiveQubitCitedGateSemantics
