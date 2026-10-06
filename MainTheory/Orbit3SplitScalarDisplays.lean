import MainTheory.ArbitrarySplitSixQubit
import MainTheory.Orbit3PrintedSplitMatrices
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit3SplitScalarDisplays
open scoped BigOperators Matrix
open Orbit2.TensorPauli MainTheory.ArbitrarySplitPerfectCode MainTheory.ArbitrarySplitSixQubit
noncomputable section

def pair (a b : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := pairOperator ![a,b,0,0,0,0]

theorem gram (a b : Fin 4) :
    Matrix.trace (pair a b)=(if a=0 ∧ b=0 then 4 else 0) ∧
    Matrix.trace (MainTheory.Orbit3PrintedSplitMatrices.ZI*pair a b)=
      (if a=3 ∧ b=0 then 4 else 0) ∧
    Matrix.trace (MainTheory.Orbit3PrintedSplitMatrices.XZ*pair a b)=
      (if a=1 ∧ b=3 then 4 else 0) := by
  fin_cases a <;> fin_cases b
  all_goals norm_num [pair,pairOperator,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    MainTheory.Orbit3PrintedSplitMatrices.ZI,MainTheory.Orbit3PrintedSplitMatrices.XZ,
    Matrix.diagonal,localC,localG,GaussianInt.toComplex_def,Fin.sum_univ_succ,Fin.succ]
  all_goals decide +kernel

theorem pair_only (p : Label 6) : pairOperator p=pair (p 0) (p 1) := rfl

theorem pair_scalar (θ : ℝ) (p : Label 6) :
    (1/2 : ℂ)*Matrix.trace
      ((MainTheory.Orbit3PrintedSplitMatrices.W θ).conjTranspose*pairOperator p*
        MainTheory.Orbit3PrintedSplitMatrices.W θ)=
      (if p 0=0 ∧ p 1=0 then 1 else 0)+
      (if p 0=3 ∧ p 1=0 then (Real.cos θ : ℂ) else 0)+
      (if p 0=1 ∧ p 1=3 then (Real.sin θ : ℂ) else 0) := by
  rw [split_trace,MainTheory.Orbit3PrintedSplitMatrices.projection,pair_only]
  simp only [Matrix.smul_mul,Matrix.add_mul,Matrix.one_mul,Matrix.trace_smul,
    Matrix.trace_add,smul_eq_mul]
  rw [(gram (p 0) (p 1)).1,(gram (p 0) (p 1)).2.1,(gram (p 0) (p 1)).2.2]
  split_ifs <;> ring

theorem physical_scalar (θ : ℝ) (p : Label 6) :
    scalar (MainTheory.Orbit3PrintedSplitMatrices.W θ) p=
      if tailLabel p=(fun _ => 0) then
        (if p 0=0 ∧ p 1=0 then 1 else 0)+
        (if p 0=3 ∧ p 1=0 then (Real.cos θ : ℂ) else 0)+
        (if p 0=1 ∧ p 1=3 then (Real.sin θ : ℂ) else 0)
      else 0 := by
  unfold scalar
  rw [pair_scalar]

end
end MainTheory.Orbit3SplitScalarDisplays
