import MainTheory.Orbit26PhysicalDependentAnchors
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26OrthogonalGram
open scoped BigOperators Matrix
open MainTheory.Orbit26DependentAnchors
open MainTheory.Orbit26 (M2)
noncomputable section
def perp (v : Vec) : Vec := ![-star (v 1),star (v 0)]

theorem perp_unit (v : Vec) (hv : nsq v=1) : nsq (perp v)=1 := by
  simpa [nsq,perp,Fin.sum_univ_two,add_comm] using hv

theorem perp_projector (v : Vec) (hv : nsq v=1) :
    projector (perp v)=1-projector v := by
  have hC : star (v 0)*v 0+star (v 1)*v 1=1 := by
    rw [SixQubit.star_mul_self,SixQubit.star_mul_self,← Complex.ofReal_add]
    simpa [nsq,Fin.sum_univ_two] using congrArg (fun x : ℝ => (x : ℂ)) hv
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [perp,projector,Matrix.vecMulVec_apply,Pi.star_apply,
    Matrix.sub_apply,Matrix.one_apply] at hC ⊢
  all_goals simp only [starRingEnd_apply] at hC ⊢
  all_goals first | (solve | ring) | linear_combination hC

theorem orthogonal_projector (v w : Vec) (hv : nsq v=1) (ho : star v ⬝ᵥ w=0) :
    projector w=(nsq w : ℂ) • (1-projector v) := by
  have hC : star (v 0)*v 0+star (v 1)*v 1=1 := by
    rw [SixQubit.star_mul_self,SixQubit.star_mul_self,← Complex.ofReal_add]
    simpa [nsq,Fin.sum_univ_two] using congrArg (fun x : ℝ => (x : ℂ)) hv
  have hoC : star (v 0)*w 0+star (v 1)*w 1=0 := by
    simpa [dotProduct,Fin.sum_univ_two] using ho
  let t : ℂ := v 0*w 1-v 1*w 0
  have hw : ∀ i,w i=t*perp v i := by
    intro i
    fin_cases i
    · change w 0=(v 0*w 1-v 1*w 0)*(-star (v 1))
      linear_combination v 0*hoC-w 0*hC
    · change w 1=(v 0*w 1-v 1*w 0)*star (v 0)
      linear_combination v 1*hoC-w 1*hC
  have hn : nsq w=Complex.normSq t := by
    simp only [nsq,hw,map_mul]
    rw [← Finset.mul_sum,show ∑ i,Complex.normSq (perp v i)=1 from perp_unit v hv,mul_one]
  rw [hn,← perp_projector v hv]
  ext i j
  simp only [projector,Matrix.vecMulVec_apply,Pi.star_apply,hw,star_mul',
    Matrix.smul_apply,smul_eq_mul]
  rw [← SixQubit.star_mul_self]
  ring

theorem gram_columns (A : M2) :
    A*Aᴴ=projector (col A 0)+projector (col A 1) := by
  ext i j
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two,
    Matrix.add_apply,projector,Matrix.vecMulVec_apply,col]

theorem orthogonal_gram (A : M2) (v : Vec) (hv : nsq v=1) (ho : row v A=0) :
    A*Aᴴ=((nsq (col A 0)+nsq (col A 1) : ℝ) : ℂ) • (1-projector v) := by
  have hc (j : Fin 2) : star v ⬝ᵥ col A j=0 := congrFun ho j
  rw [gram_columns,orthogonal_projector v (col A 0) hv (hc 0),
    orthogonal_projector v (col A 1) hv (hc 1),Complex.ofReal_add,add_smul]
end
end MainTheory.Orbit26OrthogonalGram
