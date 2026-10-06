import MainTheory.PrimitiveSplitDisplays

/-! The split matrix in the orbit-three attainment subsection, whose output
site order is the reverse of the W3 convention used in the family subsection. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit3PrintedSplitMatrices
open scoped BigOperators Matrix
noncomputable section

def a (θ : ℝ) : ℝ := Real.cos (θ/2)
def b (θ : ℝ) : ℝ := Real.sin (θ/2)
def W (θ : ℝ) : Matrix (Fin 4) (Fin 2) ℂ :=
  ![![(a θ : ℂ),0],![0,(a θ : ℂ)],![(b θ : ℂ),0],![0,-(b θ : ℂ)]]
def ZI : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1,1,-1,-1]
def IZ : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1,-1,1,-1]
def XZ : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,0,1,0],![0,0,0,-1],![1,0,0,0],![0,-1,0,0]]
def outputSwap : Fin 4 → Fin 4 := ![0,2,1,3]

theorem columns (θ : ℝ) : W θ=
    ![![(Real.cos (θ/2) : ℂ),0],![0,(Real.cos (θ/2) : ℂ)],
      ![(Real.sin (θ/2) : ℂ),0],![0,-(Real.sin (θ/2) : ℂ)]] := rfl
theorem output_order (θ : ℝ) : W θ=(MainTheory.PrimitiveSplitDisplays.W3 θ).submatrix outputSwap id := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem isometry (θ : ℝ) : (W θ).conjTranspose*W θ=1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext
  all_goals norm_num [W,a,b,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.one_apply,Fin.sum_univ_succ,Fin.succ,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.star_def,Complex.ofReal_re,
    Complex.ofReal_im,-Complex.ofReal_cos,-Complex.ofReal_sin]
  all_goals nlinarith [MainTheory.Orbit2TrigonometricSplit.half_norm θ]

theorem logical (θ : ℝ) : IZ*W θ=W θ*Orbit2.zTwo := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [W,a,b,IZ,Orbit2.zTwo,Matrix.mul_apply,Matrix.diagonal,
    Fin.sum_univ_succ,Fin.succ]

theorem projection (θ : ℝ) : W θ*(W θ).conjTranspose=
    (1/2 : ℂ) • (1+(Real.cos θ : ℂ) • ZI+(Real.sin θ : ℂ) • XZ) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext
  all_goals norm_num [W,a,b,ZI,XZ,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.diagonal,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,
    Fin.sum_univ_succ,Fin.succ,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.star_def,Complex.ofReal_re,
    Complex.ofReal_im,-Complex.ofReal_cos,-Complex.ofReal_sin]
  all_goals nlinarith [MainTheory.Orbit2TrigonometricSplit.half_norm θ,
    MainTheory.Orbit2TrigonometricSplit.cos_difference θ,
    MainTheory.Orbit2TrigonometricSplit.sin_product θ]

theorem trace_identity (W : Matrix (Fin 4) (Fin 2) ℂ) (E : Matrix (Fin 4) (Fin 4) ℂ) :
    (1/2 : ℂ)*Matrix.trace (W.conjTranspose*E*W)=
      (1/2 : ℂ)*Matrix.trace (E*(W*W.conjTranspose)) := by
  rw [Matrix.trace_mul_cycle,Matrix.trace_mul_comm]

end
end MainTheory.Orbit3PrintedSplitMatrices
