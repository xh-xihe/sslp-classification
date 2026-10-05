import MainTheory.Orbit2TrigonometricSplit
import MainTheory.Generated.OrbitTableNumeric

/-! Literal q=2 records and both split-qubit isometries printed in the SI. -/

namespace MainTheory.PrimitiveSplitDisplays
open scoped BigOperators Matrix
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def records : Fin 4 → Fin 6 → ℕ :=
  ![![0,0,0,1,1,1],![0,0,1,1,1,1],![0,1,1,1,1,1],![1,1,1,1,1,1]]
def activeWeight (a : Fin 6 → ℕ) : ℕ := ∑ j,if a j=0 then 0 else 1

theorem records_checked : ∀ r : Fin 4,
    MainTheory.Generated.OrbitTableNumericData.paperQ ⟨r.val,by omega⟩=2 ∧
    MainTheory.Generated.OrbitTableNumericData.paperM ⟨r.val,by omega⟩=2 ∧
    MainTheory.Generated.OrbitTableNumericData.paperAngle ⟨r.val,by omega⟩=records r ∧
    activeWeight (records r)=r.val+3 := by decide +kernel

def W3 (θ : ℝ) : Matrix (Fin 4) (Fin 2) ℂ :=
  ![![(Real.cos (θ/2) : ℂ),0],![(Real.sin (θ/2) : ℂ),0],
    ![0,(Real.cos (θ/2) : ℂ)],![0,-(Real.sin (θ/2) : ℂ)]]
def IZ : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1,-1,1,-1]
def ZX : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,1,0,0],![1,0,0,0],![0,0,0,-1],![0,0,-1,0]]

theorem W2_columns (θ : ℝ) : MainTheory.Orbit2TrigonometricSplit.W θ=
    ![![(Real.cos (θ/2) : ℂ),0],![0,(Real.cos (θ/2) : ℂ)],
      ![0,(Real.sin (θ/2) : ℂ)],![(Real.sin (θ/2) : ℂ),0]] := rfl

theorem W3_isometry (θ : ℝ) : (W3 θ).conjTranspose*W3 θ=1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext
  all_goals norm_num [W3,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.one_apply,Fin.sum_univ_succ,Fin.succ,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.star_def,Complex.ofReal_re,
    Complex.ofReal_im,-Complex.ofReal_cos,-Complex.ofReal_sin]
  all_goals nlinarith [MainTheory.Orbit2TrigonometricSplit.half_norm θ]

theorem W3_logical (θ : ℝ) : Orbit2.ziFour*W3 θ=W3 θ*Orbit2.zTwo := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [W3,Orbit2.ziFour,Orbit2.zTwo,Matrix.mul_apply,
    Matrix.diagonal,Fin.sum_univ_succ,Fin.succ]

theorem W3_projection (θ : ℝ) : W3 θ*(W3 θ).conjTranspose=
    (1/2 : ℂ) • (1+(Real.cos θ : ℂ) • IZ+(Real.sin θ : ℂ) • ZX) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext
  all_goals norm_num [W3,IZ,ZX,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.diagonal,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,
    Fin.sum_univ_succ,Fin.succ,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.star_def,Complex.ofReal_re,
    Complex.ofReal_im,-Complex.ofReal_cos,-Complex.ofReal_sin]
  all_goals nlinarith [MainTheory.Orbit2TrigonometricSplit.half_norm θ,
    MainTheory.Orbit2TrigonometricSplit.cos_difference θ,
    MainTheory.Orbit2TrigonometricSplit.sin_product θ]

end
end MainTheory.PrimitiveSplitDisplays
