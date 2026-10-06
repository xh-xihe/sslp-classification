import MainTheory.Orbit33PrintedReflection

/-! Complex scalar form of the actual six-block character reflection.
Only the stated linear identities are used; no no-code conclusion is invoked.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit33ScalarReflection
open scoped BigOperators Matrix
noncomputable section

def C : Matrix (Fin 6) (Fin 6) ℂ := ![![1,1,1,1,1,1],![1,1,-1,-1,-1,-1],![1,-1,1,-1,-1,-1],![1,-1,-1,1,1,-1],![1,-1,-1,1,-1,1],![1,-1,-1,-1,1,1]]
def inverseC : Matrix (Fin 6) (Fin 6) ℂ := ![![3/10,1/5,1/5,1/10,1/10,1/10],![1/5,3/10,-1/5,-1/10,-1/10,-1/10],![1/5,-1/5,3/10,-1/10,-1/10,-1/10],![1/10,-1/10,-1/10,1/5,1/5,-3/10],![1/10,-1/10,-1/10,1/5,-3/10,1/5],![1/10,-1/10,-1/10,-3/10,1/5,1/5]]
def J : Matrix (Fin 6) (Fin 6) ℂ := Matrix.diagonal ![1,-1,-1,-1,-1,-1]
def R : Fin 6 → ℂ := ![3/10,1/5,1/5,1/10,1/10,1/10]

theorem inverse_left : inverseC*C=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C,inverseC,Matrix.mul_apply,Fin.sum_univ_succ,Fin.succ]

theorem reflection_entries : inverseC*J*C=fun i j => 2*R i-(if i=j then 1 else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C,inverseC,J,R,Matrix.mul_apply,Fin.sum_univ_succ,Fin.succ]

theorem inverse : C⁻¹=inverseC := Matrix.inv_eq_left_inv inverse_left

theorem C_cast : C=fun i j => (MainTheory.Orbit33PrintedReflection.C i j : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C,MainTheory.Orbit33PrintedReflection.C]

theorem character_rows (f g : Fin 6 → ℂ)
    (h : ∀ i, f i+g i=2*R i*(∑ j, f j)) : C.mulVec f=J.mulVec (C.mulVec g) := by
  have h0 := h ⟨0,by decide⟩
  have h1 := h ⟨1,by decide⟩
  have h2 := h ⟨2,by decide⟩
  have h3 := h ⟨3,by decide⟩
  have h4 := h ⟨4,by decide⟩
  have h5 := h ⟨5,by decide⟩
  norm_num [R,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3 h4 h5
  funext i
  fin_cases i
  · norm_num [C,J,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Fin.succ]
    linear_combination (-1 : ℂ) * h0 + (-1 : ℂ) * h1 + (-1 : ℂ) * h2 + (-1 : ℂ) * h3 + (-1 : ℂ) * h4 + (-1 : ℂ) * h5
  · norm_num [C,J,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Fin.succ]
    linear_combination (1 : ℂ) * h0 + (1 : ℂ) * h1 + (-1 : ℂ) * h2 + (-1 : ℂ) * h3 + (-1 : ℂ) * h4 + (-1 : ℂ) * h5
  · norm_num [C,J,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Fin.succ]
    linear_combination (1 : ℂ) * h0 + (-1 : ℂ) * h1 + (1 : ℂ) * h2 + (-1 : ℂ) * h3 + (-1 : ℂ) * h4 + (-1 : ℂ) * h5
  · norm_num [C,J,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Fin.succ]
    linear_combination (1 : ℂ) * h0 + (-1 : ℂ) * h1 + (-1 : ℂ) * h2 + (1 : ℂ) * h3 + (1 : ℂ) * h4 + (-1 : ℂ) * h5
  · norm_num [C,J,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Fin.succ]
    linear_combination (1 : ℂ) * h0 + (-1 : ℂ) * h1 + (-1 : ℂ) * h2 + (1 : ℂ) * h3 + (-1 : ℂ) * h4 + (1 : ℂ) * h5
  · norm_num [C,J,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,Fin.succ]
    linear_combination (1 : ℂ) * h0 + (-1 : ℂ) * h1 + (-1 : ℂ) * h2 + (-1 : ℂ) * h3 + (1 : ℂ) * h4 + (1 : ℂ) * h5

theorem inverse_character_rows (f g : Fin 6 → ℂ)
    (h : ∀ i, f i+g i=2*R i*(∑ j, f j)) :
    f=inverseC.mulVec (J.mulVec (C.mulVec g)) := by
  rw [← character_rows f g h,Matrix.mulVec_mulVec,inverse_left,Matrix.one_mulVec]

theorem common_sum (f g : Fin 6 → ℂ)
    (h : ∀ i, f i+g i=2*R i*(∑ j, f j)) : (∑ j, f j)=(∑ j, g j) := by
  have h0 := h ⟨0,by decide⟩
  have h1 := h ⟨1,by decide⟩
  have h2 := h ⟨2,by decide⟩
  have h3 := h ⟨3,by decide⟩
  have h4 := h ⟨4,by decide⟩
  have h5 := h ⟨5,by decide⟩
  norm_num [R,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination -(h0+h1+h2+h3+h4+h5)

end
end MainTheory.Orbit33ScalarReflection
