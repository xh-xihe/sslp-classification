import MainTheory.LocalUnitaryKL

set_option autoImplicit false

namespace MainTheory.DiagonalLocalKernel

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel

noncomputable def localMatrix {n : ℕ} (u : LocalPhase n) (j : Fin n) :
    Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,(u j : ℂ)]

theorem local_unitary {n : ℕ} (u : LocalPhase n) (j : Fin n) :
    IsOneQubitUnitary (localMatrix u j) := by
  constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [localMatrix,Matrix.mul_apply,Fin.sum_univ_two]
  · exact Unitary.coe_star_mul_self (u j)
  · exact Unitary.coe_mul_star_self (u j)

theorem tensor_diagonal {n : ℕ} (u : LocalPhase n) :
    tensorKernel (localMatrix u)=diagonalKernel u := by
  classical
  ext x y
  by_cases hxy : x=y
  · subst y
    simp only [tensorKernel,diagonalKernel,if_true,diagonalValue]
    apply Finset.prod_congr rfl
    intro j _
    cases x j <;> simp [localMatrix,bitIndex]
  · have hdiff : ∃ j,x j ≠ y j := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    obtain ⟨j,hj⟩ := hdiff
    rw [diagonalKernel,if_neg hxy]
    unfold tensorKernel
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hi : bitIndex (x j) ≠ bitIndex (y j) := fun h => hj (bitIndex_injective h)
    simp [localMatrix,hi]

theorem action {n : ℕ} (u : LocalPhase n) (f : SS.State n ℂ) :
    kernelAction (tensorKernel (localMatrix u)) f=diagonalAction u f := by
  rw [tensor_diagonal,kernelAction_diagonalKernel]

theorem commute {n : ℕ} (u v : LocalPhase n) (f : SS.State n ℂ) :
    diagonalAction u (diagonalAction v f)=diagonalAction v (diagonalAction u f) := by
  funext x
  simp only [diagonalAction]
  ring

theorem hasDistance {n K d : ℕ} (C : MainTheory.CodeSpec.ExactCode n K d) (u : LocalPhase n) :
    SS.HasDistance (fun i => diagonalAction u (C.frame.vec i)) d := by
  have h := MainTheory.LocalUnitaryKL.hasDistance_unitaryFrame C (localMatrix u) (local_unitary u)
  have he : (MainTheory.LocalUnitaryKL.unitaryFrame C.frame (tensorKernel (localMatrix u))
      (tensorKernel_unitary (localMatrix u) (local_unitary u)).1).vec=
      fun i => diagonalAction u (C.frame.vec i) := by
    funext i
    rw [MainTheory.LocalUnitaryKL.unitaryFrame_vec,action]
  rwa [he] at h

end MainTheory.DiagonalLocalKernel
