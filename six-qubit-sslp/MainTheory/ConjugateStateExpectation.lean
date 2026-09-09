import MainTheory.ClassificationLevels

set_option autoImplicit false

namespace MainTheory.ConjugateStateExpectation

theorem inner_adjoint {n : ℕ} (A : MainTheory.ClassificationLevels.OperatorKernel n)
    (v w : SS.State n ℂ) : SS.innerC (A.mulVec v) w = SS.innerC v ((star A).mulVec w) := by
  simp only [SS.innerC, Matrix.mulVec, dotProduct, star_sum, star_mul',
    Matrix.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem conjugate_expectation {n : ℕ} (A : MainTheory.ClassificationLevels.OperatorKernel n)
    (v : SS.State n ℂ) : SS.innerC (fun i => star (v i)) (A.mulVec (fun i => star (v i))) =
      SS.innerC v (A.transpose.mulVec v) := by
  simp only [SS.innerC, Matrix.mulVec, dotProduct, star_star, Matrix.transpose_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem transformed_expectation {n : ℕ}
    (A U : MainTheory.ClassificationLevels.OperatorKernel n) (v : SS.State n ℂ) :
    SS.innerC (U.mulVec (fun i => star (v i))) (A.mulVec (U.mulVec (fun i => star (v i)))) =
      SS.innerC v ((star U * A * U).transpose.mulVec v) := by
  rw [inner_adjoint, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact conjugate_expectation _ _

end MainTheory.ConjugateStateExpectation
