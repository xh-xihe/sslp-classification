import MainTheory.FiniteKrausChannel

/-! # Ancilla identity and trace preservation of Kraus amplification -/

namespace MainTheory.FiniteKrausChannel

open scoped Kronecker

noncomputable section

set_option linter.unusedSectionVars false

variable {I H G A : Type*} [Fintype I] [Fintype H] [Fintype G] [Fintype A]
  [DecidableEq H] [DecidableEq A]

theorem action_amplify_tensor (E : I → Matrix G H ℂ)
    (X : Matrix H H ℂ) (Y : Matrix A A ℂ) :
    action (amplify E A) (X ⊗ₖ Y) = action E X ⊗ₖ Y := by
  simp only [action, amplify, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext ga gb
  simp [Matrix.kroneckerMap, Matrix.sum_apply, Finset.sum_mul]

theorem amplify_tracePreserving (E : I → Matrix G H ℂ) (hE : TracePreserving E) :
    TracePreserving (amplify E A) := by
  unfold TracePreserving
  simp only [amplify, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  calc
    (∑ i, ((E i).conjTranspose * E i) ⊗ₖ (1 : Matrix A A ℂ)) =
        (∑ i, (E i).conjTranspose * E i) ⊗ₖ (1 : Matrix A A ℂ) := by
      ext ha hb
      simp [Matrix.kroneckerMap, Matrix.sum_apply, Finset.sum_mul]
    _ = 1 := by rw [hE, Matrix.one_kronecker_one]

end

end MainTheory.FiniteKrausChannel
