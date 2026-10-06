import MainTheory.PauliWordBridge

/-! # Actual Hermitian Pauli expectations are real

This connects squared real correlation coefficients with complex squared
norms in the amplitude and enumerator layers.
-/

namespace MainTheory.PauliExpectationReal

open MainTheory.PauliWordBridge MainTheory.PauliTensorTransfer
open MainTheory.LocalTensorKernel MainTheory.PauliTransferTwo MainTheory.PauliKernelTrace

noncomputable section
variable {n : ℕ}

theorem kernel_hermitian (P : SS.PauliString n) : (pauliKernel P).IsHermitian := by
  rw [← wordKernel_pauliWordEquiv P]
  change star (tensorKernel (fun j => pauli (pauliWordEquiv P j))) = _
  rw [← tensorKernel_star]
  simp only [pauli_star]
  rfl

theorem expectation_im_zero (w : SS.State n ℂ) (P : SS.PauliString n) :
    (SS.innerC w (SS.pauliAct P w)).im = 0 := by
  have h := (kernel_hermitian P).im_star_dotProduct_mulVec_self w
  change (SS.innerC w (MainTheory.ClassificationLevels.kernelAction (pauliKernel P) w)).im = 0 at h
  rw [kernelAction_pauliKernel] at h
  exact h

theorem normSq_eq_square (w : SS.State n ℂ) (P : SS.PauliString n) :
    Complex.normSq (SS.innerC w (SS.pauliAct P w)) =
      (SS.innerC w (SS.pauliAct P w)).re ^ 2 := by
  rw [Complex.normSq_apply, expectation_im_zero]
  ring

end
end MainTheory.PauliExpectationReal
