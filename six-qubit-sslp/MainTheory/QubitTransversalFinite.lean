import MainTheory.TransversalLogicalOrder

/-! # The arbitrary-subsystem transversal theorem specializes to actual qubit KL codes -/

namespace MainTheory.QubitTransversalFinite

open CodeSpec ClassificationLevels PauliKernelBTrace KLTensorSupport

noncomputable section

variable {n K d : ℕ}

@[simp] theorem finTwoEquiv_bitIndex (b : Bool) : finTwoEquiv (bitIndex b) = b := by
  cases b <;> rfl

theorem bool_tensor_eq (U : Fin n → Matrix Bool Bool ℂ) :
    FiniteTensorKernel.tensor U =
      LocalTensorKernel.tensorKernel (fun j a b => U j (finTwoEquiv a) (finTwoEquiv b)) := by
  ext x y
  simp [FiniteTensorKernel.tensor, LocalTensorKernel.tensorKernel]

theorem detectsLocal_of_hasDistance (C : ExactCode n K d) (hd : 2 ≤ d) :
    FiniteTensorDetection.DetectsLocal (A := fun _ : Fin n => Bool) (frameMatrix C.frame) := by
  classical
  intro j M
  have hdet : FiniteTensorKernel.localKernel j M ∈ detectedOperators C.frame := by
    rw [FiniteTensorKernel.localKernel, bool_tensor_eq]
    apply tensor_mem_detectedOperators C {j} (by simp; omega)
    intro k hk
    have hkj : k ≠ j := by simpa using hk
    ext a b
    simp [Function.update_of_ne hkj, Matrix.one_apply, finTwoEquiv.injective.eq_iff]
  exact hdet

theorem finite_projective_transversal_image (C : ExactCode n K d) (hd : 2 ≤ d) :
    Finite ((TransversalLogicalOrder.transversalLogicalGroup (A := fun _ : Fin n => Bool)
      (frameMatrix C.frame)).map UnitaryAdjointRepresentation.adjoint) :=
  TransversalLogicalOrder.finite_projective_transversal_image (frameMatrix C.frame)
    (KLCodeBridge.frameMatrix_gram C.frame) C.positiveRank (detectsLocal_of_hasDistance C hd)

end

end MainTheory.QubitTransversalFinite
