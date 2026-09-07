import MainTheory.KLCodeBridge

/-! # Actual KL distance under arbitrary local unitary changes of basis -/

namespace MainTheory.LocalUnitaryKL

open CodeSpec ClassificationLevels PauliKernelBTrace PauliKernelTrace
open LocalTensorKernel KLTensorSupport PauliTensorTransfer PauliTransferTwo PauliWordBridge

noncomputable section

variable {n K d : ℕ}

def frameOfMatrix (V : Matrix (SS.BitString n) (Fin K) ℂ)
    (hV : V.conjTranspose * V = 1) : OrthonormalFrame n K where
  vec k x := V x k
  orthonormal k l := by
    simpa only [SS.innerC, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using congrFun (congrFun hV k) l

@[simp] theorem frameMatrix_frameOfMatrix (V : Matrix (SS.BitString n) (Fin K) ℂ)
    (hV : V.conjTranspose * V = 1) : frameMatrix (frameOfMatrix V hV) = V := rfl

def unitaryFrame (F : OrthonormalFrame n K) (T : OperatorKernel n)
    (hT : T.conjTranspose * T = 1) : OrthonormalFrame n K :=
  frameOfMatrix (T * frameMatrix F) (by
    calc
      _ = (frameMatrix F).conjTranspose * (T.conjTranspose * T) * frameMatrix F := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hT]; simpa using KLCodeBridge.frameMatrix_gram F)

@[simp] theorem frameMatrix_unitaryFrame (F : OrthonormalFrame n K) (T : OperatorKernel n)
    (hT : T.conjTranspose * T = 1) :
    frameMatrix (unitaryFrame F T hT) = T * frameMatrix F := rfl

@[simp] theorem unitaryFrame_vec (F : OrthonormalFrame n K) (T : OperatorKernel n)
    (hT : T.conjTranspose * T = 1) (k : Fin K) :
    (unitaryFrame F T hT).vec k = kernelAction T (F.vec k) := rfl

theorem conjugated_pauli_detected (C : ExactCode n K d)
    (U : Fin n → Mat2) (hU : ∀ j, IsOneQubitUnitary (U j))
    (P : SS.PauliString n) (hP : P.wt < d) :
    (tensorKernel U).conjTranspose * pauliKernel P * tensorKernel U ∈
      detectedOperators C.frame := by
  classical
  let p := pauliWordEquiv P
  let J : Finset (Fin n) := Finset.univ.filter (fun j => p j ≠ 0)
  have hJ : J.card < d := by
    change wordWeight p < d
    simpa only [p, wordWeight_pauliWordEquiv] using hP
  rw [← wordKernel_pauliWordEquiv P]
  change star (tensorKernel U) * tensorKernel (fun j => pauli (p j)) * tensorKernel U ∈ _
  rw [← tensorKernel_star, ← tensorKernel_mul, ← tensorKernel_mul]
  apply tensor_mem_detectedOperators C J hJ
  intro j hj
  have hp : p j = 0 := by simpa [J] using hj
  simpa only [hp, pauli_zero, Matrix.mul_one] using (hU j).1

/-- Every Pauli KL equation of the original target distance is transported
through the full tensor product of arbitrary `U(2)` matrices. -/
theorem hasDistance_unitaryFrame (C : ExactCode n K d)
    (U : Fin n → Mat2) (hU : ∀ j, IsOneQubitUnitary (U j)) :
    SS.HasDistance (unitaryFrame C.frame (tensorKernel U) (tensorKernel_unitary U hU).1).vec d := by
  intro P hP
  let C' : ExactCode n K (max d 1) := {
    positiveRank := C.positiveRank
    frame := C.frame
    hasDistance := by
      change SS.Detects C.frame.vec (max d 1 - 1)
      rw [show max d 1 - 1 = d - 1 by omega]
      exact C.hasDistance }
  obtain ⟨c, hc⟩ := conjugated_pauli_detected C' U hU P (by omega)
  have hdet : pauliKernel P ∈ detectedOperators
      (unitaryFrame C.frame (tensorKernel U) (tensorKernel_unitary U hU).1) := by
    refine ⟨c, ?_⟩
    simpa only [frameMatrix_unitaryFrame, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hc
  simpa only [kernelAction_pauliKernel] using (mem_detectedOperators_iff _ _).1 hdet

def unitaryCode (C : ExactCode n K d) (U : Fin n → Mat2)
    (hU : ∀ j, IsOneQubitUnitary (U j)) : ExactCode n K d where
  positiveRank := C.positiveRank
  frame := unitaryFrame C.frame (tensorKernel U) (tensorKernel_unitary U hU).1
  hasDistance := hasDistance_unitaryFrame C U hU

end

end MainTheory.LocalUnitaryKL
