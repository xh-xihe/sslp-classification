import MainTheory.PauliKernelBTrace
import MainTheory.PairPartialTrace
import MainTheory.PauliWordBridge

set_option autoImplicit false

namespace MainTheory.MixedFamilyTrace

open MainTheory.PairPartialTrace MainTheory.ClassificationLevels

noncomputable def columns (psi : Fin 2 → SS.State 6 ℂ) :
    Matrix (SS.BitString 6) (Fin 2) ℂ := fun x i => psi i x

theorem family_factor (psi : Fin 2 → SS.State 6 ℂ) :
    familyKernel psi=columns psi*(columns psi).conjTranspose := by
  ext x y
  rfl

theorem compressed (psi phi : Fin 2 → SS.State 6 ℂ) (M : OperatorKernel 6) (i j : Fin 2) :
    ((columns psi).conjTranspose*M*columns phi) i j=
      SS.innerC (psi i) (kernelAction M (phi j)) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,columns,SS.innerC,kernelAction,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem trace_identity (psi phi : Fin 2 → SS.State 6 ℂ) (M : OperatorKernel 6) :
    Matrix.trace (M*familyKernel phi*M.conjTranspose*familyKernel psi)=
      ((∑ i,∑ j,Complex.normSq (SS.innerC (psi i) (kernelAction M (phi j))) : ℝ) : ℂ) := by
  let V := columns psi
  let W := columns phi
  let A := V.conjTranspose*M*W
  have ht : Matrix.trace (M*familyKernel phi*M.conjTranspose*familyKernel psi)=
      Matrix.trace (A*A.conjTranspose) := by
    rw [family_factor,family_factor]
    change Matrix.trace (M*(W*W.conjTranspose)*M.conjTranspose*(V*V.conjTranspose))=_
    calc
      _ = Matrix.trace ((M*W*W.conjTranspose*M.conjTranspose*V)*V.conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (V.conjTranspose*(M*W*W.conjTranspose*M.conjTranspose*V)) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [A,Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [ht,MainTheory.PauliKernelBTrace.trace_mul_conjTranspose]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show A i j=SS.innerC (psi i) (kernelAction M (phi j)) from compressed psi phi M i j]

theorem pauli_self_adjoint (P : SS.PauliString 6) :
    (MainTheory.PauliKernelTrace.pauliKernel P).conjTranspose=
      MainTheory.PauliKernelTrace.pauliKernel P := by
  rw [← MainTheory.PauliWordBridge.wordKernel_pauliWordEquiv]
  change star (MainTheory.LocalTensorKernel.tensorKernel
    (fun j => MainTheory.PauliTransferTwo.pauli (MainTheory.PauliWordBridge.pauliWordEquiv P j)))=_
  rw [← MainTheory.LocalTensorKernel.tensorKernel_star]
  simp only [MainTheory.PauliTransferTwo.pauli_star]
  rfl

theorem pauli_trace (psi phi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) :
    Matrix.trace (familyKernel psi*MainTheory.PauliKernelTrace.pauliKernel P*
      familyKernel phi*MainTheory.PauliKernelTrace.pauliKernel P)=
      ((∑ i,∑ j,Complex.normSq (SS.innerC (psi i) (SS.pauliAct P (phi j))) : ℝ) : ℂ) := by
  have h := trace_identity psi phi (MainTheory.PauliKernelTrace.pauliKernel P)
  rw [pauli_self_adjoint] at h
  simp only [MainTheory.PauliKernelTrace.kernelAction_pauliKernel] at h
  rw [Matrix.trace_mul_comm] at h
  simpa only [Matrix.mul_assoc] using h

end MainTheory.MixedFamilyTrace
