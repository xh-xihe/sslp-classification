import MainTheory.Orbit36Antiunitary
import MainTheory.PauliAntiunitaryTensor
import MainTheory.ConjugateStateExpectation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit36ExpectationSign

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.PauliTransferTwo MainTheory.PauliTensorTransfer MainTheory.PauliWordBridge
open MainTheory.PauliAntiunitaryTensor MainTheory.Orbit36Antiunitary

def firstFour (j : Fin 6) : Bool := decide (j.val < 4)
noncomputable def physicalKernel : OperatorKernel 6 := tensorKernel (fun j => localFactor (firstFour j))

theorem physicalKernel_eq : physicalKernel =
    MainTheory.PauliKernelTrace.pauliKernel zLastTwo * MainTheory.PauliKernelTrace.pauliKernel xAll := by
  have hlocal : (fun j => pauli (pauliWordEquiv zLastTwo j) * pauli (pauliWordEquiv xAll j)) =
      fun j => localFactor (firstFour j) := by
    funext j
    fin_cases j <;> simp [localFactor, firstFour, pauliWordEquiv, label, xAll, zLastTwo]
  rw [← wordKernel_pauliWordEquiv, ← wordKernel_pauliWordEquiv, wordKernel, wordKernel,
    ← tensorKernel_mul, hlocal]
  rfl

theorem theta_tensor (c : SS.State 6 ℂ) :
    theta c = physicalKernel.mulVec (fun x => star (c x)) := by
  rw [physical_action, physicalKernel_eq, ← Matrix.mulVec_mulVec]
  change SS.pauliAct zLastTwo (SS.pauliAct xAll (fun x => star (c x))) =
    kernelAction (MainTheory.PauliKernelTrace.pauliKernel zLastTwo)
      (kernelAction (MainTheory.PauliKernelTrace.pauliKernel xAll) (fun x => star (c x)))
  rw [MainTheory.PauliKernelTrace.kernelAction_pauliKernel,
    MainTheory.PauliKernelTrace.kernelAction_pauliKernel]

def firstZCount (P : SS.PauliString 6) : ℕ :=
  (Finset.univ.filter (fun j : Fin 6 => j.val < 4 ∧ P.x j = false ∧ P.z j = true)).card
def lastNontrivialCount (P : SS.PauliString 6) : ℕ :=
  (Finset.univ.filter (fun j : Fin 6 => 4 ≤ j.val ∧ (P.x j || P.z j) = true)).card
def epsilon (P : SS.PauliString 6) : ℂ := (-1) ^ (firstZCount P + lastNontrivialCount P)

theorem negative_count : ∀ P : SS.PauliString 6,
    (Finset.univ.filter (fun j => negative (firstFour j) (pauliWordEquiv P j))).card =
      firstZCount P + lastNontrivialCount P := by decide +kernel

theorem pauli_transform (P : SS.PauliString 6) :
    (star physicalKernel * MainTheory.PauliKernelTrace.pauliKernel P * physicalKernel).transpose =
      epsilon P • MainTheory.PauliKernelTrace.pauliKernel P := by
  have h := word_transform firstFour (pauliWordEquiv P)
  rw [wordKernel_pauliWordEquiv, sign_product, negative_count] at h
  exact h

theorem expectation_sign (P : SS.PauliString 6) (c : SS.State 6 ℂ) :
    SS.innerC (theta c) (SS.pauliAct P (theta c)) =
      epsilon P * SS.innerC c (SS.pauliAct P c) := by
  rw [theta_tensor, ← MainTheory.PauliKernelTrace.kernelAction_pauliKernel,
    ← MainTheory.PauliKernelTrace.kernelAction_pauliKernel]
  change SS.innerC (physicalKernel.mulVec (fun x => star (c x)))
      ((MainTheory.PauliKernelTrace.pauliKernel P).mulVec
        (physicalKernel.mulVec (fun x => star (c x)))) = _
  rw [MainTheory.ConjugateStateExpectation.transformed_expectation, pauli_transform,
    Matrix.smul_mulVec]
  simp only [SS.innerC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change star (c x) * (epsilon P * ((MainTheory.PauliKernelTrace.pauliKernel P).mulVec c x)) =
    epsilon P * (star (c x) * ((MainTheory.PauliKernelTrace.pauliKernel P).mulVec c x))
  ring

end MainTheory.Orbit36ExpectationSign
