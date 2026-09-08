import MainTheory.KLTensorSupport
import MainTheory.KLCodeBridge

/-!
# `eq:KL`, the distance form of the Knill--Laflamme equations

The manuscript writes the detection hypothesis as

  `P E P = lambda_E P`   for every Pauli `E` of weight below `d`,

with `P` the code projector.

In this repository the *frame* form is the definition: `SS.KLCondition psi E`
is `<psi_j, E psi_k> = c delta_jk`, and `SS.HasDistance` quantifies it over
Paulis of weight below `d`.  The projector form was reachable but never
assembled: `KLCodeBridge.projector_compression_iff` converts between the two,
but it is stated for an arbitrary operator kernel `M` and nothing instantiated
it at a Pauli; `KLTensorSupport.pauli_mem_detectedOperators` is that instance
and was used only inside the tensor-support argument.

Composing them is the display.  The tensor version is recorded alongside,
since it is the form the Eastin--Knill argument consumes: any operator
supported on fewer than `d` sites, Pauli or not, compresses to a scalar.
-/

namespace MainTheory.ProjectorCompression

open MainTheory
open MainTheory.ClassificationLevels

variable {n K d : ℕ}

/-- **`eq:KL`.**  For an exact `((n,K,d))` code and every Pauli of weight below
`d`, the compression of that Pauli to the code is a scalar multiple of the
projector. -/
theorem pauli_compression (C : CodeSpec.ExactCode n K d)
    (E : SS.PauliString n) (hE : E.wt < d) :
    ∃ lam : ℂ,
      (CodeProjector.ofFrame C.frame).kernel * PauliKernelTrace.pauliKernel E
          * (CodeProjector.ofFrame C.frame).kernel
        = lam • (CodeProjector.ofFrame C.frame).kernel := by
  obtain ⟨lam, hlam⟩ := KLTensorSupport.pauli_mem_detectedOperators C E hE
  exact ⟨lam, (KLCodeBridge.projector_compression_iff C.frame _ lam).2 hlam⟩

/-- The same for any operator supported on fewer than `d` sites, whose factors
need not be Pauli matrices. -/
theorem tensor_compression (C : CodeSpec.ExactCode n K d)
    (J : Finset (Fin n)) (hJ : J.card < d) (U : Fin n → PauliTransferTwo.Mat2)
    (hout : ∀ j, j ∉ J → U j = 1) :
    ∃ lam : ℂ,
      (CodeProjector.ofFrame C.frame).kernel * LocalTensorKernel.tensorKernel U
          * (CodeProjector.ofFrame C.frame).kernel
        = lam • (CodeProjector.ofFrame C.frame).kernel := by
  obtain ⟨lam, hlam⟩ := KLTensorSupport.tensor_mem_detectedOperators C J hJ U hout
  exact ⟨lam, (KLCodeBridge.projector_compression_iff C.frame _ lam).2 hlam⟩

end MainTheory.ProjectorCompression
