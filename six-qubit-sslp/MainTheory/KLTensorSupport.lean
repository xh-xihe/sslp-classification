import MainTheory.PauliWordBridge
import MainTheory.PauliKernelBTrace

/-! # Pauli KL detection extends to every operator on a small subsystem -/

namespace MainTheory.KLTensorSupport

open ClassificationLevels PauliKernelBTrace PauliTensorTransfer PauliWordBridge PauliTransferTwo
open LocalTensorKernel

noncomputable section

variable {n K d : ℕ}

/-- Operators whose compression to the actual logical frame is scalar. -/
def detectedOperators (F : CodeSpec.OrthonormalFrame n K) : Submodule ℂ (OperatorKernel n) where
  carrier := {M | ∃ c : ℂ, (frameMatrix F).conjTranspose * M * frameMatrix F = c • 1}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [Matrix.mul_add, Matrix.add_mul, ha, hb, add_smul]⟩
  smul_mem' := by
    rintro c A ⟨a, ha⟩
    exact ⟨c * a, by rw [Matrix.mul_smul, Matrix.smul_mul, ha, smul_smul]⟩

theorem mem_detectedOperators_iff (F : CodeSpec.OrthonormalFrame n K) (M : OperatorKernel n) :
    M ∈ detectedOperators F ↔
      ∃ c : ℂ, ∀ k l, SS.innerC (F.vec k) (kernelAction M (F.vec l)) = if k = l then c else 0 := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun k l => by
      have h := congrFun (congrFun hc k) l
      simpa [compressed_entry, Matrix.smul_apply, Matrix.one_apply] using h⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext k l
    simpa [compressed_entry, Matrix.smul_apply, Matrix.one_apply] using hc k l

theorem pauli_mem_detectedOperators (C : CodeSpec.ExactCode n K d)
    (P : SS.PauliString n) (hP : P.wt < d) : PauliKernelTrace.pauliKernel P ∈ detectedOperators C.frame := by
  apply (mem_detectedOperators_iff C.frame _).2
  simpa only [PauliKernelTrace.kernelAction_pauliKernel] using C.hasDistance P (by omega)

/-- Any tensor operator supported on fewer than `d` sites is detected, even
when its factors are arbitrary complex matrices rather than Pauli matrices. -/
theorem tensor_mem_detectedOperators (C : CodeSpec.ExactCode n K d)
    (J : Finset (Fin n)) (hJ : J.card < d) (U : Fin n → Mat2)
    (hout : ∀ j, j ∉ J → U j = 1) : tensorKernel U ∈ detectedOperators C.frame := by
  classical
  rw [tensor_basis_expansion]
  apply Submodule.sum_mem
  intro p _
  by_cases hc : (∏ j, coefficient (p j) (U j)) = 0
  · simp [hc]
  · apply Submodule.smul_mem
    have houtp : ∀ j, j ∉ J → p j = 0 := by
      intro j hj
      have hne := (Finset.prod_ne_zero_iff.1 hc) j (Finset.mem_univ j)
      rw [hout j hj, ← pauli_zero, coefficient_pauli] at hne
      by_contra h
      exact hne (if_neg h)
    have hp : wordWeight p ≤ J.card := by
      apply Finset.card_le_card
      intro j hj
      have hne := (Finset.mem_filter.1 hj).2
      by_contra h
      exact hne (houtp j h)
    let P := pauliWordEquiv.symm p
    have hkernel : wordKernel p = PauliKernelTrace.pauliKernel P := by
      simpa only [P, Equiv.apply_symm_apply] using wordKernel_pauliWordEquiv P
    rw [hkernel]
    apply pauli_mem_detectedOperators C P
    have hwt : wordWeight p = P.wt := by
      simpa only [P, Equiv.apply_symm_apply] using wordWeight_pauliWordEquiv P
    omega

end

end MainTheory.KLTensorSupport
