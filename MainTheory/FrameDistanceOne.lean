import MainTheory.LocalUnitaryKL

/-! # The minimal distance carried by every orthonormal code frame -/

namespace MainTheory.FrameDistanceOne

open CodeSpec ClassificationLevels LocalTensorKernel PauliTensorTransfer
open PauliTransferTwo PauliWordBridge PauliKernelTrace

noncomputable section

variable {n K : ℕ}

theorem pauliKernel_eq_one_of_weight_zero (P : SS.PauliString n) (hP : P.wt = 0) :
    pauliKernel P = 1 := by
  classical
  have hp (j : Fin n) : pauliWordEquiv P j = 0 := by
    by_contra hj
    have hc : 0 < wordWeight (pauliWordEquiv P) :=
      Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    rw [wordWeight_pauliWordEquiv, hP] at hc
    omega
  rw [← wordKernel_pauliWordEquiv]
  simp only [wordKernel, hp, pauli_zero, tensorKernel_one]

theorem hasDistance_one (F : OrthonormalFrame n K) : SS.HasDistance F.vec 1 := by
  classical
  intro P hP
  have hp : P.wt = 0 := by omega
  refine ⟨1, fun k l => ?_⟩
  rw [← kernelAction_pauliKernel, pauliKernel_eq_one_of_weight_zero P hp]
  have ha : kernelAction (1 : OperatorKernel n) (F.vec l) = F.vec l := by
    funext x
    simp [kernelAction, Matrix.one_apply]
  rw [ha]
  exact F.orthonormal k l

def codeOfFrame (F : OrthonormalFrame n K) (hK : 0 < K) : ExactCode n K 1 where
  positiveRank := hK
  frame := F
  hasDistance := hasDistance_one F

end

end MainTheory.FrameDistanceOne
