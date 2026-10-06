import MainTheory.DiagonalAdjointOrder
import MainTheory.TransversalDiagonalization
import MainTheory.MinimumLengthOrderFive
import MainTheory.QMinBound
import MainTheory.SmallBetaValues
import MainTheory.QubitTransversalFinite

/-! Projective orders below six qubits, for literal arbitrary U(2) products. -/

namespace MainTheory.SmallTransversalOrders

open CodeSpec ClassificationLevels LocalTensorKernel PauliKernelBTrace
open UnitaryAdjointRepresentation

noncomputable section

variable {n d : ℕ}

theorem bounded_order (C : ExactCode n 2 d) (hd : 3 ≤ d) (hn : n ≤ 5)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (Q : Matrix.unitaryGroup (Fin 2) ℂ)
    (hQ : tensorKernel U * frameMatrix C.frame = frameMatrix C.frame * Q.val) :
    0 < orderOf (adjoint Q) ∧ orderOf (adjoint Q) ≤ 4 := by
  let C3 : ExactCode n 2 3 := {
    positiveRank := C.positiveRank
    frame := C.frame
    hasDistance := fun P hP => C.hasDistance P (by omega) }
  obtain ⟨C', u, a, _, hinter⟩ :=
    TransversalDiagonalization.exists_diagonal_normal_form C3 U hU Q.val hQ
  obtain ⟨g, hg⟩ := DiagonalAdjointOrder.normalized_intrinsic_order C'
    (by decide) u Q a hinter
  have hb5 : BinaryBeta.BetaBound 5 5 := by
    simpa only [SmallBetaValues.betaOf_five] using BetaExists.betaBound_betaOf 5
  have hbn : BinaryBeta.BetaBound n 5 := by
    intro s hs hsn A hA hdet
    exact hb5 s hs (le_trans hsn hn) A hA hdet
  obtain ⟨q, hqpos, hqle, _, hdiv⟩ :=
    QMinBound.d3_bound_same_class hbn (by decide) C' g
  rw [hg] at hdiv
  have hle : orderOf (adjoint Q) ≤ 5 := (Nat.le_of_dvd hqpos hdiv).trans hqle
  have hpos : 0 < orderOf (adjoint Q) := by
    by_contra hp
    have hz : orderOf (adjoint Q) = 0 := by omega
    rw [hz, zero_dvd_iff] at hdiv
    omega
  have hnot : orderOf (adjoint Q) ≠ 5 := by
    intro h5
    have hl := MinimumLengthOrderFive.minimum_length C hd U hU Q hQ h5
    omega
  exact ⟨hpos, by omega⟩

end

end MainTheory.SmallTransversalOrders
