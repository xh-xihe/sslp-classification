import MainTheory.BoundedProjectiveCliffordGroup
import MainTheory.SmallTransversalOrders

/-! The entire transversal logical group of a rank-two distance-three code below six qubits. -/

namespace MainTheory.SmallTransversalClifford

noncomputable section

open CodeSpec ClassificationLevels PauliKernelBTrace MainTheory.QuaternionCliffordMatrixBridge
  MainTheory.UnitaryAdjointRepresentation

theorem bool_unitary (M : Matrix Bool Bool ℂ)
    (hM : M.conjTranspose*M=1 ∧ M*M.conjTranspose=1) :
    IsOneQubitUnitary (M.submatrix finTwoEquiv finTwoEquiv) := by
  have hs : star (M.submatrix finTwoEquiv finTwoEquiv)=
      M.conjTranspose.submatrix finTwoEquiv finTwoEquiv := rfl
  constructor
  · rw [hs,Matrix.submatrix_mul_equiv, hM.1,Matrix.submatrix_one_equiv]
  · rw [hs,Matrix.submatrix_mul_equiv, hM.2,Matrix.submatrix_one_equiv]

theorem common_basis {n d : ℕ} (C : ExactCode n 2 d) (hd : 3≤d) (hn : n≤5) :
    ∃ B : Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ Q∈TransversalLogicalOrder.transversalLogicalGroup
        (A := fun _ : Fin n => Bool) (frameMatrix C.frame),IsClifford (B*Q*B⁻¹) := by
  apply MainTheory.BoundedProjectiveCliffordGroup.common_basis
  intro Q hQ
  obtain ⟨U,hU,hQ⟩ := hQ
  exact SmallTransversalOrders.bounded_order C hd hn
    (fun j => (U j).submatrix finTwoEquiv finTwoEquiv)
    (fun j => bool_unitary (U j) (hU j)) Q
    (by simpa only [QubitTransversalFinite.bool_tensor_eq,Matrix.submatrix] using hQ)

theorem minimum_length {n d : ℕ} (C : ExactCode n 2 d) (hd : 3≤d)
    (hno : ¬∃ B : Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ Q∈TransversalLogicalOrder.transversalLogicalGroup
        (A := fun _ : Fin n => Bool) (frameMatrix C.frame),IsClifford (B*Q*B⁻¹)) : 6≤n := by
  by_contra hn
  exact hno (common_basis C hd (by omega))

end

end MainTheory.SmallTransversalClifford
