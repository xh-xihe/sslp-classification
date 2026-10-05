import MainTheory.SmallTransversalClifford
import MainTheory.CliffordProjectiveOrder

/-! Six is attained in the logical-basis-independent non-Clifford sense. -/

namespace MainTheory.SmallNonCliffordMinimum

noncomputable section

open CodeSpec ClassificationLevels PauliKernelBTrace MainTheory.QuaternionCliffordMatrixBridge
  MainTheory.UnitaryAdjointRepresentation

theorem fin_unitary (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : IsOneQubitUnitary M) :
    (M.submatrix finTwoEquiv.symm finTwoEquiv.symm).conjTranspose*
      (M.submatrix finTwoEquiv.symm finTwoEquiv.symm)=1 ∧
    (M.submatrix finTwoEquiv.symm finTwoEquiv.symm)*
      (M.submatrix finTwoEquiv.symm finTwoEquiv.symm).conjTranspose=1 := by
  have hs : (M.submatrix finTwoEquiv.symm finTwoEquiv.symm).conjTranspose=
      (star M).submatrix finTwoEquiv.symm finTwoEquiv.symm := rfl
  constructor
  · rw [hs,Matrix.submatrix_mul_equiv,hM.1,Matrix.submatrix_one_equiv]
  · rw [hs,Matrix.submatrix_mul_equiv,hM.2,Matrix.submatrix_one_equiv]

theorem canonical_attains :
    ¬∃ B : Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ Q∈TransversalLogicalOrder.transversalLogicalGroup
        (A := fun _ : Fin 6 => Bool) (frameMatrix MinimumLengthOrderFive.canonicalCode.frame),
        IsClifford (B*Q*B⁻¹) := by
  obtain ⟨U,Q,hU,hQ,horder⟩ := MinimumLengthOrderFive.canonical_attains
  have hm : Q∈TransversalLogicalOrder.transversalLogicalGroup
      (A := fun _ : Fin 6 => Bool) (frameMatrix MinimumLengthOrderFive.canonicalCode.frame) := by
    refine ⟨fun j => (U j).submatrix finTwoEquiv.symm finTwoEquiv.symm,
      fun j => fin_unitary (U j) (hU j),?_⟩
    simpa only [QubitTransversalFinite.bool_tensor_eq,Matrix.submatrix,
      Matrix.of_apply,Equiv.symm_apply_apply] using hQ
  rintro ⟨B,hB⟩
  exact MainTheory.CliffordProjectiveOrder.order_five_no_clifford_basis Q horder B (hB Q hm)

theorem minimum_attained :
    (∀ {n d : ℕ},∀ C : ExactCode n 2 d,3≤d →
      (¬∃ B : Matrix.unitaryGroup (Fin 2) ℂ,
        ∀ Q∈TransversalLogicalOrder.transversalLogicalGroup
          (A := fun _ : Fin n => Bool) (frameMatrix C.frame),IsClifford (B*Q*B⁻¹)) → 6≤n) ∧
    (¬∃ B : Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ Q∈TransversalLogicalOrder.transversalLogicalGroup
        (A := fun _ : Fin 6 => Bool) (frameMatrix MinimumLengthOrderFive.canonicalCode.frame),
        IsClifford (B*Q*B⁻¹)) :=
  ⟨fun C hd hno => SmallTransversalClifford.minimum_length C hd hno,canonical_attains⟩

end

end MainTheory.SmallNonCliffordMinimum
