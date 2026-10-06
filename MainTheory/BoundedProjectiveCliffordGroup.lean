import MainTheory.QuaternionCliffordMatrixBridge
import MainTheory.QuaternionProjectiveSurjectivity

/-! A common Pauli basis for an entire subgroup of actual U(2) matrices. -/

namespace MainTheory.BoundedProjectiveCliffordGroup

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionProjectiveOrders MainTheory.QuaternionCliffordMatrixBridge
  MainTheory.UnitaryAdjointRepresentation

def spinProjective : unitary ℍ[ℝ] →* Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  adjoint.comp unitarySpin

theorem common_basis (G : Subgroup (Matrix.unitaryGroup (Fin 2) ℂ))
    (hG : ∀ Q∈G,0<orderOf (adjoint Q) ∧ orderOf (adjoint Q)≤4) :
    ∃ B : Matrix.unitaryGroup (Fin 2) ℂ,∀ Q∈G,IsClifford (B*Q*B⁻¹) := by
  let H := (G.map adjoint).comap spinProjective
  have hH : MainTheory.QuaternionQuarterPair.Bounded H := by
    intro q hq
    obtain ⟨Q,hQ,he⟩ := hq
    change adjoint Q=adjoint (unitarySpin q) at he
    obtain ⟨hp,hb⟩ := hG Q hQ
    rw [he] at hp hb
    exact allowed_of_projective_order q hp hb
  have hneg : (-1 : unitary ℍ[ℝ])∈H := by
    have he : adjoint (unitarySpin (-1 : unitary ℍ[ℝ]))=1 :=
      (projective_kernel _).2 (Or.inr rfl)
    change spinProjective (-1)∈G.map adjoint
    exact ⟨1,G.one_mem,by change adjoint 1=adjoint (unitarySpin (-1)); simpa using he.symm⟩
  obtain ⟨u,hu⟩ := MainTheory.QuaternionBoundedGroup.bounded_group H hH hneg
  refine ⟨unitarySpin u,?_⟩
  intro Q hQ
  obtain ⟨q,hq⟩ := MainTheory.QuaternionProjectiveSurjectivity.adjoint_surjective Q
  have hm : q∈H := by
    change adjoint (unitarySpin q)∈G.map adjoint
    exact ⟨Q,hQ,hq.symm⟩
  have he : adjoint (unitarySpin (conjugate u q))=
      adjoint (unitarySpin u*Q*(unitarySpin u)⁻¹) := by
    simp only [conjugate, map_mul, map_inv]
    rw [hq]
  exact clifford_of_same_adjoint _ _ he (normalizer_clifford _ (hu q hm))

end

end MainTheory.BoundedProjectiveCliffordGroup
