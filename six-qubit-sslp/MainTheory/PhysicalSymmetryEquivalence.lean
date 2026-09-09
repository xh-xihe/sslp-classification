import MainTheory.PhysicalIntrinsicBridge
import Mathlib.Analysis.CStarAlgebra.Basic

namespace MainTheory.PhysicalIntrinsicBridge

open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells
open MainTheory.CodePreservingUnitary

noncomputable section

variable {n : ℕ}

theorem kernel_eq_of_action_eq (A B : OperatorKernel n)
    (h : ∀ ψ, kernelAction A ψ = kernelAction B ψ) : A = B := by
  ext x y
  simpa [kernelAction] using congrFun (h (fun z => if z = y then 1 else 0)) x

theorem projector_action_in_range (P : CodeProjector n) (ψ : SS.State n ℂ) :
    InProjectorRange P (kernelAction P.kernel ψ) := by
  change kernelAction P.kernel (kernelAction P.kernel ψ) = _
  rw [← kernelAction_mul, P.idempotent]

theorem compression_eq_of_maps_range (P : CodeProjector n) (W : OperatorKernel n)
    (h : ∀ ψ, InProjectorRange P ψ → InProjectorRange P (kernelAction W ψ)) :
    P.kernel * W * P.kernel = W * P.kernel := by
  apply kernel_eq_of_action_eq
  intro ψ
  simp only [kernelAction_mul]
  exact h _ (projector_action_in_range P ψ)

theorem operator_inv (u : Torus n) : operator u⁻¹ = star (operator u) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [operator, Matrix.star_apply, Matrix.diagonal_apply_eq, phase_inv]
    exact Circle.coe_inv_eq_conj (phase u x)
  · simp [operator, Matrix.star_apply, Matrix.diagonal, hxy, Ne.symm hxy]

theorem mem_stabilizer_of_preserves_range (P : CodeProjector n) (u : Torus n)
    (hu : PreservesProjectorRange P (localPhase u)) : u ∈ stabilizerSubgroup P := by
  have hf : P.kernel * operator u * P.kernel = operator u * P.kernel := by
    apply compression_eq_of_maps_range
    intro ψ hψ
    have he := kernelAction_diagonalKernel (localPhase u) ψ
    rw [diagonalKernel_eq] at he
    rw [he]
    exact hu.1 ψ hψ
  have hb : P.kernel * star (operator u) * P.kernel = star (operator u) * P.kernel := by
    apply compression_eq_of_maps_range
    intro ψ hψ
    have he := kernelAction_diagonalKernel (localPhase u⁻¹) ψ
    rw [diagonalKernel_eq, operator_inv, localPhase_inv] at he
    rw [he]
    exact hu.2 ψ hψ
  have hs := congrArg star hb
  simp only [star_mul, star_star, P.hermitian] at hs
  apply (mem_stabilizer_iff_commute P u).mpr
  rw [← hf]
  simpa only [Matrix.mul_assoc] using hs

def phaseTorus (v : LocalPhase n) : Torus n := fun j =>
  ⟨v j, mem_sphere_zero_iff_norm.mpr (CStarRing.norm_of_mem_unitary (v j).property)⟩

theorem localPhase_phaseTorus (v : LocalPhase n) : localPhase (phaseTorus v) = v := by
  funext j
  apply Subtype.ext
  rfl

/-- Every range-defined physical symmetry occurs in the topological matrix
stabilizer. Thus no symmetry is lost in the component-group factorization. -/
theorem symmetryHom_surjective (P : CodeProjector n) : Function.Surjective (symmetryHom P) := by
  intro v
  have hp : PreservesProjectorRange P (localPhase (phaseTorus v.val)) := by
    rw [localPhase_phaseTorus]
    exact v.property
  refine ⟨⟨phaseTorus v.val, mem_stabilizer_of_preserves_range P _ hp⟩, ?_⟩
  apply Subtype.ext
  exact localPhase_phaseTorus v.val

end

end MainTheory.PhysicalIntrinsicBridge
