import MainTheory.PhysicalIntrinsicBridge
import MainTheory.PhysicalConnectedScalar

namespace MainTheory.PhysicalComponentFactor

open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells
open MainTheory.PhysicalIntrinsicBridge

noncomputable section

variable {n : ℕ}

def logicalHom (P : CodeProjector n) :
    stabilizerSubgroup P →* IntrinsicProjectiveDiagonalLogicalGroup P :=
  (QuotientGroup.mk' (projectivelyTrivialSubgroup P)).comp (symmetryHom P)

theorem logicalHom_eq_one_of_scalar (P : CodeProjector n) (u : stabilizerSubgroup P)
    (z : Circle) (hu : operator u.val * P.kernel = (z : ℂ) • P.kernel) : logicalHom P u = 1 := by
  change QuotientGroup.mk (symmetryHom P u) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨(z : ℂ), Circle.coe_ne_zero z, ?_⟩
  intro ψ hψ
  have he := congrArg (fun A : OperatorKernel n => kernelAction A ψ) hu
  dsimp only at he
  rw [MainTheory.CodePreservingUnitary.kernelAction_mul] at he
  have hs : kernelAction ((z : ℂ) • P.kernel) ψ = (z : ℂ) • kernelAction P.kernel ψ := by
    funext x
    simp [kernelAction, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hs, show kernelAction P.kernel ψ = ψ from hψ] at he
  have hd := kernelAction_diagonalKernel (localPhase u.val) ψ
  rw [diagonalKernel_eq] at hd
  exact hd.symm.trans he

theorem connected_component_le_kernel {K d : ℕ}
    (C : MainTheory.CodeSpec.ExactCode n K d) (hd : 2 ≤ d) :
    Subgroup.connectedComponentOfOne (stabilizerSubgroup (CodeProjector.ofFrame C.frame)) ≤
      (logicalHom (CodeProjector.ofFrame C.frame)).ker := by
  intro u hu
  obtain ⟨z, hz⟩ := MainTheory.PhysicalRelativeAction.exact_code_connected_component_scalar C hd u hu
  exact logicalHom_eq_one_of_scalar _ u z hz

/-- The actual intrinsic logical action factors through the finite physical
component group, at the manuscript's distance-two hypothesis. -/
def componentFactor {K d : ℕ} (C : MainTheory.CodeSpec.ExactCode n K d) (hd : 2 ≤ d) :
    ((stabilizerSubgroup (CodeProjector.ofFrame C.frame)) ⧸
      Subgroup.connectedComponentOfOne (stabilizerSubgroup (CodeProjector.ofFrame C.frame))) →*
        IntrinsicProjectiveDiagonalLogicalGroup (CodeProjector.ofFrame C.frame) :=
  QuotientGroup.lift _ (logicalHom _) (connected_component_le_kernel C hd)

theorem componentFactor_mk {K d : ℕ} (C : MainTheory.CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (u : stabilizerSubgroup (CodeProjector.ofFrame C.frame)) :
    componentFactor C hd (QuotientGroup.mk u) = logicalHom (CodeProjector.ofFrame C.frame) u := rfl

end

end MainTheory.PhysicalComponentFactor
