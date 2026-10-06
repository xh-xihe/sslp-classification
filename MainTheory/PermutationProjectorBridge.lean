import MainTheory.PhysicalProjectorBridge

/-!
# `CodeEquiv.permAct` at projector level

The direction of the permutation in a matrix kernel is easy to reverse by
accident.  This leaf proves explicitly that
`qubitPermutationKernel σ.symm` acts on amplitudes as `CodeEquiv.permAct σ`,
then lifts that equality to the level-(iv) projector relation.
-/

namespace MainTheory.PermutationProjectorBridge

noncomputable section

/-- Exact action convention for the computational-basis permutation kernel. -/
theorem kernelAction_qubitPermutationKernel {n : Nat}
    (σ : Equiv.Perm (Fin n)) (psi : SS.State n ℂ) :
    MainTheory.ClassificationLevels.kernelAction
        (MainTheory.ClassificationLevels.qubitPermutationKernel σ.symm) psi =
      SixQubit.CodeEquiv.permAct σ psi := by
  classical
  funext x
  unfold MainTheory.ClassificationLevels.kernelAction
  rw [Finset.sum_eq_single (SixQubit.CodeEquiv.permStr σ x)]
  · have hinv :
        SixQubit.CodeEquiv.permStr σ.symm
            (SixQubit.CodeEquiv.permStr σ x) = x :=
      (SixQubit.CodeEquiv.permStrEquiv σ).left_inv x
    simp [MainTheory.ClassificationLevels.qubitPermutationKernel,
      SixQubit.CodeEquiv.permAct, hinv]
  · intro y _ hy
    have hne : ¬x = SixQubit.CodeEquiv.permStr σ.symm y := by
      intro h
      have heq : SixQubit.CodeEquiv.permStr σ x = y := by
        rw [h]
        exact (SixQubit.CodeEquiv.permStrEquiv σ).right_inv y
      exact hy heq.symm
    simp [MainTheory.ClassificationLevels.qubitPermutationKernel, hne]
  · simp

/-- Applying `CodeEquiv.permAct σ` to every vector of a frame is precisely one
allowed physical-qubit-permutation step in `LUEquivalent`. -/
theorem luEquivalent_of_permAct_frames {n K : Nat}
    (F G : MainTheory.CodeSpec.OrthonormalFrame n K)
    (σ : Equiv.Perm (Fin n))
    (hvec : ∀ k, G.vec k = SixQubit.CodeEquiv.permAct σ (F.vec k)) :
    MainTheory.ClassificationLevels.LUEquivalent
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame F)
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame G) := by
  apply MainTheory.ClassificationLevels.luEquivalent_of_permutation
    (MainTheory.ClassificationLevels.CodeProjector.ofFrame F)
    (MainTheory.ClassificationLevels.CodeProjector.ofFrame G) σ.symm
  apply MainTheory.PhysicalProjectorBridge.projectorKernel_eq_conjugate_of_vec_eq_kernelAction
  intro k
  rw [hvec k]
  exact (kernelAction_qubitPermutationKernel σ (F.vec k)).symm

end

end MainTheory.PermutationProjectorBridge
