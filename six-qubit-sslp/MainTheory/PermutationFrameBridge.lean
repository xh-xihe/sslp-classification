import MainTheory.PermutationProjectorBridge

/-!
# Orthonormal-frame closure under physical-qubit permutations

This constructs the intermediate frame needed before applying the six local
monomial factors of `CodeEquiv.LocalMonomial.act`.
-/

namespace MainTheory.PermutationFrameBridge

open scoped BigOperators ComplexConjugate

noncomputable section

theorem innerC_permAct {n : Nat} (σ : Equiv.Perm (Fin n))
    (psi phi : SS.State n ℂ) :
    SS.innerC (SixQubit.CodeEquiv.permAct σ psi)
        (SixQubit.CodeEquiv.permAct σ phi) = SS.innerC psi phi := by
  unfold SS.innerC SixQubit.CodeEquiv.permAct
  exact Equiv.sum_comp (SixQubit.CodeEquiv.permStrEquiv σ)
    (fun s => star (psi s) * phi s)

def permFrame {n K : Nat} (F : MainTheory.CodeSpec.OrthonormalFrame n K)
    (σ : Equiv.Perm (Fin n)) : MainTheory.CodeSpec.OrthonormalFrame n K where
  vec k := SixQubit.CodeEquiv.permAct σ (F.vec k)
  orthonormal := by
    intro k l
    rw [innerC_permAct]
    exact F.orthonormal k l

theorem permFrame_luEquivalent {n K : Nat}
    (F : MainTheory.CodeSpec.OrthonormalFrame n K)
    (σ : Equiv.Perm (Fin n)) :
    MainTheory.ClassificationLevels.LUEquivalent
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame F)
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame (permFrame F σ)) := by
  apply MainTheory.PermutationProjectorBridge.luEquivalent_of_permAct_frames
  intro k
  rfl

end

end MainTheory.PermutationFrameBridge
