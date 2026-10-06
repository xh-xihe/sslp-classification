import MainTheory.CompletionCodeBridge
import MainTheory.Orbit3Target
import MainTheory.PauliExpectationReal

/-! # Norm and homogeneous target of the actual orbit-3 amplitude vector

The sqrt-free superposition has norm squared two. Thus the normalized target
equation is expressed homogeneously without dividing any individual amplitude.
-/

namespace MainTheory.Orbit3AmplitudeNormalization

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3Target
open MainTheory.PhysicalPauliCategories MainTheory.PauliExpectationReal
open SixQubit.ParityLogicalState SixQubit.CodeEquiv
open scoped BigOperators

noncomputable section

theorem superposition_norm (W : Encoder) :
    SS.innerC (superposition W.states) (superposition W.states) = 2 := by
  unfold SS.innerC superposition
  simp only [star_add, mul_add, add_mul, Finset.sum_add_distrib]
  change (SS.innerC (W.states 0) (W.states 0) + SS.innerC (W.states 1) (W.states 0)) +
    (SS.innerC (W.states 0) (W.states 1) + SS.innerC (W.states 1) (W.states 1)) = 2
  rw [MainTheory.CompletionCodeBridge.orthonormal W 0 0,
    MainTheory.CompletionCodeBridge.orthonormal W 1 0,
    MainTheory.CompletionCodeBridge.orthonormal W 0 1,
    MainTheory.CompletionCodeBridge.orthonormal W 1 1]
  norm_num

theorem normSq_sum (W : Encoder) :
    (∑ s : SS.BitString 6, Complex.normSq (superposition W.states s)) = 2 := by
  have h := superposition_norm W
  unfold SS.innerC at h
  simp_rw [star_mul_self, ← Complex.ofReal_sum] at h
  exact_mod_cast h

theorem homogeneous_target (W : Encoder) :
    (∑ s : SS.BitString 6, Complex.normSq (superposition W.states s)) *
      (∑ P : SS.PauliString 6, if category P = targetCategory then
        (SS.innerC (superposition W.states) (SS.pauliAct P (superposition W.states))).re ^ 2 else 0) =
      8 * (SS.MacWilliams.Aco W.states 3 / 4) := by
  simp_rw [← normSq_eq_square]
  rw [normSq_sum, target_sum_eq_Aco]
  ring

end
end MainTheory.Orbit3AmplitudeNormalization
