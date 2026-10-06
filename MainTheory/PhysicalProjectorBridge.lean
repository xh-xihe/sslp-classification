import MainTheory.ClassificationLevels

/-!
# Covariance of frame projectors under explicit physical kernels

This leaf proves the matrix identity needed by the physical half of the
`CodeEquiv`-to-LU bridge.  If every vector of a frame is acted on by a kernel
`W`, then the new frame projector is exactly `W P W*`.  The statement is
purely algebraic; unitarity is needed only when the kernel is admitted as an
`ElementaryLU` generator.
-/

namespace MainTheory.PhysicalProjectorBridge

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Projector covariance for a pointwise transformed frame. -/
theorem projectorKernel_eq_conjugate_of_vec_eq_kernelAction {n K : Nat}
    (F G : MainTheory.CodeSpec.OrthonormalFrame n K)
    (W : MainTheory.ClassificationLevels.OperatorKernel n)
    (hvec : ∀ k,
      G.vec k = MainTheory.ClassificationLevels.kernelAction W (F.vec k)) :
    MainTheory.CodeSpec.projectorKernel G =
      MainTheory.ClassificationLevels.conjugateProjector W
        (MainTheory.ClassificationLevels.CodeProjector.ofFrame F) := by
  funext x y
  unfold MainTheory.CodeSpec.projectorKernel
  calc
    (∑ k, G.vec k x * star (G.vec k y)) =
        ∑ k, ∑ b, ∑ a,
          (W x a * F.vec k a) *
            (star (W y b) * star (F.vec k b)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hvec k]
      simp only [MainTheory.ClassificationLevels.kernelAction, star_sum,
        star_mul', Finset.mul_sum, Finset.sum_mul]
    _ = ∑ b, ∑ k, ∑ a,
          (W x a * F.vec k a) *
            (star (W y b) * star (F.vec k b)) := by
      exact Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ k,
          (W x a * F.vec k a) *
            (star (W y b) * star (F.vec k b)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ k,
          (W x a * (F.vec k a * star (F.vec k b))) *
            star (W y b) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = MainTheory.ClassificationLevels.conjugateProjector W
          (MainTheory.ClassificationLevels.CodeProjector.ofFrame F) x y := by
      simp only [MainTheory.ClassificationLevels.conjugateProjector,
        MainTheory.ClassificationLevels.CodeProjector.ofFrame,
        Matrix.mul_apply, Matrix.star_apply,
        MainTheory.CodeSpec.projectorKernel,
        Finset.mul_sum, Finset.sum_mul]

/-- A frame transformed by one certified one-qubit unitary is one explicit
level-(iv) LU step. -/
theorem luEquivalent_of_oneQubit_frames {n K : Nat}
    (F G : MainTheory.CodeSpec.OrthonormalFrame n K)
    (j : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : MainTheory.ClassificationLevels.IsOneQubitUnitary U)
    (hvec : ∀ k, G.vec k =
      MainTheory.ClassificationLevels.kernelAction
        (MainTheory.ClassificationLevels.oneQubitKernel j U) (F.vec k)) :
    MainTheory.ClassificationLevels.LUEquivalent
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame F)
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame G) := by
  apply MainTheory.ClassificationLevels.luEquivalent_of_oneQubit
    (MainTheory.ClassificationLevels.CodeProjector.ofFrame F)
    (MainTheory.ClassificationLevels.CodeProjector.ofFrame G) j U hU
  exact projectorKernel_eq_conjugate_of_vec_eq_kernelAction F G
    (MainTheory.ClassificationLevels.oneQubitKernel j U) hvec

end

end MainTheory.PhysicalProjectorBridge
