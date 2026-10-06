import MainTheory.ClassificationLevels

/-!
# Logical-gauge invariance of the frame projector

`SixQubit.CodeEquiv.Equivalent` contains two conceptually different actions:
a physical local monomial/permutation, and a logical rephasing/interchange of
the two displayed codewords.  This leaf certifies the second part at the
matrix-kernel level: unit phases and a swap of an orthonormal frame do not
change its projector.

This is one required component of an eventual
`CodeEquiv.Equivalent → ClassificationLevels.LUEquivalent` bridge.  It does
not by itself claim that the physical `LocalMonomial` action has been expanded
as a word in `ClassificationLevels.ElementaryLU`.
-/

namespace MainTheory.CodeEquivProjectorBridge

open scoped BigOperators ComplexConjugate

noncomputable section

private def logicalSwapEquiv (sw : Bool) : Fin 2 ≃ Fin 2 where
  toFun := SixQubit.CodeEquiv.swapIdx sw
  invFun := SixQubit.CodeEquiv.swapIdx sw
  left_inv := SixQubit.CodeEquiv.swapIdx_involutive sw
  right_inv := SixQubit.CodeEquiv.swapIdx_involutive sw

/-- Rephasing the two logical words by unit scalars and optionally swapping
them leaves the projector kernel pointwise unchanged. -/
theorem projectorKernel_eq_of_logicalGauge {n : Nat}
    (F G : MainTheory.CodeSpec.OrthonormalFrame n 2)
    (lam : Fin 2 → ℂ) (sw : Bool)
    (hlam : ∀ k, Complex.normSq (lam k) = 1)
    (hvec : ∀ k,
      G.vec k = SixQubit.CodeEquiv.scal (lam k)
        (F.vec (SixQubit.CodeEquiv.swapIdx sw k))) :
    MainTheory.CodeSpec.projectorKernel G =
      MainTheory.CodeSpec.projectorKernel F := by
  funext x y
  unfold MainTheory.CodeSpec.projectorKernel
  calc
    (∑ k, G.vec k x * star (G.vec k y)) =
        ∑ k, F.vec (SixQubit.CodeEquiv.swapIdx sw k) x *
          star (F.vec (SixQubit.CodeEquiv.swapIdx sw k) y) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hvec k]
      change
        (lam k * F.vec (SixQubit.CodeEquiv.swapIdx sw k) x) *
            star (lam k * F.vec (SixQubit.CodeEquiv.swapIdx sw k) y) =
          F.vec (SixQubit.CodeEquiv.swapIdx sw k) x *
            star (F.vec (SixQubit.CodeEquiv.swapIdx sw k) y)
      simp only [star_mul']
      have hunit : lam k * star (lam k) = 1 := by
        simpa [mul_comm] using
          SixQubit.CodeEquiv.unit_of_normSq (hlam k)
      calc
        (lam k * F.vec (SixQubit.CodeEquiv.swapIdx sw k) x) *
              (star (lam k) *
                star (F.vec (SixQubit.CodeEquiv.swapIdx sw k) y)) =
            (lam k * star (lam k)) *
              (F.vec (SixQubit.CodeEquiv.swapIdx sw k) x *
                star (F.vec (SixQubit.CodeEquiv.swapIdx sw k) y)) := by ring
        _ = F.vec (SixQubit.CodeEquiv.swapIdx sw k) x *
              star (F.vec (SixQubit.CodeEquiv.swapIdx sw k) y) := by
            rw [hunit, one_mul]
    _ = ∑ k, F.vec k x * star (F.vec k y) := by
      exact Equiv.sum_comp (logicalSwapEquiv sw)
        (fun k => F.vec k x * star (F.vec k y))

/-- The same fact packaged at level (i)'s `CodeProjector` type. -/
theorem ofFrame_eq_of_logicalGauge {n : Nat}
    (F G : MainTheory.CodeSpec.OrthonormalFrame n 2)
    (lam : Fin 2 → ℂ) (sw : Bool)
    (hlam : ∀ k, Complex.normSq (lam k) = 1)
    (hvec : ∀ k,
      G.vec k = SixQubit.CodeEquiv.scal (lam k)
        (F.vec (SixQubit.CodeEquiv.swapIdx sw k))) :
    MainTheory.ClassificationLevels.CodeProjector.ofFrame G =
      MainTheory.ClassificationLevels.CodeProjector.ofFrame F := by
  apply MainTheory.ClassificationLevels.CodeProjector.ext
  exact projectorKernel_eq_of_logicalGauge F G lam sw hlam hvec

end

end MainTheory.CodeEquivProjectorBridge
