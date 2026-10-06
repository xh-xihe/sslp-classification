import MainTheory.ClassificationLevels

/-!
# `eq:code-preserving-unitary`

The manuscript defines a physical unitary to preserve the code by

  `U P U^dagger = P`,

and says it then induces a logical unitary on `Q`.

This repository carried no such predicate.  `CodeSpec.CodePreserving F U` says
only that the endomorphism `U` maps `codeSpan F` into itself -- it has no
unitarity hypothesis and is not a statement about the projector -- and
`ClassificationLevels.conjugateProjector` builds `W P W^dagger` but was used
only inside `ElementaryLU`, never as a predicate.  So the display had no Lean
object.

`PreservesProjector` is that predicate.  The two facts recorded with it are
the ones the manuscript uses: the code-preserving operators are closed under
composition and contain the identity, and a code-preserving *isometry* really
does map the code space into itself, which is the "induces a logical unitary"
clause.
-/

namespace MainTheory.CodePreservingUnitary

open MainTheory.ClassificationLevels

/-- **`eq:code-preserving-unitary`.**  A physical operator preserves the code
when conjugation by it fixes the projector. -/
def PreservesProjector {n : ℕ} (W : OperatorKernel n) (P : CodeProjector n) : Prop :=
  conjugateProjector W P = P.kernel

theorem preservesProjector_iff {n : ℕ} (W : OperatorKernel n) (P : CodeProjector n) :
    PreservesProjector W P ↔ W * P.kernel * star W = P.kernel := Iff.rfl

theorem preservesProjector_one {n : ℕ} (P : CodeProjector n) :
    PreservesProjector (1 : OperatorKernel n) P := by
  simp [PreservesProjector, conjugateProjector]

theorem preservesProjector_mul {n : ℕ} {W V : OperatorKernel n} {P : CodeProjector n}
    (hW : PreservesProjector W P) (hV : PreservesProjector V P) :
    PreservesProjector (W * V) P := by
  rw [preservesProjector_iff] at hW hV ⊢
  rw [star_mul]
  calc W * V * P.kernel * (star V * star W)
      = W * (V * P.kernel * star V) * star W := by noncomm_ring
    _ = W * P.kernel * star W := by rw [hV]
    _ = P.kernel := hW

/-- The kernel action is the matrix action, so it composes. -/
theorem kernelAction_mul {n : ℕ} (A B : OperatorKernel n) (phi : SS.State n ℂ) :
    kernelAction (A * B) phi = kernelAction A (kernelAction B phi) := by
  funext x
  simp only [kernelAction, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring

/-- A code-preserving operator commutes with the projector once it is an
isometry. -/
theorem commute_of_preservesProjector {n : ℕ} {W : OperatorKernel n}
    {P : CodeProjector n} (hW : PreservesProjector W P) (hu : star W * W = 1) :
    P.kernel * W = W * P.kernel := by
  rw [preservesProjector_iff] at hW
  calc P.kernel * W = (W * P.kernel * star W) * W := by rw [hW]
    _ = W * P.kernel * (star W * W) := by noncomm_ring
    _ = W * P.kernel := by rw [hu, mul_one]

/-- **"It then induces a logical unitary."**  A code-preserving isometry maps
the code space into itself. -/
theorem mapsTo_of_preservesProjector {n : ℕ} {W : OperatorKernel n}
    {P : CodeProjector n} (hW : PreservesProjector W P) (hu : star W * W = 1)
    (phi : SS.State n ℂ) (hphi : InProjectorRange P phi) :
    InProjectorRange P (kernelAction W phi) := by
  have hcomm := commute_of_preservesProjector hW hu
  unfold InProjectorRange at hphi ⊢
  rw [← kernelAction_mul, hcomm, kernelAction_mul, hphi]

end MainTheory.CodePreservingUnitary
