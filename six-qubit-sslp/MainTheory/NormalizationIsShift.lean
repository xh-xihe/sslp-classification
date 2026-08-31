import MainTheory.IntrinsicTransport
import MainTheory.D3NormalizedFreshPhase

/-!
# The normalization is the frame shift

`MainTheory/IntrinsicTransport.lean` transports the intrinsic group along
`shiftFrame F x0`.  The normalization the entrance actually performs is
`D3NormalizedFreshPhase.normalizedFrame`, and this file records that the two are
the same object, so the transport applies to the entrance's own data rather than
to an abstract shift that merely resembles it.

With `FiniteGeneratorResolution.span_eq` -- the eigenframe spans the same code as
the original frame -- and `IntrinsicTransport.diagonalSymmetryGroup_congr`, the
correspondence produced for the eigenframe reads off directly on the original
code.
-/

namespace MainTheory.NormalizationIsShift

open MainTheory.IntrinsicTransport
open MainTheory.LocalPhaseConjugation
open MainTheory.D3NormalizedFreshPhase

/-- **The normalized frame is the shifted eigenframe.**

Both are `fun k s => G.eigenFrame.vec k (SS.bxor s T.x0)`; recording the
equality keeps the transport from being applied to a lookalike. -/
theorem normalizedFrame_eq_shiftFrame
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    normalizedFrame T = shiftFrame G.eigenFrame T.x0 :=
  frame_ext rfl

/-- The symmetry group of the original code is the symmetry group of the
eigenframe, since they span the same space. -/
theorem symmetryGroup_eigenFrame
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    ClassificationLevels.diagonalSymmetryGroup
        (ClassificationLevels.CodeProjector.ofFrame C.frame)
      = ClassificationLevels.diagonalSymmetryGroup
        (ClassificationLevels.CodeProjector.ofFrame G.eigenFrame) :=
  diagonalSymmetryGroup_congr G.span_eq

/-- **The entrance's normalization is covered by the transport.**

A diagonal symmetry of the normalized code flips to one of the original code --
not merely of the eigenframe, by `symmetryGroup_eigenFrame`. -/
theorem mem_symmetryGroup_flip_normalized
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G)
    (u : ClassificationLevels.LocalPhase 6)
    (hu : u ∈ ClassificationLevels.diagonalSymmetryGroup
      (ClassificationLevels.CodeProjector.ofFrame (normalizedFrame T))) :
    flipPhase u T.x0 ∈ ClassificationLevels.diagonalSymmetryGroup
      (ClassificationLevels.CodeProjector.ofFrame C.frame) := by
  rw [symmetryGroup_eigenFrame G]
  refine mem_symmetryGroup_flip G.eigenFrame T.x0 u ?_
  rwa [← normalizedFrame_eq_shiftFrame T]

end MainTheory.NormalizationIsShift
