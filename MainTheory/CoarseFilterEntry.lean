import MainTheory.CodeFiberBridge
import MainTheory.MaskRankBridge

/-!
# Entering the coarse affine-rank filter from a code

`CoarseFilter` reduces the 11,422 labelled pairs to 508 by discarding every
pair failing

  `rMin q ≤ min (maskAffineRank mask0) (maskAffineRank mask1)`,

and its soundness theorem `fullFiberCriterion_of_realization` says no genuine
code is discarded -- *given* a `PrimitiveLiftRealization`, whose `rank` field
must satisfy `maskAffineRank support = rank` for supports inside both fibres.
Nothing constructed one, and the reason is not plumbing.

The paper's `r` is the **affine** dimension of the actual supports
(`six:eq:ractual`: `r := affdim T_0 = affdim T_1 = rank Σ`), and its bound is
`q ≤ β_r` at that affine rank (`six:eq:qbetar`).  What this development proves
is the **linear**-rank version: `SixQubitSemanticEntrance.SupportedBitBasis`
takes raw bit rows, not differences, so `D3SparseRationalization`'s minor has
the size of the `ℝ`-linear rank of the support's Boolean points, which is the
affine rank or one more.

This file closes the half where that difference does not matter.  The
zero-residue fibre contains the all-zero word, so its affine and linear ranks
coincide (`MaskRankBridge.residueZeroMask_affineRank_eq_span`), and a linear
independence statement about the support is exactly what is needed.  The `q/m`
fibre does not contain the origin, and there the linear-rank bound gives one
less than the filter asks for; that half is not closed here, and is not papered
over.
-/

namespace MainTheory.CoarseFilterEntry

open MainTheory
open MainTheory.CodeFiberBridge
open MainTheory.MaskRankBridge
open MainTheory.OuterCompleteness
open MainTheory.SortedForm

noncomputable section

variable {C : CodeSpec.ExactCode 6 2 3}

/-- A word encoding a given six-bit string. -/
def wordOf (s : SS.BitString 6) : FinitePipeline.Word6 :=
  Classical.choose (exists_word_bitString s)

@[simp] theorem wordBitString_wordOf (s : SS.BitString 6) :
    wordBitString (wordOf s) = s :=
  Classical.choose_spec (exists_word_bitString s)

/-- The supported Boolean basis of a sorted normal form's first logical word,
read as pipeline words. -/
def basisWords (S : SortedNormalForm C) :
    Fin (SixQubitSemanticEntrance.supportedBitBasis (S.frame.vec 0)).rank →
      FinitePipeline.Word6 :=
  fun i => wordOf ((SixQubitSemanticEntrance.supportedBitBasis
    (S.frame.vec 0)).vertex i)

/-- Every basis word is supported, hence lies in the record's zero-residue
fibre. -/
theorem basisWords_inMask (S : SortedNormalForm C) (i) :
    FinitePipeline.InMask (recordFiberPair (recordOf S)).mask0
      (basisWords S i) := by
  refine support_mask0 S (basisWords S i) ?_
  rw [basisWords, wordBitString_wordOf]
  exact (SixQubitSemanticEntrance.supportedBitBasis
    (S.frame.vec 0)).vertex_supported i

/-- Their real Boolean points are linearly independent, by construction of the
supported basis. -/
theorem basisWords_independent (S : SortedNormalForm C) :
    LinearIndependent ℝ (fun i =>
      CodeAffineSpanBridge.bitPoint (wordBitString (basisWords S i))) := by
  have h := (SixQubitSemanticEntrance.supportedBitBasis
    (S.frame.vec 0)).independent
  have hfun : (fun i =>
      CodeAffineSpanBridge.bitPoint (wordBitString (basisWords S i))) =
      fun i => CodeAffineSpanBridge.bitPoint
        ((SixQubitSemanticEntrance.supportedBitBasis
          (S.frame.vec 0)).vertex i) := by
    funext i
    rw [basisWords, wordBitString_wordOf]
  rw [hfun]
  exact h

/-- **The zero-residue fibre of a code's record has affine rank at least the
support rank of its first logical word.**

This is the `S_0` half of the coarse filter's hypothesis, obtained from the
code itself rather than assumed.  Together with a bound `rMin q ≤ rank` -- the
arithmetic half, which is where the paper's affine-versus-linear rank question
lives -- it is `min` clause one of `six:eq:coarserank`. -/
theorem supportRank_le_maskAffineRank_mask0 (S : SortedNormalForm C) :
    (SixQubitSemanticEntrance.supportedBitBasis (S.frame.vec 0)).rank ≤
      AffineRankCertificate.maskAffineRank
        (recordFiberPair (recordOf S)).mask0 :=
  le_maskAffineRank_mask0 (recordOf S) (basisWords S)
    (basisWords_inMask S) (basisWords_independent S)

end

end MainTheory.CoarseFilterEntry
