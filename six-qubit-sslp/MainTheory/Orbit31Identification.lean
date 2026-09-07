import MainTheory.Generated.FiniteRankDataShard67
import MainTheory.OuterCompleteness
import SixQubit.Orbit31

/-!
# The orbit-31 hand certificate and the pipeline pair are the same fibres

Orbit 31's LP affine dimension is certified twice by routes that never meet.
`SixQubit.Orbit31.momentPolytope_affine_dimension` computes it as `9` on the
thirty-two-coordinate normal form of the hand certificate, and
`Generated.OrbitTableSemantics31.lp_affine_dimension` computes it as `9` on
the full-fibre polytope of the pipeline pair `pair67`.  They agree
numerically, and until now nothing said they were about the same object: two
independent certifications rather than one, which is weaker than it looks,
since a coincidence of numbers is not an identification.

This file supplies the identification at the level that matters first -- the
fibres.  The hand certificate's two sixteen-element word sets `S0` and `S1`
are *exactly* the two masks of `pair67`, under the pipeline's own word
encoding `wordBitString w = fun i => w.1.testBit i`.  So the two arguments do
constrain the same pair of computational-basis supports, and orbit 31 is one
orbit rather than two objects that happen to share a number.

What is still missing is the second half: an affine isomorphism carrying
`SixQubit.Orbit31.momentPolytope`, a set of `Fin 32 -> R`, onto
`FiniteMomentLP.polytope pair67`, a set of `LabeledWord -> R` with ninety-six
forced-zero coordinates, so that the two dimension theorems become one.  The
index map is now determined -- it is the order-preserving enumeration of each
mask -- but the transport is not written, and the README still records the
duplication.
-/

namespace MainTheory.Orbit31Identification

open MainTheory.OuterCompleteness

set_option maxRecDepth 100000

/-- **The hand certificate's first fibre is the pipeline mask.** -/
theorem fibre0 (w : FinitePipeline.Word6) :
    FinitePipeline.InMask
        MainTheory.Generated.FiniteRankDataShard67.pair67.mask0 w ↔
      wordBitString w ∈ SixQubit.Orbit31.S0 := by
  revert w
  decide

/-- **The hand certificate's second fibre is the other pipeline mask.** -/
theorem fibre1 (w : FinitePipeline.Word6) :
    FinitePipeline.InMask
        MainTheory.Generated.FiniteRankDataShard67.pair67.mask1 w ↔
      wordBitString w ∈ SixQubit.Orbit31.S1 := by
  revert w
  decide

/-- **The two presentations of orbit 31 carry the same fibre pair.**

Neither mask is the other's: the two sixteen-element supports are distinct, so
this is an identification and not a relabelling that could have matched either
way. -/
theorem same_fibre_pair :
    (∀ w : FinitePipeline.Word6,
        FinitePipeline.InMask
          MainTheory.Generated.FiniteRankDataShard67.pair67.mask0 w ↔
        wordBitString w ∈ SixQubit.Orbit31.S0) ∧
    (∀ w : FinitePipeline.Word6,
        FinitePipeline.InMask
          MainTheory.Generated.FiniteRankDataShard67.pair67.mask1 w ↔
        wordBitString w ∈ SixQubit.Orbit31.S1) ∧
    MainTheory.Generated.FiniteRankDataShard67.pair67.mask0 ≠
      MainTheory.Generated.FiniteRankDataShard67.pair67.mask1 :=
  ⟨fibre0, fibre1, by decide⟩

end MainTheory.Orbit31Identification
