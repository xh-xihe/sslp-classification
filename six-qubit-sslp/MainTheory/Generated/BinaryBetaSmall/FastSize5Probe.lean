-- One near-widest resource probe for the low-overhead size-five checker.
-- The fixed codes 1,2,4 are linearly independent, so this does not obtain a
-- misleadingly cheap pass merely from a repeated or zero prefix row.
import MainTheory.BinaryDetFiveFast

namespace MainTheory.Generated.BinaryBetaSmall.FastSize5Probe

open MainTheory.BinaryDetLastRow
open MainTheory.BinaryBetaSmallSemantic
open MainTheory.BinaryDetFiveFast

/-- Twenty-eight closed prefixes (`d = 4,...,31`) in one ordinary-kernel
`decide` call.  This is a resource probe, not a complete size-five table. -/
theorem representativeSlice : FastLastCodeSlice 1 2 4 5 := by
  decide

/-- The slice can be consumed through the semantic bridge, demonstrated for
an arbitrary final five-bit row rather than only for a closed numeral. -/
theorem representativeSlice_semantic (d : BitVec 5)
    (hd : 4 <= d.toNat) :
    ReducedAtRow
      (prefixRowsMatrix ![
        BitVec.ofNat 5 1, BitVec.ofNat 5 2, BitVec.ofNat 5 4, d])
      (4 : Fin 5) 5 := by
  apply FastPrefixBound.toReducedAtRowBits
  have hdLt : d.toNat < 32 := by simpa using d.isLt
  have hs := representativeSlice.lookup hd hdLt
  simpa [BitVec.toNat_ofNat] using hs

end MainTheory.Generated.BinaryBetaSmall.FastSize5Probe
