-- A single dense-top, 64-pair resource probe for the polynomial checker.
import MainTheory.BinaryDetFast

namespace MainTheory.Generated.BinaryBetaReduced.FastDenseSliceProbe

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetFast

/-- Columns `(1,2,3,4,5,6)`, chosen because many top minors are nonzero. -/
def denseTop : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- The first sixteen entries of the widest `a = 0` slice.  It is a resource
probe, not an aggregate beta certificate. -/
theorem denseChunkZero : FastPairChunk denseTop 0 0 16 9 := by
  decide

end MainTheory.Generated.BinaryBetaReduced.FastDenseSliceProbe
