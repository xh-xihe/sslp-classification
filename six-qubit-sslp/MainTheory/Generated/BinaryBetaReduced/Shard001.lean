-- Second closed arithmetic leaf in the small triangular-table prototype.
import MainTheory.Generated.BinaryBetaReduced.Shard000

namespace MainTheory.Generated.BinaryBetaReduced.Shard001

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetCofactor
open MainTheory.Generated.BinaryBetaReduced.Shard000

/-- Pattern 45, first free row code 0, second free row code 1. -/
theorem pair000_001 :
    PairReducedBound explicitTop
      (rowOfBits (BitVec.ofNat 6 0))
      (rowOfBits (BitVec.ofNat 6 1)) 9 := by
  norm_num [PairReducedBound, negativeCoefficientSum,
    positiveCoefficientSum, lastRowCoefficient, rowOfBits, basisRow,
    bottomOfRows, bitZ, explicitTop,
    MainTheory.BinaryDetCircuit.laplace33Grouped,
    MainTheory.BinaryDetCircuit.minor3Poly,
    MainTheory.BinaryDetCircuit.minor3, Matrix.det_fin_three]

end MainTheory.Generated.BinaryBetaReduced.Shard001
